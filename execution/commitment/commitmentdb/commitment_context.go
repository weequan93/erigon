package commitmentdb

import (
	"bytes"
	"context"
	"crypto/sha256"
	"encoding/binary"
	"encoding/hex"
	"errors"
	"fmt"
	"math"
	"sort"
	"sync/atomic"
	"time"

	"github.com/erigontech/erigon-lib/common"
	"github.com/erigontech/erigon-lib/common/assert"
	"github.com/erigontech/erigon-lib/common/dbg"
	"github.com/erigontech/erigon-lib/common/empty"
	"github.com/erigontech/erigon-lib/crypto"
	"github.com/erigontech/erigon-lib/log/v3"
	"github.com/erigontech/erigon-lib/metrics"
	"github.com/erigontech/erigon/db/kv"
	"github.com/erigontech/erigon/db/kv/order"
	"github.com/erigontech/erigon/db/kv/rawdbv3"
	"github.com/erigontech/erigon/execution/commitment"
	"github.com/erigontech/erigon/execution/trie"
	"github.com/erigontech/erigon/execution/types/accounts"
	witnesstypes "github.com/erigontech/erigon/execution/types/witness"
)

var (
	mxCommitmentRunning = metrics.GetOrCreateGauge("domain_running_commitment")
	mxCommitmentTook    = metrics.GetOrCreateSummary("domain_commitment_took")
)

type sd interface {
	SetBlockNum(blockNum uint64)
	SetTxNum(blockNum uint64)
	AsGetter(tx kv.TemporalTx) kv.TemporalGetter
	AsPutDel(tx kv.TemporalTx) kv.TemporalPutDel
	StepSize() uint64
}

type SharedDomainsCommitmentContext struct {
	sharedDomains sd
	mainTtx       *TrieContext

	updates      *commitment.Updates
	patriciaTrie commitment.Trie
	justRestored atomic.Bool // set to true when commitment trie was just restored from snapshot

	trace bool

	debugLastPlainKeys atomic.Value // [][]byte
}

var debugDumpTouchedAccounts = dbg.EnvBool("ERIGON_BAD_ROOT_DUMP_TOUCHED_ACCOUNTS", false)
var debugBadRootCommitmentProbe = dbg.EnvBool("ERIGON_BAD_ROOT_DEBUG", false)
var debugBadRootProbeStorageKey = common.FromHex(dbg.EnvString("ERIGON_BAD_ROOT_PROBE_STORAGE_KEY", ""))

func commitmentHexPreview(v []byte, max int) string {
	if len(v) == 0 {
		return "0x"
	}
	if max <= 0 || len(v) <= max {
		return fmt.Sprintf("0x%x", v)
	}
	return fmt.Sprintf("0x%x...(+%d bytes)", v[:max], len(v)-max)
}

// debugUpdatesValueDigest returns a stable digest over current update keys and
// the values resolved from trie read context (accounts/storage/code), to help
// compare builder vs exec3 commitment inputs when keys-only digests match.
func (sdc *SharedDomainsCommitmentContext) debugUpdatesValueDigest(maxSamples int) (count uint64, digest string, samples []string) {
	if sdc == nil || sdc.mainTtx == nil || sdc.updates == nil {
		return 0, "", nil
	}
	if maxSamples < 0 {
		maxSamples = 0
	}

	keys := sdc.updates.DebugPlainKeys()
	sort.Slice(keys, func(i, j int) bool { return bytes.Compare(keys[i], keys[j]) < 0 })

	h := sha256.New()
	writeLen := func(n int) {
		var b [8]byte
		binary.BigEndian.PutUint64(b[:], uint64(n))
		_, _ = h.Write(b[:])
	}
	appendSample := func(s string) {
		if len(samples) < maxSamples {
			samples = append(samples, s)
		}
	}

	for _, key := range keys {
		count++

		domain := kv.AccountsDomain
		if len(key) > 20 {
			domain = kv.StorageDomain
		}
		val, step, readErr := sdc.mainTtx.readDomain(domain, key)
		if domain == kv.AccountsDomain {
			// If account read is empty, attempt code domain as a debug fallback.
			codeVal, codeStep, codeErr := sdc.mainTtx.readDomain(kv.CodeDomain, key)
			if codeErr == nil && len(codeVal) > 0 {
				domain = kv.CodeDomain
				val = codeVal
				step = codeStep
				readErr = nil
			}
		}

		writeLen(len(key))
		_, _ = h.Write(key)
		domainName := domain.String()
		writeLen(len(domainName))
		_, _ = h.Write([]byte(domainName))

		var stepBuf [8]byte
		binary.BigEndian.PutUint64(stepBuf[:], uint64(step))
		_, _ = h.Write(stepBuf[:])

		if readErr != nil {
			errText := readErr.Error()
			writeLen(len(errText))
			_, _ = h.Write([]byte(errText))
			appendSample(fmt.Sprintf("key=%x domain=%s step=%d err=%s", key, domainName, step, errText))
			continue
		}

		writeLen(len(val))
		_, _ = h.Write(val)
		appendSample(fmt.Sprintf(
			"key=%x domain=%s step=%d val_len=%d val=%s",
			key,
			domainName,
			step,
			len(val),
			commitmentHexPreview(val, 24),
		))
	}

	return count, fmt.Sprintf("%x", h.Sum(nil)), samples
}

func (sdc *SharedDomainsCommitmentContext) SetTrace(enable bool) {
	sdc.trace = enable
}

// Limits max txNum for read operations. If set to 0, all read operations will be from latest value.
// If domainOnly=true and txNum > 0, then read operations will be limited to domain files only.
func (sdc *SharedDomainsCommitmentContext) SetLimitReadAsOfTxNum(txNum uint64, domainOnly bool) {
	sdc.mainTtx.SetLimitReadAsOfTxNum(txNum, domainOnly)
}

func NewSharedDomainsCommitmentContext(sd sd, tx kv.TemporalTx, mode commitment.Mode, trieVariant commitment.TrieVariant, tmpDir string) *SharedDomainsCommitmentContext {
	ctx := &SharedDomainsCommitmentContext{
		sharedDomains: sd,
	}

	ctx.patriciaTrie, ctx.updates = commitment.InitializeTrieAndUpdates(trieVariant, mode, tmpDir)
	trieCtx := &TrieContext{
		roTtx:  tx,
		getter: sd.AsGetter(tx),
		putter: sd.AsPutDel(tx),

		stepSize: sd.StepSize(),
	}
	ctx.mainTtx = trieCtx
	ctx.patriciaTrie.ResetContext(trieCtx)
	return ctx
}

func (sdc *SharedDomainsCommitmentContext) Close() {
	sdc.updates.Close()
}

func (sdc *SharedDomainsCommitmentContext) Reset() {
	if !sdc.justRestored.Load() {
		sdc.patriciaTrie.Reset()
	}
}
func (sdc *SharedDomainsCommitmentContext) ClearRam() {
	sdc.updates.Reset()
	sdc.Reset()
}

func (sdc *SharedDomainsCommitmentContext) SetTxNum(txNum uint64) {
	sdc.mainTtx.txNum = txNum
}

func (sdc *SharedDomainsCommitmentContext) KeysCount() uint64 {
	return sdc.updates.Size()
}

func (sdc *SharedDomainsCommitmentContext) Trie() commitment.Trie {
	return sdc.patriciaTrie
}

// TouchKey marks plainKey as updated and applies different fn for different key types
// (different behaviour for Code, Account and Storage key modifications).
func (sdc *SharedDomainsCommitmentContext) TouchKey(d kv.Domain, key string, val []byte) {
	if sdc.updates.Mode() == commitment.ModeDisabled {
		return
	}

	switch d {
	case kv.AccountsDomain:
		sdc.updates.TouchPlainKey(key, val, sdc.updates.TouchAccount)
	case kv.CodeDomain:
		sdc.updates.TouchPlainKey(key, val, sdc.updates.TouchCode)
	case kv.StorageDomain:
		sdc.updates.TouchPlainKey(key, val, sdc.updates.TouchStorage)
	//case kv.CommitmentDomain, kv.ReceiptDomain:
	default:
		//panic(fmt.Errorf("TouchKey: unknown domain %s", d))
	}
}

func (sdc *SharedDomainsCommitmentContext) Witness(ctx context.Context, codeReads map[common.Hash]witnesstypes.CodeWithHash, expectedRoot []byte, logPrefix string) (proofTrie *trie.Trie, rootHash []byte, err error) {
	hexPatriciaHashed, ok := sdc.Trie().(*commitment.HexPatriciaHashed)
	if ok {
		return hexPatriciaHashed.GenerateWitness(ctx, sdc.updates, codeReads, expectedRoot, logPrefix)
	}

	return nil, nil, errors.New("shared domains commitment context doesn't have HexPatriciaHashed")
}

// Evaluates commitment for gathered updates.
func (sdc *SharedDomainsCommitmentContext) ComputeCommitment(ctx context.Context, saveState bool, blockNum uint64, txNum uint64, logPrefix string) (rootHash []byte, err error) {
	mxCommitmentRunning.Inc()
	defer mxCommitmentRunning.Dec()
	defer func(s time.Time) { mxCommitmentTook.ObserveDuration(s) }(time.Now())

	updateCount := sdc.updates.Size()
	if debugBadRootCommitmentProbe && blockNum >= 33 {
		var (
			hasTrieCtx            bool
			ctxTxNum              uint64
			ctxLimitReadAsOfTxNum uint64
			ctxWithHistory        bool
			probeDomain           string
			probeKeyHex           string
			probeValLen           int
			probeValPreview       string
			probeStep             kv.Step
			probeReadErr          error
			probeAsOfOK           bool
			probeAsOfLen          int
			probeAsOfPreview      string
			probeAsOfErr          error
			probeLatestLen        int
			probeLatestPreview    string
			probeLatestStep       kv.Step
			probeLatestErr        error
			updatesDigestCount    uint64
			updatesDigest         string
			updatesDigestSamples  []string
			updatesValueCount     uint64
			updatesValueDigest    string
			updatesValueSamples   []string
		)

		ctxTxNum, ctxLimitReadAsOfTxNum, ctxWithHistory, hasTrieCtx = sdc.DebugReadContext()
		updatesDigestCount, updatesDigest, updatesDigestSamples = sdc.updates.DebugDigest(64)
		updatesValueCount, updatesValueDigest, updatesValueSamples = sdc.debugUpdatesValueDigest(64)
		if hasTrieCtx {
			accountKey, storageKey := probePlainKeys(sdc.updates.DebugPlainKeys())
			targetDomain := kv.AccountsDomain
			var targetKey []byte
			targetChosen := false
			switch {
			case len(debugBadRootProbeStorageKey) > 0:
				targetDomain = kv.StorageDomain
				targetKey = debugBadRootProbeStorageKey
				targetChosen = true
			case updateCount > 0 && len(storageKey) > 0:
				targetDomain = kv.StorageDomain
				targetKey = storageKey
				targetChosen = true
			case updateCount > 0 && len(accountKey) > 0:
				targetDomain = kv.AccountsDomain
				targetKey = accountKey
				targetChosen = true
			}
			if targetChosen && len(targetKey) > 0 {
				probeDomain = targetDomain.String()
				probeKeyHex = hex.EncodeToString(targetKey)
				probeVal, step, readErr := sdc.mainTtx.readDomain(targetDomain, targetKey)
				probeStep = step
				probeReadErr = readErr
				probeValLen = len(probeVal)
				probeValPreview = commitmentHexPreview(probeVal, 32)
				if sdc.mainTtx.roTtx != nil {
					asOfVal, asOfOK, asOfErr := sdc.mainTtx.roTtx.GetAsOf(targetDomain, targetKey, txNum)
					probeAsOfOK = asOfOK
					probeAsOfErr = asOfErr
					probeAsOfLen = len(asOfVal)
					probeAsOfPreview = commitmentHexPreview(asOfVal, 32)

					latestVal, latestStep, latestErr := sdc.mainTtx.roTtx.GetLatest(targetDomain, targetKey)
					probeLatestErr = latestErr
					probeLatestStep = latestStep
					probeLatestLen = len(latestVal)
					probeLatestPreview = commitmentHexPreview(latestVal, 32)
				}
			}
		}

		log.Warn("commitment compute context",
			"block", blockNum,
			"tx_num_arg", txNum,
			"log_prefix", logPrefix,
			"update_count", updateCount,
			"ctx_has_trie", hasTrieCtx,
			"ctx_txnum", ctxTxNum,
			"ctx_limit_read_as_of_txnum", ctxLimitReadAsOfTxNum,
			"ctx_with_history", ctxWithHistory,
			"probe_domain", probeDomain,
			"probe_key", probeKeyHex,
			"probe_step", probeStep,
			"probe_val_len", probeValLen,
			"probe_val_preview", probeValPreview,
			"probe_read_err", probeReadErr,
			"probe_asof_ok", probeAsOfOK,
			"probe_asof_len", probeAsOfLen,
			"probe_asof_preview", probeAsOfPreview,
			"probe_asof_err", probeAsOfErr,
			"probe_latest_step", probeLatestStep,
			"probe_latest_len", probeLatestLen,
			"probe_latest_preview", probeLatestPreview,
			"probe_latest_err", probeLatestErr,
			"updates_digest_count", updatesDigestCount,
			"updates_digest", updatesDigest,
			"updates_digest_samples", updatesDigestSamples,
			"updates_value_count", updatesValueCount,
			"updates_value_digest", updatesValueDigest,
			"updates_value_samples", updatesValueSamples,
		)
	}
	if sdc.trace {
		start := time.Now()
		defer func() {
			log.Trace("ComputeCommitment", "block", blockNum, "keys", common.PrettyCounter(updateCount), "mode", sdc.updates.Mode(), "spent", time.Since(start))
		}()
	}
	if debugDumpTouchedAccounts && updateCount > 0 {
		sdc.debugLastPlainKeys.Store(sdc.updates.DebugPlainKeys())
	}
	if updateCount == 0 {
		rootHash, err = sdc.patriciaTrie.RootHash()
		return rootHash, err
	}

	// data accessing functions should be set when domain is opened/shared context updated
	sdc.patriciaTrie.SetTrace(sdc.trace)
	sdc.Reset()

	rootHash, err = sdc.patriciaTrie.Process(ctx, sdc.updates, logPrefix)
	if err != nil {
		return nil, err
	}
	sdc.justRestored.Store(false)

	if saveState {
		if err = sdc.encodeAndStoreCommitmentState(blockNum, txNum, rootHash); err != nil {
			return nil, err
		}
	}

	return rootHash, err
}

type noopTemporalPutDel struct{}

func (noopTemporalPutDel) DomainPut(kv.Domain, []byte, []byte, uint64, []byte, kv.Step) error {
	return nil
}
func (noopTemporalPutDel) DomainDel(kv.Domain, []byte, uint64, []byte, kv.Step) error { return nil }
func (noopTemporalPutDel) DomainDelPrefix(kv.Domain, []byte, uint64) error            { return nil }

// DebugRootHash computes the commitment root for the current updates without mutating the live context.
// Intended for debug-only use; it snapshots trie state, runs a temporary commitment, then restores.
func (sdc *SharedDomainsCommitmentContext) DebugRootHash(ctx context.Context, logPrefix string) (rootHash []byte, err error) {
	if sdc == nil || sdc.patriciaTrie == nil {
		return nil, errors.New("commitment context is not initialized")
	}
	if sdc.mainTtx == nil {
		return nil, errors.New("commitment context is missing trie context")
	}
	if sdc.updates == nil || sdc.updates.Size() == 0 {
		return sdc.patriciaTrie.RootHash()
	}

	snapshot := sdc.updates.DebugSnapshot()
	if snapshot == nil || snapshot.Size() == 0 {
		return sdc.patriciaTrie.RootHash()
	}
	defer snapshot.Close()

	state, err := sdc.encodeCommitmentState(0, sdc.mainTtx.txNum)
	if err != nil {
		return nil, err
	}

	prevPutter := sdc.mainTtx.putter
	prevJustRestored := sdc.justRestored.Load()
	sdc.mainTtx.putter = noopTemporalPutDel{}

	rootHash, err = func() ([]byte, error) {
		sdc.patriciaTrie.SetTrace(sdc.trace)
		sdc.Reset()
		return sdc.patriciaTrie.Process(ctx, snapshot, logPrefix)
	}()

	restoreErr := func() error {
		_, _, err := sdc.restorePatriciaState(state)
		return err
	}()
	sdc.justRestored.Store(prevJustRestored)
	sdc.mainTtx.putter = prevPutter

	if err == nil && restoreErr != nil {
		err = restoreErr
	} else if err != nil && restoreErr != nil {
		log.Warn("mdbx-migrate debug: failed to restore commitment state", "err", restoreErr)
	}

	return rootHash, err
}

// DebugPlainKeys returns a snapshot of current plain keys tracked by updates.
func (sdc *SharedDomainsCommitmentContext) DebugPlainKeys() [][]byte {
	if sdc == nil || sdc.updates == nil {
		return nil
	}
	snapshot := sdc.updates.DebugSnapshot()
	if snapshot == nil {
		return nil
	}
	defer snapshot.Close()
	return snapshot.DebugPlainKeys()
}

// DebugLastPlainKeys returns the most recent plain keys snapshot captured during ComputeCommitment.
func (sdc *SharedDomainsCommitmentContext) DebugLastPlainKeys() [][]byte {
	if sdc == nil {
		return nil
	}
	if v := sdc.debugLastPlainKeys.Load(); v != nil {
		return v.([][]byte)
	}
	return nil
}

// DebugReadContext returns current trie read context details used by commitment reads.
func (sdc *SharedDomainsCommitmentContext) DebugReadContext() (txNum uint64, limitReadAsOfTxNum uint64, withHistory bool, ok bool) {
	if sdc == nil || sdc.mainTtx == nil {
		return 0, 0, false, false
	}
	return sdc.mainTtx.txNum, sdc.mainTtx.limitReadAsOfTxNum, sdc.mainTtx.withHistory, true
}

// DebugCurrentRootHash returns the trie root for the current in-memory trie state.
func (sdc *SharedDomainsCommitmentContext) DebugCurrentRootHash() ([]byte, error) {
	if sdc == nil || sdc.patriciaTrie == nil {
		return nil, errors.New("commitment context is not initialized")
	}
	return sdc.patriciaTrie.RootHash()
}

// RestoreLatestCommitmentState restores trie state from the latest encoded
// commitment state available in the commitment domain (including in-memory writes).
// Returns restored block/tx numbers when a state exists.
func (sdc *SharedDomainsCommitmentContext) RestoreLatestCommitmentState() (blockNum uint64, txNum uint64, restored bool, err error) {
	if sdc == nil || sdc.mainTtx == nil || sdc.patriciaTrie == nil {
		return 0, 0, false, errors.New("commitment context is not initialized")
	}
	state, _, err := sdc.mainTtx.Branch(KeyCommitmentState)
	if err != nil {
		return 0, 0, false, err
	}
	if len(state) == 0 {
		return 0, 0, false, nil
	}
	blockNum, txNum, err = sdc.restorePatriciaState(state)
	if err != nil {
		return 0, 0, false, err
	}
	return blockNum, txNum, true, nil
}

// RestoreLatestCommitmentStateFromTx restores trie state from the latest
// commitment state available in the provided temporal tx (raw DB view, without
// SharedDomains RAM overlay). Returns restored block/tx numbers and root hash.
func (sdc *SharedDomainsCommitmentContext) RestoreLatestCommitmentStateFromTx(tx kv.TemporalTx) (blockNum uint64, txNum uint64, rootHash []byte, restored bool, err error) {
	if sdc == nil || sdc.mainTtx == nil || sdc.patriciaTrie == nil {
		return 0, 0, nil, false, errors.New("commitment context is not initialized")
	}
	if tx == nil {
		return 0, 0, nil, false, errors.New("restore commitment state: temporal tx is nil")
	}
	state, _, err := tx.GetLatest(kv.CommitmentDomain, KeyCommitmentState)
	if err != nil {
		return 0, 0, nil, false, err
	}
	if len(state) == 0 {
		return 0, 0, nil, false, nil
	}
	blockNum, txNum, err = sdc.restorePatriciaState(state)
	if err != nil {
		return 0, 0, nil, false, err
	}
	rootHash, err = sdc.patriciaTrie.RootHash()
	if err != nil {
		return 0, 0, nil, false, err
	}
	return blockNum, txNum, rootHash, true, nil
}

// DebugStateRootFromEncoded decodes a persisted commitment state payload and returns
// the corresponding trie root, restoring the previous in-memory trie state afterward.
func (sdc *SharedDomainsCommitmentContext) DebugStateRootFromEncoded(value []byte) (blockNum uint64, txNum uint64, rootHash []byte, err error) {
	if sdc == nil || sdc.mainTtx == nil || sdc.patriciaTrie == nil {
		return 0, 0, nil, errors.New("commitment context is not initialized")
	}

	prevJustRestored := sdc.justRestored.Load()
	prevState, err := sdc.encodeCommitmentState(0, sdc.mainTtx.txNum)
	if err != nil {
		return 0, 0, nil, err
	}

	defer func() {
		_, _, restoreErr := sdc.restorePatriciaState(prevState)
		sdc.justRestored.Store(prevJustRestored)
		if err == nil && restoreErr != nil {
			err = fmt.Errorf("restore previous trie state: %w", restoreErr)
		}
	}()

	blockNum, txNum, err = sdc.restorePatriciaState(value)
	if err != nil {
		return 0, 0, nil, err
	}
	rootHash, err = sdc.patriciaTrie.RootHash()
	if err != nil {
		return 0, 0, nil, err
	}
	return blockNum, txNum, rootHash, nil
}

func probePlainKeys(plainKeys [][]byte) (accountKey []byte, storageKey []byte) {
	for _, key := range plainKeys {
		if len(key) == 20 && len(accountKey) == 0 {
			accountKey = append([]byte(nil), key...)
		}
		if len(key) > 20 && len(storageKey) == 0 {
			storageKey = append([]byte(nil), key...)
		}
		if len(accountKey) > 0 && len(storageKey) > 0 {
			break
		}
	}
	return accountKey, storageKey
}

// by that key stored latest root hash and tree state
const keyCommitmentStateS = "state"

var KeyCommitmentState = []byte(keyCommitmentStateS)

var ErrBehindCommitment = errors.New("behind commitment")

func _decodeTxBlockNums(v []byte) (txNum, blockNum uint64) {
	return binary.BigEndian.Uint64(v), binary.BigEndian.Uint64(v[8:16])
}

// LatestCommitmentState searches for last encoded state for CommitmentContext.
// Found value does not become current state.
func (sdc *SharedDomainsCommitmentContext) LatestCommitmentState() (blockNum, txNum uint64, state []byte, err error) {
	if sdc.patriciaTrie.Variant() != commitment.VariantHexPatriciaTrie && sdc.patriciaTrie.Variant() != commitment.VariantConcurrentHexPatricia {
		return 0, 0, nil, errors.New("state storing is only supported hex patricia trie")
	}
	state, _, err = sdc.mainTtx.Branch(KeyCommitmentState)
	if err != nil {
		return 0, 0, nil, err
	}
	if len(state) < 16 {
		return 0, 0, nil, nil
	}

	txNum, blockNum = _decodeTxBlockNums(state)
	return blockNum, txNum, state, nil
}

// enable concurrent commitment if we are using concurrent patricia trie and this trie diverges on very top (first branch is straight at nibble 0)
func (sdc *SharedDomainsCommitmentContext) enableConcurrentCommitmentIfPossible() error {
	if pt, ok := sdc.patriciaTrie.(*commitment.ConcurrentPatriciaHashed); ok {
		nextConcurrent, err := pt.CanDoConcurrentNext()
		if err != nil {
			return err
		}
		sdc.updates.SetConcurrentCommitment(nextConcurrent)
	}
	return nil
}

// SeekCommitment searches for last encoded state from DomainCommitted
// and if state found, sets it up to current domain
func (sdc *SharedDomainsCommitmentContext) SeekCommitment(ctx context.Context, tx kv.TemporalTx) (blockNum, txNum uint64, ok bool, err error) {
	_, _, state, err := sdc.LatestCommitmentState()
	if err != nil {
		return 0, 0, false, err
	}
	if state != nil {
		blockNum, txNum, err = sdc.restorePatriciaState(state)
		if err != nil {
			return 0, 0, false, err
		}
		if blockNum > 0 {
			lastBn, _, err := rawdbv3.TxNums.Last(tx)
			if err != nil {
				return 0, 0, false, err
			}
			if lastBn < blockNum {
				return 0, 0, false, fmt.Errorf("%w: TxNums index is at block %d and behind commitment %d", ErrBehindCommitment, lastBn, blockNum)
			}
		}
		sdc.sharedDomains.SetBlockNum(blockNum)
		sdc.sharedDomains.SetTxNum(txNum)
		if err = sdc.enableConcurrentCommitmentIfPossible(); err != nil {
			return 0, 0, false, err
		}
		return blockNum, txNum, true, nil
	}
	// handle case when we have no commitment, but have executed blocks
	bnBytes, err := tx.GetOne(kv.SyncStageProgress, []byte("Execution")) //TODO: move stages to erigon-lib
	if err != nil {
		return 0, 0, false, err
	}
	if len(bnBytes) == 8 {
		blockNum = binary.BigEndian.Uint64(bnBytes)
		txNum, err = rawdbv3.TxNums.Max(tx, blockNum)
		if err != nil {
			return 0, 0, false, err
		}
	}
	sdc.sharedDomains.SetBlockNum(blockNum)
	sdc.sharedDomains.SetTxNum(txNum)
	if blockNum == 0 && txNum == 0 {
		return 0, 0, true, nil
	}
	//
	//newRh, err := sdc.rebuildCommitment(ctx, tx, blockNum, txNum)
	//if err != nil {
	//	return 0, 0, false, err
	//}
	//if bytes.Equal(newRh, empty.RootHash.Bytes()) {
	//	sdc.sharedDomains.SetBlockNum(0)
	//	sdc.sharedDomains.SetTxNum(0)
	//	return 0, 0, false, err
	//}
	//if sdc.trace {
	//	fmt.Printf("rebuilt commitment %x bn=%d txn=%d\n", newRh, blockNum, txNum)
	//}
	if err = sdc.enableConcurrentCommitmentIfPossible(); err != nil {
		return 0, 0, false, err
	}
	return blockNum, txNum, true, nil
}

// encodes current trie state and saves it in SharedDomains
func (sdc *SharedDomainsCommitmentContext) encodeAndStoreCommitmentState(blockNum, txNum uint64, rootHash []byte) error {
	if sdc.mainTtx == nil {
		return errors.New("store commitment state: AggregatorContext is not initialized")
	}
	encodedState, err := sdc.encodeCommitmentState(blockNum, txNum)
	if err != nil {
		return err
	}
	prevState, prevStep, err := sdc.mainTtx.Branch(KeyCommitmentState)
	if err != nil {
		return err
	}
	if len(prevState) == 0 && prevState != nil {
		prevState = nil
	}
	// state could be equal but txnum/blocknum could be different.
	// We do skip only full matches
	if bytes.Equal(prevState, encodedState) {
		//fmt.Printf("[commitment] skip store txn %d block %d (prev b=%d t=%d) rh %x\n",
		//	binary.BigEndian.Uint64(prevState[8:16]), binary.BigEndian.Uint64(prevState[:8]), dc.ht.iit.txNum, blockNum, rh)
		return nil
	}

	log.Debug("[commitment] store state", "block", blockNum, "txNum", txNum, "rootHash", hex.EncodeToString(rootHash))
	return sdc.mainTtx.PutBranch(KeyCommitmentState, encodedState, prevState, prevStep)
}

// Encodes current trie state and returns it
func (sdc *SharedDomainsCommitmentContext) encodeCommitmentState(blockNum, txNum uint64) ([]byte, error) {
	var state []byte
	var err error

	switch trie := (sdc.patriciaTrie).(type) {
	case *commitment.HexPatriciaHashed:
		state, err = trie.EncodeCurrentState(nil)
		if err != nil {
			return nil, err
		}
	case *commitment.ConcurrentPatriciaHashed:
		state, err = trie.RootTrie().EncodeCurrentState(nil)
		if err != nil {
			return nil, err
		}
	default:
		return nil, fmt.Errorf("unsupported state storing for patricia trie type: %T", sdc.patriciaTrie)
	}

	cs := &commitmentState{trieState: state, blockNum: blockNum, txNum: txNum}
	encoded, err := cs.Encode()
	if err != nil {
		return nil, err
	}
	return encoded, nil
}

// After commitment state is retored, method .Reset() should NOT be called until new updates.
// Otherwise state should be restorePatriciaState()d again.
func (sdc *SharedDomainsCommitmentContext) restorePatriciaState(value []byte) (uint64, uint64, error) {
	cs := new(commitmentState)
	if err := cs.Decode(value); err != nil {
		if len(value) > 0 {
			return 0, 0, fmt.Errorf("failed to decode previous stored commitment state: %w", err)
		}
		// nil value is acceptable for SetState and will reset trie
	}
	tv := sdc.patriciaTrie.Variant()

	var hext *commitment.HexPatriciaHashed
	if tv == commitment.VariantHexPatriciaTrie {
		var ok bool
		hext, ok = sdc.patriciaTrie.(*commitment.HexPatriciaHashed)
		if !ok {
			return 0, 0, errors.New("cannot typecast hex patricia trie")
		}
	}
	if tv == commitment.VariantConcurrentHexPatricia {
		phext, ok := sdc.patriciaTrie.(*commitment.ConcurrentPatriciaHashed)
		if !ok {
			return 0, 0, errors.New("cannot typecast parallel hex patricia trie")
		}
		hext = phext.RootTrie()
	}
	if tv == commitment.VariantBinPatriciaTrie || hext == nil {
		return 0, 0, errors.New("state storing is only supported hex patricia trie")
	}

	if err := hext.SetState(cs.trieState); err != nil {
		return 0, 0, fmt.Errorf("failed restore state : %w", err)
	}
	sdc.justRestored.Store(true) // to prevent double reset
	if sdc.trace {
		rootHash, err := hext.RootHash()
		if err != nil {
			return 0, 0, fmt.Errorf("failed to get root hash after state restore: %w", err)
		}
		log.Debug(fmt.Sprintf("[commitment] restored state: block=%d txn=%d rootHash=%x\n", cs.blockNum, cs.txNum, rootHash))
	}
	return cs.blockNum, cs.txNum, nil
}

// Dummy way to rebuild commitment. Dummy because works for small state only.
// To rebuild commitment correctly for any state size - use RebuildCommitmentFiles.
func (sdc *SharedDomainsCommitmentContext) rebuildCommitment(ctx context.Context, roTx kv.TemporalTx, blockNum, txNum uint64) ([]byte, error) {
	it, err := roTx.HistoryRange(kv.StorageDomain, int(txNum), math.MaxInt64, order.Asc, -1)
	if err != nil {
		return nil, err
	}
	defer it.Close()
	for it.HasNext() {
		k, _, err := it.Next()
		if err != nil {
			return nil, err
		}
		sdc.TouchKey(kv.AccountsDomain, string(k), nil)
	}

	it, err = roTx.HistoryRange(kv.StorageDomain, int(txNum), math.MaxInt64, order.Asc, -1)
	if err != nil {
		return nil, err
	}
	defer it.Close()

	for it.HasNext() {
		k, _, err := it.Next()
		if err != nil {
			return nil, err
		}
		sdc.TouchKey(kv.StorageDomain, string(k), nil)
	}

	sdc.Reset()
	return sdc.ComputeCommitment(ctx, true, blockNum, txNum, "rebuild commit")
}

type TrieContext struct {
	roTtx  kv.TemporalTx
	getter kv.TemporalGetter
	putter kv.TemporalPutDel
	txNum  uint64

	limitReadAsOfTxNum uint64
	stepSize           uint64
	withHistory        bool // if true, do not use history reader and limit to domain files only
	trace              bool
}

func (sdc *TrieContext) Branch(pref []byte) ([]byte, kv.Step, error) {
	return sdc.readDomain(kv.CommitmentDomain, pref)
}

func (sdc *TrieContext) PutBranch(prefix []byte, data []byte, prevData []byte, prevStep kv.Step) error {
	if sdc.limitReadAsOfTxNum > 0 && sdc.withHistory { // do not store branches if explicitly operate on history
		return nil
	}
	if sdc.trace {
		fmt.Printf("[SDC] PutBranch: %x: %x\n", prefix, data)
	}
	//if sdc.patriciaTrie.Variant() == commitment.VariantConcurrentHexPatricia {
	//	sdc.mu.Lock()
	//	defer sdc.mu.Unlock()
	//}

	return sdc.putter.DomainPut(kv.CommitmentDomain, prefix, data, sdc.txNum, prevData, prevStep)
}

// readDomain reads data from domain, dereferences key and returns encoded value and step.
// Step returned only when reading from domain files, otherwise it is always 0.
// Step is used in Trie for memo stats and file depth access statistics.
func (sdc *TrieContext) readDomain(d kv.Domain, plainKey []byte) (enc []byte, step kv.Step, err error) {
	//if sdc.patriciaTrie.Variant() == commitment.VariantConcurrentHexPatricia {
	//	sdc.mu.Lock()
	//	defer sdc.mu.Unlock()
	//}

	if sdc.limitReadAsOfTxNum > 0 {
		if sdc.withHistory {
			enc, _, err = sdc.roTtx.GetAsOf(d, plainKey, sdc.limitReadAsOfTxNum)
		}

		if enc == nil {
			var ok bool
			// reading from domain files this way will dereference domain key correctly,
			// rotx.GetAsOf itself does not dereference keys in commitment domain values
			enc, ok, _, _, err = sdc.roTtx.Debug().GetLatestFromFiles(d, plainKey, sdc.limitReadAsOfTxNum)
			if !ok {
				enc = nil
			}
		}
		if err != nil {
			return nil, 0, fmt.Errorf("readDomain %q: (limitTxNum=%d): %w", d, sdc.limitReadAsOfTxNum, err)
		}
	}

	if enc == nil {
		enc, step, err = sdc.getter.GetLatest(d, plainKey)
	}

	if err != nil {
		return nil, 0, fmt.Errorf("readDomain %q: %w", d, err)
	}
	return enc, step, nil
}

func (sdc *TrieContext) Account(plainKey []byte) (u *commitment.Update, err error) {
	encAccount, _, err := sdc.readDomain(kv.AccountsDomain, plainKey)
	if err != nil {
		return nil, err
	}

	// Defensive: treat history tombstones/short markers as deletions.
	// Accounts are RLP-encoded and start with a small bitset (< 0x10). Values
	// beginning with 0xFF (or otherwise too short to be a valid encoding) are
	// tombstone markers left in the values table and must not be included in the trie.
	if len(encAccount) > 0 {
		if encAccount[0] == 0xff || len(encAccount) < 4 {
			encAccount = nil
		}
	}

	u = &commitment.Update{CodeHash: empty.CodeHash}
	if len(encAccount) == 0 {
		u.Flags = commitment.DeleteUpdate
		return u, nil
	}

	acc := new(accounts.Account)
	if err = accounts.DeserialiseV3(acc, encAccount); err != nil {
		return nil, err
	}

	u.Flags |= commitment.NonceUpdate
	u.Nonce = acc.Nonce

	u.Flags |= commitment.BalanceUpdate
	u.Balance = acc.Balance

	if ch := acc.CodeHash.Bytes(); len(ch) > 0 {
		u.Flags |= commitment.CodeUpdate
		u.CodeHash = acc.CodeHash
	}

	if assert.Enable {
		code, _, err := sdc.readDomain(kv.CodeDomain, plainKey)
		if err != nil {
			return nil, err
		}
		if len(code) > 0 {
			copy(u.CodeHash[:], crypto.Keccak256(code))
			u.Flags |= commitment.CodeUpdate
		}
		if acc.CodeHash != u.CodeHash {
			return nil, fmt.Errorf("code hash mismatch: account '%x' != codeHash '%x'", acc.CodeHash.Bytes(), u.CodeHash[:])
		}
	}
	return u, nil
}

func (sdc *TrieContext) Storage(plainKey []byte) (u *commitment.Update, err error) {
	enc, _, err := sdc.readDomain(kv.StorageDomain, plainKey)
	if err != nil {
		return nil, err
	}
	u = &commitment.Update{
		Flags:      commitment.DeleteUpdate,
		StorageLen: len(enc),
	}

	if u.StorageLen > 0 {
		u.Flags = commitment.StorageUpdate
		copy(u.Storage[:u.StorageLen], enc)
	}

	return u, nil
}

// Limits max txNum for read operations. If set to 0, all read operations will be from latest value.
// If domainOnly=true and txNum > 0, then read operations will be limited to domain files only.
func (sdc *TrieContext) SetLimitReadAsOfTxNum(txNum uint64, domainOnly bool) {
	sdc.limitReadAsOfTxNum = txNum
	sdc.withHistory = !domainOnly
}

type ValueMerger func(prev, current []byte) (merged []byte, err error)

// TODO revisit encoded commitmentState.
//   - Add versioning
//   - add trie variant marker
//   - simplify decoding. Rn it's 3 embedded structure: RootNode encoded, Trie state encoded and commitmentState wrapper for search.
//     | search through states seems mostly useless so probably commitmentState should become header of trie state.
type commitmentState struct {
	txNum     uint64
	blockNum  uint64
	trieState []byte
}

func (cs *commitmentState) Decode(buf []byte) error {
	if len(buf) < 10 {
		return fmt.Errorf("ivalid commitment state buffer size %d, expected at least 10b", len(buf))
	}
	pos := 0
	cs.txNum = binary.BigEndian.Uint64(buf[pos : pos+8])
	pos += 8
	cs.blockNum = binary.BigEndian.Uint64(buf[pos : pos+8])
	pos += 8
	cs.trieState = make([]byte, binary.BigEndian.Uint16(buf[pos:pos+2]))
	pos += 2
	if len(cs.trieState) == 0 && len(buf) == 10 {
		return nil
	}
	copy(cs.trieState, buf[pos:pos+len(cs.trieState)])
	return nil
}

func (cs *commitmentState) Encode() ([]byte, error) {
	buf := bytes.NewBuffer(nil)
	var v [18]byte
	binary.BigEndian.PutUint64(v[:], cs.txNum)
	binary.BigEndian.PutUint64(v[8:16], cs.blockNum)
	binary.BigEndian.PutUint16(v[16:18], uint16(len(cs.trieState)))
	if _, err := buf.Write(v[:]); err != nil {
		return nil, err
	}
	if _, err := buf.Write(cs.trieState); err != nil {
		return nil, err
	}
	return buf.Bytes(), nil
}

func LatestBlockNumWithCommitment(tx kv.TemporalGetter) (uint64, error) {
	stateVal, _, err := tx.GetLatest(kv.CommitmentDomain, KeyCommitmentState)
	if err != nil {
		return 0, err
	}
	if len(stateVal) == 0 {
		return 0, nil
	}
	_, minUnwindale := _decodeTxBlockNums(stateVal)
	return minUnwindale, nil
}
