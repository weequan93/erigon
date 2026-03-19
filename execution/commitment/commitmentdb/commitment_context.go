package commitmentdb

import (
	"bytes"
	"context"
	"crypto/sha256"
	"encoding/binary"
	"encoding/hex"
	"errors"
	"fmt"
	"sort"
	"strings"
	"sync"
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

type sharedDomainsMemLatestProvider interface {
	DebugGetLatestFromMem(domain kv.Domain, key []byte) (v []byte, step kv.Step, ok bool)
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
var debugWitnessRetryPathMarkerOnce sync.Once
var debugCommitmentCompareContexts = dbg.EnvBool("ERIGON_BAD_ROOT_COMPARE_CONTEXTS", false)
var debugCommitmentCompareContextsBlock = dbg.EnvUint("ERIGON_BAD_ROOT_COMPARE_CONTEXTS_BLOCK", 0)
var debugCommitmentCompareContextsMaxKeys = dbg.EnvInt("ERIGON_BAD_ROOT_COMPARE_CONTEXTS_MAX_KEYS", 0)
var debugCommitmentCompareContextsMaxMismatches = dbg.EnvInt("ERIGON_BAD_ROOT_COMPARE_CONTEXTS_MAX_MISMATCHES", 8)

type debugCommitmentResolvedValue struct {
	domain string
	step   uint64
	value  string
}

type debugCommitmentContextSnapshot struct {
	source      string
	blockNum    uint64
	txNum       uint64
	updateCount uint64
	keyDigest   string
	valueDigest string
	values      map[string]debugCommitmentResolvedValue
	truncated   bool
}

var debugCommitmentCompareSnapshots = struct {
	sync.Mutex
	builderByBlock map[uint64]*debugCommitmentContextSnapshot
}{
	builderByBlock: make(map[uint64]*debugCommitmentContextSnapshot),
}

// Keep latest fallback opt-in only. Falling back from as-of reads to latest can
// hide history gaps and produce witness roots that diverge from header roots.
var debugBadRootAsOfAccountLatestFallback = dbg.EnvBool("ERIGON_BAD_ROOT_ASOF_ACCOUNT_LATEST_FALLBACK", false)

// Keep commitment-branch latest fallback opt-in. Enabling this can mix latest
// commitment branch structure with as-of account/storage payloads.
var debugBadRootAsOfCommitmentLatestFallback = dbg.EnvBool("ERIGON_BAD_ROOT_ASOF_COMMITMENT_LATEST_FALLBACK", false)
var debugBadRootProbeStorageKey = common.FromHex(dbg.EnvString("ERIGON_BAD_ROOT_PROBE_STORAGE_KEY", ""))
var debugBadRootTraceReadDomain = dbg.EnvBool("ERIGON_BAD_ROOT_TRACE_READ_DOMAIN", dbg.EnvBool("ERIGON_BAD_ROOT_TRACE_GET_LATEST", false))
var debugBadRootTraceReadDomainMax = dbg.EnvInt("ERIGON_BAD_ROOT_TRACE_READ_DOMAIN_MAX", 4000)
var debugBadRootTraceReadDomainCount atomic.Uint64

const (
	debugReadDomainBucketAccounts = iota
	debugReadDomainBucketStorage
	debugReadDomainBucketCode
	debugReadDomainBucketCommitment
	debugReadDomainBucketOther
	debugReadDomainBucketCount
)

const (
	debugReadDomainStageHistoryHit = iota
	debugReadDomainStageHistoryMiss
	debugReadDomainStageFilesHit
	debugReadDomainStageFilesMiss
	debugReadDomainStageLatestHit
	debugReadDomainStageLatestMiss
	debugReadDomainStageAsOfMiss
	debugReadDomainStageReadErr
	debugReadDomainStageCount
)

var debugReadDomainBucketNames = [debugReadDomainBucketCount]string{
	"accounts",
	"storage",
	"code",
	"commitment",
	"other",
}

var debugReadDomainStageNames = [debugReadDomainStageCount]string{
	"history_hit",
	"history_miss",
	"files_hit",
	"files_miss",
	"latest_hit",
	"latest_miss",
	"asof_miss",
	"read_err",
}

var debugBadRootReadDomainStats [debugReadDomainBucketCount][debugReadDomainStageCount]atomic.Uint64
var debugBadRootTraceReadDomainAccounts = func() map[string]struct{} {
	out := make(map[string]struct{})
	for _, raw := range dbg.EnvStrings("ERIGON_BAD_ROOT_ACCOUNTS", ",", nil) {
		raw = strings.TrimSpace(raw)
		if raw == "" || !common.IsHexAddress(raw) {
			continue
		}
		addr := common.HexToAddress(raw)
		out[string(addr.Bytes())] = struct{}{}
	}
	if len(debugBadRootProbeStorageKey) >= 20 {
		out[string(debugBadRootProbeStorageKey[:20])] = struct{}{}
	}
	return out
}()

func commitmentHexPreview(v []byte, max int) string {
	if len(v) == 0 {
		return "0x"
	}
	if max <= 0 || len(v) <= max {
		return fmt.Sprintf("0x%x", v)
	}
	return fmt.Sprintf("0x%x...(+%d bytes)", v[:max], len(v)-max)
}

func shouldDebugCompareCommitmentContexts(blockNum uint64) bool {
	if !debugCommitmentCompareContexts {
		return false
	}
	if debugCommitmentCompareContextsBlock > 0 && blockNum != debugCommitmentCompareContextsBlock {
		return false
	}
	return true
}

func debugCommitmentValuePreview(v string) string {
	if strings.HasPrefix(v, "ERR:") {
		const maxErr = 200
		if len(v) <= maxErr {
			return v
		}
		return v[:maxErr] + "...(truncated)"
	}
	if len(v) <= 66 {
		return v
	}
	return v[:66] + "...(truncated)"
}

func shouldTraceBadRootReadDomain(domain kv.Domain, plainKey []byte) bool {
	if !debugBadRootTraceReadDomain || len(plainKey) < 20 {
		return false
	}
	switch domain {
	case kv.AccountsDomain, kv.CodeDomain:
		_, ok := debugBadRootTraceReadDomainAccounts[string(plainKey[:20])]
		return ok
	case kv.StorageDomain:
		if len(debugBadRootProbeStorageKey) > 0 {
			if bytes.Equal(plainKey, debugBadRootProbeStorageKey) {
				return true
			}
			if len(debugBadRootProbeStorageKey) >= 20 && bytes.Equal(plainKey[:20], debugBadRootProbeStorageKey[:20]) {
				return true
			}
		}
		_, ok := debugBadRootTraceReadDomainAccounts[string(plainKey[:20])]
		return ok
	default:
		return false
	}
}

func shouldEmitBadRootReadDomainLog() bool {
	if !debugBadRootTraceReadDomain {
		return false
	}
	if debugBadRootTraceReadDomainMax <= 0 {
		return true
	}
	return int(debugBadRootTraceReadDomainCount.Add(1)) <= debugBadRootTraceReadDomainMax
}

func debugReadDomainBucket(domain kv.Domain) int {
	switch domain {
	case kv.AccountsDomain:
		return debugReadDomainBucketAccounts
	case kv.StorageDomain:
		return debugReadDomainBucketStorage
	case kv.CodeDomain:
		return debugReadDomainBucketCode
	case kv.CommitmentDomain:
		return debugReadDomainBucketCommitment
	default:
		return debugReadDomainBucketOther
	}
}

func debugReadDomainCount(domain kv.Domain, stage int) {
	if stage < 0 || stage >= debugReadDomainStageCount {
		return
	}
	bucket := debugReadDomainBucket(domain)
	debugBadRootReadDomainStats[bucket][stage].Add(1)
}

func debugReadDomainStatsSnapshot() map[string]uint64 {
	out := make(map[string]uint64, debugReadDomainBucketCount*debugReadDomainStageCount)
	for bucket := 0; bucket < debugReadDomainBucketCount; bucket++ {
		for stage := 0; stage < debugReadDomainStageCount; stage++ {
			key := debugReadDomainBucketNames[bucket] + "." + debugReadDomainStageNames[stage]
			out[key] = debugBadRootReadDomainStats[bucket][stage].Load()
		}
	}
	return out
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

func (sdc *SharedDomainsCommitmentContext) debugResolvedValues(maxKeys int) (map[string]debugCommitmentResolvedValue, bool) {
	out := make(map[string]debugCommitmentResolvedValue)
	if sdc == nil || sdc.mainTtx == nil || sdc.updates == nil {
		return out, false
	}

	keys := sdc.updates.DebugPlainKeys()
	sort.Slice(keys, func(i, j int) bool { return bytes.Compare(keys[i], keys[j]) < 0 })
	truncated := false
	if maxKeys > 0 && len(keys) > maxKeys {
		keys = keys[:maxKeys]
		truncated = true
	}

	for _, key := range keys {
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

		keyHex := hex.EncodeToString(key)
		domainName := domain.String()
		if readErr != nil {
			out[keyHex] = debugCommitmentResolvedValue{
				domain: domainName,
				step:   uint64(step),
				value:  "ERR:" + readErr.Error(),
			}
			continue
		}
		out[keyHex] = debugCommitmentResolvedValue{
			domain: domainName,
			step:   uint64(step),
			value:  "0x" + hex.EncodeToString(val),
		}
	}

	return out, truncated
}

func debugCommitmentCompareMismatches(
	baseline *debugCommitmentContextSnapshot,
	current *debugCommitmentContextSnapshot,
	maxMismatches int,
) []string {
	if maxMismatches <= 0 {
		maxMismatches = 1
	}
	if baseline == nil || current == nil {
		return nil
	}

	keySet := make(map[string]struct{}, len(baseline.values)+len(current.values))
	for key := range baseline.values {
		keySet[key] = struct{}{}
	}
	for key := range current.values {
		keySet[key] = struct{}{}
	}
	keys := make([]string, 0, len(keySet))
	for key := range keySet {
		keys = append(keys, key)
	}
	sort.Strings(keys)

	mismatches := make([]string, 0, maxMismatches)
	for _, key := range keys {
		bv, bok := baseline.values[key]
		cv, cok := current.values[key]
		if !bok {
			mismatches = append(mismatches, fmt.Sprintf("key=%s missing_in_builder current(domain=%s step=%d val=%s)", key, cv.domain, cv.step, debugCommitmentValuePreview(cv.value)))
		} else if !cok {
			mismatches = append(mismatches, fmt.Sprintf("key=%s missing_in_current builder(domain=%s step=%d val=%s)", key, bv.domain, bv.step, debugCommitmentValuePreview(bv.value)))
		} else if bv.domain != cv.domain || bv.step != cv.step || bv.value != cv.value {
			mismatches = append(mismatches, fmt.Sprintf(
				"key=%s builder(domain=%s step=%d val=%s) current(domain=%s step=%d val=%s)",
				key,
				bv.domain,
				bv.step,
				debugCommitmentValuePreview(bv.value),
				cv.domain,
				cv.step,
				debugCommitmentValuePreview(cv.value),
			))
		}
		if len(mismatches) >= maxMismatches {
			break
		}
	}
	return mismatches
}

func debugCommitmentCompareAndLog(snapshot *debugCommitmentContextSnapshot) {
	if snapshot == nil {
		return
	}
	source := strings.TrimSpace(snapshot.source)
	isBuilderSource := source == "erigonexec"

	if isBuilderSource {
		debugCommitmentCompareSnapshots.Lock()
		debugCommitmentCompareSnapshots.builderByBlock[snapshot.blockNum] = snapshot
		debugCommitmentCompareSnapshots.Unlock()
		log.Warn(
			"commitment context compare baseline stored",
			"block", snapshot.blockNum,
			"source", source,
			"tx_num_arg", snapshot.txNum,
			"update_count", snapshot.updateCount,
			"key_digest", snapshot.keyDigest,
			"value_digest", snapshot.valueDigest,
			"entries", len(snapshot.values),
			"truncated", snapshot.truncated,
		)
		return
	}

	var baseline *debugCommitmentContextSnapshot
	debugCommitmentCompareSnapshots.Lock()
	baseline = debugCommitmentCompareSnapshots.builderByBlock[snapshot.blockNum]
	delete(debugCommitmentCompareSnapshots.builderByBlock, snapshot.blockNum)
	debugCommitmentCompareSnapshots.Unlock()

	if baseline == nil {
		log.Warn(
			"commitment context compare skipped (missing builder baseline)",
			"block", snapshot.blockNum,
			"source", source,
			"tx_num_arg", snapshot.txNum,
			"update_count", snapshot.updateCount,
			"key_digest", snapshot.keyDigest,
			"value_digest", snapshot.valueDigest,
			"entries", len(snapshot.values),
			"truncated", snapshot.truncated,
		)
		return
	}

	mismatches := debugCommitmentCompareMismatches(baseline, snapshot, debugCommitmentCompareContextsMaxMismatches)
	if len(mismatches) == 0 {
		log.Warn(
			"commitment context compare match",
			"block", snapshot.blockNum,
			"source", source,
			"tx_num_arg", snapshot.txNum,
			"baseline_tx_num_arg", baseline.txNum,
			"update_count", snapshot.updateCount,
			"baseline_update_count", baseline.updateCount,
			"key_digest", snapshot.keyDigest,
			"baseline_key_digest", baseline.keyDigest,
			"value_digest", snapshot.valueDigest,
			"baseline_value_digest", baseline.valueDigest,
			"entries", len(snapshot.values),
			"baseline_entries", len(baseline.values),
			"truncated", snapshot.truncated,
			"baseline_truncated", baseline.truncated,
		)
		return
	}

	log.Warn(
		"commitment context compare mismatch",
		"block", snapshot.blockNum,
		"source", source,
		"tx_num_arg", snapshot.txNum,
		"baseline_tx_num_arg", baseline.txNum,
		"update_count", snapshot.updateCount,
		"baseline_update_count", baseline.updateCount,
		"key_digest", snapshot.keyDigest,
		"baseline_key_digest", baseline.keyDigest,
		"value_digest", snapshot.valueDigest,
		"baseline_value_digest", baseline.valueDigest,
		"entries", len(snapshot.values),
		"baseline_entries", len(baseline.values),
		"truncated", snapshot.truncated,
		"baseline_truncated", baseline.truncated,
		"mismatch_count", len(mismatches),
		"mismatches", mismatches,
	)
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
	if memProvider, ok := sd.(sharedDomainsMemLatestProvider); ok {
		trieCtx.getLatestFromMem = memProvider.DebugGetLatestFromMem
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

// ClearUpdates drops currently tracked touched keys while keeping the current
// trie state untouched. Useful when a temporary commitment rebuild populated
// updates only for diagnostics and callers need a fresh witness key set.
func (sdc *SharedDomainsCommitmentContext) ClearUpdates() {
	sdc.updates.Reset()
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
		if debugBadRootCommitmentProbe {
			debugWitnessRetryPathMarkerOnce.Do(func() {
				log.Warn(
					"witness retry path marker",
					"version", "commitment-context-2026-03-03-3",
					"keydiag_skip_enabled", true,
					"retry_snapshot_enabled", true,
				)
			})
		}
		// GenerateWitness consumes update iterators (HashSort clears keyset in direct mode).
		// Keep a debug snapshot so retry paths can run on the same touched-key set.
		retryUpdates := sdc.updates.DebugSnapshot()
		if retryUpdates != nil {
			defer retryUpdates.Close()
		}

		proofTrie, rootHash, err = hexPatriciaHashed.GenerateWitness(ctx, sdc.updates, codeReads, expectedRoot, logPrefix)
		if err == nil || sdc.mainTtx == nil || !strings.Contains(err.Error(), "empty branch data read during unfold") {
			return proofTrie, rootHash, err
		}
		if strings.Contains(logPrefix, "/keydiag/") {
			if debugBadRootCommitmentProbe {
				log.Warn("witness retry skipped for keydiag prefix", "log_prefix", logPrefix)
			}
			return nil, nil, err
		}
		if retryUpdates == nil || retryUpdates.Size() == 0 {
			return nil, nil, err
		}

		// Retry once with commitment-branch latest fallback enabled. This is a
		// narrow diagnostic path for as-of witness extraction where branch rows
		// may be missing from history/files despite a restored root.
		if debugBadRootCommitmentProbe {
			log.Warn(
				"witness retry with commitment latest fallback",
				"log_prefix", logPrefix,
				"tx_num", sdc.mainTtx.txNum,
				"limit_asof_txnum", sdc.mainTtx.limitReadAsOfTxNum,
				"with_history", sdc.mainTtx.withHistory,
				"initial_err", err,
			)
		}
		sdc.mainTtx.SetCommitmentLatestFallback(true)
		proofTrie, rootHash, retryErr := hexPatriciaHashed.GenerateWitness(ctx, retryUpdates, codeReads, expectedRoot, logPrefix+"/retry_latest_commitment")
		sdc.mainTtx.SetCommitmentLatestFallback(false)
		if retryErr == nil {
			if debugBadRootCommitmentProbe {
				log.Warn(
					"witness retry with commitment latest fallback succeeded",
					"log_prefix", logPrefix,
					"root", common.BytesToHash(rootHash),
					"expected_root", common.BytesToHash(expectedRoot),
				)
			}
			return proofTrie, rootHash, nil
		}
		if debugBadRootCommitmentProbe {
			log.Warn(
				"witness retry with commitment latest fallback failed",
				"log_prefix", logPrefix,
				"initial_err", err,
				"retry_err", retryErr,
			)
		}
		return nil, nil, retryErr
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
			compareSnapshot       *debugCommitmentContextSnapshot
		)

		ctxTxNum, ctxLimitReadAsOfTxNum, ctxWithHistory, hasTrieCtx = sdc.DebugReadContext()
		updatesDigestCount, updatesDigest, updatesDigestSamples = sdc.updates.DebugDigest(64)
		updatesValueCount, updatesValueDigest, updatesValueSamples = sdc.debugUpdatesValueDigest(64)
		if shouldDebugCompareCommitmentContexts(blockNum) && updateCount > 0 {
			resolvedValues, truncated := sdc.debugResolvedValues(debugCommitmentCompareContextsMaxKeys)
			compareSnapshot = &debugCommitmentContextSnapshot{
				source:      strings.TrimSpace(logPrefix),
				blockNum:    blockNum,
				txNum:       txNum,
				updateCount: updateCount,
				keyDigest:   updatesDigest,
				valueDigest: updatesValueDigest,
				values:      resolvedValues,
				truncated:   truncated,
			}
		}
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
		if compareSnapshot != nil {
			debugCommitmentCompareAndLog(compareSnapshot)
		}
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
	// Once a process attempt has started, clear justRestored regardless of
	// success. Leaving it set on errors causes future Reset() calls to no-op
	// and can pin the trie to stale restored state.
	sdc.justRestored.Store(false)
	if err != nil {
		return nil, err
	}

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

// DebugUpdatesDigests returns stable key/value digests for currently tracked updates.
// key digest is based on tracked plain keys and in-memory update payloads.
// value digest is based on values resolved through the current trie read context.
func (sdc *SharedDomainsCommitmentContext) DebugUpdatesDigests(maxSamples int) (
	keyCount uint64,
	keyDigest string,
	keySamples []string,
	valueCount uint64,
	valueDigest string,
	valueSamples []string,
) {
	if sdc == nil || sdc.updates == nil {
		return 0, "", nil, 0, "", nil
	}
	keyCount, keyDigest, keySamples = sdc.updates.DebugDigest(maxSamples)
	valueCount, valueDigest, valueSamples = sdc.debugUpdatesValueDigest(maxSamples)
	return keyCount, keyDigest, keySamples, valueCount, valueDigest, valueSamples
}

// DebugUpdatePayloadStats summarizes whether current tracked keys include
// in-memory update payloads (ModeUpdate) or only keys (ModeDirect).
func (sdc *SharedDomainsCommitmentContext) DebugUpdatePayloadStats(maxSamples int) (
	mode string,
	total uint64,
	withPayload uint64,
	nilPayload uint64,
	deleteCount uint64,
	balanceCount uint64,
	nonceCount uint64,
	codeCount uint64,
	storageCount uint64,
	samples []string,
) {
	if sdc == nil || sdc.updates == nil {
		return "nil", 0, 0, 0, 0, 0, 0, 0, 0, nil
	}
	return sdc.updates.DebugPayloadStats(maxSamples)
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

// DebugReadDomainStatsSnapshot returns cumulative read-domain counters grouped by domain/stage.
// Intended for debug-only deltas around witness or commitment calls.
func (sdc *SharedDomainsCommitmentContext) DebugReadDomainStatsSnapshot() map[string]uint64 {
	return debugReadDomainStatsSnapshot()
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

// RestoreCommitmentStateAsOfTxNum restores trie state from commitment state as-of
// a specific txnum. It first tries history lookup and then files-only lookup.
func (sdc *SharedDomainsCommitmentContext) RestoreCommitmentStateAsOfTxNum(tx kv.TemporalTx, asOfTxNum uint64) (blockNum uint64, txNum uint64, rootHash []byte, restored bool, err error) {
	if sdc == nil || sdc.mainTtx == nil || sdc.patriciaTrie == nil {
		return 0, 0, nil, false, errors.New("commitment context is not initialized")
	}
	if tx == nil {
		return 0, 0, nil, false, errors.New("restore commitment state as-of: temporal tx is nil")
	}
	// Read from the provided temporal tx directly (not trie context), so as-of
	// lookup is not polluted by in-memory batch overlays.
	state, _, err := tx.GetAsOf(kv.CommitmentDomain, KeyCommitmentState, asOfTxNum)
	if err != nil {
		return 0, 0, nil, false, err
	}
	if len(state) == 0 {
		var ok bool
		state, ok, _, _, err = tx.Debug().GetLatestFromFiles(kv.CommitmentDomain, KeyCommitmentState, asOfTxNum)
		if err != nil {
			return 0, 0, nil, false, err
		}
		if !ok || len(state) == 0 {
			return 0, 0, nil, false, nil
		}
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

// RebuildCommitmentAsOfTxNum rebuilds commitment trie for the given txnum.
// Intended as a fallback when historical commitment snapshots are unavailable.
func (sdc *SharedDomainsCommitmentContext) RebuildCommitmentAsOfTxNum(ctx context.Context, tx kv.TemporalTx, blockNum uint64, txNum uint64) ([]byte, error) {
	if sdc == nil || sdc.mainTtx == nil || sdc.patriciaTrie == nil {
		return nil, errors.New("commitment context is not initialized")
	}
	if tx == nil {
		return nil, errors.New("rebuild commitment as-of: temporal tx is nil")
	}
	return sdc.rebuildCommitment(ctx, tx, blockNum, txNum)
}

// RebuildCommitmentAsOfTxNumFullScan is a debug-oriented rebuild path that
// touches all latest accounts/storage keys (plus history-range keys for
// post-asof deletions) before recomputing commitment as-of txNum.
// It is significantly more expensive than RebuildCommitmentAsOfTxNum.
func (sdc *SharedDomainsCommitmentContext) RebuildCommitmentAsOfTxNumFullScan(ctx context.Context, tx kv.TemporalTx, blockNum uint64, txNum uint64) ([]byte, error) {
	if sdc == nil || sdc.mainTtx == nil || sdc.patriciaTrie == nil {
		return nil, errors.New("commitment context is not initialized")
	}
	if tx == nil {
		return nil, errors.New("rebuild commitment full-scan as-of: temporal tx is nil")
	}

	accLatestCount := 0
	storageLatestCount := 0
	accHistoryCount := 0
	storageHistoryCount := 0

	latestAccIt, err := tx.Debug().RangeLatest(kv.AccountsDomain, nil, nil, -1)
	if err != nil {
		return nil, err
	}
	defer latestAccIt.Close()
	for latestAccIt.HasNext() {
		k, _, err := latestAccIt.Next()
		if err != nil {
			return nil, err
		}
		accLatestCount++
		sdc.TouchKey(kv.AccountsDomain, string(k), nil)
	}

	latestStorageIt, err := tx.Debug().RangeLatest(kv.StorageDomain, nil, nil, -1)
	if err != nil {
		return nil, err
	}
	defer latestStorageIt.Close()
	for latestStorageIt.HasNext() {
		k, _, err := latestStorageIt.Next()
		if err != nil {
			return nil, err
		}
		storageLatestCount++
		sdc.TouchKey(kv.StorageDomain, string(k), nil)
	}

	// Include keys changed after txNum so deletes that vanished from latest
	// state are still part of the as-of reconstruction keyset.
	accHistoryIt, err := tx.HistoryRange(kv.AccountsDomain, int(txNum), -1, order.Asc, -1)
	if err != nil {
		return nil, err
	}
	defer accHistoryIt.Close()
	for accHistoryIt.HasNext() {
		k, _, err := accHistoryIt.Next()
		if err != nil {
			return nil, err
		}
		accHistoryCount++
		sdc.TouchKey(kv.AccountsDomain, string(k), nil)
	}

	storageHistoryIt, err := tx.HistoryRange(kv.StorageDomain, int(txNum), -1, order.Asc, -1)
	if err != nil {
		return nil, err
	}
	defer storageHistoryIt.Close()
	for storageHistoryIt.HasNext() {
		k, _, err := storageHistoryIt.Next()
		if err != nil {
			return nil, err
		}
		storageHistoryCount++
		sdc.TouchKey(kv.StorageDomain, string(k), nil)
	}

	if debugBadRootCommitmentProbe {
		log.Warn(
			"commitment rebuild fullscan key scan",
			"block", blockNum,
			"tx_num_arg", txNum,
			"accounts_latest_count", accLatestCount,
			"storage_latest_count", storageLatestCount,
			"accounts_history_count", accHistoryCount,
			"storage_history_count", storageHistoryCount,
			"updates_count_after_touch", sdc.updates.Size(),
			"updates_mode", sdc.updates.Mode(),
		)
	}

	prevAllowHistoryBranchWrites := sdc.mainTtx.allowHistoryBranchWrites
	sdc.mainTtx.SetAllowHistoryBranchWrites(true)
	defer sdc.mainTtx.SetAllowHistoryBranchWrites(prevAllowHistoryBranchWrites)

	sdc.justRestored.Store(false)
	sdc.Reset()
	return sdc.ComputeCommitment(ctx, true, blockNum, txNum, "rebuild commit fullscan")
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
				asOfTxNum, err := rawdbv3.TxNums.Max(tx, lastBn)
				if err != nil {
					return 0, 0, false, err
				}
				restoredBlock, restoredTxNum, _, restored, restoreErr := sdc.RestoreCommitmentStateAsOfTxNum(tx, asOfTxNum)
				if restoreErr == nil && restored && restoredBlock <= lastBn {
					log.Warn(
						"commitment context recovered from ahead-of-txnums state",
						"commitment_block", blockNum,
						"commitment_txnum", txNum,
						"txnums_last_block", lastBn,
						"txnums_asof_txnum", asOfTxNum,
						"restored_block", restoredBlock,
						"restored_txnum", restoredTxNum,
					)
					blockNum = restoredBlock
					txNum = restoredTxNum
				} else {
					if restoreErr != nil {
						return 0, 0, false, fmt.Errorf(
							"%w: TxNums index is at block %d and behind commitment %d (as-of restore failed: %v)",
							ErrBehindCommitment,
							lastBn,
							blockNum,
							restoreErr,
						)
					}
					return 0, 0, false, fmt.Errorf("%w: TxNums index is at block %d and behind commitment %d", ErrBehindCommitment, lastBn, blockNum)
				}
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
	accHistoryCount := 0
	storageHistoryCount := 0
	it, err := roTx.HistoryRange(kv.AccountsDomain, int(txNum), -1, order.Asc, -1)
	if err != nil {
		return nil, err
	}
	defer it.Close()
	for it.HasNext() {
		k, _, err := it.Next()
		if err != nil {
			return nil, err
		}
		accHistoryCount++
		sdc.TouchKey(kv.AccountsDomain, string(k), nil)
	}

	it, err = roTx.HistoryRange(kv.StorageDomain, int(txNum), -1, order.Asc, -1)
	if err != nil {
		return nil, err
	}
	defer it.Close()

	for it.HasNext() {
		k, _, err := it.Next()
		if err != nil {
			return nil, err
		}
		storageHistoryCount++
		sdc.TouchKey(kv.StorageDomain, string(k), nil)
	}

	if debugBadRootCommitmentProbe {
		log.Warn(
			"commitment rebuild history scan",
			"block", blockNum,
			"tx_num_arg", txNum,
			"accounts_history_count", accHistoryCount,
			"storage_history_count", storageHistoryCount,
			"updates_count_after_touch", sdc.updates.Size(),
			"updates_mode", sdc.updates.Mode(),
		)
	}

	prevAllowHistoryBranchWrites := sdc.mainTtx.allowHistoryBranchWrites
	sdc.mainTtx.SetAllowHistoryBranchWrites(true)
	defer sdc.mainTtx.SetAllowHistoryBranchWrites(prevAllowHistoryBranchWrites)

	// Rebuild must start from a clean trie even if a previous restore/process
	// sequence failed and left justRestored=true.
	sdc.justRestored.Store(false)
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
	// allowCommitmentLatestFallback enables a targeted retry path for witness
	// generation when historical commitment branches are missing for an as-of
	// txnum. Keep false by default to avoid leaking latest commitment data into
	// regular as-of reads.
	allowCommitmentLatestFallback bool
	// As-of history mode is normally read-only for commitment branches. Rebuild
	// paths enable this flag to materialize branch rows in RAM for subsequent
	// witness reads at the same as-of txnum.
	allowHistoryBranchWrites bool
	// Optional direct RAM overlay lookup for commitment domain reads. This is
	// used to pick up freshly rebuilt branch rows before history/files fallback.
	getLatestFromMem func(domain kv.Domain, key []byte) (v []byte, step kv.Step, ok bool)
	trace            bool
}

func (sdc *TrieContext) Branch(pref []byte) ([]byte, kv.Step, error) {
	return sdc.readDomain(kv.CommitmentDomain, pref)
}

func (sdc *TrieContext) SetCommitmentLatestFallback(enable bool) {
	sdc.allowCommitmentLatestFallback = enable
}

func (sdc *TrieContext) SetAllowHistoryBranchWrites(enable bool) {
	sdc.allowHistoryBranchWrites = enable
}

func (sdc *TrieContext) PutBranch(prefix []byte, data []byte, prevData []byte, prevStep kv.Step) error {
	if sdc.limitReadAsOfTxNum > 0 && sdc.withHistory && !sdc.allowHistoryBranchWrites {
		// keep history-only reads write-free unless explicitly enabled by rebuild paths
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
	traceRead := shouldTraceBadRootReadDomain(d, plainKey) && shouldEmitBadRootReadDomainLog()
	traceStage := "init"
	historyOK := false
	historyLen := -1
	historyPreview := ""
	var historyErr error
	filesOK := false
	filesLen := -1
	filesPreview := ""
	var filesErr error
	latestLen := -1
	latestPreview := ""
	var latestErr error

	asOfMode := sdc.limitReadAsOfTxNum > 0
	if asOfMode {
		if d == kv.CommitmentDomain && sdc.getLatestFromMem != nil {
			memVal, memStep, memOK := sdc.getLatestFromMem(d, plainKey)
			if memOK && len(memVal) > 0 {
				traceStage = "mem_asof_overlay"
				latestLen = len(memVal)
				latestPreview = commitmentHexPreview(memVal, 32)
				debugReadDomainCount(d, debugReadDomainStageLatestHit)
				if traceRead {
					log.Warn(
						"bad root trace readDomain",
						"domain", d.String(),
						"key", commitmentHexPreview(plainKey, 64),
						"asof_mode", asOfMode,
						"with_history", sdc.withHistory,
						"limit_asof_txnum", sdc.limitReadAsOfTxNum,
						"stage", traceStage,
						"history_ok", historyOK,
						"history_len", historyLen,
						"history_preview", historyPreview,
						"history_err", historyErr,
						"files_ok", filesOK,
						"files_len", filesLen,
						"files_preview", filesPreview,
						"files_err", filesErr,
						"latest_len", latestLen,
						"latest_preview", latestPreview,
						"latest_err", latestErr,
						"step", memStep,
						"result_len", len(memVal),
						"result_preview", commitmentHexPreview(memVal, 32),
					)
				}
				return memVal, memStep, nil
			}
		}
		if sdc.withHistory {
			// Use GetAsOf semantics (history + safe fallback) in history mode.
			// HistorySeek-only reads can return false negatives for keys that have
			// no history row at/after the requested tx but do exist in mutable data.
			var ok bool
			enc, ok, err = sdc.roTtx.GetAsOf(d, plainKey, sdc.limitReadAsOfTxNum)
			if err != nil {
				if traceRead {
					log.Warn(
						"bad root trace readDomain",
						"domain", d.String(),
						"key", commitmentHexPreview(plainKey, 64),
						"asof_mode", asOfMode,
						"with_history", sdc.withHistory,
						"limit_asof_txnum", sdc.limitReadAsOfTxNum,
						"stage", "history_error",
						"err", err,
					)
				}
				return nil, 0, fmt.Errorf("readDomain %q: (limitTxNum=%d): %w", d, sdc.limitReadAsOfTxNum, err)
			}
			historyOK = ok
			historyLen = len(enc)
			historyPreview = commitmentHexPreview(enc, 32)
			if ok && len(enc) > 0 {
				debugReadDomainCount(d, debugReadDomainStageHistoryHit)
			} else {
				debugReadDomainCount(d, debugReadDomainStageHistoryMiss)
			}
			if !ok {
				enc = nil
			}
			// Treat empty/tombstone payloads as missing key.
			if len(enc) == 0 {
				enc = nil
			}
			traceStage = "history"
		}

		if enc == nil {
			var ok bool
			// reading from domain files this way will dereference domain key correctly,
			// rotx.GetAsOf itself does not dereference keys in commitment domain values
			enc, ok, _, _, err = sdc.roTtx.Debug().GetLatestFromFiles(d, plainKey, sdc.limitReadAsOfTxNum)
			filesOK = ok
			filesLen = len(enc)
			filesPreview = commitmentHexPreview(enc, 32)
			filesErr = err
			if ok && len(enc) > 0 {
				debugReadDomainCount(d, debugReadDomainStageFilesHit)
			} else {
				debugReadDomainCount(d, debugReadDomainStageFilesMiss)
			}
			if !ok {
				enc = nil
			}
			traceStage = "files"
		}
		if err != nil {
			debugReadDomainCount(d, debugReadDomainStageReadErr)
			if traceRead {
				log.Warn(
					"bad root trace readDomain",
					"domain", d.String(),
					"key", commitmentHexPreview(plainKey, 64),
					"asof_mode", asOfMode,
					"with_history", sdc.withHistory,
					"limit_asof_txnum", sdc.limitReadAsOfTxNum,
					"stage", "files_error",
					"history_ok", historyOK,
					"history_len", historyLen,
					"history_preview", historyPreview,
					"files_ok", filesOK,
					"files_len", filesLen,
					"files_preview", filesPreview,
					"err", err,
				)
			}
			return nil, 0, fmt.Errorf("readDomain %q: (limitTxNum=%d): %w", d, sdc.limitReadAsOfTxNum, err)
		}

		// In as-of mode, missing value means the key does not exist at the
		// requested tx. Never fall back to latest by default, otherwise
		// future-state values leak into witness/commitment reconstruction.
		if enc == nil {
			// Optional exception for commitment domain, controlled by env.
			if d == kv.CommitmentDomain && (debugBadRootAsOfCommitmentLatestFallback || sdc.allowCommitmentLatestFallback) {
				enc, step, err = sdc.getter.GetLatest(d, plainKey)
				if err != nil {
					debugReadDomainCount(d, debugReadDomainStageReadErr)
				} else if len(enc) > 0 {
					debugReadDomainCount(d, debugReadDomainStageLatestHit)
				} else {
					debugReadDomainCount(d, debugReadDomainStageLatestMiss)
				}
				if err != nil {
					if traceRead {
						log.Warn(
							"bad root trace readDomain",
							"domain", d.String(),
							"key", commitmentHexPreview(plainKey, 64),
							"asof_mode", asOfMode,
							"with_history", sdc.withHistory,
							"limit_asof_txnum", sdc.limitReadAsOfTxNum,
							"stage", "latest_commitment_error",
							"history_ok", historyOK,
							"history_len", historyLen,
							"history_preview", historyPreview,
							"files_ok", filesOK,
							"files_len", filesLen,
							"files_preview", filesPreview,
							"err", err,
						)
					}
					return nil, 0, fmt.Errorf("readDomain %q: %w", d, err)
				}
				latestLen = len(enc)
				latestPreview = commitmentHexPreview(enc, 32)
				traceStage = "latest_commitment"
				if enc != nil {
					if traceRead {
						log.Warn(
							"bad root trace readDomain",
							"domain", d.String(),
							"key", commitmentHexPreview(plainKey, 64),
							"asof_mode", asOfMode,
							"with_history", sdc.withHistory,
							"limit_asof_txnum", sdc.limitReadAsOfTxNum,
							"stage", traceStage,
							"history_ok", historyOK,
							"history_len", historyLen,
							"history_preview", historyPreview,
							"history_err", historyErr,
							"files_ok", filesOK,
							"files_len", filesLen,
							"files_preview", filesPreview,
							"files_err", filesErr,
							"latest_len", latestLen,
							"latest_preview", latestPreview,
							"latest_err", latestErr,
							"step", step,
							"result_len", len(enc),
							"result_preview", commitmentHexPreview(enc, 32),
						)
					}
					return enc, step, nil
				}
			}
			if traceRead {
				log.Warn(
					"bad root trace readDomain",
					"domain", d.String(),
					"key", commitmentHexPreview(plainKey, 64),
					"asof_mode", asOfMode,
					"with_history", sdc.withHistory,
					"limit_asof_txnum", sdc.limitReadAsOfTxNum,
					"stage", "asof_miss",
					"history_ok", historyOK,
					"history_len", historyLen,
					"history_preview", historyPreview,
					"history_err", historyErr,
					"files_ok", filesOK,
					"files_len", filesLen,
					"files_preview", filesPreview,
					"files_err", filesErr,
					"latest_len", latestLen,
					"latest_preview", latestPreview,
					"latest_err", latestErr,
					"step", step,
					"result_len", 0,
					"result_preview", "0x",
				)
			}
			debugReadDomainCount(d, debugReadDomainStageAsOfMiss)
			return nil, 0, nil
		}
	}

	if !asOfMode && enc == nil {
		enc, step, err = sdc.getter.GetLatest(d, plainKey)
		latestLen = len(enc)
		latestPreview = commitmentHexPreview(enc, 32)
		latestErr = err
		traceStage = "latest"
		if err != nil {
			debugReadDomainCount(d, debugReadDomainStageReadErr)
		} else if len(enc) > 0 {
			debugReadDomainCount(d, debugReadDomainStageLatestHit)
		} else {
			debugReadDomainCount(d, debugReadDomainStageLatestMiss)
		}
	}

	if err != nil {
		if traceRead {
			log.Warn(
				"bad root trace readDomain",
				"domain", d.String(),
				"key", commitmentHexPreview(plainKey, 64),
				"asof_mode", asOfMode,
				"with_history", sdc.withHistory,
				"limit_asof_txnum", sdc.limitReadAsOfTxNum,
				"stage", traceStage,
				"history_ok", historyOK,
				"history_len", historyLen,
				"history_preview", historyPreview,
				"history_err", historyErr,
				"files_ok", filesOK,
				"files_len", filesLen,
				"files_preview", filesPreview,
				"files_err", filesErr,
				"latest_len", latestLen,
				"latest_preview", latestPreview,
				"latest_err", latestErr,
				"err", err,
			)
		}
		return nil, 0, fmt.Errorf("readDomain %q: %w", d, err)
	}
	if traceRead {
		log.Warn(
			"bad root trace readDomain",
			"domain", d.String(),
			"key", commitmentHexPreview(plainKey, 64),
			"asof_mode", asOfMode,
			"with_history", sdc.withHistory,
			"limit_asof_txnum", sdc.limitReadAsOfTxNum,
			"stage", traceStage,
			"history_ok", historyOK,
			"history_len", historyLen,
			"history_preview", historyPreview,
			"history_err", historyErr,
			"files_ok", filesOK,
			"files_len", filesLen,
			"files_preview", filesPreview,
			"files_err", filesErr,
			"latest_len", latestLen,
			"latest_preview", latestPreview,
			"latest_err", latestErr,
			"step", step,
			"result_len", len(enc),
			"result_preview", commitmentHexPreview(enc, 32),
		)
	}
	return enc, step, nil
}

func (sdc *TrieContext) Account(plainKey []byte) (u *commitment.Update, err error) {
	encAccount, _, err := sdc.readDomain(kv.AccountsDomain, plainKey)
	if err != nil {
		return nil, err
	}

	// In as-of witness/debug mode, account history can occasionally miss values
	// that are still required to reconstruct canonical branch commitments.
	// Allow an explicit latest fallback so witness generation can proceed while
	// we continue investigating history gaps.
	if len(encAccount) == 0 && sdc.limitReadAsOfTxNum > 0 && debugBadRootAsOfAccountLatestFallback {
		latestEnc, _, latestErr := sdc.getter.GetLatest(kv.AccountsDomain, plainKey)
		if latestErr != nil {
			return nil, latestErr
		}
		if len(latestEnc) >= 4 && latestEnc[0] != 0xff {
			encAccount = latestEnc
			if debugBadRootCommitmentProbe {
				log.Warn(
					"bad root account asof miss fallback latest",
					"key", commitmentHexPreview(plainKey, 64),
					"limit_asof_txnum", sdc.limitReadAsOfTxNum,
					"latest_len", len(latestEnc),
					"latest_preview", commitmentHexPreview(latestEnc, 32),
				)
			}
		}
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

	// Preserve account storage root for witness/account leaf construction.
	// Keep it out of flags so regular state-update semantics stay unchanged.
	u.StorageLen = len(acc.Root[:])
	copy(u.Storage[:], acc.Root[:])

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

// StorageLatest bypasses as-of limits and returns the latest storage-domain value.
// Witness diagnostics use this as a fallback only when as-of payloads cannot
// materialize the branch child hash already present in commitment cells.
func (sdc *TrieContext) StorageLatest(plainKey []byte) (u *commitment.Update, err error) {
	var enc []byte
	if sdc.roTtx != nil {
		enc, _, err = sdc.roTtx.GetLatest(kv.StorageDomain, plainKey)
	} else {
		enc, _, err = sdc.getter.GetLatest(kv.StorageDomain, plainKey)
	}
	if err != nil {
		return nil, err
	}

	u = &commitment.Update{
		Flags:      commitment.DeleteUpdate,
		StorageLen: len(enc),
	}
	if u.StorageLen > len(u.Storage) {
		u.StorageLen = len(u.Storage)
	}
	if u.StorageLen > 0 {
		u.Flags = commitment.StorageUpdate
		copy(u.Storage[:u.StorageLen], enc[:u.StorageLen])
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
