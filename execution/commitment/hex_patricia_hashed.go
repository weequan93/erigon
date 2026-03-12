// Copyright 2022 The Erigon Authors
// This file is part of Erigon.
//
// Erigon is free software: you can redistribute it and/or modify
// it under the terms of the GNU Lesser General Public License as published by
// the Free Software Foundation, either version 3 of the License, or
// (at your option) any later version.
//
// Erigon is distributed in the hope that it will be useful,
// but WITHOUT ANY WARRANTY; without even the implied warranty of
// MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE. See the
// GNU Lesser General Public License for more details.
//
// You should have received a copy of the GNU Lesser General Public License
// along with Erigon. If not, see <http://www.gnu.org/licenses/>.

package commitment

import (
	"bytes"
	"context"
	"encoding/binary"
	"encoding/hex"
	"errors"
	"fmt"
	"hash"
	"io"
	"math/bits"
	"os"
	"runtime"
	"sort"
	"strings"
	"sync"
	"sync/atomic"
	"time"

	"golang.org/x/crypto/sha3"

	"github.com/erigontech/erigon-lib/common"
	"github.com/erigontech/erigon-lib/common/dbg"
	"github.com/erigontech/erigon-lib/common/empty"
	"github.com/erigontech/erigon-lib/common/length"
	"github.com/erigontech/erigon-lib/crypto"
	"github.com/erigontech/erigon-lib/log/v3"
	"github.com/erigontech/erigon/execution/rlp"
	"github.com/erigontech/erigon/execution/trie"
	"github.com/erigontech/erigon/execution/types/accounts"
	witnesstypes "github.com/erigontech/erigon/execution/types/witness"
)

var (
	erigonCommitmentTraceKeys    = dbg.EnvBool("ERIGON_COMMITMENT_TRACE_KEYS", false)
	erigonCommitmentTraceKeysMax = dbg.EnvInt("ERIGON_COMMITMENT_TRACE_KEYS_MAX", 200)
	erigonBadRootDebug           = dbg.EnvBool("ERIGON_BAD_ROOT_DEBUG", false)
	erigonWitnessDiagSampleMax   = dbg.EnvInt("ERIGON_BAD_ROOT_WITNESS_KEY_SAMPLE_MAX", 24)
	erigonWitnessAccountDiagMax  = dbg.EnvInt("ERIGON_BAD_ROOT_WITNESS_ACCOUNT_DIAG_MAX", 200)
	erigonWitnessTombstoneLogMax = dbg.EnvInt("ERIGON_BAD_ROOT_WITNESS_TOMBSTONE_LOG_MAX", 300)
	// Witness diagnostics can optionally apply update payloads to in-memory grid
	// cells. This is OFF by default and must be explicitly enabled.
	// ERIGON_WITNESS_DISABLE_CTX_UPDATES_UNSAFE=true always wins and forces OFF.
	erigonWitnessApplyCtxUpdates = dbg.EnvBool("ERIGON_WITNESS_APPLY_CTX_UPDATES", false) &&
		!dbg.EnvBool("ERIGON_WITNESS_DISABLE_CTX_UPDATES_UNSAFE", false)
	// ModeDirect carries touched keys without canonical payloads. In record mode
	// we still need ctx-derived payloads to mutate touched keys toward post-state.
	// Keep this OFF by default; enable explicitly via env when diagnosing roots.
	erigonWitnessApplyCtxUpdatesModeDirect = dbg.EnvBool("ERIGON_WITNESS_APPLY_CTX_UPDATES_MODE_DIRECT", false) &&
		!dbg.EnvBool("ERIGON_WITNESS_DISABLE_CTX_UPDATES_MODE_DIRECT", false)
	// Backward-compatible alias retained for existing env setups. Treated as an
	// additional enable switch (not a stricter mode).
	erigonWitnessApplyCtxUpdatesModeDirectUnsafe = dbg.EnvBool("ERIGON_WITNESS_APPLY_CTX_UPDATES_MODE_DIRECT_UNSAFE", false)
	// Optional guard for witness diagnostics: when true, each witness cell read
	// is forced through PatriciaContext instead of reusing already-loaded cell data.
	// Default false to avoid turning valid in-memory cell payloads into tombstones
	// under as-of read constraints.
	erigonWitnessForceCtxReload = dbg.EnvBool("ERIGON_WITNESS_FORCE_CTX_RELOAD", false)
	erigonWitnessTracePlainKey  = common.FromHex(dbg.EnvString(
		"ERIGON_WITNESS_TRACE_PLAIN_KEY",
		dbg.EnvString("ERIGON_BAD_ROOT_PROBE_STORAGE_KEY", ""),
	))
	erigonWitnessTraceHashedKey = common.FromHex(dbg.EnvString("ERIGON_WITNESS_TRACE_HASHED_KEY", ""))
	erigonWitnessTracePrefix    = strings.TrimSpace(dbg.EnvString("ERIGON_WITNESS_TRACE_PREFIX", ""))
	erigonWitnessTraceRows      = dbg.EnvInt("ERIGON_WITNESS_TRACE_ROWS", 32)
	// Extra witness branch diagnostics (parent node roots + optional RLP snapshots).
	// Keep OFF by default due to very verbose logs.
	erigonWitnessTraceBranchDetail = dbg.EnvBool("ERIGON_WITNESS_TRACE_BRANCH_DETAIL", false)
	// Unsafe opt-in: only when true, allow ERIGON_WITNESS_DISABLE_KEYPOS_SKIP to
	// force processing rows already consumed by extension traversal.
	erigonWitnessAllowKeyPosDriftUnsafe = dbg.EnvBool("ERIGON_WITNESS_ALLOW_KEYPOS_DRIFT_UNSAFE", false)
	// Debug-only escape hatch: when true, do not skip rows whose selected nibble
	// appears already consumed by a previous extension while building witness trie.
	// This is guarded by ERIGON_WITNESS_ALLOW_KEYPOS_DRIFT_UNSAFE because forcing
	// already-consumed rows can corrupt witness shape and roots.
	erigonWitnessDisableKeyPosSkip = dbg.EnvBool("ERIGON_WITNESS_DISABLE_KEYPOS_SKIP", false) &&
		erigonWitnessAllowKeyPosDriftUnsafe
	// Capture non-embedded trie node RLP preimages generated during witness build.
	// Enabled by default in bad-root debug mode.
	erigonWitnessCaptureNodePreimages = dbg.EnvBool("ERIGON_WITNESS_CAPTURE_NODE_PREIMAGES", erigonBadRootDebug)

	erigonWitnessAccountDiagCount atomic.Uint64
	erigonWitnessTombstoneLogCnt  atomic.Uint64

	capturedWitnessNodePreimagesMu sync.Mutex
	capturedWitnessNodePreimages   = make(map[common.Hash][]byte)
)

func captureWitnessNodePreimage(preimage []byte) {
	if !erigonWitnessCaptureNodePreimages || len(preimage) == 0 {
		return
	}
	hash := crypto.Keccak256Hash(preimage)
	preimageCopy := common.Copy(preimage)

	capturedWitnessNodePreimagesMu.Lock()
	if _, exists := capturedWitnessNodePreimages[hash]; !exists {
		capturedWitnessNodePreimages[hash] = preimageCopy
	}
	capturedWitnessNodePreimagesMu.Unlock()
}

// captureWitnessNodePreimagesFromNode captures canonical RLP preimages for a
// materialized trie subnode (and descendants). This is a safety net for witness
// paths where we synthesize short/account bridge nodes that may not be reached
// by later proof traversal fallbacks.
func captureWitnessNodePreimagesFromNode(node trie.Node) {
	if !erigonWitnessCaptureNodePreimages || node == nil {
		return
	}
	tmpTrie := trie.NewInMemoryTrie(node)
	nodePreimages, err := tmpTrie.CollectNodeRLPPreimages()
	if err != nil {
		return
	}
	for _, preimage := range nodePreimages {
		captureWitnessNodePreimage(preimage)
	}
}

func ResetCapturedWitnessNodePreimages() {
	if !erigonWitnessCaptureNodePreimages {
		return
	}
	capturedWitnessNodePreimagesMu.Lock()
	clear(capturedWitnessNodePreimages)
	capturedWitnessNodePreimagesMu.Unlock()
}

func ConsumeCapturedWitnessNodePreimages() map[common.Hash][]byte {
	if !erigonWitnessCaptureNodePreimages {
		return nil
	}

	capturedWitnessNodePreimagesMu.Lock()
	defer capturedWitnessNodePreimagesMu.Unlock()

	if len(capturedWitnessNodePreimages) == 0 {
		return nil
	}
	out := make(map[common.Hash][]byte, len(capturedWitnessNodePreimages))
	for hash, preimage := range capturedWitnessNodePreimages {
		out[hash] = common.Copy(preimage)
	}
	clear(capturedWitnessNodePreimages)
	return out
}

func witnessDiagSampleMax() int {
	if erigonWitnessDiagSampleMax < 1 {
		return 1
	}
	if erigonWitnessDiagSampleMax > 256 {
		return 256
	}
	return erigonWitnessDiagSampleMax
}

func witnessAccountDiagMax() uint64 {
	if erigonWitnessAccountDiagMax < 1 {
		return 0
	}
	if erigonWitnessAccountDiagMax > 100000 {
		return 100000
	}
	return uint64(erigonWitnessAccountDiagMax)
}

func witnessTombstoneLogMax() uint64 {
	if erigonWitnessTombstoneLogMax < 1 {
		return 0
	}
	if erigonWitnessTombstoneLogMax > 100000 {
		return 100000
	}
	return uint64(erigonWitnessTombstoneLogMax)
}

func parseWitnessEnvBool(raw string, def bool) bool {
	raw = strings.TrimSpace(raw)
	if raw == "" {
		return def
	}
	switch strings.ToLower(raw) {
	case "1", "true", "yes", "y", "on":
		return true
	case "0", "false", "no", "n", "off":
		return false
	default:
		return def
	}
}

type witnessCtxUpdateRuntimeFlags struct {
	ApplyEffective       bool
	ApplyDisabledUnsafe  bool
	ModeDirectRequested  bool
	ModeDirectDisabled   bool
	ModeDirectEnabled    bool
	ModeDirectUnsafe     bool
	ModeDirectResolution string
}

func resolveWitnessCtxUpdateRuntimeFlags() witnessCtxUpdateRuntimeFlags {
	applyDisabledUnsafe := parseWitnessEnvBool(os.Getenv("ERIGON_WITNESS_DISABLE_CTX_UPDATES_UNSAFE"), false)
	applyRequested := parseWitnessEnvBool(os.Getenv("ERIGON_WITNESS_APPLY_CTX_UPDATES"), erigonWitnessApplyCtxUpdates)
	applyEffective := applyRequested && !applyDisabledUnsafe

	modeDirectRequested := parseWitnessEnvBool(os.Getenv("ERIGON_WITNESS_APPLY_CTX_UPDATES_MODE_DIRECT"), erigonWitnessApplyCtxUpdatesModeDirect)
	modeDirectDisabled := parseWitnessEnvBool(os.Getenv("ERIGON_WITNESS_DISABLE_CTX_UPDATES_MODE_DIRECT"), false)
	modeDirectUnsafe := parseWitnessEnvBool(os.Getenv("ERIGON_WITNESS_APPLY_CTX_UPDATES_MODE_DIRECT_UNSAFE"), erigonWitnessApplyCtxUpdatesModeDirectUnsafe)
	modeDirectEnabled := (modeDirectRequested || modeDirectUnsafe) && !modeDirectDisabled
	modeDirectApply := modeDirectEnabled && !applyDisabledUnsafe

	resolution := "ctx updates disabled (default)"
	if applyDisabledUnsafe && (applyRequested || modeDirectRequested || modeDirectUnsafe) {
		resolution = "ctx updates disabled by ERIGON_WITNESS_DISABLE_CTX_UPDATES_UNSAFE"
	} else if applyEffective {
		resolution = "ctx updates enabled via ERIGON_WITNESS_APPLY_CTX_UPDATES"
	} else if modeDirectApply {
		if modeDirectUnsafe && !modeDirectRequested {
			resolution = "ctx updates enabled via ERIGON_WITNESS_APPLY_CTX_UPDATES_MODE_DIRECT_UNSAFE"
		} else {
			resolution = "ctx updates enabled via mode-direct flags"
		}
	}

	return witnessCtxUpdateRuntimeFlags{
		ApplyEffective:       applyEffective,
		ApplyDisabledUnsafe:  applyDisabledUnsafe,
		ModeDirectRequested:  modeDirectRequested,
		ModeDirectDisabled:   modeDirectDisabled,
		ModeDirectEnabled:    modeDirectEnabled,
		ModeDirectUnsafe:     modeDirectUnsafe,
		ModeDirectResolution: resolution,
	}
}

func witnessTraceRowsMax() int {
	if erigonWitnessTraceRows < 1 {
		return 1
	}
	if erigonWitnessTraceRows > 128 {
		return 128
	}
	return erigonWitnessTraceRows
}

func shouldTraceWitnessKey(logPrefix string, plainKey, hashedKey []byte) bool {
	if !erigonBadRootDebug {
		return false
	}
	if erigonWitnessTracePrefix != "" && !strings.Contains(logPrefix, erigonWitnessTracePrefix) {
		return false
	}
	if len(erigonWitnessTracePlainKey) > 0 && bytes.Equal(plainKey, erigonWitnessTracePlainKey) {
		return true
	}
	if len(erigonWitnessTraceHashedKey) > 0 && bytes.Equal(hashedKey, erigonWitnessTraceHashedKey) {
		return true
	}
	return false
}

func (hph *HexPatriciaHashed) witnessTraceRowsSummary(hashedKey []byte) []string {
	rowLimit := hph.activeRows
	maxRows := witnessTraceRowsMax()
	if rowLimit > maxRows {
		rowLimit = maxRows
	}

	out := make([]string, 0, rowLimit)
	for row := 0; row < rowLimit; row++ {
		depth := hph.depths[row]
		selectedNibble := "n/a"
		if row < hph.currentKeyLen {
			selectedNibble = fmt.Sprintf("%x", hph.currentKey[row])
		}
		hashedNibble := "n/a"
		hashedNibblePos := depth - 1
		if hashedNibblePos >= 0 && hashedNibblePos < len(hashedKey) {
			hashedNibble = fmt.Sprintf("%x", hashedKey[hashedNibblePos])
		}

		nonEmpty := 0
		colSamples := make([]string, 0, 4)
		for col := 0; col < 16; col++ {
			cell := &hph.grid[row][col]
			if cell.IsEmpty() {
				continue
			}
			nonEmpty++
			if len(colSamples) >= 4 {
				continue
			}
			marker := ""
			if row < hph.currentKeyLen && byte(col) == hph.currentKey[row] {
				marker += "*"
			}
			if hashedNibblePos >= 0 && hashedNibblePos < len(hashedKey) && byte(col) == hashedKey[hashedNibblePos] {
				marker += "#"
			}
			colSamples = append(colSamples, fmt.Sprintf(
				"%x%s(h=%d ext=%d a=%d s=%d)",
				col,
				marker,
				cell.hashLen,
				cell.hashedExtLen,
				cell.accountAddrLen,
				cell.storageAddrLen,
			))
		}

		out = append(out, fmt.Sprintf(
			"row=%d depth=%d selected=%s hashed=%s before=%t after=%04x touch=%04x non_empty=%d cols=%v",
			row,
			depth,
			selectedNibble,
			hashedNibble,
			hph.branchBefore[row],
			hph.afterMap[row],
			hph.touchMap[row],
			nonEmpty,
			colSamples,
		))
	}
	return out
}

func allowWitnessAccountDiagLog() bool {
	if !erigonBadRootDebug {
		return false
	}
	max := witnessAccountDiagMax()
	if max == 0 {
		return false
	}
	return erigonWitnessAccountDiagCount.Add(1) <= max
}

func allowWitnessTombstoneLog() bool {
	if !erigonBadRootDebug {
		return false
	}
	max := witnessTombstoneLogMax()
	if max == 0 {
		return false
	}
	return erigonWitnessTombstoneLogCnt.Add(1) <= max
}

func witnessUpdateSummary(update *Update) string {
	if update == nil {
		return "<nil>"
	}
	if update.Flags&DeleteUpdate != 0 {
		return "Delete"
	}
	parts := make([]string, 0, 5)
	if update.Flags&BalanceUpdate != 0 {
		parts = append(parts, fmt.Sprintf("Balance=%s", update.Balance.String()))
	}
	if update.Flags&NonceUpdate != 0 {
		parts = append(parts, fmt.Sprintf("Nonce=%d", update.Nonce))
	}
	if update.Flags&CodeUpdate != 0 {
		parts = append(parts, fmt.Sprintf("Code=%s", update.CodeHash.Hex()))
	}
	if update.Flags&StorageUpdate != 0 {
		storageValue := "0x"
		if update.StorageLen > 0 {
			storageValue = fmt.Sprintf("0x%x", update.Storage[:update.StorageLen])
		}
		parts = append(parts, fmt.Sprintf("Storage(len=%d,val=%s)", update.StorageLen, storageValue))
	}
	if len(parts) == 0 {
		return fmt.Sprintf("Flags=%s", update.Flags.String())
	}
	return fmt.Sprintf("Flags=%s [%s]", update.Flags.String(), strings.Join(parts, ","))
}

// witnessStableNodeRoot recomputes a node root from its current shape and
// avoids reusing cached references from earlier hashes.
func witnessStableNodeRoot(node trie.Node) []byte {
	if node == nil {
		return nil
	}
	t := trie.NewInMemoryTrie(node)
	t.Reset()
	return t.Root()
}

func witnessUpdateEquivalent(a, b *Update) bool {
	if a == nil || b == nil {
		return a == b
	}
	if a.Flags != b.Flags {
		return false
	}
	if a.Flags&DeleteUpdate != 0 {
		return true
	}
	if a.Flags&BalanceUpdate != 0 && a.Balance.Cmp(&b.Balance) != 0 {
		return false
	}
	if a.Flags&NonceUpdate != 0 && a.Nonce != b.Nonce {
		return false
	}
	if a.Flags&CodeUpdate != 0 && a.CodeHash != b.CodeHash {
		return false
	}
	if a.Flags&StorageUpdate != 0 {
		if a.StorageLen != b.StorageLen {
			return false
		}
		if a.StorageLen > 0 && !bytes.Equal(a.Storage[:a.StorageLen], b.Storage[:b.StorageLen]) {
			return false
		}
	}
	return true
}

// keccakState wraps sha3.state. In addition to the usual hash methods, it also supports
// Read to get a variable amount of data from the hash state. Read is faster than Sum
// because it doesn't copy the internal state, but also modifies the internal state.
type keccakState interface {
	hash.Hash
	Read([]byte) (int, error)
}

// HexPatriciaHashed implements commitment based on patricia merkle tree with radix 16,
// with keys pre-hashed by keccak256
type HexPatriciaHashed struct {
	root cell // Root cell of the tree
	// How many rows (starting from row 0) are currently active and have corresponding selected columns
	// Last active row does not have selected column
	activeRows int
	// Length of the key that reflects current positioning of the grid. It may be larger than number of active rows,
	// if an account leaf cell represents multiple nibbles in the key
	currentKeyLen int
	accountKeyLen int
	// Rows of the grid correspond to the level of depth in the patricia tree
	// Columns of the grid correspond to pointers to the nodes further from the root
	grid          [128][16]cell // First 64 rows of this grid are for account trie, and next 64 rows are for storage trie
	currentKey    [128]byte     // For each row indicates which column is currently selected
	depths        [128]int      // For each row, the depth of cells in that row
	branchBefore  [128]bool     // For each row, whether there was a branch node in the database loaded in unfold
	touchMap      [128]uint16   // For each row, bitmap of cells that were either present before modification, or modified or deleted
	afterMap      [128]uint16   // For each row, bitmap of cells that were present after modification
	keccak        keccakState
	keccak2       keccakState
	rootChecked   bool // Set to false if it is not known whether the root is empty, set to true if it is checked
	rootTouched   bool
	rootPresent   bool
	trace         bool
	ctx           PatriciaContext
	hashAuxBuffer [128]byte     // buffer to compute cell hash or write hash-related things
	auxBuffer     *bytes.Buffer // auxiliary buffer used during branch updates encoding
	branchEncoder *BranchEncoder

	mounted      bool                 // true if this trie is mounted to some root trie
	mountedNib   int                  // if 0 <= nib <= 15 means mounted to some root. If -1, means it's a storage subtrie so must not be folded above depth 63
	mountedTries []*HexPatriciaHashed // list of mounted tries to unmount

	memoizationOff bool // if true, do not rely on memoized hashes
	//temp buffers
	accValBuf rlp.RlpEncodedBytes

	//processing metrics
	metrics       *Metrics
	depthsToTxNum [129]uint64 // endTxNum of file with branch data for that depth
	hadToLoadL    map[uint64]skipStat
}

// Clones current trie state to allow concurrent processing.
func (hph *HexPatriciaHashed) SpawnSubTrie(ctx PatriciaContext, forNibble int) *HexPatriciaHashed {
	subTrie := NewHexPatriciaHashed(hph.accountKeyLen, ctx)

	subTrie.mountTo(hph, forNibble)
	return subTrie
}

func NewHexPatriciaHashed(accountKeyLen int, ctx PatriciaContext) *HexPatriciaHashed {
	hph := &HexPatriciaHashed{
		ctx:           ctx,
		keccak:        sha3.NewLegacyKeccak256().(keccakState),
		keccak2:       sha3.NewLegacyKeccak256().(keccakState),
		accountKeyLen: accountKeyLen,
		auxBuffer:     bytes.NewBuffer(make([]byte, 8192)),
		hadToLoadL:    make(map[uint64]skipStat),
		accValBuf:     make(rlp.RlpEncodedBytes, 128),
		metrics:       NewMetrics(),
		branchEncoder: NewBranchEncoder(1024),
	}

	hph.branchEncoder.setMetrics(hph.metrics)
	return hph
}

type cell struct {
	hashedExtension [128]byte
	extension       [64]byte
	accountAddr     common.Address                                       // account plain key
	storageAddr     [length.Addr + length.Incarnation + length.Hash]byte // storage plain key
	hash            common.Hash                                          // cell hash
	stateHash       common.Hash
	hashedExtLen    int       // length of the hashed extension, if any
	extLen          int       // length of the extension, if any
	accountAddrLen  int       // length of account plain key
	storageAddrLen  int       // length of the storage plain key
	hashLen         int       // Length of the hash (or embedded)
	stateHashLen    int       // stateHash length, if > 0 can reuse
	loaded          loadFlags // folded Cell have only hash, unfolded have all fields
	Update                    // state update

	// temporary buffers
	hashBuf common.Hash
}

type loadFlags uint8

func (f loadFlags) String() string {
	var b strings.Builder
	if f == cellLoadNone {
		b.WriteString("false")
	} else {
		if f.account() {
			b.WriteString("Account ")
		}
		if f.storage() {
			b.WriteString("Storage ")
		}
	}
	return b.String()
}

func (f loadFlags) account() bool {
	return f&cellLoadAccount != 0
}

func (f loadFlags) storage() bool {
	return f&cellLoadStorage != 0
}

func (f loadFlags) addFlag(loadFlags loadFlags) loadFlags {
	if loadFlags == cellLoadNone {
		return f
	}
	return f | loadFlags
}

const (
	cellLoadNone    = loadFlags(0)
	cellLoadAccount = loadFlags(1)
	cellLoadStorage = loadFlags(2)
)

var (
	emptyRootHashBytes = empty.RootHash.Bytes()
)

func (cell *cell) hashAccKey(keccak keccakState, depth int) error {
	return hashKey(keccak, cell.accountAddr[:cell.accountAddrLen], cell.hashedExtension[:], depth, cell.hashBuf[:])
}

func (cell *cell) hashStorageKey(keccak keccakState, accountKeyLen, downOffset int, hashedKeyOffset int) error {
	var preimage []byte
	switch cell.storageAddrLen {
	case length.Addr + length.Hash: // address || slot
		preimage = cell.storageAddr[accountKeyLen:cell.storageAddrLen]
	case length.Addr + length.Incarnation + length.Hash: // address || incarnation || slot
		switch accountKeyLen {
		case 0:
			// drop incarnation, hash addr||slot
			var buf [length.Addr + length.Hash]byte
			copy(buf[:length.Addr], cell.storageAddr[:length.Addr])
			copy(buf[length.Addr:], cell.storageAddr[length.Addr+length.Incarnation:]) // skip inc
			preimage = buf[:]
		case length.Addr:
			// storage trie path: hash slot only (skip incarnation)
			preimage = cell.storageAddr[length.Addr+length.Incarnation : cell.storageAddrLen]
		default:
			preimage = cell.storageAddr[accountKeyLen:cell.storageAddrLen]
		}
	default:
		return fmt.Errorf("unexpected storage plain key len=%d (addr part=%d)", cell.storageAddrLen, accountKeyLen)
	}
	return hashKey(keccak, preimage, cell.hashedExtension[downOffset:], hashedKeyOffset, cell.hashBuf[:])
}

func (cell *cell) reset() {
	cell.accountAddrLen = 0
	cell.storageAddrLen = 0
	cell.hashedExtLen = 0
	cell.extLen = 0
	cell.hashLen = 0
	cell.stateHashLen = 0
	cell.loaded = cellLoadNone
	clear(cell.hashedExtension[:])
	clear(cell.extension[:])
	clear(cell.accountAddr[:])
	clear(cell.storageAddr[:])
	clear(cell.hash[:])
	cell.Update.Reset()
}

func (cell *cell) FullString() string {
	b := new(strings.Builder)
	b.WriteString("{")
	b.WriteString(fmt.Sprintf("loaded=%v ", cell.loaded))
	if cell.Deleted() {
		b.WriteString("DELETED ")
	}

	if cell.accountAddrLen > 0 {
		b.WriteString(fmt.Sprintf("addr=%x ", cell.accountAddr[:cell.accountAddrLen]))
		b.WriteString(fmt.Sprintf("balance=%s ", cell.Balance.String()))
		b.WriteString(fmt.Sprintf("nonce=%d ", cell.Nonce))
		if cell.CodeHash != empty.CodeHash {
			b.WriteString(fmt.Sprintf("codeHash=%x ", cell.CodeHash[:]))
		} else {
			b.WriteString("codeHash=EMPTY ")
		}
	}
	if cell.storageAddrLen > 0 {
		b.WriteString(fmt.Sprintf("addr[s]=%x ", cell.storageAddr[:cell.storageAddrLen]))
		b.WriteString(fmt.Sprintf("storage=%x ", cell.Storage[:cell.StorageLen]))
	}
	if cell.hashLen > 0 {
		b.WriteString(fmt.Sprintf("h=%x ", cell.hash[:cell.hashLen]))
	}
	if cell.stateHashLen > 0 {
		b.WriteString(fmt.Sprintf("memHash=%x ", cell.stateHash[:cell.stateHashLen]))
	}
	if cell.extLen > 0 {
		b.WriteString(fmt.Sprintf("extension=%x ", cell.extension[:cell.extLen]))
	}
	if cell.hashedExtLen > 0 {
		b.WriteString(fmt.Sprintf("hashedExtension=%x ", cell.hashedExtension[:cell.hashedExtLen]))
	}

	b.WriteString("}")
	return b.String()
}

func (cell *cell) setFromUpdate(update *Update) {
	cell.Update.Merge(update)
	if update.Flags&StorageUpdate != 0 {
		cell.loaded = cell.loaded.addFlag(cellLoadStorage)
		mxTrieStateLoadRate.Inc()
		hadToLoad.Add(1)
	}
	if update.Flags&BalanceUpdate != 0 || update.Flags&NonceUpdate != 0 || update.Flags&CodeUpdate != 0 {
		cell.loaded = cell.loaded.addFlag(cellLoadAccount)
		mxTrieStateLoadRate.Inc()
		hadToLoad.Add(1)
	}
}

func (cell *cell) fillFromUpperCell(upCell *cell, depth, depthIncrement int) {
	if upCell.hashedExtLen >= depthIncrement {
		cell.hashedExtLen = upCell.hashedExtLen - depthIncrement
	} else {
		cell.hashedExtLen = 0
	}
	if upCell.hashedExtLen > depthIncrement {
		copy(cell.hashedExtension[:], upCell.hashedExtension[depthIncrement:upCell.hashedExtLen])
	}
	if upCell.extLen >= depthIncrement {
		cell.extLen = upCell.extLen - depthIncrement
	} else {
		cell.extLen = 0
	}
	if upCell.extLen > depthIncrement {
		copy(cell.extension[:], upCell.extension[depthIncrement:upCell.extLen])
	}
	if depth <= 64 {
		cell.accountAddrLen = upCell.accountAddrLen
		if upCell.accountAddrLen > 0 {
			copy(cell.accountAddr[:], upCell.accountAddr[:cell.accountAddrLen])
			cell.Balance.Set(&upCell.Balance)
			cell.Nonce = upCell.Nonce
			cell.CodeHash = upCell.CodeHash
			cell.extLen = upCell.extLen
			if upCell.extLen > 0 {
				copy(cell.extension[:], upCell.extension[:upCell.extLen])
			}
		}
	} else {
		cell.accountAddrLen = 0
	}
	cell.storageAddrLen = upCell.storageAddrLen
	if upCell.storageAddrLen > 0 {
		copy(cell.storageAddr[:], upCell.storageAddr[:upCell.storageAddrLen])
		cell.StorageLen = upCell.StorageLen
		if upCell.StorageLen > 0 {
			copy(cell.Storage[:], upCell.Storage[:upCell.StorageLen])
		}
	}
	cell.hashLen = upCell.hashLen
	if upCell.hashLen > 0 {
		copy(cell.hash[:], upCell.hash[:upCell.hashLen])
	}
	cell.loaded = upCell.loaded
}

// fillFromLowerCell fills the cell with the data from the cell of the lower row during fold
func (cell *cell) fillFromLowerCell(lowCell *cell, lowDepth int, preExtension []byte, nibble int) {
	if lowCell.accountAddrLen > 0 || lowDepth < 64 {
		cell.accountAddrLen = lowCell.accountAddrLen
	}
	if lowCell.accountAddrLen > 0 {
		copy(cell.accountAddr[:], lowCell.accountAddr[:cell.accountAddrLen])
		cell.Balance.Set(&lowCell.Balance)
		cell.Nonce = lowCell.Nonce
		cell.CodeHash = lowCell.CodeHash
	}
	cell.storageAddrLen = lowCell.storageAddrLen
	if lowCell.storageAddrLen > 0 {
		copy(cell.storageAddr[:], lowCell.storageAddr[:cell.storageAddrLen])
		cell.StorageLen = lowCell.StorageLen
		if lowCell.StorageLen > 0 {
			copy(cell.Storage[:], lowCell.Storage[:lowCell.StorageLen])
		}
	}
	if lowCell.hashLen > 0 {
		if (lowCell.accountAddrLen == 0 && lowDepth < 64) || (lowCell.storageAddrLen == 0 && lowDepth > 64) {
			// Extension is related to either accounts branch node, or storage branch node, we prepend it by preExtension | nibble
			if len(preExtension) > 0 {
				copy(cell.extension[:], preExtension)
			}
			cell.extension[len(preExtension)] = byte(nibble)
			if lowCell.extLen > 0 {
				copy(cell.extension[1+len(preExtension):], lowCell.extension[:lowCell.extLen])
			}
			cell.extLen = lowCell.extLen + 1 + len(preExtension)
		} else {
			// Extension is related to a storage branch node, so we copy it upwards as is
			cell.extLen = lowCell.extLen
			if lowCell.extLen > 0 {
				copy(cell.extension[:], lowCell.extension[:lowCell.extLen])
			}
		}
	}
	cell.hashLen = lowCell.hashLen
	if lowCell.hashLen > 0 {
		copy(cell.hash[:], lowCell.hash[:lowCell.hashLen])
	}
	cell.loaded = lowCell.loaded
}

func (cell *cell) deriveHashedKeys(depth int, keccak keccakState, accountKeyLen int) error {
	extraLen := 0
	if cell.accountAddrLen > 0 {
		if depth > 64 {
			return errors.New("deriveHashedKeys accountAddr present at depth > 64")
		}
		extraLen = 64 - depth
	}
	if cell.storageAddrLen > 0 {
		if depth >= 64 {
			extraLen = 128 - depth
		} else {
			extraLen += 64
		}
	}
	if extraLen > 0 {
		if cell.hashedExtLen > 0 {
			copy(cell.hashedExtension[extraLen:], cell.hashedExtension[:cell.hashedExtLen])
		}
		cell.hashedExtLen = min(extraLen+cell.hashedExtLen, len(cell.hashedExtension))
		var hashedKeyOffset, downOffset int
		if cell.accountAddrLen > 0 {
			if err := cell.hashAccKey(keccak, depth); err != nil {
				return err
			}
			downOffset = 64 - depth
		}
		if cell.storageAddrLen > 0 {
			if depth >= 64 {
				hashedKeyOffset = depth - 64
			}
			if depth == 0 {
				accountKeyLen = 0
			}
			if err := cell.hashStorageKey(keccak, accountKeyLen, downOffset, hashedKeyOffset); err != nil {
				return err
			}
		}
	}
	return nil
}

func (cell *cell) fillFromFields(data []byte, pos int, fieldBits cellFields) (int, error) {
	fields := []struct {
		flag      cellFields
		lenField  *int
		dataField []byte
		extraFunc func(int)
	}{
		{fieldExtension, &cell.hashedExtLen, cell.hashedExtension[:], func(l int) {
			cell.extLen = l
			if l > 0 {
				copy(cell.extension[:], cell.hashedExtension[:l])
			}
		}},
		{fieldAccountAddr, &cell.accountAddrLen, cell.accountAddr[:], nil},
		{fieldStorageAddr, &cell.storageAddrLen, cell.storageAddr[:], nil},
		{fieldHash, &cell.hashLen, cell.hash[:], nil},
		{fieldStateHash, &cell.stateHashLen, cell.stateHash[:], nil},
	}

	for _, f := range fields {
		if fieldBits&f.flag != 0 {
			l, n, err := readUvarint(data[pos:])
			if err != nil {
				return 0, err
			}
			pos += n

			if len(data) < pos+int(l) {
				return 0, fmt.Errorf("buffer too small for %v", f.flag)
			}

			*f.lenField = int(l)
			if l > 0 {
				copy(f.dataField, data[pos:pos+int(l)])
				pos += int(l)
			}
			if f.extraFunc != nil {
				f.extraFunc(int(l))
			}
		} else {
			*f.lenField = 0
			if f.flag == fieldExtension {
				cell.extLen = 0
			}
		}
	}

	if fieldBits&fieldAccountAddr != 0 {
		cell.CodeHash = empty.CodeHash
	}
	return pos, nil
}

func readUvarint(data []byte) (uint64, int, error) {
	l, n := binary.Uvarint(data)
	if n == 0 {
		return 0, 0, errors.New("buffer too small for length")
	} else if n < 0 {
		return 0, 0, errors.New("value overflow for length")
	}
	return l, n, nil
}

func (cell *cell) accountForHashing(buffer []byte, storageRootHash common.Hash) int {
	balanceBytes := 0
	if !cell.Balance.LtUint64(128) {
		balanceBytes = cell.Balance.ByteLen()
	}

	var nonceBytes int
	if cell.Nonce < 128 && cell.Nonce != 0 {
		nonceBytes = 0
	} else {
		nonceBytes = common.BitLenToByteLen(bits.Len64(cell.Nonce))
	}

	var structLength = uint(balanceBytes + nonceBytes + 2)
	structLength += 66 // Two 32-byte arrays + 2 prefixes

	var pos int
	if structLength < 56 {
		buffer[0] = byte(192 + structLength)
		pos = 1
	} else {
		lengthBytes := common.BitLenToByteLen(bits.Len(structLength))
		buffer[0] = byte(247 + lengthBytes)

		for i := lengthBytes; i > 0; i-- {
			buffer[i] = byte(structLength)
			structLength >>= 8
		}

		pos = lengthBytes + 1
	}

	// Encoding nonce
	if cell.Nonce < 128 && cell.Nonce != 0 {
		buffer[pos] = byte(cell.Nonce)
	} else {
		buffer[pos] = byte(128 + nonceBytes)
		var nonce = cell.Nonce
		for i := nonceBytes; i > 0; i-- {
			buffer[pos+i] = byte(nonce)
			nonce >>= 8
		}
	}
	pos += 1 + nonceBytes

	// Encoding balance
	if cell.Balance.LtUint64(128) && !cell.Balance.IsZero() {
		buffer[pos] = byte(cell.Balance.Uint64())
		pos++
	} else {
		buffer[pos] = byte(128 + balanceBytes)
		pos++
		cell.Balance.WriteToSlice(buffer[pos : pos+balanceBytes])
		pos += balanceBytes
	}

	// Encoding Root and CodeHash
	buffer[pos] = 128 + 32
	pos++
	copy(buffer[pos:], storageRootHash[:])
	pos += 32
	buffer[pos] = 128 + 32
	pos++
	copy(buffer[pos:], cell.CodeHash[:])
	pos += 32
	return pos
}

func (hph *HexPatriciaHashed) witnessCaptureMemoizedStorageLeafPreimage(cell *cell, hashedKeyOffset int, singleton bool) {
	if !erigonWitnessCaptureNodePreimages || cell == nil || cell.stateHashLen != length.Hash {
		return
	}
	keyLen := 64 - hashedKeyOffset + 1
	if keyLen <= 0 || keyLen > len(cell.hashedExtension) {
		return
	}
	leafHash, err := hph.leafHashWithKeyVal(
		make([]byte, 0, length.Hash+1),
		cell.hashedExtension[:keyLen],
		cell.Storage[:cell.StorageLen],
		singleton,
	)
	if err != nil || len(leafHash) != length.Hash+1 {
		return
	}
	if !bytes.Equal(leafHash[1:], cell.stateHash[:cell.stateHashLen]) {
		return
	}
	// completeLeafHash captures node RLP preimages when enabled.
}

func (hph *HexPatriciaHashed) witnessCaptureMemoizedAccountLeafPreimage(c *cell, depth int, storageRootHash common.Hash) {
	if !erigonWitnessCaptureNodePreimages || c == nil || c.stateHashLen != length.Hash {
		return
	}
	keyLen := 65 - depth
	if keyLen <= 0 || keyLen > len(c.hashedExtension) {
		return
	}

	rootCandidates := make([]common.Hash, 0, 4)
	addRootCandidate := func(root common.Hash) {
		for _, existing := range rootCandidates {
			if existing == root {
				return
			}
		}
		rootCandidates = append(rootCandidates, root)
	}
	addRootCandidate(storageRootHash)
	if c.hashLen == length.Hash {
		var hashRoot common.Hash
		copy(hashRoot[:], c.hash[:])
		addRootCandidate(hashRoot)
	}
	addRootCandidate(empty.RootHash)

	accountCandidates := make([]*cell, 0, 2)
	accountCandidates = append(accountCandidates, c)
	if c.accountAddrLen > 0 {
		if accountUpdate, err := hph.ctx.Account(c.accountAddr[:c.accountAddrLen]); err == nil && accountUpdate != nil && !accountUpdate.Deleted() {
			if accountUpdate.StorageLen == length.Hash {
				var updateRoot common.Hash
				copy(updateRoot[:], accountUpdate.Storage[:length.Hash])
				addRootCandidate(updateRoot)
			}
			// Try account payload from context as an additional candidate.
			candidate := *c
			candidate.Nonce = accountUpdate.Nonce
			candidate.Balance = accountUpdate.Balance
			candidate.CodeHash = accountUpdate.CodeHash
			candidate.loaded |= cellLoadAccount
			accountCandidates = append(accountCandidates, &candidate)
		}
	}

	var valBuf [128]byte
	for _, rootCandidate := range rootCandidates {
		for _, accountCandidate := range accountCandidates {
			valLen := accountCandidate.accountForHashing(valBuf[:], rootCandidate)
			leafHash, err := hph.accountLeafHashWithKey(
				make([]byte, 0, length.Hash+1),
				accountCandidate.hashedExtension[:keyLen],
				rlp.RlpEncodedBytes(valBuf[:valLen]),
			)
			if err != nil || len(leafHash) != length.Hash+1 {
				continue
			}
			if bytes.Equal(leafHash[1:], c.stateHash[:c.stateHashLen]) {
				// completeLeafHash captures node RLP preimages when enabled.
				return
			}
		}
	}
}

func (hph *HexPatriciaHashed) completeLeafHash(buf []byte, compactLen int, key []byte, compact0 byte, ni int, val rlp.RlpSerializable, singleton bool) ([]byte, error) {
	// Compute the total length of binary representation
	var kp, kl int
	var keyPrefix [1]byte
	if compactLen > 1 {
		keyPrefix[0] = 0x80 + byte(compactLen)
		kp = 1
		kl = compactLen
	} else {
		kl = 1
	}

	totalLen := kp + kl + val.DoubleRLPLen()
	var lenPrefix [4]byte
	pl := rlp.GenerateStructLen(lenPrefix[:], totalLen)
	canEmbed := !singleton && totalLen+pl < length.Hash
	var writer io.Writer
	var nodePreimageBuf bytes.Buffer
	if canEmbed {
		//hph.byteArrayWriter.Setup(buf)
		hph.auxBuffer.Reset()
		writer = hph.auxBuffer
	} else {
		hph.keccak.Reset()
		if erigonWitnessCaptureNodePreimages {
			nodePreimageBuf.Reset()
			writer = io.MultiWriter(hph.keccak, &nodePreimageBuf)
		} else {
			writer = hph.keccak
		}
	}
	if _, err := writer.Write(lenPrefix[:pl]); err != nil {
		return nil, err
	}
	if _, err := writer.Write(keyPrefix[:kp]); err != nil {
		return nil, err
	}
	b := [1]byte{compact0}
	if _, err := writer.Write(b[:]); err != nil {
		return nil, err
	}
	for i := 1; i < compactLen; i++ {
		b[0] = key[ni]*16 + key[ni+1]
		if _, err := writer.Write(b[:]); err != nil {
			return nil, err
		}
		ni += 2
	}
	var prefixBuf [8]byte
	if err := val.ToDoubleRLP(writer, prefixBuf[:]); err != nil {
		return nil, err
	}
	if canEmbed {
		buf = hph.auxBuffer.Bytes()
	} else {
		if erigonWitnessCaptureNodePreimages {
			captureWitnessNodePreimage(nodePreimageBuf.Bytes())
		}
		var hashBuf [33]byte
		hashBuf[0] = 0x80 + length.Hash
		if _, err := hph.keccak.Read(hashBuf[1:]); err != nil {
			return nil, err
		}
		buf = append(buf, hashBuf[:]...)
	}
	return buf, nil
}

func (hph *HexPatriciaHashed) leafHashWithKeyVal(buf, key []byte, val rlp.RlpSerializableBytes, singleton bool) ([]byte, error) {
	// Write key
	var compactLen int
	var ni int
	var compact0 byte
	compactLen = (len(key)-1)/2 + 1
	if len(key)&1 == 0 {
		compact0 = 0x30 + key[0] // Odd: (3<<4) + first nibble
		ni = 1
	} else {
		compact0 = 0x20
	}
	return hph.completeLeafHash(buf, compactLen, key, compact0, ni, val, singleton)
}

func (hph *HexPatriciaHashed) accountLeafHashWithKey(buf, key []byte, val rlp.RlpSerializable) ([]byte, error) {
	// Write key
	var compactLen int
	var ni int
	var compact0 byte
	if hasTerm(key) {
		compactLen = (len(key)-1)/2 + 1
		if len(key)&1 == 0 {
			compact0 = 48 + key[0] // Odd (1<<4) + first nibble
			ni = 1
		} else {
			compact0 = 32
		}
	} else {
		compactLen = len(key)/2 + 1
		if len(key)&1 == 1 {
			compact0 = terminatorHexByte + key[0] // Odd (1<<4) + first nibble
			ni = 1
		}
	}
	return hph.completeLeafHash(buf, compactLen, key, compact0, ni, val, true)
}

func (hph *HexPatriciaHashed) extensionHash(key []byte, hash []byte) (common.Hash, error) {
	var hashBuf common.Hash

	// Compute the total length of binary representation
	var kp, kl int
	// Write key
	var compactLen int
	var ni int
	var compact0 byte
	if hasTerm(key) {
		compactLen = (len(key)-1)/2 + 1
		if len(key)&1 == 0 {
			compact0 = 0x30 + key[0] // Odd: (3<<4) + first nibble
			ni = 1
		} else {
			compact0 = 0x20
		}
	} else {
		compactLen = len(key)/2 + 1
		if len(key)&1 == 1 {
			compact0 = 0x10 + key[0] // Odd: (1<<4) + first nibble
			ni = 1
		}
	}
	var keyPrefix [1]byte
	if compactLen > 1 {
		keyPrefix[0] = 0x80 + byte(compactLen)
		kp = 1
		kl = compactLen
	} else {
		kl = 1
	}
	totalLen := kp + kl + 33
	var lenPrefix [4]byte
	pt := rlp.GenerateStructLen(lenPrefix[:], totalLen)
	hph.keccak.Reset()

	writer := io.Writer(hph.keccak)
	var nodePreimageBuf bytes.Buffer
	if erigonWitnessCaptureNodePreimages {
		nodePreimageBuf.Reset()
		writer = io.MultiWriter(hph.keccak, &nodePreimageBuf)
	}

	if _, err := writer.Write(lenPrefix[:pt]); err != nil {
		return hashBuf, err
	}
	if _, err := writer.Write(keyPrefix[:kp]); err != nil {
		return hashBuf, err
	}
	var b [1]byte
	b[0] = compact0
	if _, err := writer.Write(b[:]); err != nil {
		return hashBuf, err
	}
	for i := 1; i < compactLen; i++ {
		b[0] = key[ni]*16 + key[ni+1]
		if _, err := writer.Write(b[:]); err != nil {
			return hashBuf, err
		}
		ni += 2
	}
	b[0] = 0x80 + length.Hash
	if _, err := writer.Write(b[:]); err != nil {
		return hashBuf, err
	}
	if _, err := writer.Write(hash); err != nil {
		return hashBuf, err
	}
	// Replace previous hash with the new one
	if _, err := hph.keccak.Read(hashBuf[:]); err != nil {
		return hashBuf, err
	}
	if erigonWitnessCaptureNodePreimages {
		captureWitnessNodePreimage(nodePreimageBuf.Bytes())
	}
	return hashBuf, nil
}

func (hph *HexPatriciaHashed) computeCellHashLen(cell *cell, depth int) int {
	if cell.storageAddrLen > 0 && depth >= 64 {
		if cell.stateHashLen > 0 {
			return cell.stateHashLen + 1
		}

		keyLen := 128 - depth + 1 // Length of hex key with terminator character
		var kp, kl int
		compactLen := (keyLen-1)/2 + 1
		if compactLen > 1 {
			kp = 1
			kl = compactLen
		} else {
			kl = 1
		}
		val := rlp.RlpSerializableBytes(cell.Storage[:cell.StorageLen])
		totalLen := kp + kl + val.DoubleRLPLen()
		var lenPrefix [4]byte
		pt := rlp.GenerateStructLen(lenPrefix[:], totalLen)
		if totalLen+pt < length.Hash {
			return totalLen + pt
		}
	}
	return length.Hash + 1
}

func (hph *HexPatriciaHashed) witnessComputeCellHashWithStorage(cell *cell, depth int, buf []byte) ([]byte, bool, []byte, error) {
	if cell == nil {
		return nil, false, nil, errors.New("witnessComputeCellHashWithStorage: nil cell")
	}
	// Witness extraction must be read-only over the shared grid state.
	// Work on a copy so memo/loaded/hash fields mutated during hash assembly
	// do not leak into subsequent keys and skew final root recomputation.
	work := *cell
	cell = &work

	var err error
	var storageRootHash common.Hash
	var storageRootHashIsSet bool
	if hph.memoizationOff {
		// We already operate on a local copy, so preserving stateHashLen is safe
		// and required for hash-only/account-boundary cells where as-of account
		// reads can legitimately return Delete. Clearing stateHashLen here turns
		// those cells into empty-root fallbacks and corrupts branch child hashes.
		if erigonWitnessForceCtxReload {
			cell.loaded = cellLoadNone
		}
	}
	if cell.storageAddrLen > 0 {
		var hashedKeyOffset int
		if depth >= 64 {
			hashedKeyOffset = depth - 64
		}
		singleton := depth <= 64
		koffset := hph.accountKeyLen
		if depth == 0 && cell.accountAddrLen == 0 {
			// if account key is empty, then we need to hash storage key from the key beginning
			koffset = 0
		}
		if err = hashKey(hph.keccak, cell.storageAddr[koffset:cell.storageAddrLen], cell.hashedExtension[:], hashedKeyOffset, cell.hashBuf[:]); err != nil {
			return nil, storageRootHashIsSet, nil, err
		}
		cell.hashedExtension[64-hashedKeyOffset] = terminatorHexByte // Add terminator

		if cell.stateHashLen > 0 {
			// Recording/validation needs concrete node preimages. If this cell only
			// carries a memoized hash, try materializing payload from PatriciaContext
			// and recomputing instead of returning a hash-only reference.
			if hph.memoizationOff && !cell.loaded.storage() {
				hph.metrics.StorageLoad(cell.storageAddr[:cell.storageAddrLen])
				if update, loadErr := hph.ctx.Storage(cell.storageAddr[:cell.storageAddrLen]); loadErr == nil && update != nil && !update.Deleted() {
					cell.setFromUpdate(update)
					cell.stateHashLen = 0
				} else if hph.trace {
					fmt.Printf("REUSE storage stateHash fallback (materialize failed) spk=%x err=%v deleted=%v nil=%v\n",
						cell.storageAddr[:cell.storageAddrLen], loadErr, update != nil && update.Deleted(), update == nil)
				}
			}
		}
		if cell.stateHashLen > 0 {
			hph.witnessCaptureMemoizedStorageLeafPreimage(cell, hashedKeyOffset, singleton)
			res := append([]byte{160}, cell.stateHash[:cell.stateHashLen]...)
			hph.keccak.Reset()
			if hph.trace {
				fmt.Printf("REUSED stateHash %x spk %x\n", res, cell.storageAddr[:cell.storageAddrLen])
			}
			mxTrieStateSkipRate.Inc()
			skippedLoad.Add(1)
			if !singleton {
				return res, storageRootHashIsSet, nil, err
			} else {
				storageRootHashIsSet = true
				storageRootHash = *(*common.Hash)(res[1:])
				//copy(storageRootHash[:], res[1:])
				//cell.stateHashLen = 0
			}
		} else {
			if !cell.loaded.storage() {
				hph.metrics.StorageLoad(cell.storageAddr[:cell.storageAddrLen])
				update, err := hph.ctx.Storage(cell.storageAddr[:cell.storageAddrLen])
				if err != nil {
					return nil, storageRootHashIsSet, nil, err
				}
				cell.setFromUpdate(update)
				if hph.trace {
					fmt.Printf("Storage %x was not loaded\n", cell.storageAddr[:cell.storageAddrLen])
				}
			}
			if singleton {
				if hph.trace {
					fmt.Printf("leafHashWithKeyVal(singleton) for [%x]=>[%x]\n", cell.hashedExtension[:64-hashedKeyOffset+1], cell.Storage[:cell.StorageLen])
				}
				aux := make([]byte, 0, 33)
				if aux, err = hph.leafHashWithKeyVal(aux, cell.hashedExtension[:64-hashedKeyOffset+1], cell.Storage[:cell.StorageLen], true); err != nil {
					return nil, storageRootHashIsSet, nil, err
				}
				if hph.trace {
					fmt.Printf("leafHashWithKeyVal(singleton) storage hash [%x]\n", aux)
				}
				storageRootHash = *(*common.Hash)(aux[1:])
				storageRootHashIsSet = true
				cell.stateHashLen = 0
				hadToReset.Add(1)
			} else {
				if hph.trace {
					fmt.Printf("leafHashWithKeyVal for [%x]=>[%x] %v\n", cell.hashedExtension[:64-hashedKeyOffset+1], cell.Storage[:cell.StorageLen], cell.String())
				}
				leafHash, err := hph.leafHashWithKeyVal(buf, cell.hashedExtension[:64-hashedKeyOffset+1], cell.Storage[:cell.StorageLen], false)
				if err != nil {
					return nil, storageRootHashIsSet, nil, err
				}

				copy(cell.stateHash[:], leafHash[1:])
				cell.stateHashLen = len(leafHash) - 1
				if hph.trace {
					fmt.Printf("STATE HASH storage memoized %x spk %x\n", leafHash, cell.storageAddr[:cell.storageAddrLen])
				}

				return leafHash, storageRootHashIsSet, storageRootHash[:], nil
			}
		}
	}
	if cell.accountAddrLen > 0 {
		if err := hashKey(hph.keccak, cell.accountAddr[:cell.accountAddrLen], cell.hashedExtension[:], depth, cell.hashBuf[:]); err != nil {
			return nil, storageRootHashIsSet, nil, err
		}
		cell.hashedExtension[64-depth] = terminatorHexByte // Add terminator
		if !storageRootHashIsSet {
			if cell.storageAddrLen > 0 && depth <= 64 {
				// Storage exists but root wasn't set; compute from singleton storage leaf.
				var hashedKeyOffset int
				if depth >= 64 {
					hashedKeyOffset = depth - 64
				}
				koffset := hph.accountKeyLen
				if depth == 0 && cell.accountAddrLen == 0 {
					koffset = 0
				}
				var storageExt [65]byte
				var storageHashBuf [64]byte
				if err = hashKey(hph.keccak, cell.storageAddr[koffset:cell.storageAddrLen], storageExt[:], hashedKeyOffset, storageHashBuf[:]); err != nil {
					return nil, storageRootHashIsSet, nil, err
				}
				storageExt[64-hashedKeyOffset] = terminatorHexByte
				aux := make([]byte, 0, 33)
				if aux, err = hph.leafHashWithKeyVal(aux, storageExt[:64-hashedKeyOffset+1], cell.Storage[:cell.StorageLen], true); err != nil {
					return nil, storageRootHashIsSet, nil, err
				}
				storageRootHash = *(*common.Hash)(aux[1:])
				storageRootHashIsSet = true
			}
		}
		if !storageRootHashIsSet {
			if cell.extLen > 0 { // Extension
				if cell.hashLen == 0 {
					return nil, storageRootHashIsSet, nil, errors.New("computeCellHash extension without hash")
				}
				if hph.trace {
					fmt.Printf("extensionHash for [%x]=>[%x]\n", cell.extension[:cell.extLen], cell.hash[:cell.hashLen])
				}
				if storageRootHash, err = hph.extensionHash(cell.extension[:cell.extLen], cell.hash[:cell.hashLen]); err != nil {
					return nil, storageRootHashIsSet, nil, err
				}
				if hph.trace {
					fmt.Printf("EXTENSION HASH %x DROPS stateHash\n", storageRootHash)
				}
				cell.stateHashLen = 0
				hadToReset.Add(1)
			} else if cell.hashLen > 0 {
				storageRootHash = cell.hash
				storageRootHashIsSet = true
			} else {
				storageRootHash = empty.RootHash
			}
		}
		if !cell.loaded.account() {
			// Recording/validation needs concrete node preimages. When possible,
			// materialize account payload and recompute leaf hash instead of
			// returning a memoized hash-only reference.
			if cell.stateHashLen > 0 && hph.memoizationOff {
				hph.metrics.AccountLoad(cell.accountAddr[:cell.accountAddrLen])
				if update, loadErr := hph.ctx.Account(cell.accountAddr[:cell.accountAddrLen]); loadErr == nil && update != nil && !update.Deleted() {
					cell.setFromUpdate(update)
					cell.stateHashLen = 0
				} else if hph.trace {
					fmt.Printf("REUSE account stateHash fallback (materialize failed) apk=%x err=%v deleted=%v nil=%v\n",
						cell.accountAddr[:cell.accountAddrLen], loadErr, update != nil && update.Deleted(), update == nil)
				}
			}
			if cell.stateHashLen > 0 {
				hph.witnessCaptureMemoizedAccountLeafPreimage(cell, depth, storageRootHash)
				res := append([]byte{160}, cell.stateHash[:cell.stateHashLen]...)
				hph.keccak.Reset()

				mxTrieStateSkipRate.Inc()
				skippedLoad.Add(1)
				if hph.trace {
					fmt.Printf("REUSED stateHash %x apk %x\n", res, cell.accountAddr[:cell.accountAddrLen])
				}
				return res, storageRootHashIsSet, storageRootHash[:], nil
			}
			// storage root update or extension update could invalidate older stateHash, so we need to reload state
			hph.metrics.AccountLoad(cell.accountAddr[:cell.accountAddrLen])
			update, err := hph.ctx.Account(cell.accountAddr[:cell.accountAddrLen])
			if err != nil {
				return nil, storageRootHashIsSet, storageRootHash[:], err
			}
			if update != nil && update.Deleted() {
				// Missing account at this as-of point: keep hash-only commitment
				// branch semantics. Materializing an empty account leaf here can
				// rewrite sibling branch roots and corrupt witness reconstruction.
				//
				// Important: do NOT mark the cell as deleted here. This helper runs
				// repeatedly during witness extraction and must remain read-only over
				// grid membership semantics; leaking Delete flags into the shared
				// grid causes later keys to be treated as tombstones.
				if allowWitnessTombstoneLog() {
					log.Warn(
						"witness account tombstone fallback",
						"section", "compute_cell_hash",
						"account", fmt.Sprintf("0x%x", cell.accountAddr[:cell.accountAddrLen]),
						"depth", depth,
						"hash_len", cell.hashLen,
						"state_hash_len", cell.stateHashLen,
						"loaded", cell.loaded.String(),
						"cell_deleted_before", cell.Deleted(),
						"force_ctx_reload", erigonWitnessForceCtxReload,
					)
				}
				if cell.stateHashLen > 0 {
					out := append(buf[:0], 0x80+byte(cell.stateHashLen))
					out = append(out, cell.stateHash[:cell.stateHashLen]...)
					return out, storageRootHashIsSet, storageRootHash[:], nil
				}
				if cell.hashLen > 0 {
					buf = append(buf[:0], 0x80+byte(cell.hashLen))
					buf = append(buf, cell.hash[:cell.hashLen]...)
					return buf, storageRootHashIsSet, storageRootHash[:], nil
				}
				// No account payload/hash is available for this touched path.
				// Keep a deterministic fallback hash for callers that still expect
				// a byte slice, while trie assembly treats this as an empty child.
				return append(append(buf[:0], 0x80+32), emptyRootHashBytes...), storageRootHashIsSet, storageRootHash[:], nil
			}
			cell.setFromUpdate(update)
		}

		var valBuf [128]byte
		valLen := cell.accountForHashing(valBuf[:], storageRootHash)
		if hph.trace {
			fmt.Printf("accountLeafHashWithKey for [%x]=>[%x]\n", cell.hashedExtension[:65-depth], rlp.RlpEncodedBytes(valBuf[:valLen]))
		}
		leafHash, err := hph.accountLeafHashWithKey(buf, cell.hashedExtension[:65-depth], rlp.RlpEncodedBytes(valBuf[:valLen]))
		if err != nil {
			return nil, storageRootHashIsSet, nil, err
		}
		if hph.trace {
			fmt.Printf("STATE HASH account memoized %x\n", leafHash)
		}
		copy(cell.stateHash[:], leafHash[1:])
		cell.stateHashLen = len(leafHash) - 1
		return leafHash, storageRootHashIsSet, storageRootHash[:], nil
	}

	buf = append(buf, 0x80+32)
	if cell.extLen > 0 { // Extension
		if cell.hashLen > 0 {
			if hph.trace {
				fmt.Printf("extensionHash for [%x]=>[%x]\n", cell.extension[:cell.extLen], cell.hash[:cell.hashLen])
			}
			var hash common.Hash
			if hash, err = hph.extensionHash(cell.extension[:cell.extLen], cell.hash[:cell.hashLen]); err != nil {
				return nil, storageRootHashIsSet, storageRootHash[:], err
			}
			buf = append(buf, hash[:]...)
		} else {
			return nil, storageRootHashIsSet, storageRootHash[:], errors.New("computeCellHash extension without hash")
		}
	} else if cell.hashLen > 0 {
		buf = append(buf, cell.hash[:cell.hashLen]...)
	} else if storageRootHashIsSet {
		buf = append(buf, storageRootHash[:]...)
		copy(cell.hash[:], storageRootHash[:])
		cell.hashLen = len(storageRootHash)
	} else {
		buf = append(buf, emptyRootHashBytes...)
	}
	return buf, storageRootHashIsSet, storageRootHash[:], nil
}

func (hph *HexPatriciaHashed) computeCellHash(cell *cell, depth int, buf []byte) ([]byte, error) {
	var err error
	var storageRootHash common.Hash
	var storageRootHashIsSet bool
	if hph.memoizationOff {
		cell.stateHashLen = 0 // Reset stateHashLen to force recompute
	}
	if cell.storageAddrLen > 0 {
		var hashedKeyOffset int
		if depth >= 64 {
			hashedKeyOffset = depth - 64
		}
		singleton := depth <= 64
		koffset := hph.accountKeyLen
		if depth == 0 && cell.accountAddrLen == 0 {
			// if account key is empty, then we need to hash storage key from the key beginning
			koffset = 0
		}
		if err = cell.hashStorageKey(hph.keccak, koffset, 0, hashedKeyOffset); err != nil {
			return nil, err
		}
		cell.hashedExtension[64-hashedKeyOffset] = terminatorHexByte // Add terminator

		if cell.stateHashLen > 0 {
			hph.keccak.Reset()
			if hph.trace {
				fmt.Printf("REUSED stateHash %x spk %x\n", cell.stateHash[:cell.stateHashLen], cell.storageAddr[:cell.storageAddrLen])
			}
			mxTrieStateSkipRate.Inc()
			skippedLoad.Add(1)
			if !singleton {
				return append(append(buf[:0], byte(160)), cell.stateHash[:cell.stateHashLen]...), nil
			}
			storageRootHashIsSet = true
			storageRootHash = *(*common.Hash)(cell.stateHash[:cell.stateHashLen])
		} else {
			if !cell.loaded.storage() {
				return nil, fmt.Errorf("storage %x was not loaded as expected: cell %v", cell.storageAddr[:cell.storageAddrLen], cell.String())
				// update, err := hph.ctx.Storage(cell.storageAddr[:cell.storageAddrLen])
				// if err != nil {
				// 	return nil, err
				// }
				// cell.setFromUpdate(update)
			}

			leafHash, err := hph.leafHashWithKeyVal(buf, cell.hashedExtension[:64-hashedKeyOffset+1], cell.Storage[:cell.StorageLen], singleton)
			if err != nil {
				return nil, err
			}
			if hph.trace {
				fmt.Printf("leafHashWithKeyVal(singleton=%t) {%x} for [%x]=>[%x] %v\n",
					singleton, leafHash, cell.hashedExtension[:64-hashedKeyOffset+1], cell.Storage[:cell.StorageLen], cell.String())
			}
			if !singleton {
				copy(cell.stateHash[:], leafHash[1:])
				cell.stateHashLen = len(leafHash) - 1
				return leafHash, nil
			}
			storageRootHash = *(*common.Hash)(leafHash[1:])
			storageRootHashIsSet = true
			cell.stateHashLen = 0
			hadToReset.Add(1)
		}
	}
	if cell.accountAddrLen > 0 {
		if err := cell.hashAccKey(hph.keccak, depth); err != nil {
			return nil, err
		}
		cell.hashedExtension[64-depth] = terminatorHexByte // Add terminator
		if !storageRootHashIsSet {
			if cell.storageAddrLen > 0 && depth <= 64 {
				// Storage exists but root wasn't set; compute from singleton storage leaf.
				var hashedKeyOffset int
				if depth >= 64 {
					hashedKeyOffset = depth - 64
				}
				koffset := hph.accountKeyLen
				if depth == 0 && cell.accountAddrLen == 0 {
					koffset = 0
				}
				var storageExt [65]byte
				var storageHashBuf [64]byte
				if err = hashKey(hph.keccak, cell.storageAddr[koffset:cell.storageAddrLen], storageExt[:], hashedKeyOffset, storageHashBuf[:]); err != nil {
					return nil, err
				}
				storageExt[64-hashedKeyOffset] = terminatorHexByte
				aux := make([]byte, 0, 33)
				if aux, err = hph.leafHashWithKeyVal(aux, storageExt[:64-hashedKeyOffset+1], cell.Storage[:cell.StorageLen], true); err != nil {
					return nil, err
				}
				storageRootHash = *(*common.Hash)(aux[1:])
				storageRootHashIsSet = true
			}
		}
		if !storageRootHashIsSet {
			if cell.extLen > 0 { // Extension
				if cell.hashLen == 0 {
					return nil, errors.New("computeCellHash extension without hash")
				}
				if hph.trace {
					fmt.Printf("extensionHash for [%x]=>[%x]\n", cell.extension[:cell.extLen], cell.hash[:cell.hashLen])
				}
				if storageRootHash, err = hph.extensionHash(cell.extension[:cell.extLen], cell.hash[:cell.hashLen]); err != nil {
					return nil, err
				}
				if hph.trace {
					fmt.Printf("EXTENSION HASH %x DROPS stateHash\n", storageRootHash)
				}
				cell.stateHashLen = 0
				hadToReset.Add(1)
			} else if cell.hashLen > 0 {
				storageRootHash = cell.hash
			} else {
				storageRootHash = empty.RootHash
			}
		}
		if !cell.loaded.account() {
			if cell.stateHashLen > 0 {
				hph.keccak.Reset()

				mxTrieStateSkipRate.Inc()
				skippedLoad.Add(1)
				if hph.trace {
					fmt.Printf("REUSED stateHash %x apk %x\n", cell.stateHash[:cell.stateHashLen], cell.accountAddr[:cell.accountAddrLen])
				}
				return append(append(buf[:0], byte(160)), cell.stateHash[:cell.stateHashLen]...), nil
			}
			// storage root update or extension update could invalidate older stateHash, so we need to reload state
			hph.metrics.AccountLoad(cell.accountAddr[:cell.accountAddrLen])
			update, err := hph.ctx.Account(cell.accountAddr[:cell.accountAddrLen])
			if err != nil {
				return nil, err
			}
			cell.setFromUpdate(update)
		}

		valLen := cell.accountForHashing(hph.accValBuf, storageRootHash)
		buf, err = hph.accountLeafHashWithKey(buf, cell.hashedExtension[:65-depth], hph.accValBuf[:valLen])
		if err != nil {
			return nil, err
		}
		if hph.trace {
			fmt.Printf("accountLeafHashWithKey {%x} (memorised) for [%x]=>[%x]\n", buf, cell.hashedExtension[:65-depth], hph.accValBuf[:valLen])
		}
		copy(cell.stateHash[:], buf[1:])
		cell.stateHashLen = len(buf) - 1
		return buf, nil
	}

	buf = append(buf, 0x80+32)
	if cell.extLen > 0 { // Extension
		if cell.hashLen > 0 {
			if hph.trace {
				fmt.Printf("extensionHash for [%x]=>[%x]\n", cell.extension[:cell.extLen], cell.hash[:cell.hashLen])
			}
			if storageRootHash, err = hph.extensionHash(cell.extension[:cell.extLen], cell.hash[:cell.hashLen]); err != nil {
				return nil, err
			}
			buf = append(buf, storageRootHash[:]...)
		} else {
			return nil, errors.New("computeCellHash extension without hash")
		}
	} else if cell.hashLen > 0 {
		buf = append(buf, cell.hash[:cell.hashLen]...)
	} else if storageRootHashIsSet {
		buf = append(buf, storageRootHash[:]...)
		copy(cell.hash[:], storageRootHash[:])
		cell.hashLen = len(storageRootHash)
	} else {
		buf = append(buf, emptyRootHashBytes...)
	}
	return buf, nil
}

func (hph *HexPatriciaHashed) needUnfolding(hashedKey []byte) int {
	var cell *cell
	var depth int
	if hph.activeRows == 0 {
		if hph.trace {
			fmt.Printf("needUnfolding root, rootChecked = %t\n", hph.rootChecked)
		}
		if hph.root.hashedExtLen == 64 && hph.root.accountAddrLen > 0 && hph.root.storageAddrLen > 0 {
			// in case if root is a leaf node with storage and account, we need to derive storage part of a key
			if err := hph.root.deriveHashedKeys(depth, hph.keccak, hph.accountKeyLen); err != nil {
				log.Warn("deriveHashedKeys for root with storage", "err", err, "cell", hph.root.FullString())
				return 0
			}
			//copy(hph.currentKey[:], hph.root.hashedExtension[:])
			if hph.trace {
				fmt.Printf("derived prefix %x\n", hph.currentKey[:hph.currentKeyLen])
			}
		}
		if hph.root.hashedExtLen == 0 && hph.root.hashLen == 0 {
			if hph.rootChecked {
				return 0 // Previously checked, empty root, no unfolding needed
			}
			return 1 // Need to attempt to unfold the root
		}
		cell = &hph.root
	} else {
		col := int(hashedKey[hph.currentKeyLen])
		cell = &hph.grid[hph.activeRows-1][col]
		depth = hph.depths[hph.activeRows-1]
		if hph.trace {
			fmt.Printf("currentKey [%x] needUnfolding cell (%d, %x, depth=%d) cell.hash=[%x]\n", hph.currentKey[:hph.currentKeyLen], hph.activeRows-1, col, depth, cell.hash[:cell.hashLen])
		}
	}
	if len(hashedKey) <= depth {
		return 0
	}
	if cell.hashedExtLen == 0 {
		if cell.hashLen == 0 {
			// cell is empty, no need to unfold further
			return 0
		}
		// unfold branch node
		return 1
	}
	cpl := commonPrefixLen(hashedKey[depth:], cell.hashedExtension[:cell.hashedExtLen-1])
	if hph.trace {
		fmt.Printf("cpl=%d cell.hashedExtension=[%x] hashedKey[depth=%d:]=[%x]\n", cpl, cell.hashedExtension[:cell.hashedExtLen], depth, hashedKey[depth:])
	}
	unfolding := cpl + 1
	if depth < 64 && depth+unfolding > 64 {
		// This is to make sure that unfolding always breaks at the level where storage subtrees start
		unfolding = 64 - depth
		if hph.trace {
			fmt.Printf("adjusted unfolding=%d <- %d\n", unfolding, cpl+1)
		}
	}
	return unfolding
}

func (c *cell) IsEmpty() bool {
	return c.hashLen == 0 && c.hashedExtLen == 0 && c.extLen == 0 && c.accountAddrLen == 0 && c.storageAddrLen == 0
}

func (c *cell) String() string {
	s := "("
	if c.hashLen > 0 {
		s += fmt.Sprintf("hash(len=%d)=%x, ", c.hashLen, c.hash)
	}
	if c.hashedExtLen > 0 {
		s += fmt.Sprintf("hashedExtension(len=%d)=%x, ", c.hashedExtLen, c.hashedExtension[:c.hashedExtLen])
	}
	if c.extLen > 0 {
		s += fmt.Sprintf("extension(len=%d)=%x, ", c.extLen, c.extension[:c.extLen])
	}
	if c.accountAddrLen > 0 {
		s += fmt.Sprintf("accountAddr=%x, ", c.accountAddr)
	}
	if c.storageAddrLen > 0 {
		s += fmt.Sprintf("storageAddr=%x, ", c.storageAddr)
	}

	s += ")"
	return s
}

func (hph *HexPatriciaHashed) PrintGrid() {
	fmt.Printf("GRID:\n")
	for row := 0; row < hph.activeRows; row++ {
		fmt.Printf("row %d depth %d:\n", row, hph.depths[row])
		for col := 0; col < 16; col++ {
			cell := &hph.grid[row][col]
			if cell.hashedExtLen > 0 || cell.accountAddrLen > 0 {
				var cellHash []byte
				cellHash, _, _, err := hph.witnessComputeCellHashWithStorage(cell, hph.depths[row], nil)
				if err != nil {
					panic("failed to compute cell hash")
				}
				fmt.Printf("\t %x: %v cellHash=%x, \n", col, cell, cellHash)
			} else {
				fmt.Printf("\t %x: %v , \n", col, cell)
			}
		}
		fmt.Printf("\n")
	}
	fmt.Printf("\n")
}

func witnessCellDeletedWithoutHash(c *cell) bool {
	if c == nil || !c.Deleted() {
		return false
	}
	if c.hashLen > 0 || c.stateHashLen > 0 {
		return false
	}
	// Keep extension/hash-backed deleted paths materialized as hash nodes.
	// Only plain tombstones (no hash payload) map to an empty branch child.
	if c.extLen > 0 || c.hashedExtLen > 0 {
		return false
	}
	return true
}

// witnessCellDeletedAsOfNoHash checks whether the cell should map to a nil child
// at the current as-of read context. This extends flag-based tombstone detection
// for ModeDirect key touches that carry no hash payload.
func (hph *HexPatriciaHashed) witnessCellDeletedAsOfNoHash(c *cell) (bool, error) {
	if witnessCellDeletedWithoutHash(c) {
		return true, nil
	}
	if c == nil {
		return false, nil
	}
	// Cells that already carry commitment hashes stay materialized as hash nodes.
	if c.hashLen > 0 || c.stateHashLen > 0 {
		return false, nil
	}
	// Keep extension paths materialized. A large class of legitimate branch
	// children are represented as "hashed extension, no hash payload" cells in
	// as-of views. Collapsing them to nil rewrites branch commitments and causes
	// witness root drift.
	if c.extLen > 0 || c.hashedExtLen > 0 {
		return false, nil
	}
	if c.accountAddrLen > 0 {
		update, err := hph.ctx.Account(c.accountAddr[:c.accountAddrLen])
		if err != nil {
			return false, err
		}
		if update != nil && update.Deleted() {
			return true, nil
		}
	}
	if c.storageAddrLen > 0 {
		update, err := hph.ctx.Storage(c.storageAddr[:c.storageAddrLen])
		if err != nil {
			return false, err
		}
		if update != nil && update.Deleted() {
			return true, nil
		}
	}
	return false, nil
}

func (hph *HexPatriciaHashed) logWitnessTombstoneChild(row int, c *cell, kind string) {
	if !allowWitnessTombstoneLog() || c == nil {
		return
	}
	account := "0x"
	if c.accountAddrLen > 0 {
		account = fmt.Sprintf("0x%x", c.accountAddr[:c.accountAddrLen])
	}
	storage := "0x"
	if c.storageAddrLen > 0 {
		storage = fmt.Sprintf("0x%x", c.storageAddr[:c.storageAddrLen])
	}
	depth := 0
	if row >= 0 && row < len(hph.depths) {
		depth = hph.depths[row]
	}
	log.Warn(
		"witness tombstone child nil",
		"section", "to_witness_trie",
		"kind", kind,
		"row", row,
		"depth", depth,
		"account", account,
		"storage", storage,
		"hash_len", c.hashLen,
		"state_hash_len", c.stateHashLen,
		"ext_len", c.extLen,
		"hashed_ext_len", c.hashedExtLen,
	)
}

// this function is only related to the witness
func (hph *HexPatriciaHashed) witnessCreateAccountNode(c *cell, row int, hashedKey []byte, codeReads map[common.Hash]witnesstypes.CodeWithHash) (*trie.AccountNode, []byte, error) {
	cellHash, storageIsSet, storageRootHash, err := hph.witnessComputeCellHashWithStorage(c, hph.depths[row], nil)
	if err != nil {
		return nil, nil, err
	}
	accountUpdate, err := hph.ctx.Account(c.accountAddr[:c.accountAddrLen])
	if err != nil {
		return nil, nil, err
	}
	var account accounts.Account
	accountSource := "ctx_missing"
	accountFromUpdate := accountUpdate != nil && !accountUpdate.Deleted()
	switch {
	case accountFromUpdate:
		account.Nonce = accountUpdate.Nonce
		account.Balance = accountUpdate.Balance
		account.CodeHash = accountUpdate.CodeHash
		accountSource = "ctx_update"
	case c.loaded.account():
		account.Nonce = c.Nonce
		account.Balance = c.Balance
		account.CodeHash = c.CodeHash
		accountSource = "cell_loaded"
	default:
		// No account payload to materialize. Let callers decide whether to keep
		// a hash-only proof node via expectedCellHash.
		return nil, cellHash, nil
	}
	account.Initialised = true

	var (
		updateStorageRoot common.Hash
		cellStorageRoot   common.Hash
		hasUpdateRoot     bool
		hasCellRoot       bool
		rootSource        = "empty"
	)
	if accountFromUpdate && accountUpdate.StorageLen == length.Hash {
		hasUpdateRoot = true
		copy(updateStorageRoot[:], accountUpdate.Storage[:length.Hash])
	}
	// witnessComputeCellHashWithStorage always returns a 32-byte buffer shape,
	// but it is meaningful only when storageIsSet=true.
	if storageIsSet && len(storageRootHash) == length.Hash {
		hasCellRoot = true
		copy(cellStorageRoot[:], storageRootHash[:length.Hash])
	}
	// Many account cells already carry the canonical storage root in their hash field.
	// Prefer that as a fallback when witnessComputeCellHashWithStorage cannot infer
	// storage root from singleton storage data.
	if !hasCellRoot && c.hashLen == length.Hash {
		hasCellRoot = true
		copy(cellStorageRoot[:], c.hash[:])
		rootSource = "cell_hash"
	}

	// Witness should follow the trie cell root whenever available.
	// Some account-domain payloads (e.g. V3) do not persist storage root and
	// deserialize as empty-root placeholders; blindly preferring that value can
	// erase real non-empty storage roots in witness account leaves.
	account.Root = empty.RootHash
	if hasCellRoot {
		copy(account.Root[:], cellStorageRoot[:])
		if rootSource == "empty" {
			rootSource = "cell_storage"
		}
	}
	if hasUpdateRoot {
		updateIsEmptyRoot := updateStorageRoot == empty.RootHash
		// Witness root fidelity should follow trie-cell commitment when available.
		// Account-domain root is a fallback only when trie-cell root is absent.
		if !hasCellRoot {
			copy(account.Root[:], updateStorageRoot[:])
			rootSource = "account_update"
		} else if updateIsEmptyRoot {
			rootSource = "cell_storage(update_empty)"
		} else if updateStorageRoot == cellStorageRoot {
			rootSource = "cell_storage(update_match)"
		} else {
			rootSource = "cell_storage(update_mismatch)"
		}
	}

	rootMismatch := hasUpdateRoot && hasCellRoot && updateStorageRoot != cellStorageRoot
	nonceMismatch := accountFromUpdate && c.loaded.account() && c.Nonce != accountUpdate.Nonce
	balanceMismatch := accountFromUpdate && c.loaded.account() && !c.Balance.Eq(&accountUpdate.Balance)
	codeHashMismatch := accountFromUpdate && c.loaded.account() && c.CodeHash != accountUpdate.CodeHash
	if (rootMismatch || nonceMismatch || balanceMismatch || codeHashMismatch) && allowWitnessAccountDiagLog() {
		log.Warn(
			"witness account diag",
			"addr", fmt.Sprintf("0x%x", c.accountAddr[:c.accountAddrLen]),
			"row", row,
			"account_source", accountSource,
			"cell_loaded", c.loaded.String(),
			"root_mismatch", rootMismatch,
			"storage_is_set", storageIsSet,
			"update_root", updateStorageRoot,
			"cell_root", cellStorageRoot,
			"selected_root_source", rootSource,
			"selected_root", account.Root,
			"nonce_mismatch", nonceMismatch,
			"cell_nonce", c.Nonce,
			"update_nonce", func() uint64 {
				if accountFromUpdate {
					return accountUpdate.Nonce
				}
				return 0
			}(),
			"balance_mismatch", balanceMismatch,
			"cell_balance", c.Balance.String(),
			"update_balance", func() string {
				if accountFromUpdate {
					return accountUpdate.Balance.String()
				}
				return "<nil>"
			}(),
			"codehash_mismatch", codeHashMismatch,
			"cell_codehash", c.CodeHash,
			"update_codehash", func() common.Hash {
				if accountFromUpdate {
					return accountUpdate.CodeHash
				}
				return common.Hash{}
			}(),
			"storage_key_hint", fmt.Sprintf("0x%x", c.storageAddr[:c.storageAddrLen]),
		)
	}

	addrHash, err := compactKey(hashedKey[:64])
	if err != nil {
		return nil, nil, err
	}

	// get code
	var code []byte
	codeWithHash, hasCode := codeReads[[32]byte(addrHash)]
	if !hasCode {
		code = nil
	} else {
		code = codeWithHash.Code
		// sanity check
		if account.CodeHash != codeWithHash.CodeHash {
			return nil, nil, fmt.Errorf("account.CodeHash(%x)!=codeReads[%x].CodeHash(%x)", account.CodeHash, addrHash, codeWithHash.CodeHash)
		}
	}

	var storageNode trie.Node
	if account.Root != trie.EmptyRoot {
		// Keep a hash reference to the storage root when non-empty.
		storageNode = trie.NewHashNode(common.Copy(account.Root[:]))
	} else if storageIsSet {
		// Defensive fallback: preserve explicit empty/non-empty indication from
		// witnessComputeCellHashWithStorage for singleton-storage paths.
		storageNode = trie.NewHashNode(common.Copy(storageRootHash[:]))
	}

	return &trie.AccountNode{
		Account:     account,
		Storage:     storageNode,
		RootCorrect: true,
		Code:        code,
		CodeSize:    -1,
	}, cellHash, nil
}

func (hph *HexPatriciaHashed) nCellsInRow(row int) int { //nolint:unused
	count := 0
	for col := 0; col < 16; col++ {
		c := &hph.grid[row][col]
		if !c.IsEmpty() {
			count++
		}
	}
	return count
}

type witnessStorageLatestProvider interface {
	StorageLatest(plainKey []byte) (*Update, error)
}

func (hph *HexPatriciaHashed) witnessStorageNodeFromUpdate(update *Update, expectedChildRoot []byte) (trie.Node, bool) {
	if update == nil || update.Deleted() {
		return nil, false
	}
	storageValue := trie.ValueNode(common.Copy(update.Storage[:update.StorageLen]))
	candidate := trie.Node(&storageValue)
	if bytes.Equal(trie.NewInMemoryTrie(candidate).Root(), expectedChildRoot) {
		return candidate, true
	}
	termCandidate := &trie.ShortNode{Key: []byte{terminatorHexByte}, Val: storageValue}
	if bytes.Equal(trie.NewInMemoryTrie(termCandidate).Root(), expectedChildRoot) {
		return termCandidate, true
	}
	return nil, false
}

func (hph *HexPatriciaHashed) witnessStorageLatestUpdate(plainKey []byte) (*Update, error) {
	latestReader, ok := hph.ctx.(witnessStorageLatestProvider)
	if !ok {
		return nil, nil
	}
	return latestReader.StorageLatest(plainKey)
}

// Traverse the grid following `hashedKey` and produce the witness `triedeprecated.Trie` for that key
func (hph *HexPatriciaHashed) toWitnessTrie(hashedKey []byte, codeReads map[common.Hash]witnesstypes.CodeWithHash) (*trie.Trie, error) {
	var rootNode trie.Node = &trie.FullNode{}
	var currentNode trie.Node = rootNode
	keyPos := 0 // current position in hashedKey (usually same as row, but could be different due to extension nodes)

	if hph.root.hashedExtLen > 0 {
		currentNode = &trie.ShortNode{Key: common.Copy(hph.root.hashedExtension[:hph.root.hashedExtLen]), Val: &trie.FullNode{}}
		// currentNode = &trie.ShortNode{Val: &trie.FullNode{}}
		rootNode = currentNode             // use root node as the current node
		keyPos = hph.root.hashedExtLen - 1 // start from the end of the root extension
		fmt.Printf("[witness] root node %s, pos %d\n", hph.root.FullString(), keyPos)
	}

	for row := 0; row < hph.activeRows && keyPos < len(hashedKey); row++ {
		rowDepth := hph.depths[row]
		// hph.depths[row] is one-past the branch nibble selected at this row.
		// Example: depth=1 selects hashedKey[0], depth=2 selects hashedKey[1].
		rowNibblePos := rowDepth - 1
		accountStorageBoundaryRow := len(hashedKey) > length.Hash*2 &&
			rowDepth == length.Hash*2 &&
			rowNibblePos+1 == keyPos
		if rowNibblePos < 0 || rowNibblePos >= len(hashedKey) {
			// Defensive: out-of-range means there is no key nibble to follow for this row.
			break
		}
		// Extension rows can consume multiple nibbles in one step. When that happens,
		// subsequent rows whose selected nibble is already behind keyPos must be skipped,
		// otherwise we replay account-boundary rows and corrupt account->storage bridging.
		if row > 0 && rowNibblePos < keyPos && !erigonWitnessDisableKeyPosSkip && !accountStorageBoundaryRow {
			if hph.trace {
				nibbleFromKeyPos := "n/a"
				if keyPos >= 0 && keyPos < len(hashedKey) {
					nibbleFromKeyPos = fmt.Sprintf("%x", hashedKey[keyPos])
				}
				log.Warn(
					"witness trace keypos drift",
					"row", row,
					"depth", rowDepth,
					"key_pos_before", keyPos,
					"nibble_from_keypos", nibbleFromKeyPos,
					"nibble_from_row", fmt.Sprintf("%x", hashedKey[rowNibblePos]),
					"disable_keypos_skip_effective", erigonWitnessDisableKeyPosSkip,
					"allow_keypos_drift_unsafe", erigonWitnessAllowKeyPosDriftUnsafe,
					"action", "skip_row_already_consumed",
				)
			}
			continue
		}
		if row > 0 && rowNibblePos < keyPos && accountStorageBoundaryRow && hph.trace {
			nibbleFromKeyPos := "n/a"
			if keyPos >= 0 && keyPos < len(hashedKey) {
				nibbleFromKeyPos = fmt.Sprintf("%x", hashedKey[keyPos])
			}
			log.Warn(
				"witness trace keypos drift",
				"row", row,
				"depth", rowDepth,
				"key_pos_before", keyPos,
				"nibble_from_keypos", nibbleFromKeyPos,
				"nibble_from_row", fmt.Sprintf("%x", hashedKey[rowNibblePos]),
				"disable_keypos_skip_effective", erigonWitnessDisableKeyPosSkip,
				"allow_keypos_drift_unsafe", erigonWitnessAllowKeyPosDriftUnsafe,
				"action", "process_account_storage_boundary_row",
			)
		}
		if row > 0 && rowNibblePos < keyPos && erigonWitnessDisableKeyPosSkip && hph.trace {
			nibbleFromKeyPos := "n/a"
			if keyPos >= 0 && keyPos < len(hashedKey) {
				nibbleFromKeyPos = fmt.Sprintf("%x", hashedKey[keyPos])
			}
			log.Warn(
				"witness trace keypos drift",
				"row", row,
				"depth", rowDepth,
				"key_pos_before", keyPos,
				"nibble_from_keypos", nibbleFromKeyPos,
				"nibble_from_row", fmt.Sprintf("%x", hashedKey[rowNibblePos]),
				"disable_keypos_skip_effective", erigonWitnessDisableKeyPosSkip,
				"allow_keypos_drift_unsafe", erigonWitnessAllowKeyPosDriftUnsafe,
				"action", "force_process_row",
			)
		}
		targetNibblePos := rowNibblePos
		// Default to the row-selected nibble: row depth is authoritative for the
		// branch child that must be expanded at this step.
		//
		// Allow boundary drift only behind explicit unsafe flag. Keeping keyPos at
		// the first storage nibble on depth=64 can make selected nibble diverge
		// from row nibble and overwrite the wrong branch child.
		if accountStorageBoundaryRow && keyPos == rowNibblePos+1 && erigonWitnessAllowKeyPosDriftUnsafe {
			targetNibblePos = keyPos
		}
		if hph.trace && keyPos != targetNibblePos {
			nibbleFromKeyPos := "n/a"
			if keyPos >= 0 && keyPos < len(hashedKey) {
				nibbleFromKeyPos = fmt.Sprintf("%x", hashedKey[keyPos])
			}
			nibbleFromTargetPos := "n/a"
			if targetNibblePos >= 0 && targetNibblePos < len(hashedKey) {
				nibbleFromTargetPos = fmt.Sprintf("%x", hashedKey[targetNibblePos])
			}
			action := "sync_to_row_nibble"
			if accountStorageBoundaryRow && targetNibblePos == keyPos && erigonWitnessAllowKeyPosDriftUnsafe {
				action = "keep_account_storage_boundary_nibble"
			}
			log.Warn(
				"witness trace keypos drift",
				"row", row,
				"depth", rowDepth,
				"key_pos_before", keyPos,
				"nibble_from_keypos", nibbleFromKeyPos,
				"nibble_from_row", fmt.Sprintf("%x", hashedKey[rowNibblePos]),
				"target_nibble_pos", targetNibblePos,
				"nibble_from_target", nibbleFromTargetPos,
				"disable_keypos_skip_effective", erigonWitnessDisableKeyPosSkip,
				"allow_keypos_drift_unsafe", erigonWitnessAllowKeyPosDriftUnsafe,
				"action", action,
			)
		}
		// Keep traversal nibble aligned with the row's selected branch nibble.
		// keyPos can drift across extension/root transitions; rowNibblePos is
		// canonical except at the account/storage boundary where keyPos may
		// already point at the first storage nibble.
		keyPos = targetNibblePos
		currentNibble := hashedKey[keyPos]
		stopAfterCurrentNode := false
		// determine the type of the next node to expand (in the next iteration)
		var nextNode trie.Node
		nextNodeSource := "unset"
		setNextNode := func(node trie.Node, source string) {
			nextNode = node
			nextNodeSource = source
		}
		// need to check node type along the key path
		cellToExpand := &hph.grid[row][currentNibble]
		// determine the next node
		if hph.root.hashedExtLen > 0 && currentNode == rootNode {
			currentNode = currentNode.(*trie.ShortNode).Val
			keyPos++
			continue

		} else if cellToExpand.hashedExtLen > 0 { // extension cell
			depthAdjusted := false
			extKeyLength := cellToExpand.hashedExtLen
			if hph.depths[row] < 64 && extKeyLength+hph.depths[row] > 64 { //&& cellToExpand.accountAddrLen > 0 {
				extKeyLength = 64 - hph.depths[row] // adjust depth to stop before storage trie
				depthAdjusted = true
				if hph.trace {
					fmt.Printf("[witness] adjusted hashExtLen=%d <- %d\n", extKeyLength, cellToExpand.hashedExtLen)
				}
			}

			// keyPos currently points to the branch nibble selecting this extension.
			// Move past that nibble and the full extension payload.
			keyPos += extKeyLength + 1
			hashedExtKey := cellToExpand.hashedExtension[:extKeyLength]
			// Add path terminator only when this extension ends the full key.
			// For storage keys (len>64), reaching account boundary (depth=64)
			// is not terminal: account node carries the account/storage bridge.
			needsTerminator := keyPos == len(hashedKey) || (keyPos == 64 && len(hashedKey) <= 64)
			if needsTerminator {
				extKeyLength++ //  +1 for the terminator 0x10 ([16])  byte when on a terminal extension node
			}
			extensionKey := make([]byte, extKeyLength)
			copy(extensionKey, hashedExtKey)
			if needsTerminator {
				extensionKey[len(extensionKey)-1] = terminatorHexByte // append terminator byte
			}
			setNextNode(&trie.ShortNode{Key: extensionKey}, "extension:short") // Value will be in the next iteration
			// For storage witnesses, account extension cells must keep the account leaf
			// attached even when the key continues into storage. Otherwise the selected
			// branch child loses the account payload and diverges from the cell hash.
			//
			// Some storage-only touches arrive without accountAddr on this extension
			// cell (hash-only account path). In that case, synthesize accountAddr from
			// the storage plain key prefix so witnessCreateAccountNode can materialize
			// the account leaf and preserve the account/storage trie boundary.
			// Account->storage bridge must be materialized exactly at the account
			// boundary. Running this branch deeper in storage trie (keyPos > 64)
			// injects spurious account wrappers and corrupts witness shape/hash.
			if len(hashedKey) > 64 && keyPos == 64 {
				accountCell := cellToExpand
				if accountCell.accountAddrLen == 0 && accountCell.storageAddrLen > hph.accountKeyLen {
					cloned := *cellToExpand
					cloned.accountAddrLen = hph.accountKeyLen
					copy(cloned.accountAddr[:], cloned.storageAddr[:hph.accountKeyLen])
					accountCell = &cloned
					if allowWitnessAccountDiagLog() {
						log.Warn(
							"witness synthesized account bridge",
							"row", row,
							"depth", hph.depths[row],
							"addr", fmt.Sprintf("0x%x", cloned.accountAddr[:cloned.accountAddrLen]),
							"storage_key_hint", fmt.Sprintf("0x%x", cloned.storageAddr[:cloned.storageAddrLen]),
						)
					}
				}

				if accountCell.accountAddrLen > 0 {
					deletedNoHash, deletedErr := hph.witnessCellDeletedAsOfNoHash(accountCell)
					if deletedErr != nil {
						return nil, deletedErr
					}
					if deletedNoHash {
						hph.logWitnessTombstoneChild(row, accountCell, "extension_account_continue")
						setNextNode(nil, "extension:account_bridge_tombstone")
					} else {
						accNode, _, accErr := hph.witnessCreateAccountNode(accountCell, row, hashedKey, codeReads)
						if accErr != nil {
							return nil, accErr
						}
						if accNode != nil {
							accountLeafKey := extensionKey
							// Storage touched keys are represented as account-hash || storage-hash.
							// When an extension reaches account boundary (pos=64), keep the account
							// leaf terminator so this short node hashes exactly like the cell leaf.
							if keyPos == 64 && len(hashedKey) > 64 {
								if len(accountLeafKey) == 0 || accountLeafKey[len(accountLeafKey)-1] != terminatorHexByte {
									accountLeafKey = append(common.Copy(accountLeafKey), terminatorHexByte)
								}
							}
							accountBridgeNode := &trie.ShortNode{Key: accountLeafKey, Val: accNode}
							setNextNode(accountBridgeNode, "extension:account_bridge_short")
							captureWitnessNodePreimagesFromNode(accountBridgeNode)
							if hph.trace {
								fmt.Printf("[witness] extension account continuation (%d, %0x, depth=%d) %s\n", row, currentNibble, hph.depths[row], accountCell.FullString())
							}
						}
					}
				}

				if accountCell.accountAddrLen == 0 && allowWitnessAccountDiagLog() {
					log.Warn(
						"witness missing account bridge on extension",
						"row", row,
						"depth", hph.depths[row],
						"key_pos", keyPos,
						"hashed_key_len", len(hashedKey),
						"account_addr_len", accountCell.accountAddrLen,
						"storage_addr_len", accountCell.storageAddrLen,
						"cell", accountCell.FullString(),
					)
				}
			}
			if keyPos == len(hashedKey) {
				if cellToExpand.storageAddrLen > 0 && !depthAdjusted {
					storageUpdate, err := hph.ctx.Storage(cellToExpand.storageAddr[:cellToExpand.storageAddrLen])
					if err != nil {
						return nil, err
					}
					if storageUpdate != nil && !storageUpdate.Deleted() {
						storageValueNode := trie.ValueNode(storageUpdate.Storage[:storageUpdate.StorageLen])
						setNextNode(&trie.ShortNode{Key: extensionKey, Val: storageValueNode}, "extension:storage_ctx_value")
					} else {
						deletedNoHash, deletedErr := hph.witnessCellDeletedAsOfNoHash(cellToExpand)
						if deletedErr != nil {
							return nil, deletedErr
						}
						if deletedNoHash {
							hph.logWitnessTombstoneChild(row, cellToExpand, "extension_storage")
							setNextNode(nil, "extension:storage_tombstone")
						} else {
							expectedCellHash, _, _, hashErr := hph.witnessComputeCellHashWithStorage(cellToExpand, hph.depths[row], nil)
							if hashErr != nil {
								return nil, hashErr
							}
							setNextNode(trie.NewHashNode(common.Copy(expectedCellHash[1:])), "extension:storage_expected_hash")
						}
					}
				} else if cellToExpand.accountAddrLen > 0 || cellToExpand.storageAddrLen > hph.accountKeyLen {
					accountCell := cellToExpand
					if accountCell.accountAddrLen == 0 && accountCell.storageAddrLen > hph.accountKeyLen {
						cloned := *cellToExpand
						cloned.accountAddrLen = hph.accountKeyLen
						copy(cloned.accountAddr[:], cloned.storageAddr[:hph.accountKeyLen])
						accountCell = &cloned
					}
					accNode, expectedCellHash, err := hph.witnessCreateAccountNode(accountCell, row, hashedKey, codeReads)
					if err != nil {
						return nil, err
					}
					deletedNoHash, deletedErr := hph.witnessCellDeletedAsOfNoHash(accountCell)
					if deletedErr != nil {
						return nil, deletedErr
					}
					if deletedNoHash {
						hph.logWitnessTombstoneChild(row, accountCell, "extension_account")
						setNextNode(nil, "extension:account_tombstone")
					} else if accNode != nil {
						extensionAccountNode := &trie.ShortNode{Key: extensionKey, Val: accNode}
						setNextNode(extensionAccountNode, "extension:account_short")
						captureWitnessNodePreimagesFromNode(extensionAccountNode)
						extNodeSubTrie := trie.NewInMemoryTrie(nextNode)
						subTrieRoot := extNodeSubTrie.Root()
						if !bytes.Equal(subTrieRoot, expectedCellHash[1:]) {
							// In some as-of views, account payload reconstruction may not
							// exactly match the stored cell hash (e.g. sparse/history edge
							// cases). Preserve canonical witness shape by anchoring to the
							// expected cell hash instead of aborting witness generation.
							if erigonBadRootDebug {
								log.Warn(
									"witness account extension subtrie mismatch, using hash fallback",
									"row", row,
									"depth", hph.depths[row],
									"plain_account", fmt.Sprintf("0x%x", accountCell.accountAddr[:accountCell.accountAddrLen]),
									"subtrie_root", common.BytesToHash(subTrieRoot),
									"expected_cell_root", common.BytesToHash(expectedCellHash[1:]),
								)
							}
							setNextNode(trie.NewHashNode(common.Copy(expectedCellHash[1:])), "extension:account_subtrie_hash_fallback")
						}
					} else {
						setNextNode(trie.NewHashNode(common.Copy(expectedCellHash[1:])), "extension:account_expected_hash")
					}
					// // DEBUG patch with cell hash which we know to be correct
					//fmt.Printf("witness cell (%d, %0x, depth=%d) %s\n", row, currentNibble, hph.depths[row], cellToExpand.FullString())
					//nextNode = trie.NewHashNode(cellToExpand.stateHash[:])
				}
			}
		} else if cellToExpand.accountAddrLen > 0 { // account cell
			accNode, expectedCellHash, err := hph.witnessCreateAccountNode(cellToExpand, row, hashedKey, codeReads)
			if err != nil {
				return nil, err
			}
			deletedNoHash, deletedErr := hph.witnessCellDeletedAsOfNoHash(cellToExpand)
			if deletedErr != nil {
				return nil, deletedErr
			}
			if deletedNoHash {
				// Touched tombstone with no hash payload represents an empty slot.
				hph.logWitnessTombstoneChild(row, cellToExpand, "account")
				setNextNode(nil, "account:tombstone")
			} else if accNode != nil {
				parentHasTerminator := false
				if parentShort, ok := currentNode.(*trie.ShortNode); ok && len(parentShort.Key) > 0 {
					parentHasTerminator = parentShort.Key[len(parentShort.Key)-1] == terminatorHexByte
				}
				// Account leaves may sit either directly in the branch slot or under a
				// single-nibble terminator short node. Pick the shape that matches the
				// canonical cell hash for this row. If the parent short node already
				// terminates the key, keep the account leaf direct to avoid || double-
				// terminator paths in the witness trie.
				candidate := trie.Node(accNode)
				if !parentHasTerminator {
					candidateRoot := trie.NewInMemoryTrie(candidate).Root()
					if !bytes.Equal(candidateRoot, expectedCellHash[1:]) {
						termCandidate := &trie.ShortNode{Key: []byte{terminatorHexByte}, Val: accNode}
						termRoot := trie.NewInMemoryTrie(termCandidate).Root()
						if bytes.Equal(termRoot, expectedCellHash[1:]) {
							candidate = termCandidate
						} else {
							candidate = trie.NewHashNode(common.Copy(expectedCellHash[1:]))
						}
					}
				}
				setNextNode(candidate, "account:candidate")
			} else {
				setNextNode(trie.NewHashNode(common.Copy(expectedCellHash[1:])), "account:expected_hash")
			}
			keyPos++ // only move one nibble
		} else if cellToExpand.storageAddrLen > 0 { // storage cell (no account in this cell)
			plainStorageKey := cellToExpand.storageAddr[:cellToExpand.storageAddrLen]
			expectedCellHash, _, _, hashErr := hph.witnessComputeCellHashWithStorage(cellToExpand, hph.depths[row], nil)
			if hashErr != nil {
				return nil, hashErr
			}
			expectedChildRoot := common.Copy(expectedCellHash[1:])

			storageUpdate, err := hph.ctx.Storage(plainStorageKey)
			if err != nil {
				return nil, err
			}

			matchedNode, matched := hph.witnessStorageNodeFromUpdate(storageUpdate, expectedChildRoot)
			matchedSource := "ctx_asof"

			if !matched {
				latestUpdate, latestErr := hph.witnessStorageLatestUpdate(plainStorageKey)
				if latestErr != nil {
					return nil, latestErr
				}
				if latestNode, latestMatched := hph.witnessStorageNodeFromUpdate(latestUpdate, expectedChildRoot); latestMatched {
					matchedNode = latestNode
					matched = true
					matchedSource = "ctx_latest"
				}
			}

			if matched {
				if erigonBadRootDebug && matchedSource == "ctx_latest" {
					log.Warn(
						"witness storage node source fallback",
						"row", row,
						"depth", hph.depths[row],
						"key", fmt.Sprintf("0x%x", plainStorageKey),
						"source", matchedSource,
						"expected_child_root", common.BytesToHash(expectedChildRoot),
						"asof_update", witnessUpdateSummary(storageUpdate),
					)
				}
				setNextNode(matchedNode, "storage:"+matchedSource)
			} else {
				deletedNoHash, deletedErr := hph.witnessCellDeletedAsOfNoHash(cellToExpand)
				if deletedErr != nil {
					return nil, deletedErr
				}
				if deletedNoHash {
					hph.logWitnessTombstoneChild(row, cellToExpand, "storage")
					setNextNode(nil, "storage:tombstone")
				} else {
					setNextNode(trie.NewHashNode(expectedChildRoot), "storage:expected_hash")
				}
			}
			// This branch can be terminal for the key path, but we still need to
			// materialize `nextNode` into the current node before exiting the loop.
			stopAfterCurrentNode = true
		} else if cellToExpand.hashLen > 0 { // hash-only cell: preserve canonical hash edge
			expectedCellHash, _, _, hashErr := hph.witnessComputeCellHashWithStorage(cellToExpand, hph.depths[row], nil)
			if hashErr != nil {
				return nil, hashErr
			}
			if len(expectedCellHash) <= 1 {
				return nil, fmt.Errorf("hash-only cell missing expected hash row=%d depth=%d cell=%s", row, hph.depths[row], cellToExpand.FullString())
			}
			setNextNode(trie.NewHashNode(common.Copy(expectedCellHash[1:])), "hash_cell:expected_hash")
			// No expanded payload in this cell; keep hash edge and stop descent.
			stopAfterCurrentNode = true
		} else if cellToExpand.IsEmpty() {
			setNextNode(nil, "empty_cell:nil") // no more expanding can happen (this could be due )
		} else { // default for now before we handle extLen
			setNextNode(&trie.FullNode{}, "default:empty_fullnode")
			keyPos++

			if hph.trace {
				fmt.Printf("[witness] DefaultFullNode cell (%d, %0x, depth=%d) %s %+v\n", row, currentNibble, hph.depths[row], cellToExpand.FullString(), nextNode)
			}
		}

		if hph.trace {
			fmt.Printf("[witness] nextNode (%d, %0x, depth=%d) %T %+v %s keyPos %d\n", row, currentNibble, hph.depths[row], nextNode, nextNode, cellToExpand.FullString(), keyPos)
			fmt.Printf("[witness] currentNode (%d, %0x, depth=%d) %T %+v %s keyPos %d\n", row, currentNibble, hph.depths[row], currentNode, currentNode, cellToExpand.FullString(), keyPos)
		}

		// process the current node
		if fullNode, ok := currentNode.(*trie.FullNode); ok { // handle full node case
			for col := 0; col < 16; col++ {
				currentCell := &hph.grid[row][col]
				if currentCell.IsEmpty() {
					fullNode.Children[col] = nil
					continue
				}
				deletedNoHash, deletedErr := hph.witnessCellDeletedAsOfNoHash(currentCell)
				if deletedErr != nil {
					return nil, deletedErr
				}
				if deletedNoHash {
					hph.logWitnessTombstoneChild(row, currentCell, "fullnode_child")
					fullNode.Children[col] = nil
					continue
				}
				cellHash, _, _, err := hph.witnessComputeCellHashWithStorage(currentCell, hph.depths[row], nil)
				if err != nil {
					return nil, err
				}
				fullNode.Children[col] = trie.NewHashNode(cellHash[1:]) // because cellHash has 33 bytes and we want 32

				if hph.trace {
					fmt.Printf("[witness, pos %d] FullNodeChild Hash (%d, %0x, depth=%d) %s proof %+v\n", keyPos, row, col, hph.depths[row], currentCell.FullString(), fullNode.Children[col])
				}
			}

			// Keep the selected path expandable while preserving sibling commitments.
			// Comparing hash-only placeholder nodes before deeper rows are attached can
			// incorrectly collapse the path and produce truncated witnesses.
			parentRootBeforeSet := witnessStableNodeRoot(fullNode)
			selectedChildRootBeforeSet := []byte(nil)
			selectedChildTypeBeforeSet := "<nil>"
			selectedChildPtrBeforeSet := "nil"
			if child := fullNode.Children[currentNibble]; child != nil {
				selectedChildRootBeforeSet = witnessStableNodeRoot(child)
				selectedChildTypeBeforeSet = fmt.Sprintf("%T", child)
				selectedChildPtrBeforeSet = fmt.Sprintf("%p", child)
			}
			var parentRLPBeforeSet []byte
			var parentRLPBeforeSetErr error
			if erigonWitnessTraceBranchDetail {
				parentRLPBeforeSet, parentRLPBeforeSetErr = rlp.EncodeToBytes(fullNode)
			}
			fullNode.Children[currentNibble] = nextNode
			if hph.trace {
				expectedChildHash, _, _, expectedChildHashErr := hph.witnessComputeCellHashWithStorage(cellToExpand, hph.depths[row], nil)
				expectedChildRoot := []byte(nil)
				if expectedChildHashErr == nil && len(expectedChildHash) > 1 {
					expectedChildRoot = expectedChildHash[1:]
				}
				nextNodeRoot := []byte(nil)
				nextNodePtr := "nil"
				nextNodeNonNilChildren := -1
				if nextNode != nil {
					nextNodeRoot = witnessStableNodeRoot(nextNode)
					nextNodePtr = fmt.Sprintf("%p", nextNode)
					if nextFullNode, ok := nextNode.(*trie.FullNode); ok {
						nextNodeNonNilChildren = 0
						for _, child := range nextFullNode.Children {
							if child != nil {
								nextNodeNonNilChildren++
							}
						}
					}
				}
				parentRootAfterSet := witnessStableNodeRoot(fullNode)
				selectedChildRootAfterSet := []byte(nil)
				selectedChildTypeAfterSet := "<nil>"
				selectedChildPtrAfterSet := "nil"
				if child := fullNode.Children[currentNibble]; child != nil {
					selectedChildRootAfterSet = witnessStableNodeRoot(child)
					selectedChildTypeAfterSet = fmt.Sprintf("%T", child)
					selectedChildPtrAfterSet = fmt.Sprintf("%p", child)
				}
				var parentRLPAfterSet []byte
				var parentRLPAfterSetErr error
				if erigonWitnessTraceBranchDetail {
					parentRLPAfterSet, parentRLPAfterSetErr = rlp.EncodeToBytes(fullNode)
				}
				action := "set_child"
				if nextNode == nil {
					action = "set_nil"
				}
				log.Warn(
					"witness trace branch child",
					"row", row,
					"depth", hph.depths[row],
					"nibble", fmt.Sprintf("%x", currentNibble),
					"action", action,
					"next_node_type", fmt.Sprintf("%T", nextNode),
					"next_node_root", common.BytesToHash(nextNodeRoot),
					"next_node_ptr", nextNodePtr,
					"next_node_source", nextNodeSource,
					"next_node_non_nil_children", nextNodeNonNilChildren,
					"next_matches_expected", expectedChildHashErr == nil && len(expectedChildRoot) > 0 && bytes.Equal(nextNodeRoot, expectedChildRoot),
					"expected_child_root", common.BytesToHash(expectedChildRoot),
					"expected_child_err", expectedChildHashErr,
					"selected_child_type_before_set", selectedChildTypeBeforeSet,
					"selected_child_ptr_before_set", selectedChildPtrBeforeSet,
					"selected_child_before_set", common.BytesToHash(selectedChildRootBeforeSet),
					"selected_child_type_after_set", selectedChildTypeAfterSet,
					"selected_child_ptr_after_set", selectedChildPtrAfterSet,
					"selected_child_after_set", common.BytesToHash(selectedChildRootAfterSet),
					"parent_root_before_set", common.BytesToHash(parentRootBeforeSet),
					"parent_root_after_set", common.BytesToHash(parentRootAfterSet),
					"trace_branch_detail", erigonWitnessTraceBranchDetail,
					"parent_rlp_before_set", fmt.Sprintf("0x%x", parentRLPBeforeSet),
					"parent_rlp_before_set_err", parentRLPBeforeSetErr,
					"parent_rlp_after_set", fmt.Sprintf("0x%x", parentRLPAfterSet),
					"parent_rlp_after_set_err", parentRLPAfterSetErr,
					"cell", cellToExpand.FullString(),
				)
			}
		} else if accNode, ok := currentNode.(*trie.AccountNode); ok {
			if len(hashedKey) <= 64 { // no storage, stop here
				nextNode = nil // nolint:ineffassign, wastedassign
				if hph.trace {
					fmt.Printf("[witness] AccountNode (break) (%d, %0x, depth=%d) %s proof %+v\n", row, currentNibble, hph.depths[row], cellToExpand.FullString(), accNode)
				}
				break
			}

			// there is storage so we need to expand further
			if nextNode == nil {
				nextNode = accNode.Storage
			}
			accNode.Storage = nextNode
			if hph.trace {
				fmt.Printf("[witness] AccountNode (+storage) (%d, %0x, depth=%d) %s proof %+v\n", row, currentNibble, hph.depths[row], cellToExpand.FullString(), accNode)
			}
		} else if extNode, ok := currentNode.(*trie.ShortNode); ok { // handle extension node case
			// expect only one item in this row, so take the first one
			// technically it should be at the last nibble of the key but we will adjust this later
			if extNode.Val != nil {
				// Storage paths may still continue when the account leaf is represented as
				// a terminal short node (key=0x10) that wraps *trie.AccountNode.
				// In that case, attach/advance into account storage trie instead of
				// terminating early.
				var wrappedAccount *trie.AccountNode
				switch v := extNode.Val.(type) {
				case *trie.AccountNode:
					wrappedAccount = v
				case *trie.ShortNode:
					if len(v.Key) == 1 && v.Key[0] == terminatorHexByte {
						if acc, ok := v.Val.(*trie.AccountNode); ok {
							wrappedAccount = acc
						}
					}
				}
				if wrappedAccount != nil && len(hashedKey) > 64 {
					if nextNode == nil {
						nextNode = &trie.FullNode{}
					}
					wrappedAccount.Storage = nextNode
					if hph.trace {
						fmt.Printf("[witness] ShortNode(account+storage) (%d, %0x, depth=%d) %s proof %+v\n", row, currentNibble, hph.depths[row], cellToExpand.FullString(), extNode)
					}
				} else { // early termination
					break
				}
			} else {
				if len(hashedKey) > 64 {
					if _, ok := nextNode.(*trie.FullNode); ok && allowWitnessAccountDiagLog() {
						log.Warn(
							"witness extension attached storage trie without account wrapper",
							"row", row,
							"depth", hph.depths[row],
							"cell", cellToExpand.FullString(),
						)
					}
				}
				extNode.Val = nextNode
			}

			if hph.trace {
				fmt.Printf("[witness, pos %d] ShortNode (%d, %0x, depth=%d) %s proof %+v\n", keyPos, row, currentNibble, hph.depths[row], cellToExpand.FullString(), extNode)
			}
		} else {
			if hph.trace {
				fmt.Printf("[witness] current node is nil (%d, %0x, depth=%d) %s proof %+v\n", row, currentNibble, hph.depths[row], cellToExpand.FullString(), currentNode)
			}
			break // break if currentNode is nil
		}
		// we need to check if we are dealing with the next node being an account node and we have a storage key,
		// in that case start a new tree for the storage
		if nextAccNode, ok := nextNode.(*trie.AccountNode); ok && len(hashedKey) > 64 {
			nextNode = &trie.FullNode{}
			nextAccNode.Storage = nextNode
			if hph.trace {
				fmt.Printf("[witness] AccountNode (+StorageTrie) (%d, %0x, depth=%d) %s [proof %+v\n", row, currentNibble, hph.depths[row], cellToExpand.FullString(), nextAccNode)
			}
		}
		currentNode = nextNode
		if stopAfterCurrentNode {
			break
		}
	}
	tr := trie.NewInMemoryTrie(rootNode)
	// Ensure no stale cached node references from intermediate hash probes leak
	// into the final witness trie returned to callers.
	tr.Reset()
	return tr, nil
}

// unfoldBranchNode returns true if unfolding has been done
func (hph *HexPatriciaHashed) unfoldBranchNode(row, depth int, deleted bool) (bool, error) {
	key := hexNibblesToCompactBytes(hph.currentKey[:hph.currentKeyLen])
	hph.metrics.BranchLoad(hph.currentKey[:hph.currentKeyLen])
	branchData, step, err := hph.ctx.Branch(key)
	if err != nil {
		return false, err
	}
	fileEndTxNum := uint64(step) // TODO: investigate why we cast step to txNum!
	hph.depthsToTxNum[depth] = fileEndTxNum
	if len(branchData) >= 2 {
		branchData = branchData[2:] // skip touch map and keep the rest
	}
	if hph.trace {
		fmt.Printf("unfoldBranchNode prefix '%x', nibbles [%x] depth %d row %d '%x'\n",
			key, hph.currentKey[:hph.currentKeyLen], depth, row, branchData)
	}
	if !hph.rootChecked && hph.currentKeyLen == 0 && len(branchData) == 0 {
		// Special case - empty or deleted root
		hph.rootChecked = true
		return false, nil
	}
	if len(branchData) == 0 {
		log.Warn("got empty branch data during unfold", "key", hex.EncodeToString(key), "row", row, "depth", depth, "deleted", deleted)
		if hph.trace {
			branchData, _, _ = hph.ctx.Branch(key)
			fmt.Printf("unfoldBranchNode prefix '%x', nibbles [%x] depth %d row %d '%x' %s\n", key, hph.currentKey[:hph.currentKeyLen], depth, row, branchData, BranchData(branchData).String())
		}
		return false, fmt.Errorf("empty branch data read during unfold, compact prefix %x nibbles %x", key, hph.currentKey[:hph.currentKeyLen])
	}
	hph.branchBefore[row] = true
	bitmap := binary.BigEndian.Uint16(branchData[0:])
	pos := 2
	if deleted {
		// All cells come as deleted (touched but not present after)
		hph.afterMap[row] = 0
		hph.touchMap[row] = bitmap
	} else {
		hph.afterMap[row] = bitmap
		hph.touchMap[row] = 0
	}
	//fmt.Printf("unfoldBranchNode prefix '%x' [%x], afterMap = [%016b], touchMap = [%016b]\n", key, branchData, hph.afterMap[row], hph.touchMap[row])
	// Loop iterating over the set bits of modMask
	for bitset, j := bitmap, 0; bitset != 0; j++ {
		bit := bitset & -bitset
		nibble := bits.TrailingZeros16(bit)
		cell := &hph.grid[row][nibble]
		fieldBits := branchData[pos]
		pos++
		if pos, err = cell.fillFromFields(branchData, pos, cellFields(fieldBits)); err != nil {
			return false, fmt.Errorf("prefix [%x] branchData[%x]: %w", hph.currentKey[:hph.currentKeyLen], branchData, err)
		}
		if hph.trace {
			fmt.Printf("cell (%d, %x, depth=%d) %s\n", row, nibble, depth, cell.FullString())
		}

		// relies on plain account/storage key so need to be dereferenced before hashing
		if err = cell.deriveHashedKeys(depth, hph.keccak, hph.accountKeyLen); err != nil {
			return false, err
		}
		bitset ^= bit
	}
	return true, nil
}

func (hph *HexPatriciaHashed) unfold(hashedKey []byte, unfolding int) error {
	if hph.trace {
		fmt.Printf("unfold %d: activeRows: %d\n", unfolding, hph.activeRows)
	}
	var upCell *cell
	var touched, present bool
	var upDepth, depth int
	if hph.activeRows == 0 {
		if hph.rootChecked && hph.root.hashLen == 0 && hph.root.hashedExtLen == 0 {
			// No unfolding for empty root
			return nil
		}
		upCell = &hph.root
		touched = hph.rootTouched
		present = hph.rootPresent
		if hph.trace {
			fmt.Printf("unfold root: touched: %t present: %t %s\n", touched, present, upCell.FullString())
		}
	} else {
		upDepth = hph.depths[hph.activeRows-1]
		nib := hashedKey[upDepth-1]
		upCell = &hph.grid[hph.activeRows-1][nib]
		touched = hph.touchMap[hph.activeRows-1]&(uint16(1)<<nib) != 0
		present = hph.afterMap[hph.activeRows-1]&(uint16(1)<<nib) != 0
		if hph.trace {
			fmt.Printf("upCell (%d, %x, updepth=%d) touched: %t present: %t\n", hph.activeRows-1, nib, upDepth, touched, present)
		}
		hph.currentKey[hph.currentKeyLen] = nib
		hph.currentKeyLen++
	}
	row := hph.activeRows
	for i := 0; i < 16; i++ {
		hph.grid[row][i].reset()
	}
	hph.touchMap[row], hph.afterMap[row] = 0, 0
	hph.branchBefore[row] = false

	if upCell.hashedExtLen == 0 {
		depth = upDepth + 1
		unfolded, err := hph.unfoldBranchNode(row, depth, touched && !present)
		if err != nil {
			return err
		}
		if unfolded {
			hph.depths[hph.activeRows] = depth
			hph.activeRows++
		}
		// Return here to prevent activeRow from being incremented when !unfolded
		return nil
	}

	var nibble, copyLen int
	if upCell.hashedExtLen >= unfolding {
		depth = upDepth + unfolding
		nibble = int(upCell.hashedExtension[unfolding-1])
		copyLen = unfolding - 1
	} else {
		depth = upDepth + upCell.hashedExtLen
		nibble = int(upCell.hashedExtension[upCell.hashedExtLen-1])
		copyLen = upCell.hashedExtLen - 1
	}

	if touched {
		hph.touchMap[row] = uint16(1) << nibble
	}
	if present {
		hph.afterMap[row] = uint16(1) << nibble
	}

	cell := &hph.grid[row][nibble]
	cell.fillFromUpperCell(upCell, depth, min(unfolding, upCell.hashedExtLen))
	if hph.trace {
		fmt.Printf("unfolded cell (%d, %x, depth=%d) %s\n", row, nibble, depth, cell.FullString())
	}

	if row >= 64 {
		cell.accountAddrLen = 0
	}
	if copyLen > 0 {
		copy(hph.currentKey[hph.currentKeyLen:], upCell.hashedExtension[:copyLen])
	}
	hph.currentKeyLen += copyLen

	hph.depths[hph.activeRows] = depth
	hph.activeRows++
	return nil
}

func (hph *HexPatriciaHashed) needFolding(hashedKey []byte) bool {
	return !bytes.HasPrefix(hashedKey, hph.currentKey[:hph.currentKeyLen])
}

var (
	hadToLoad   atomic.Uint64
	skippedLoad atomic.Uint64
	hadToReset  atomic.Uint64
)

type skipStat struct {
	accLoaded, accSkipped, accReset, storReset, storLoaded, storSkipped uint64
}

const DepthWithoutNodeHashes = 35 //nolint

func (hph *HexPatriciaHashed) createCellGetter(
	b []byte,
	updateKey []byte,
	row, depth int,
	branchWriter io.Writer,
) func(nibble int, skip bool) (*cell, error) {
	hashBefore := make([]byte, 32) // buffer reused between calls
	if branchWriter == nil {
		branchWriter = hph.keccak2
	}
	return func(nibble int, skip bool) (*cell, error) {
		if skip {
			if _, err := branchWriter.Write(b); err != nil {
				return nil, fmt.Errorf("failed to write empty nibble to hash: %w", err)
			}
			if hph.trace {
				fmt.Printf("  %x: empty(%d, %x, depth=%d)\n", nibble, row, nibble, depth)
			}
			return nil, nil
		}
		cell := &hph.grid[row][nibble]
		if cell.accountAddrLen > 0 && cell.stateHashLen == 0 && !cell.loaded.account() && !cell.Deleted() {
			//panic("account not loaded" + fmt.Sprintf("%x", cell.accountAddr[:cell.accountAddrLen]))
			log.Warn("account not loaded", "pref", updateKey, "c", fmt.Sprintf("(%d, %x, depth=%d", row, nibble, depth), "cell", cell.String())
		}
		if cell.storageAddrLen > 0 && cell.stateHashLen == 0 && !cell.loaded.storage() && !cell.Deleted() {
			//panic("storage not loaded" + fmt.Sprintf("%x", cell.storageAddr[:cell.storageAddrLen]))
			log.Warn("storage not loaded", "pref", updateKey, "c", fmt.Sprintf("(%d, %x, depth=%d", row, nibble, depth), "cell", cell.String())
		}

		loadedBefore := cell.loaded
		copy(hashBefore, cell.stateHash[:cell.stateHashLen])
		hashBefore = hashBefore[:cell.stateHashLen]

		cellHash, err := hph.computeCellHash(cell, depth, hph.hashAuxBuffer[:0])
		if err != nil {
			return nil, err
		}
		if hph.trace {
			fmt.Printf("  %x: computeCellHash(%d, %x, depth=%d)=[%x]\n", nibble, row, nibble, depth, cellHash)
		}

		if hashBefore != nil && (cell.accountAddrLen > 0 || cell.storageAddrLen > 0) {
			counters := hph.hadToLoadL[hph.depthsToTxNum[depth]]
			if !bytes.Equal(hashBefore, cell.stateHash[:cell.stateHashLen]) {
				if cell.accountAddrLen > 0 {
					counters.accReset++
					counters.accLoaded++
				}
				if cell.storageAddrLen > 0 {
					counters.storReset++
					counters.storLoaded++
				}
			} else {
				if cell.accountAddrLen > 0 && (!loadedBefore.account() && !cell.loaded.account()) {
					counters.accSkipped++
				}
				if cell.storageAddrLen > 0 && (!loadedBefore.storage() && !cell.loaded.storage()) {
					counters.storSkipped++
				}
			}
			hph.hadToLoadL[hph.depthsToTxNum[depth]] = counters
		}
		if _, err := branchWriter.Write(cellHash); err != nil {
			return nil, err
		}

		return cell, nil
	}
}

const terminatorHexByte = 16 // max nibble value +1. Defines end of nibble line in the trie or splits address and storage space in trie.

// updateKind is a type of update that is being applied to the trie structure.
type updateKind uint8

const (
	// updateKindDelete means after we processed longest common prefix, row ended up empty.
	updateKindDelete updateKind = 0b0

	// updateKindPropagate is an update operation ended up with a single nibble which is leaf or extension node.
	// We do not store keys with only one cell as a value in db, instead we copy them upwards to the parent branch.
	//
	// In case current prefix existed before and node is fused to upper level, this causes deletion for current prefix
	// and update of branch value on upper level.
	// 	e.g.: leaf was at prefix 0xbeef, but we fuse it in level above, so
	//  - delete 0xbeef
	//  - update 0xbee
	updateKindPropagate updateKind = 0b01

	// updateKindBranch is an update operation ended up as a branch of 2+ cells.
	// That does not necessarily means that branch is NEW, it could be an existing branch that was updated.
	updateKindBranch updateKind = 0b10
)

// Kind defines how exactly given update should be folded upwards to the parent branch or root.
// It also returns number of nibbles that left in branch after the operation.
func afterMapUpdateKind(afterMap uint16) (kind updateKind, nibblesAfterUpdate int) {
	nibblesAfterUpdate = bits.OnesCount16(afterMap)
	switch nibblesAfterUpdate {
	case 0:
		return updateKindDelete, nibblesAfterUpdate
	case 1:
		return updateKindPropagate, nibblesAfterUpdate
	default:
		return updateKindBranch, nibblesAfterUpdate
	}
}

// The purpose of fold is to reduce hph.currentKey[:hph.currentKeyLen]. It should be invoked
// until that current key becomes a prefix of hashedKey that we will process next
// (in other words until the needFolding function returns 0)
func (hph *HexPatriciaHashed) fold() (err error) {
	updateKeyLen := hph.currentKeyLen
	if hph.activeRows == 0 {
		return errors.New("cannot fold - no active rows")
	}
	if hph.trace {
		fmt.Printf("fold [%x] activeRows: %d touchMap: %016b afterMap: %016b\n", hph.currentKey[:hph.currentKeyLen], hph.activeRows, hph.touchMap[hph.activeRows-1], hph.afterMap[hph.activeRows-1])
	}
	// Move information to the row above
	var upCell *cell
	var nibble, upDepth int
	row := hph.activeRows - 1
	upRow := row - 1
	if row == 0 {
		if hph.trace {
			fmt.Printf("fold: parent is root %s\n", hph.root.FullString())
		}
		upCell = &hph.root
	} else {
		upDepth = hph.depths[upRow]
		nibble = int(hph.currentKey[upDepth-1])
		if hph.trace {
			fmt.Printf("fold: parent (%d, %x, depth=%d)\n", upRow, nibble, upDepth)
		}
		upCell = &hph.grid[upRow][nibble]
	}

	depth := hph.depths[row]
	updateKey := hexNibblesToCompactBytes(hph.currentKey[:updateKeyLen])
	defer func() { hph.depthsToTxNum[depth] = 0 }()

	if hph.trace {
		fmt.Printf("fold: (row=%d, {%s}, depth=%d) prefix [%x] touchMap: %016b afterMap: %016b \n",
			row, updatedNibs(hph.touchMap[row]&hph.afterMap[row]), depth, hph.currentKey[:hph.currentKeyLen], hph.touchMap[row], hph.afterMap[row])
	}

	updateKind, nibblesLeftAfterUpdate := afterMapUpdateKind(hph.afterMap[row])
	switch updateKind {
	case updateKindDelete: // Everything deleted
		if hph.touchMap[row] != 0 {
			if row == 0 {
				// Root is deleted because the tree is empty
				hph.rootTouched = true
				hph.rootPresent = false
			} else if upDepth == 64 {
				// Special case - all storage items of an account have been deleted, but it does not automatically delete the account, just makes it empty storage
				// Therefore we are not propagating deletion upwards, but turn it into a modification
				hph.touchMap[row-1] |= uint16(1) << nibble
			} else {
				// Deletion is propagated upwards
				hph.touchMap[row-1] |= uint16(1) << nibble
				hph.afterMap[row-1] &^= uint16(1) << nibble
			}
		}

		upCell.reset()
		if hph.branchBefore[row] {
			_, err := hph.branchEncoder.CollectUpdate(hph.ctx, updateKey, 0, hph.touchMap[row], 0, RetrieveCellNoop)
			if err != nil {
				return fmt.Errorf("failed to encode leaf node update: %w", err)
			}
		}
		hph.activeRows--
		if upDepth > 0 {
			hph.currentKeyLen = upDepth - 1
		} else {
			hph.currentKeyLen = 0
		}
	case updateKindPropagate: // Leaf or extension node
		if hph.touchMap[row] != 0 {
			// any modifications
			if row == 0 {
				hph.rootTouched = true
			} else {
				// Modification is propagated upwards
				hph.touchMap[row-1] |= uint16(1) << nibble
			}
		}
		nibble := bits.TrailingZeros16(hph.afterMap[row])
		cell := &hph.grid[row][nibble]
		upCell.extLen = 0
		upCell.stateHashLen = 0
		// propagate cell into parent row
		upCell.fillFromLowerCell(cell, depth, hph.currentKey[upDepth:hph.currentKeyLen], nibble)

		if hph.branchBefore[row] { // encode Delete if prefix existed before
			//fmt.Printf("delete existed row %d prefix %x\n", row, updateKey)
			_, err := hph.branchEncoder.CollectUpdate(hph.ctx, updateKey, 0, hph.touchMap[row], 0, RetrieveCellNoop)
			if err != nil {
				return fmt.Errorf("failed to encode leaf node update: %w", err)
			}
		}
		hph.activeRows--
		hph.currentKeyLen = max(upDepth-1, 0)
		if hph.trace {
			fmt.Printf("formed leaf (%d %x, depth=%d) [%x] %s\n", row, nibble, depth, updateKey, cell.FullString())
		}
	case updateKindBranch:
		if hph.touchMap[row] != 0 { // any modifications
			if row == 0 {
				hph.rootTouched = true
				hph.rootPresent = true
			} else {
				// Modification is propagated upwards
				hph.touchMap[row-1] |= uint16(1) << nibble
			}
		}
		bitmap := hph.touchMap[row] & hph.afterMap[row]
		if !hph.branchBefore[row] {
			// There was no branch node before, so we need to touch even the singular child that existed
			hph.touchMap[row] |= hph.afterMap[row]
			bitmap |= hph.afterMap[row]
		}

		// Calculate total length of all hashes
		totalBranchLen := 17 - nibblesLeftAfterUpdate // For every empty cell, one byte
		for bitset, j := hph.afterMap[row], 0; bitset != 0; j++ {
			bit := bitset & -bitset
			nibble := bits.TrailingZeros16(bit)
			cell := &hph.grid[row][nibble]

			if hph.memoizationOff {
				cell.stateHashLen = 0
			}
			/* memoization of state hashes*/
			counters := hph.hadToLoadL[hph.depthsToTxNum[depth]]
			if cell.stateHashLen > 0 && (hph.touchMap[row]&hph.afterMap[row]&uint16(1<<nibble) > 0 || cell.stateHashLen != length.Hash) {
				// drop state hash if updated or hashLen < 32 (corner case, may even not encode such leaf hashes)
				if hph.trace {
					fmt.Printf("DROP hash for (%d, %x, depth=%d) %s\n", row, nibble, depth, cell.FullString())
				}
				cell.stateHashLen = 0
				hadToReset.Add(1)
				if cell.accountAddrLen > 0 {
					counters.accReset++
				}
				if cell.storageAddrLen > 0 {
					counters.storReset++
				}
			}

			if cell.stateHashLen == 0 { // load state if needed
				if !cell.loaded.account() && cell.accountAddrLen > 0 {
					hph.metrics.AccountLoad(cell.accountAddr[:cell.accountAddrLen])
					upd, err := hph.ctx.Account(cell.accountAddr[:cell.accountAddrLen])
					if err != nil {
						return fmt.Errorf("failed to get account: %w", err)
					}
					cell.setFromUpdate(upd)
					// if update is empty, loaded flag was not updated so do it manually
					cell.loaded = cell.loaded.addFlag(cellLoadAccount)
					counters.accLoaded++
				}
				if !cell.loaded.storage() && cell.storageAddrLen > 0 {
					hph.metrics.StorageLoad(cell.storageAddr[:cell.storageAddrLen])
					upd, err := hph.ctx.Storage(cell.storageAddr[:cell.storageAddrLen])
					if err != nil {
						return fmt.Errorf("failed to get storage: %w", err)
					}
					cell.setFromUpdate(upd)
					// if update is empty, loaded flag was not updated so do it manually
					cell.loaded = cell.loaded.addFlag(cellLoadStorage)
					counters.storLoaded++
				}
				// computeCellHash can reset hash as well so have to check if node has been skipped  right after computeCellHash.
			}
			hph.hadToLoadL[hph.depthsToTxNum[depth]] = counters
			/* end of memoization */

			totalBranchLen += hph.computeCellHashLen(cell, depth)
			bitset ^= bit
		}

		hph.keccak2.Reset()
		branchWriter := io.Writer(hph.keccak2)
		var branchNodePreimageBuf bytes.Buffer
		if erigonWitnessCaptureNodePreimages {
			branchNodePreimageBuf.Reset()
			branchWriter = io.MultiWriter(hph.keccak2, &branchNodePreimageBuf)
		}
		pt := rlp.GenerateStructLen(hph.hashAuxBuffer[:], totalBranchLen)
		if _, err := branchWriter.Write(hph.hashAuxBuffer[:pt]); err != nil {
			return err
		}

		b := [...]byte{0x80}
		cellGetter := hph.createCellGetter(b[:], updateKey, row, depth, branchWriter)
		lastNibble, err := hph.branchEncoder.CollectUpdate(hph.ctx, updateKey, bitmap, hph.touchMap[row], hph.afterMap[row], cellGetter)
		if err != nil {
			return fmt.Errorf("failed to encode branch update: %w", err)
		}
		for i := lastNibble; i < 17; i++ {
			if _, err := branchWriter.Write(b[:]); err != nil {
				return err
			}
			if hph.trace {
				fmt.Printf("  %x: empty(%d, %x, depth=%d)\n", i, row, i, depth)
			}
		}
		upCell.extLen = depth - upDepth - 1
		upCell.hashedExtLen = upCell.extLen
		if upCell.extLen > 0 {
			copy(upCell.extension[:], hph.currentKey[upDepth:hph.currentKeyLen])
			copy(upCell.hashedExtension[:], hph.currentKey[upDepth:hph.currentKeyLen])
		}
		if depth < 64 {
			upCell.accountAddrLen = 0
		}
		upCell.storageAddrLen = 0
		upCell.hashLen = 32
		if _, err := hph.keccak2.Read(upCell.hash[:]); err != nil {
			return err
		}
		if erigonWitnessCaptureNodePreimages {
			captureWitnessNodePreimage(branchNodePreimageBuf.Bytes())
		}
		if hph.trace {
			fmt.Printf("} [%x]\n", upCell.hash[:])
		}
		hph.activeRows--
		if upDepth > 0 {
			hph.currentKeyLen = upDepth - 1
		} else {
			hph.currentKeyLen = 0
		}
	}
	return nil
}

func (hph *HexPatriciaHashed) deleteCell(hashedKey []byte) {
	if hph.trace {
		fmt.Printf("deleteCell, activeRows = %d\n", hph.activeRows)
	}
	var cell *cell
	if hph.activeRows == 0 { // Remove the root
		cell = &hph.root
		hph.rootTouched, hph.rootPresent = true, false
	} else {
		row := hph.activeRows - 1
		if hph.depths[row] < len(hashedKey) {
			if hph.trace {
				fmt.Printf("deleteCell skipping spurious delete depth=%d, len(hashedKey)=%d\n", hph.depths[row], len(hashedKey))
			}
			return
		}
		nibble := int(hashedKey[hph.currentKeyLen])
		cell = &hph.grid[row][nibble]
		col := uint16(1) << nibble
		if hph.afterMap[row]&col != 0 {
			// Prevent "spurious deletions", i.e. deletion of absent items
			hph.touchMap[row] |= col
			hph.afterMap[row] &^= col
			if hph.trace {
				fmt.Printf("deleteCell setting (%d, %x)\n", row, nibble)
			}
		} else {
			if hph.trace {
				fmt.Printf("deleteCell ignoring (%d, %x)\n", row, nibble)
			}
		}
	}
	cell.reset()
}

// fetches cell by key and set touch/after maps. Requires that prefix to be already unfolded
func (hph *HexPatriciaHashed) updateCell(plainKey, hashedKey []byte, u *Update) (cell *cell) {
	hph.metrics.Updates(plainKey)

	if u.Deleted() {
		hph.deleteCell(hashedKey)
		return nil
	}

	var depth int
	if hph.activeRows == 0 {
		cell = &hph.root
		hph.rootTouched, hph.rootPresent = true, true
	} else {
		row := hph.activeRows - 1
		depth = hph.depths[row]
		nibble := int(hashedKey[hph.currentKeyLen])
		cell = &hph.grid[row][nibble]
		col := uint16(1) << nibble

		hph.touchMap[row] |= col
		hph.afterMap[row] |= col
		if hph.trace {
			fmt.Printf("updateCell setting (%d, %x, depth=%d)\n", row, nibble, depth)
		}
	}
	if cell.hashedExtLen == 0 {
		copy(cell.hashedExtension[:], hashedKey[depth:])
		cell.hashedExtLen = len(hashedKey) - depth
		if hph.trace {
			fmt.Printf("set downHasheKey=[%x]\n", cell.hashedExtension[:cell.hashedExtLen])
		}
	} else {
		if hph.trace {
			fmt.Printf("keep downHasheKey=[%x]\n", cell.hashedExtension[:cell.hashedExtLen])
		}
	}
	if len(plainKey) == hph.accountKeyLen {
		cell.accountAddrLen = len(plainKey)
		copy(cell.accountAddr[:], plainKey)

		cell.CodeHash = empty.CodeHash
	} else { // set storage key
		cell.storageAddrLen = len(plainKey)
		copy(cell.storageAddr[:], plainKey)
	}
	cell.stateHashLen = 0

	cell.setFromUpdate(u)
	if hph.trace {
		fmt.Printf("updateCell %x => %s\n", plainKey, u.String())
	}
	return cell
}

func (hph *HexPatriciaHashed) RootHash() ([]byte, error) {
	hph.root.stateHashLen = 0
	rootHash, err := hph.computeCellHash(&hph.root, 0, nil)
	if err != nil {
		return nil, err
	}
	return rootHash[1:], nil // first byte is 128+hash_len=160
}

func (hph *HexPatriciaHashed) followAndUpdate(hashedKey, plainKey []byte, stateUpdate *Update) (err error) {
	//if hph.trace {
	// fmt.Printf("mnt: %0x current: %x path %x\n", hph.mountedNib, hph.currentKey[:hph.currentKeyLen], hashedKey)
	//}
	// Keep folding until the currentKey is the prefix of the key we modify
	for hph.needFolding(hashedKey) {
		foldDone := hph.metrics.StartFolding(plainKey)
		if err := hph.fold(); err != nil {
			return fmt.Errorf("fold: %w", err)
		}
		foldDone()
	}
	// Now unfold until we step on an empty cell
	for unfolding := hph.needUnfolding(hashedKey); unfolding > 0; unfolding = hph.needUnfolding(hashedKey) {
		printLater := hph.currentKeyLen == 0 && hph.mounted && hph.trace
		unfoldDone := hph.metrics.StartUnfolding(plainKey)
		if err := hph.unfold(hashedKey, unfolding); err != nil {
			return fmt.Errorf("unfold: %w", err)
		}
		unfoldDone()
		if printLater {
			fmt.Printf("[%x] subtrie pref '%x' d=%d\n", hph.mountedNib, hph.currentKey[:hph.currentKeyLen], hph.depths[max(0, hph.activeRows-1)])
		}
		// fmt.Printf("mnt: %0x current: %x path %x\n", hph.mountedNib, hph.currentKey[:hph.currentKeyLen], hashedKey)
	}

	if stateUpdate == nil {
		// Update the cell
		if len(plainKey) == hph.accountKeyLen {
			hph.metrics.AccountLoad(plainKey)
			stateUpdate, err = hph.ctx.Account(plainKey)
			if err != nil {
				return fmt.Errorf("GetAccount for key %x failed: %w", plainKey, err)
			}
		} else {
			hph.metrics.StorageLoad(plainKey)
			stateUpdate, err = hph.ctx.Storage(plainKey)
			if err != nil {
				return fmt.Errorf("GetStorage for key %x failed: %w", plainKey, err)
			}
		}
	}
	hph.updateCell(plainKey, hashedKey, stateUpdate)

	mxTrieProcessedKeys.Inc()
	return nil
}

func (hph *HexPatriciaHashed) foldMounted(nib int) (cell, error) {
	if nib != hph.mountedNib {
		panic(fmt.Sprintf("foldMounted: nib (%x)!= mountedNib (%x)", nib, hph.mountedNib))
	}

	if hph.trace {
		fmt.Printf("====[%x] folding rows %d depths %+v\n", hph.mountedNib, hph.activeRows, hph.depths[:hph.activeRows])
		defer func() { fmt.Printf("=======[%x] folded =========\n", hph.mountedNib) }()
	}

	for hph.activeRows > 0 {
		// fmt.Printf("===[%x] folding prefix %x (len %d)\n", hph.mountedNib, hph.currentKey[:hph.currentKeyLen], hph.currentKeyLen)
		if hph.activeRows == 1 && hph.depths[hph.activeRows-1] == 1 {
			if hph.trace {
				fmt.Printf("mount early as nibble %02x %s\n", hph.mountedNib, hph.grid[0][hph.mountedNib].String())
			}
			// fmt.Printf("===[%x] stop folding at %x\n", hph.mountedNib, hph.currentKey[:hph.currentKeyLen])
			return hph.grid[0][hph.mountedNib], nil
		}
		if err := hph.fold(); err != nil {
			return cell{}, fmt.Errorf("final fold: %w", err)
		}
	}

	if hph.trace {
		fmt.Printf("===[%x] !@folded to the root\n", hph.mountedNib)
	}
	if hph.rootPresent && hph.rootTouched {
		if hph.trace {
			fmt.Printf("mount root as %02x %s\n", hph.mountedNib, hph.root.String())
		}
		return hph.root, nil
	}
	if hph.trace {
		fmt.Printf("mount as nibble %02x %s\n", hph.mountedNib, hph.grid[0][hph.mountedNib].String())
	}
	// todo potential bug
	return hph.grid[0][hph.mountedNib], nil
}

// Generate the block witness. This works by loading each key from the list of updates (they are not really updates since we won't modify the trie,
// but currently need to be defined like that for the fold/unfold algorithm) into the grid and traversing the grid to convert it into `triedeprecated.Trie`.
// All the individual tries are combined to create the final witness trie.
// Because the grid is lacking information about the code in smart contract accounts which is also part of the witness, we need to provide that as an input parameter to this function (`codeReads`)
func (hph *HexPatriciaHashed) GenerateWitness(ctx context.Context, updates *Updates, codeReads map[common.Hash]witnesstypes.CodeWithHash, expectedRootHash []byte, logPrefix string) (witnessTrie *trie.Trie, rootHash []byte, err error) {
	var (
		m  runtime.MemStats
		ki uint64

		updatesCount = updates.Size()
		logEvery     = time.NewTicker(20 * time.Second)
	)
	inputUpdateNilCount := 0
	inputUpdateWithPayloadCount := 0
	inputUpdateNilSamples := make([]string, 0, witnessDiagSampleMax())
	inputUpdateWithPayloadSamples := make([]string, 0, witnessDiagSampleMax())
	ctxUpdateNilCount := 0
	ctxUpdateDeleteCount := 0
	ctxUpdateBalanceCount := 0
	ctxUpdateNonceCount := 0
	ctxUpdateCodeCount := 0
	ctxUpdateStorageCount := 0
	ctxUpdateSamples := make([]string, 0, witnessDiagSampleMax())
	keyPreview := func(k []byte) string {
		const max = 24
		if len(k) == 0 {
			return "0x"
		}
		if len(k) <= max {
			return fmt.Sprintf("0x%x", k)
		}
		return fmt.Sprintf("0x%x...(+%d bytes)", k[:max], len(k)-max)
	}
	hph.memoizationOff, hph.trace = true, false
	// defer func() {
	// 	hph.memoizationOff, hph.trace = false, false
	// }()

	defer logEvery.Stop()
	var tries []*trie.Trie = make([]*trie.Trie, 0, len(updates.keys)) // slice of tries, i.e the witness for each key, these will be all merged into single trie
	plainKeysByTrie := make([][]byte, 0, len(updates.keys))
	hashedKeysByTrie := make([][]byte, 0, len(updates.keys))
	ctxUpdatesByTrie := make([]*Update, 0, len(updates.keys))
	inputUpdatesByTrie := make([]*Update, 0, len(updates.keys))
	ctxUpdateSummaries := make([]string, 0, len(updates.keys))
	inputUpdateSummaries := make([]string, 0, len(updates.keys))
	ctxUpdatesSeen := 0
	ctxUpdatesWouldApply := 0
	ctxUpdatesApplied := 0
	ctxUpdatesDeleteSeen := 0
	ctxUpdatesSkippedNoInput := 0
	ctxUpdatesSyntheticDeleteSkipped := 0
	ctxRuntimeFlags := resolveWitnessCtxUpdateRuntimeFlags()
	ctxUpdatesModeDirect := updates.mode == ModeDirect
	ctxUpdatesModeDirectApply := ctxUpdatesModeDirect && ctxRuntimeFlags.ModeDirectEnabled && !ctxRuntimeFlags.ApplyDisabledUnsafe
	err = updates.HashSort(ctx, func(hashedKey, plainKey []byte, stateUpdate *Update) error {
		select {
		case <-logEvery.C:
			dbg.ReadMemStats(&m)
			log.Info(fmt.Sprintf("[%s][agg] computing trie", logPrefix),
				"progress", fmt.Sprintf("%s/%s", common.PrettyCounter(ki), common.PrettyCounter(updatesCount)),
				"alloc", common.ByteCount(m.Alloc), "sys", common.ByteCount(m.Sys))

		default:
		}

		var tr *trie.Trie
		if hph.trace {
			fmt.Printf("\n%d/%d) witnessing [%x] hashedKey [%x] currentKey [%x]\n", ki+1, updatesCount, plainKey, hashedKey, hph.currentKey[:hph.currentKeyLen])
		}

		var update *Update
		if len(plainKey) == hph.accountKeyLen { // account
			update, err = hph.ctx.Account(plainKey)
			if err != nil {
				return fmt.Errorf("account with plainkey=%x not found: %w", plainKey, err)
			}
			if hph.trace {
				addrHash := crypto.Keccak256(plainKey)
				fmt.Printf("account with plainKey=%x, addrHash=%x FOUND = %v\n", plainKey, addrHash, update)
			}
		} else {
			update, err = hph.ctx.Storage(plainKey)
			if err != nil {
				return fmt.Errorf("storage with plainkey=%x not found: %w", plainKey, err)
			}
			if hph.trace {
				fmt.Printf("storage found = %v\n", update.Storage[:update.StorageLen])
			}
		}
		keyType := "storage"
		if len(plainKey) == hph.accountKeyLen {
			keyType = "account"
		}
		if update == nil {
			ctxUpdateNilCount++
		} else {
			if update.Flags&DeleteUpdate != 0 {
				ctxUpdateDeleteCount++
			}
			if update.Flags&BalanceUpdate != 0 {
				ctxUpdateBalanceCount++
			}
			if update.Flags&NonceUpdate != 0 {
				ctxUpdateNonceCount++
			}
			if update.Flags&CodeUpdate != 0 {
				ctxUpdateCodeCount++
			}
			if update.Flags&StorageUpdate != 0 {
				ctxUpdateStorageCount++
			}
		}
		if erigonBadRootDebug && len(ctxUpdateSamples) < cap(ctxUpdateSamples) {
			ctxUpdateSamples = append(ctxUpdateSamples, fmt.Sprintf(
				"idx=%d type=%s key=%s ctx_update=%s",
				ki,
				keyType,
				keyPreview(plainKey),
				witnessUpdateSummary(update),
			))
		}
		traceThisKey := shouldTraceWitnessKey(logPrefix, plainKey, hashedKey)
		prevTrace := hph.trace
		if stateUpdate == nil {
			inputUpdateNilCount++
			if erigonBadRootDebug && len(inputUpdateNilSamples) < cap(inputUpdateNilSamples) {
				inputUpdateNilSamples = append(inputUpdateNilSamples, fmt.Sprintf(
					"idx=%d type=%s key=%s ctx_update=%s input_update=<nil>",
					ki,
					keyType,
					keyPreview(plainKey),
					witnessUpdateSummary(update),
				))
			}
		} else {
			inputUpdateWithPayloadCount++
			if erigonBadRootDebug && len(inputUpdateWithPayloadSamples) < cap(inputUpdateWithPayloadSamples) {
				inputUpdateWithPayloadSamples = append(inputUpdateWithPayloadSamples, fmt.Sprintf(
					"idx=%d type=%s key=%s ctx_update=%s input_update=%s",
					ki,
					keyType,
					keyPreview(plainKey),
					witnessUpdateSummary(update),
					witnessUpdateSummary(stateUpdate),
				))
			}
		}
		if traceThisKey {
			hph.trace = true
			log.Warn(
				"witness trace key begin",
				"prefix", logPrefix,
				"key_idx", ki,
				"plain_key", fmt.Sprintf("0x%x", plainKey),
				"hashed_key", fmt.Sprintf("0x%x", hashedKey),
				"ctx_update", witnessUpdateSummary(update),
				"input_update", witnessUpdateSummary(stateUpdate),
				"active_rows", hph.activeRows,
				"current_key_len", hph.currentKeyLen,
				"current_key_prefix", fmt.Sprintf("0x%x", hph.currentKey[:hph.currentKeyLen]),
			)
		}
		defer func() {
			hph.trace = prevTrace
		}()

		// Keep folding until the currentKey is the prefix of the key we modify
		for hph.needFolding(hashedKey) {
			if err := hph.fold(); err != nil {
				return fmt.Errorf("fold: %w", err)
			}
		}
		// Now unfold until we step on an empty cell
		for unfolding := hph.needUnfolding(hashedKey); unfolding > 0; unfolding = hph.needUnfolding(hashedKey) {
			if err := hph.unfold(hashedKey, unfolding); err != nil {
				return fmt.Errorf("unfold: %w", err)
			}
		}
		//hph.PrintGrid()
		if ctxRuntimeFlags.ApplyEffective || ctxUpdatesModeDirectApply {
			// Only payloaded iterator updates may mutate witness cells. ModeDirect
			// carries touched keys without canonical payloads; synthesizing from ctx
			// makes witness generation depend on the ambient as-of view and can drift
			// from the recorded block inputs.
			ctxUpdatesSeen++
			applyUpdate := stateUpdate
			if applyUpdate == nil {
				ctxUpdatesSkippedNoInput++
				if update != nil && update.Deleted() {
					ctxUpdatesSyntheticDeleteSkipped++
				}
			} else {
				if applyUpdate.Deleted() {
					ctxUpdatesDeleteSeen++
				}
				ctxUpdatesWouldApply++
				hph.updateCell(plainKey, hashedKey, applyUpdate)
				ctxUpdatesApplied++
			}
		}
		if traceThisKey {
			log.Warn(
				"witness trace key pre-trie",
				"prefix", logPrefix,
				"key_idx", ki,
				"plain_key", fmt.Sprintf("0x%x", plainKey),
				"hashed_key", fmt.Sprintf("0x%x", hashedKey),
				"active_rows", hph.activeRows,
				"current_key_len", hph.currentKeyLen,
				"current_key_prefix", fmt.Sprintf("0x%x", hph.currentKey[:hph.currentKeyLen]),
				"row_summary", hph.witnessTraceRowsSummary(hashedKey),
			)
		}

		// convert grid to trie.Trie
		tr, err = hph.toWitnessTrie(hashedKey, codeReads) // build witness trie for this key, based on the current state of the grid
		if err != nil {
			return err
		}
		if traceThisKey {
			trieRoot := []byte(nil)
			if tr != nil {
				trieRoot = tr.Root()
			}
			log.Warn(
				"witness trace key post-trie",
				"prefix", logPrefix,
				"key_idx", ki,
				"plain_key", fmt.Sprintf("0x%x", plainKey),
				"hashed_key", fmt.Sprintf("0x%x", hashedKey),
				"trie_root", common.BytesToHash(trieRoot),
				"expected_root", common.BytesToHash(expectedRootHash),
				"matches_expected", bytes.Equal(trieRoot, expectedRootHash),
				"row_summary", hph.witnessTraceRowsSummary(hashedKey),
			)
		}
		//computedRootHash := tr.Root()
		//// fmt.Printf("computedRootHash = %x\n", computedRootHash)
		//
		//if !bytes.Equal(computedRootHash, expectedRootHash) {
		//	err = fmt.Errorf("root hash mismatch computedRootHash(%x)!=expectedRootHash(%x)", computedRootHash, expectedRootHash)
		//	return err
		//}

		tries = append(tries, tr)
		plainKeysByTrie = append(plainKeysByTrie, common.Copy(plainKey))
		hashedKeysByTrie = append(hashedKeysByTrie, common.Copy(hashedKey))
		ctxUpdatesByTrie = append(ctxUpdatesByTrie, update)
		inputUpdatesByTrie = append(inputUpdatesByTrie, stateUpdate)
		ctxUpdateSummaries = append(ctxUpdateSummaries, witnessUpdateSummary(update))
		inputUpdateSummaries = append(inputUpdateSummaries, witnessUpdateSummary(stateUpdate))
		ki++
		return nil
	})

	if err != nil {
		return nil, nil, fmt.Errorf("hash sort failed: %w", err)
	}
	if erigonBadRootDebug {
		mode, statsTotal, statsWithPayload, statsNilPayload, statsDelete, statsBalance, statsNonce, statsCode, statsStorage, statsSamples := updates.DebugPayloadStats(witnessDiagSampleMax())
		log.Warn(
			"witness input update payload summary",
			"prefix", logPrefix,
			"updates_mode", mode,
			"updates_total", statsTotal,
			"updates_with_payload", statsWithPayload,
			"updates_nil_payload", statsNilPayload,
			"updates_delete_flags", statsDelete,
			"updates_balance_flags", statsBalance,
			"updates_nonce_flags", statsNonce,
			"updates_code_flags", statsCode,
			"updates_storage_flags", statsStorage,
			"updates_samples", statsSamples,
			"iter_ctx_nil_count", ctxUpdateNilCount,
			"iter_ctx_delete_flags", ctxUpdateDeleteCount,
			"iter_ctx_balance_flags", ctxUpdateBalanceCount,
			"iter_ctx_nonce_flags", ctxUpdateNonceCount,
			"iter_ctx_code_flags", ctxUpdateCodeCount,
			"iter_ctx_storage_flags", ctxUpdateStorageCount,
			"iter_ctx_samples", ctxUpdateSamples,
			"iter_nil_payload_count", inputUpdateNilCount,
			"iter_with_payload_count", inputUpdateWithPayloadCount,
			"iter_nil_payload_samples", inputUpdateNilSamples,
			"iter_with_payload_samples", inputUpdateWithPayloadSamples,
			"apply_ctx_updates", ctxRuntimeFlags.ApplyEffective,
			"apply_ctx_updates_mode_direct", ctxUpdatesModeDirect,
			"apply_ctx_updates_mode_direct_requested", ctxRuntimeFlags.ModeDirectRequested,
			"apply_ctx_updates_mode_direct_disabled", ctxRuntimeFlags.ModeDirectDisabled,
			"apply_ctx_updates_mode_direct_enabled", ctxUpdatesModeDirectApply,
			"apply_ctx_updates_mode_direct_unsafe", ctxRuntimeFlags.ModeDirectUnsafe,
			"apply_ctx_updates_resolution", ctxRuntimeFlags.ModeDirectResolution,
		)
		if (ctxRuntimeFlags.ApplyEffective || ctxUpdatesModeDirectApply) && mode == ModeDirect.String() {
			note := "ModeDirect keys are augmented from ctx updates during witness diagnostics"
			if !ctxUpdatesModeDirectApply {
				note = "ModeDirect ctx-update augmentation disabled by env"
			}
			log.Warn(
				"witness ctx update apply requested on key-only updates",
				"prefix", logPrefix,
				"updates_mode", mode,
				"note", note,
			)
		}
	}
	if (ctxRuntimeFlags.ApplyEffective || ctxUpdatesModeDirectApply) && erigonBadRootDebug {
		log.Warn(
			"witness ctx update application summary",
			"prefix", logPrefix,
			"seen", ctxUpdatesSeen,
			"would_apply", ctxUpdatesWouldApply,
			"applied", ctxUpdatesApplied,
			"delete_seen", ctxUpdatesDeleteSeen,
			"skipped_no_input", ctxUpdatesSkippedNoInput,
			"synthetic_delete_skipped", ctxUpdatesSyntheticDeleteSkipped,
			"mode_direct", ctxUpdatesModeDirect,
			"mode_direct_apply_enabled", ctxUpdatesModeDirectApply,
			"mode_direct_unsafe", ctxRuntimeFlags.ModeDirectUnsafe,
			"apply_ctx_updates", ctxRuntimeFlags.ApplyEffective,
			"apply_ctx_updates_resolution", ctxRuntimeFlags.ModeDirectResolution,
			"note", "witness extraction applies update payloads in-memory to grid cells only",
		)
	}

	// Folding everything up to the root
	for hph.activeRows > 0 {
		if err := hph.fold(); err != nil {
			return nil, nil, fmt.Errorf("final fold: %w", err)
		}
	}

	rootHash, err = hph.RootHash()
	if err != nil {
		return nil, nil, fmt.Errorf("root hash evaluation failed: %w", err)
	}
	if hph.trace {
		fmt.Printf("root hash %x updates %d\n", rootHash, updatesCount)
	}

	// merge all individual tries
	mergeRoots := make([]common.Hash, 0, len(tries))
	mergeFirstMatchExpected := -1
	mergeFirstMatchComputed := -1
	mergeFirstDivergeExpected := -1
	mergeFirstDivergeComputed := -1
	sawMatchExpected := false
	sawMatchComputed := false

	// Capture per-try roots and key metadata so merge failures can be mapped
	// back to the exact key/update pair that produced each partial trie.
	mergeTrieRootsByIdx := make([]common.Hash, 0)
	mergeTrieRootToIdx := make(map[common.Hash][]int)
	describeMergeTrieIdx := func(idx int) string {
		if idx < 0 || idx >= len(tries) {
			return fmt.Sprintf("idx=%d(out_of_range)", idx)
		}
		plain := plainKeysByTrie[idx]
		hashed := hashedKeysByTrie[idx]
		keyType := "storage"
		if len(plain) == length.Addr {
			keyType = "account"
		}
		const maxPreviewBytes = 20
		preview := func(key []byte) string {
			if len(key) == 0 {
				return "0x"
			}
			if len(key) <= maxPreviewBytes {
				return fmt.Sprintf("0x%x", key)
			}
			return fmt.Sprintf("0x%x...(+%d bytes)", key[:maxPreviewBytes], len(key)-maxPreviewBytes)
		}
		root := common.Hash{}
		if idx < len(mergeTrieRootsByIdx) {
			root = mergeTrieRootsByIdx[idx]
		}
		ctx := ""
		in := ""
		if idx < len(ctxUpdateSummaries) {
			ctx = ctxUpdateSummaries[idx]
		}
		if idx < len(inputUpdateSummaries) {
			in = inputUpdateSummaries[idx]
		}
		return fmt.Sprintf(
			"idx=%d type=%s root=%x plain=%s hashed=%s ctx=%s input=%s",
			idx,
			keyType,
			root,
			preview(plain),
			preview(hashed),
			ctx,
			in,
		)
	}
	parseMergeRoot := func(errMsg, field string) (common.Hash, bool) {
		needle := field + "="
		pos := strings.Index(errMsg, needle)
		if pos < 0 {
			return common.Hash{}, false
		}
		start := pos + len(needle)
		end := start + 64
		if start < 0 || end > len(errMsg) {
			return common.Hash{}, false
		}
		decoded, decErr := hex.DecodeString(errMsg[start:end])
		if decErr != nil {
			return common.Hash{}, false
		}
		return common.BytesToHash(decoded), true
	}

	if len(tries) > 0 {
		if erigonBadRootDebug {
			mergeTrieRootsByIdx = make([]common.Hash, len(tries))
			for i := range tries {
				root := common.BytesToHash(tries[i].Root())
				mergeTrieRootsByIdx[i] = root
				mergeTrieRootToIdx[root] = append(mergeTrieRootToIdx[root], i)
			}
		}

		// Preserve canonical merge behavior for witness output.
		witnessTrie, err = trie.MergeTries(tries)
		if err != nil {
			if erigonBadRootDebug {
				errMsg := err.Error()
				root1, hasRoot1 := parseMergeRoot(errMsg, "root1")
				root2, hasRoot2 := parseMergeRoot(errMsg, "root2")
				rootSamplesLimit := 8
				rootSamples := func(root common.Hash) []string {
					idxs := mergeTrieRootToIdx[root]
					if len(idxs) == 0 {
						return nil
					}
					limit := len(idxs)
					if limit > rootSamplesLimit {
						limit = rootSamplesLimit
					}
					samples := make([]string, 0, limit)
					for i := 0; i < limit; i++ {
						samples = append(samples, describeMergeTrieIdx(idxs[i]))
					}
					return samples
				}
				log.Warn(
					"witness merge conflict detail",
					"prefix", logPrefix,
					"tries", len(tries),
					"unique_roots", len(mergeTrieRootToIdx),
					"root1_present", hasRoot1,
					"root1", root1,
					"root1_match_count", len(mergeTrieRootToIdx[root1]),
					"root1_samples", rootSamples(root1),
					"root2_present", hasRoot2,
					"root2", root2,
					"root2_match_count", len(mergeTrieRootToIdx[root2]),
					"root2_samples", rootSamples(root2),
					"merge_err", errMsg,
				)
			}
			return nil, nil, fmt.Errorf("merge tries: %w", err)
		}

		// Keep step-by-step merge diagnostics separate from the canonical output.
		if erigonBadRootDebug {
			diagTrie := tries[0]
			mergedRoot := common.BytesToHash(diagTrie.Root())
			mergeRoots = append(mergeRoots, mergedRoot)
			if bytes.Equal(mergedRoot[:], expectedRootHash) {
				mergeFirstMatchExpected = 0
				sawMatchExpected = true
			}
			if bytes.Equal(mergedRoot[:], rootHash) {
				mergeFirstMatchComputed = 0
				sawMatchComputed = true
			}
			for i := 1; i < len(tries); i++ {
				diagTrie, err = trie.MergeTries([]*trie.Trie{diagTrie, tries[i]})
				if err != nil {
					return nil, nil, fmt.Errorf("merge tries diag idx=%d: %w", i, err)
				}
				mergedRoot = common.BytesToHash(diagTrie.Root())
				mergeRoots = append(mergeRoots, mergedRoot)
				matchExpected := bytes.Equal(mergedRoot[:], expectedRootHash)
				matchComputed := bytes.Equal(mergedRoot[:], rootHash)
				if matchExpected && mergeFirstMatchExpected < 0 {
					mergeFirstMatchExpected = i
				}
				if matchComputed && mergeFirstMatchComputed < 0 {
					mergeFirstMatchComputed = i
				}
				if sawMatchExpected && !matchExpected && mergeFirstDivergeExpected < 0 {
					mergeFirstDivergeExpected = i
				}
				if sawMatchComputed && !matchComputed && mergeFirstDivergeComputed < 0 {
					mergeFirstDivergeComputed = i
				}
				if matchExpected {
					sawMatchExpected = true
				}
				if matchComputed {
					sawMatchComputed = true
				}
			}
		}
	}

	witnessTrieRootHash := []byte(nil)
	if witnessTrie != nil {
		witnessTrieRootHash = witnessTrie.Root()
	}

	// fmt.Printf("mergedTrieRootHash = %x\n", witnessTrieRootHash)

	if !bytes.Equal(witnessTrieRootHash, expectedRootHash) {
		if erigonBadRootDebug {
			type rootCount struct {
				root  common.Hash
				count int
			}
			type rootDomainStats struct {
				account int
				storage int
			}
			type rootUpdateStats struct {
				deleteCount   int
				balanceCount  int
				nonceCount    int
				codeCount     int
				storageCount  int
				inputPresent  int
				inputMismatch int
			}

			triesMatchingExpected := 0
			triesMatchingComputed := 0
			triesMatchingWitness := 0
			accountKeys := 0
			storageKeys := 0
			duplicatePlain := 0
			duplicateHashed := 0
			inputUpdatesPresent := 0
			inputUpdatesNil := 0
			inputUpdatesMismatch := 0
			rootSampleLimit := 3

			formatKeyPreview := func(key []byte) string {
				const maxBytes = 20
				if len(key) == 0 {
					return "0x"
				}
				if len(key) <= maxBytes {
					return fmt.Sprintf("0x%x", key)
				}
				return fmt.Sprintf("0x%x...(+%d bytes)", key[:maxBytes], len(key)-maxBytes)
			}

			seenPlain := make(map[string]struct{}, len(plainKeysByTrie))
			seenHashed := make(map[string]struct{}, len(hashedKeysByTrie))
			rootHistogram := make(map[common.Hash]int, len(tries))
			rootDomainHistogram := make(map[common.Hash]rootDomainStats, len(tries))
			rootUpdateHistogram := make(map[common.Hash]rootUpdateStats, len(tries))
			rootKeySamples := make(map[common.Hash][]string, len(tries))

			for i, tr := range tries {
				trieRoot := common.BytesToHash(tr.Root())
				rootHistogram[trieRoot]++
				if bytes.Equal(trieRoot[:], expectedRootHash) {
					triesMatchingExpected++
				}
				if bytes.Equal(trieRoot[:], rootHash) {
					triesMatchingComputed++
				}
				if bytes.Equal(trieRoot[:], witnessTrieRootHash) {
					triesMatchingWitness++
				}

				keyType := "unknown"
				plainPreview := "0x"
				hashedPreview := "0x"
				ctxUpdateSummary := "<nil>"
				inputUpdateSummary := "<nil>"
				ctxUpdate := (*Update)(nil)
				inputUpdate := (*Update)(nil)
				if i < len(ctxUpdatesByTrie) {
					ctxUpdate = ctxUpdatesByTrie[i]
				}
				if i < len(inputUpdatesByTrie) {
					inputUpdate = inputUpdatesByTrie[i]
				}
				if i < len(ctxUpdateSummaries) {
					ctxUpdateSummary = ctxUpdateSummaries[i]
				}
				if i < len(inputUpdateSummaries) {
					inputUpdateSummary = inputUpdateSummaries[i]
				}
				if inputUpdate == nil {
					inputUpdatesNil++
				} else {
					inputUpdatesPresent++
				}
				inputMismatch := false
				if !witnessUpdateEquivalent(inputUpdate, ctxUpdate) {
					inputMismatch = true
					inputUpdatesMismatch++
				}
				updateStats := rootUpdateHistogram[trieRoot]
				if ctxUpdate != nil {
					if ctxUpdate.Flags&DeleteUpdate != 0 {
						updateStats.deleteCount++
					}
					if ctxUpdate.Flags&BalanceUpdate != 0 {
						updateStats.balanceCount++
					}
					if ctxUpdate.Flags&NonceUpdate != 0 {
						updateStats.nonceCount++
					}
					if ctxUpdate.Flags&CodeUpdate != 0 {
						updateStats.codeCount++
					}
					if ctxUpdate.Flags&StorageUpdate != 0 {
						updateStats.storageCount++
					}
				}
				if inputUpdate != nil {
					updateStats.inputPresent++
				}
				if inputMismatch {
					updateStats.inputMismatch++
				}
				rootUpdateHistogram[trieRoot] = updateStats
				if i < len(plainKeysByTrie) {
					pk := plainKeysByTrie[i]
					plainPreview = formatKeyPreview(pk)
					if len(pk) == hph.accountKeyLen {
						keyType = "account"
						accountKeys++
						stats := rootDomainHistogram[trieRoot]
						stats.account++
						rootDomainHistogram[trieRoot] = stats
					} else if len(pk) > hph.accountKeyLen {
						keyType = "storage"
						storageKeys++
						stats := rootDomainHistogram[trieRoot]
						stats.storage++
						rootDomainHistogram[trieRoot] = stats
					}
					if _, ok := seenPlain[string(pk)]; ok {
						duplicatePlain++
					} else {
						seenPlain[string(pk)] = struct{}{}
					}
				}
				if i < len(hashedKeysByTrie) {
					hk := hashedKeysByTrie[i]
					hashedPreview = formatKeyPreview(hk)
					if _, ok := seenHashed[string(hk)]; ok {
						duplicateHashed++
					} else {
						seenHashed[string(hk)] = struct{}{}
					}
				}
				if len(rootKeySamples[trieRoot]) < rootSampleLimit {
					rootKeySamples[trieRoot] = append(rootKeySamples[trieRoot], fmt.Sprintf(
						"idx=%d type=%s plain=%s hashed=%s ctx_update=%s input_update=%s input_mismatch=%t",
						i,
						keyType,
						plainPreview,
						hashedPreview,
						ctxUpdateSummary,
						inputUpdateSummary,
						inputMismatch,
					))
				}
			}

			roots := make([]rootCount, 0, len(rootHistogram))
			for root, count := range rootHistogram {
				roots = append(roots, rootCount{root: root, count: count})
			}
			sort.Slice(roots, func(i, j int) bool {
				if roots[i].count == roots[j].count {
					return bytes.Compare(roots[i].root[:], roots[j].root[:]) < 0
				}
				return roots[i].count > roots[j].count
			})
			topRootCount := 6
			if topRootCount > len(roots) {
				topRootCount = len(roots)
			}
			rootTop := make([]string, 0, topRootCount)
			rootTopSamples := make([]string, 0, topRootCount)
			for i := 0; i < topRootCount; i++ {
				stats := rootDomainHistogram[roots[i].root]
				updateStats := rootUpdateHistogram[roots[i].root]
				rootTop = append(rootTop, fmt.Sprintf(
					"%s:%d(acc=%d stor=%d upd={del=%d bal=%d nonce=%d code=%d stor=%d in=%d mismatch=%d})",
					roots[i].root.Hex(),
					roots[i].count,
					stats.account,
					stats.storage,
					updateStats.deleteCount,
					updateStats.balanceCount,
					updateStats.nonceCount,
					updateStats.codeCount,
					updateStats.storageCount,
					updateStats.inputPresent,
					updateStats.inputMismatch,
				))
				rootTopSamples = append(rootTopSamples, fmt.Sprintf(
					"%s samples=%v",
					roots[i].root.Hex(),
					rootKeySamples[roots[i].root],
				))
			}

			sampleMax := witnessDiagSampleMax()
			if sampleMax > len(tries) {
				sampleMax = len(tries)
			}
			keySamples := make([]string, 0, sampleMax)
			for i := 0; i < sampleMax; i++ {
				keyType := "unknown"
				plainKey := []byte(nil)
				hashedKey := []byte(nil)
				if i < len(plainKeysByTrie) {
					plainKey = plainKeysByTrie[i]
					if len(plainKey) == hph.accountKeyLen {
						keyType = "account"
					} else if len(plainKey) > hph.accountKeyLen {
						keyType = "storage"
					}
				}
				if i < len(hashedKeysByTrie) {
					hashedKey = hashedKeysByTrie[i]
				}
				trieRoot := common.BytesToHash(tries[i].Root())
				keySamples = append(keySamples, fmt.Sprintf(
					"idx=%d type=%s plain=%x hashed=%x trie_root=%s ctx_update=%s input_update=%s",
					i,
					keyType,
					plainKey,
					hashedKey,
					trieRoot.Hex(),
					ctxUpdateSummaries[i],
					inputUpdateSummaries[i],
				))
			}

			mergeIndexDetail := func(idx int) string {
				if idx < 0 || idx >= len(mergeRoots) {
					return ""
				}
				keyType := "unknown"
				plainPreview := "0x"
				hashedPreview := "0x"
				ctxUpdateSummary := "<nil>"
				inputUpdateSummary := "<nil>"
				if idx < len(plainKeysByTrie) {
					plainPreview = formatKeyPreview(plainKeysByTrie[idx])
					if len(plainKeysByTrie[idx]) == hph.accountKeyLen {
						keyType = "account"
					} else if len(plainKeysByTrie[idx]) > hph.accountKeyLen {
						keyType = "storage"
					}
				}
				if idx < len(hashedKeysByTrie) {
					hashedPreview = formatKeyPreview(hashedKeysByTrie[idx])
				}
				if idx < len(ctxUpdateSummaries) {
					ctxUpdateSummary = ctxUpdateSummaries[idx]
				}
				if idx < len(inputUpdateSummaries) {
					inputUpdateSummary = inputUpdateSummaries[idx]
				}
				return fmt.Sprintf(
					"idx=%d root=%s type=%s plain=%s hashed=%s ctx_update=%s input_update=%s",
					idx,
					mergeRoots[idx].Hex(),
					keyType,
					plainPreview,
					hashedPreview,
					ctxUpdateSummary,
					inputUpdateSummary,
				)
			}
			mergeSampleMax := witnessDiagSampleMax()
			if mergeSampleMax > len(mergeRoots) {
				mergeSampleMax = len(mergeRoots)
			}
			mergeSamples := make([]string, 0, mergeSampleMax)
			for i := 0; i < mergeSampleMax; i++ {
				mergeSamples = append(mergeSamples, mergeIndexDetail(i))
			}

			log.Warn(
				"witness root mismatch detail",
				"prefix", logPrefix,
				"ctx_update_apply_enabled", ctxRuntimeFlags.ApplyEffective,
				"ctx_update_mode_direct_apply_enabled", ctxUpdatesModeDirectApply,
				"ctx_update_mode_direct_requested", ctxRuntimeFlags.ModeDirectRequested,
				"ctx_update_mode_direct_disabled", ctxRuntimeFlags.ModeDirectDisabled,
				"ctx_update_mode_direct_unsafe", ctxRuntimeFlags.ModeDirectUnsafe,
				"ctx_update_resolution", ctxRuntimeFlags.ModeDirectResolution,
				"ctx_updates_applied", ctxUpdatesApplied > 0,
				"ctx_updates_would_apply", ctxUpdatesWouldApply > 0,
				"ctx_updates_applied_count", ctxUpdatesApplied,
				"ctx_updates_synthetic_delete_skipped", ctxUpdatesSyntheticDeleteSkipped,
				"witness_root", common.BytesToHash(witnessTrieRootHash),
				"expected_root", common.BytesToHash(expectedRootHash),
				"computed_root", common.BytesToHash(rootHash),
				"tries", len(tries),
				"updates", updatesCount,
				"tries_matching_expected", triesMatchingExpected,
				"tries_matching_computed", triesMatchingComputed,
				"tries_matching_witness", triesMatchingWitness,
				"account_keys", accountKeys,
				"storage_keys", storageKeys,
				"duplicate_plain_keys", duplicatePlain,
				"duplicate_hashed_keys", duplicateHashed,
				"input_updates_present", inputUpdatesPresent,
				"input_updates_nil", inputUpdatesNil,
				"input_updates_mismatch", inputUpdatesMismatch,
				"merge_steps", len(mergeRoots),
				"merge_first_match_expected_idx", mergeFirstMatchExpected,
				"merge_first_match_computed_idx", mergeFirstMatchComputed,
				"merge_first_diverge_expected_idx", mergeFirstDivergeExpected,
				"merge_first_diverge_computed_idx", mergeFirstDivergeComputed,
				"merge_first_diverge_expected_detail", mergeIndexDetail(mergeFirstDivergeExpected),
				"merge_first_diverge_computed_detail", mergeIndexDetail(mergeFirstDivergeComputed),
				"merge_samples", mergeSamples,
				"top_trie_roots", rootTop,
				"top_root_key_samples", rootTopSamples,
				"key_samples", keySamples,
			)
		}
		return nil, nil, fmt.Errorf(
			"root hash mismatch witnessTrieRootHash(%x)!=expectedRootHash(%x) computedRootHash(%x) tries=%d updates=%d",
			witnessTrieRootHash,
			expectedRootHash,
			rootHash,
			len(tries),
			updatesCount,
		)
	}

	return witnessTrie, rootHash, nil
}

func (hph *HexPatriciaHashed) Process(ctx context.Context, updates *Updates, logPrefix string) (rootHash []byte, err error) {
	var (
		m  runtime.MemStats
		ki uint64
		//hph.trace = true

		updatesCount = updates.Size()
		start        = time.Now()
		logEvery     = time.NewTicker(20 * time.Second)
		traceLimit   = uint64(0)
	)

	if collectCommitmentMetrics {
		hph.metrics.Reset()
		hph.metrics.updates.Store(updatesCount)
		defer func() {
			hph.metrics.TotalProcessingTimeInc(start)
			hph.metrics.WriteToCSV()
		}()
	}

	defer func() { logEvery.Stop() }()

	if erigonCommitmentTraceKeys {
		traceLimit = uint64(erigonCommitmentTraceKeysMax)
		if traceLimit == 0 {
			traceLimit = 200
		}
		log.Warn("Commitment trace keys enabled", "prefix", logPrefix, "updates", updatesCount, "max", traceLimit)
	}

	err = updates.HashSort(ctx, func(hashedKey, plainKey []byte, stateUpdate *Update) error {
		select {
		case <-logEvery.C:
			dbg.ReadMemStats(&m)
			log.Info(fmt.Sprintf("[%s][agg] computing trie", logPrefix),
				"progress", fmt.Sprintf("%s/%s", common.PrettyCounter(ki), common.PrettyCounter(updatesCount)),
				"alloc", common.ByteCount(m.Alloc), "sys", common.ByteCount(m.Sys))

		default:
		}
		if traceLimit > 0 && ki < traceLimit {
			addr := "<short>"
			if len(plainKey) >= 20 {
				addr = fmt.Sprintf("0x%x", plainKey[:20])
			}
			slot := ""
			if len(plainKey) >= 52 {
				slot = fmt.Sprintf("0x%x", plainKey[20:])
			}
			flags := "<nil>"
			if stateUpdate != nil {
				flags = stateUpdate.Flags.String()
			}
			log.Warn("Commitment touched key",
				"prefix", logPrefix,
				"idx", ki,
				"plain_len", len(plainKey),
				"addr", addr,
				"slot", slot,
				"plain", fmt.Sprintf("0x%x", plainKey),
				"hashed", fmt.Sprintf("0x%x", hashedKey),
				"flags", flags,
			)
		}
		if hph.trace {
			fmt.Printf("\n%d/%d) plainKey [%x] hashedKey [%x] currentKey [%x]\n", ki+1, updatesCount, plainKey, hashedKey, hph.currentKey[:hph.currentKeyLen])
		}
		if err := hph.followAndUpdate(hashedKey, plainKey, stateUpdate); err != nil {
			return fmt.Errorf("followAndUpdate: %w", err)
		}
		ki++
		return nil
	})
	if err != nil {
		return nil, fmt.Errorf("hash sort failed: %w", err)
	}

	// Folding everything up to the root
	for hph.activeRows > 0 {
		foldDone := hph.metrics.StartFolding(nil)
		if err = hph.fold(); err != nil {
			return nil, fmt.Errorf("final fold: %w", err)
		}
		foldDone()
	}

	rootHash, err = hph.RootHash()
	if err != nil {
		return nil, fmt.Errorf("root hash evaluation failed: %w", err)
	}
	if hph.trace {
		fmt.Printf("root hash %x updates %d\n", rootHash, updatesCount)
	}

	hph.metrics.CollectFileDepthStats(hph.hadToLoadL)
	if dbg.KVReadLevelledMetrics {
		log.Debug("commitment finished, counters updated (no reset)",
			//"hadToLoad", common.PrettyCounter(hadToLoad.Load()), "skippedLoad", common.PrettyCounter(skippedLoad.Load()),
			//"hadToReset", common.PrettyCounter(hadToReset.Load()),
			"skip ratio", fmt.Sprintf("%.1f%%", 100*(float64(skippedLoad.Load())/float64(hadToLoad.Load()+skippedLoad.Load()))),
			"reset ratio", fmt.Sprintf("%.1f%%", 100*(float64(hadToReset.Load())/float64(hadToLoad.Load()))),
			"keys", common.PrettyCounter(ki), "spent", time.Since(start),
		)
		ends := make([]uint64, 0, len(hph.hadToLoadL))
		for k := range hph.hadToLoadL {
			ends = append(ends, k)
		}
		sort.Slice(ends, func(i, j int) bool { return ends[i] > ends[j] })
		var Li int
		for _, k := range ends {
			v := hph.hadToLoadL[k]
			accs := fmt.Sprintf("load=%s skip=%s (%.1f%%) reset %.1f%%", common.PrettyCounter(v.accLoaded), common.PrettyCounter(v.accSkipped), 100*(float64(v.accSkipped)/float64(v.accLoaded+v.accSkipped)), 100*(float64(v.accReset)/float64(v.accReset+v.accSkipped)))
			stors := fmt.Sprintf("load=%s skip=%s (%.1f%%) reset %.1f%%", common.PrettyCounter(v.storLoaded), common.PrettyCounter(v.storSkipped), 100*(float64(v.storSkipped)/float64(v.storLoaded+v.storSkipped)), 100*(float64(v.storReset)/float64(v.storReset+v.storSkipped)))
			if k == 0 {
				log.Debug("branchData memoization, new branches", "endStep", k, "accounts", accs, "storages", stors)
			} else {
				log.Debug("branchData memoization", "L", Li, "endStep", k, "accounts", accs, "storages", stors)
				Li++

				mxTrieStateLevelledSkipRatesAccount[min(Li, 5)].Add(float64(v.accSkipped))
				mxTrieStateLevelledSkipRatesStorage[min(Li, 5)].Add(float64(v.storSkipped))
				mxTrieStateLevelledLoadRatesAccount[min(Li, 5)].Add(float64(v.accLoaded))
				mxTrieStateLevelledLoadRatesStorage[min(Li, 5)].Add(float64(v.storLoaded))
			}
		}
	}

	return rootHash, nil
}

func (hph *HexPatriciaHashed) SetTrace(trace bool) { hph.trace = trace }

func (hph *HexPatriciaHashed) Variant() TrieVariant { return VariantHexPatriciaTrie }

// Reset allows HexPatriciaHashed instance to be reused for the new commitment calculation
func (hph *HexPatriciaHashed) Reset() {
	hph.root.reset()
	hph.rootTouched = false
	hph.rootChecked = false
	hph.rootPresent = true
}

func (hph *HexPatriciaHashed) ResetContext(ctx PatriciaContext) {
	hph.ctx = ctx
}

type stateRootFlag int8

var (
	stateRootPresent stateRootFlag = 1
	stateRootChecked stateRootFlag = 2
	stateRootTouched stateRootFlag = 4
)

// represents state of the tree
type state struct {
	Root         []byte      // encoded root cell
	Depths       [128]int    // For each row, the depth of cells in that row
	TouchMap     [128]uint16 // For each row, bitmap of cells that were either present before modification, or modified or deleted
	AfterMap     [128]uint16 // For each row, bitmap of cells that were present after modification
	BranchBefore [128]bool   // For each row, whether there was a branch node in the database loaded in unfold
	RootChecked  bool        // Set to false if it is not known whether the root is empty, set to true if it is checked
	RootTouched  bool
	RootPresent  bool
}

func (s *state) Encode(buf []byte) ([]byte, error) {
	var rootFlags stateRootFlag
	if s.RootPresent {
		rootFlags |= stateRootPresent
	}
	if s.RootChecked {
		rootFlags |= stateRootChecked
	}
	if s.RootTouched {
		rootFlags |= stateRootTouched
	}

	ee := bytes.NewBuffer(buf)
	if err := binary.Write(ee, binary.BigEndian, int8(rootFlags)); err != nil {
		return nil, fmt.Errorf("encode rootFlags: %w", err)
	}
	if err := binary.Write(ee, binary.BigEndian, uint16(len(s.Root))); err != nil {
		return nil, fmt.Errorf("encode root len: %w", err)
	}
	if n, err := ee.Write(s.Root); err != nil || n != len(s.Root) {
		return nil, fmt.Errorf("encode root: %w", err)
	}
	d := make([]byte, len(s.Depths))
	for i := 0; i < len(s.Depths); i++ {
		d[i] = byte(s.Depths[i])
	}
	if n, err := ee.Write(d); err != nil || n != len(s.Depths) {
		return nil, fmt.Errorf("encode depths: %w", err)
	}
	if err := binary.Write(ee, binary.BigEndian, s.TouchMap); err != nil {
		return nil, fmt.Errorf("encode touchMap: %w", err)
	}
	if err := binary.Write(ee, binary.BigEndian, s.AfterMap); err != nil {
		return nil, fmt.Errorf("encode afterMap: %w", err)
	}

	var before1, before2 uint64
	for i := 0; i < 64; i++ {
		if s.BranchBefore[i] {
			before1 |= 1 << i
		}
	}
	for i, j := 64, 0; i < 128; i, j = i+1, j+1 {
		if s.BranchBefore[i] {
			before2 |= 1 << j
		}
	}
	if err := binary.Write(ee, binary.BigEndian, before1); err != nil {
		return nil, fmt.Errorf("encode branchBefore_1: %w", err)
	}
	if err := binary.Write(ee, binary.BigEndian, before2); err != nil {
		return nil, fmt.Errorf("encode branchBefore_2: %w", err)
	}
	return ee.Bytes(), nil
}

func (s *state) Decode(buf []byte) error {
	aux := bytes.NewBuffer(buf)
	var rootFlags stateRootFlag
	if err := binary.Read(aux, binary.BigEndian, &rootFlags); err != nil {
		return fmt.Errorf("rootFlags: %w", err)
	}

	if rootFlags&stateRootPresent != 0 {
		s.RootPresent = true
	}
	if rootFlags&stateRootTouched != 0 {
		s.RootTouched = true
	}
	if rootFlags&stateRootChecked != 0 {
		s.RootChecked = true
	}

	var rootSize uint16
	if err := binary.Read(aux, binary.BigEndian, &rootSize); err != nil {
		return fmt.Errorf("root size: %w", err)
	}
	s.Root = make([]byte, rootSize)
	if _, err := aux.Read(s.Root); err != nil {
		return fmt.Errorf("root: %w", err)
	}
	d := make([]byte, len(s.Depths))
	if err := binary.Read(aux, binary.BigEndian, &d); err != nil {
		return fmt.Errorf("depths: %w", err)
	}
	for i := 0; i < len(s.Depths); i++ {
		s.Depths[i] = int(d[i])
	}
	if err := binary.Read(aux, binary.BigEndian, &s.TouchMap); err != nil {
		return fmt.Errorf("touchMap: %w", err)
	}
	if err := binary.Read(aux, binary.BigEndian, &s.AfterMap); err != nil {
		return fmt.Errorf("afterMap: %w", err)
	}
	var branch1, branch2 uint64
	if err := binary.Read(aux, binary.BigEndian, &branch1); err != nil {
		return fmt.Errorf("branchBefore1: %w", err)
	}
	if err := binary.Read(aux, binary.BigEndian, &branch2); err != nil {
		return fmt.Errorf("branchBefore2: %w", err)
	}

	for i := 0; i < 64; i++ {
		if branch1&(1<<i) != 0 {
			s.BranchBefore[i] = true
		}
	}
	for i, j := 64, 0; i < 128; i, j = i+1, j+1 {
		if branch2&(1<<j) != 0 {
			s.BranchBefore[i] = true
		}
	}
	return nil
}

func (cell *cell) Encode() []byte {
	var pos = 1
	size := pos + 5 + cell.hashLen + cell.accountAddrLen + cell.storageAddrLen + cell.hashedExtLen + cell.extLen // max size
	buf := make([]byte, size)

	var flags uint8
	if cell.hashLen != 0 {
		flags |= cellFlagHash
		buf[pos] = byte(cell.hashLen)
		pos++
		copy(buf[pos:pos+cell.hashLen], cell.hash[:])
		pos += cell.hashLen
	}
	if cell.accountAddrLen != 0 {
		flags |= cellFlagAccount
		buf[pos] = byte(cell.accountAddrLen)
		pos++
		copy(buf[pos:pos+cell.accountAddrLen], cell.accountAddr[:])
		pos += cell.accountAddrLen
	}
	if cell.storageAddrLen != 0 {
		flags |= cellFlagStorage
		buf[pos] = byte(cell.storageAddrLen)
		pos++
		copy(buf[pos:pos+cell.storageAddrLen], cell.storageAddr[:])
		pos += cell.storageAddrLen
	}
	if cell.hashedExtLen != 0 {
		flags |= cellFlagDownHash
		buf[pos] = byte(cell.hashedExtLen)
		pos++
		copy(buf[pos:pos+cell.hashedExtLen], cell.hashedExtension[:cell.hashedExtLen])
		pos += cell.hashedExtLen
	}
	if cell.extLen != 0 {
		flags |= cellFlagExtension
		buf[pos] = byte(cell.extLen)
		pos++
		copy(buf[pos:pos+cell.extLen], cell.extension[:])
		pos += cell.extLen //nolint
	}
	if cell.Deleted() {
		flags |= cellFlagDelete
	}
	buf[0] = flags
	return buf
}

const (
	cellFlagHash = uint8(1 << iota)
	cellFlagAccount
	cellFlagStorage
	cellFlagDownHash
	cellFlagExtension
	cellFlagDelete
)

func (cell *cell) Decode(buf []byte) error {
	if len(buf) < 1 {
		return errors.New("invalid buffer size to contain cell (at least 1 byte expected)")
	}
	cell.reset()

	var pos int
	flags := buf[pos]
	pos++

	if flags&cellFlagHash != 0 {
		cell.hashLen = int(buf[pos])
		pos++
		copy(cell.hash[:], buf[pos:pos+cell.hashLen])
		pos += cell.hashLen
	}
	if flags&cellFlagAccount != 0 {
		cell.accountAddrLen = int(buf[pos])
		pos++
		copy(cell.accountAddr[:], buf[pos:pos+cell.accountAddrLen])
		pos += cell.accountAddrLen
	}
	if flags&cellFlagStorage != 0 {
		cell.storageAddrLen = int(buf[pos])
		pos++
		copy(cell.storageAddr[:], buf[pos:pos+cell.storageAddrLen])
		pos += cell.storageAddrLen
	}
	if flags&cellFlagDownHash != 0 {
		cell.hashedExtLen = int(buf[pos])
		pos++
		copy(cell.hashedExtension[:], buf[pos:pos+cell.hashedExtLen])
		pos += cell.hashedExtLen
	}
	if flags&cellFlagExtension != 0 {
		cell.extLen = int(buf[pos])
		pos++
		copy(cell.extension[:], buf[pos:pos+cell.extLen])
		pos += cell.extLen //nolint
	}
	if flags&cellFlagDelete != 0 {
		log.Warn("deleted cell should not be encoded", "cell", cell.String())
		cell.Update.Flags = DeleteUpdate
	}
	return nil
}

// Encode current state of hph into bytes
func (hph *HexPatriciaHashed) EncodeCurrentState(buf []byte) ([]byte, error) {
	s := state{
		RootChecked: hph.rootChecked,
		RootTouched: hph.rootTouched,
		RootPresent: hph.rootPresent,
	}
	if hph.currentKeyLen > 0 {
		panic("currentKeyLen > 0")
	}

	s.Root = hph.root.Encode()
	copy(s.Depths[:], hph.depths[:])
	copy(s.BranchBefore[:], hph.branchBefore[:])
	copy(s.TouchMap[:], hph.touchMap[:])
	copy(s.AfterMap[:], hph.afterMap[:])

	return s.Encode(buf)
}

// buf expected to be encoded hph state. Decode state and set up hph to that state.
func (hph *HexPatriciaHashed) SetState(buf []byte) error {
	hph.Reset()

	if buf == nil {
		// reset state to 'empty'
		hph.currentKeyLen = 0
		hph.rootChecked = false
		hph.rootTouched = false
		hph.rootPresent = false
		hph.activeRows = 0

		for i := 0; i < len(hph.depths); i++ {
			hph.depths[i] = 0
			hph.branchBefore[i] = false
			hph.touchMap[i] = 0
			hph.afterMap[i] = 0
		}
		return nil
	}
	if hph.activeRows != 0 {
		return errors.New("target trie has active rows, could not reset state before fold")
	}

	var s state
	if err := s.Decode(buf); err != nil {
		return err
	}

	if err := hph.root.Decode(s.Root); err != nil {
		return err
	}
	hph.rootChecked = s.RootChecked
	hph.rootTouched = s.RootTouched
	hph.rootPresent = s.RootPresent

	copy(hph.depths[:], s.Depths[:])
	copy(hph.branchBefore[:], s.BranchBefore[:])
	copy(hph.touchMap[:], s.TouchMap[:])
	copy(hph.afterMap[:], s.AfterMap[:])

	if hph.root.accountAddrLen > 0 {
		if hph.ctx == nil {
			panic("nil ctx")
		}

		update, err := hph.ctx.Account(hph.root.accountAddr[:hph.root.accountAddrLen])
		if err != nil {
			return err
		}
		hph.root.setFromUpdate(update)
	}
	if hph.root.storageAddrLen > 0 {
		if hph.ctx == nil {
			panic("nil ctx")
		}
		update, err := hph.ctx.Storage(hph.root.storageAddr[:hph.root.storageAddrLen])
		if err != nil {
			return err
		}
		hph.root.setFromUpdate(update)
		//hph.root.deriveHashedKeys(0, hph.keccak, hph.accountKeyLen)
	}

	return nil
}

func HexTrieExtractStateRoot(enc []byte) ([]byte, error) {
	if len(enc) < 18 { // 8*2+2
		return nil, fmt.Errorf("invalid state length %x (min %d expected)", len(enc), 18)
	}

	//txn := binary.BigEndian.Uint64(enc)
	//bn := binary.BigEndian.Uint64(enc[8:])
	sl := binary.BigEndian.Uint16(enc[16:18])
	var s state
	if err := s.Decode(enc[18 : 18+sl]); err != nil {
		return nil, err
	}
	root := new(cell)
	if err := root.Decode(s.Root); err != nil {
		return nil, err
	}
	return root.hash[:], nil
}

func HexTrieStateToShortString(enc []byte) (string, error) {
	if len(enc) < 18 {
		return "", fmt.Errorf("invalid state length %x (min %d expected)", len(enc), 18)
	}
	txn := binary.BigEndian.Uint64(enc)
	bn := binary.BigEndian.Uint64(enc[8:])
	sl := binary.BigEndian.Uint16(enc[16:18])

	var s state
	if err := s.Decode(enc[18 : 18+sl]); err != nil {
		return "", err
	}
	root := new(cell)
	if err := root.Decode(s.Root); err != nil {
		return "", err
	}
	return fmt.Sprintf("block: %d txn: %d rootHash: %x", bn, txn, root.hash[:]), nil
}

func HexTrieStateToString(enc []byte) (string, error) {
	if len(enc) < 18 {
		return "", fmt.Errorf("invalid state length %x (min %d expected)", len(enc), 18)
	}
	txn := binary.BigEndian.Uint64(enc)
	bn := binary.BigEndian.Uint64(enc[8:])
	sl := binary.BigEndian.Uint16(enc[16:18])

	var s state
	sb := new(strings.Builder)
	if err := s.Decode(enc[18 : 18+sl]); err != nil {
		return "", err
	}
	fmt.Fprintf(sb, "block: %d txn: %d\n", bn, txn)
	// fmt.Fprintf(sb, " touchMaps: %v\n", s.TouchMap)
	// fmt.Fprintf(sb, " afterMaps: %v\n", s.AfterMap)
	// fmt.Fprintf(sb, " depths: %v\n", s.Depths)

	printAfterMap := func(sb *strings.Builder, name string, list []uint16, depths []int, existedBefore []bool) {
		fmt.Fprintf(sb, "\t::%s::\n\n", name)
		lastNonZero := 0
		for i := len(list) - 1; i >= 0; i-- {
			if list[i] != 0 {
				lastNonZero = i
				break
			}
		}
		for i, v := range list {
			newBranchSuf := ""
			if !existedBefore[i] {
				newBranchSuf = " NEW"
			}

			fmt.Fprintf(sb, " d=%3d %016b%s\n", depths[i], v, newBranchSuf)
			if i == lastNonZero {
				break
			}
		}
	}
	fmt.Fprintf(sb, " rootNode: %x [touched=%t, present=%t, checked=%t]\n", s.Root, s.RootTouched, s.RootPresent, s.RootChecked)

	root := new(cell)
	if err := root.Decode(s.Root); err != nil {
		return "", err
	}

	fmt.Fprintf(sb, "RootHash: %x\n", root.hash)
	printAfterMap(sb, "afterMap", s.AfterMap[:], s.Depths[:], s.BranchBefore[:])

	return sb.String(), nil
}

func (hph *HexPatriciaHashed) Grid() [128][16]cell {
	return hph.grid
}

func (hph *HexPatriciaHashed) PrintAccountsInGrid() {
	fmt.Printf("SEARCHING FOR ACCOUNTS IN GRID\n")
	for row := 0; row < 128; row++ {
		for col := 0; col < 16; col++ {
			c := hph.grid[row][col]
			if c.accountAddr[19] != 0 && c.accountAddr[0] != 0 {
				fmt.Printf("FOUND account %x in position (%d,%d)\n", c.accountAddr, row, col)
			}
		}
	}
}
