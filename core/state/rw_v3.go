// Copyright 2024 The Erigon Authors
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

package state

import (
	"bytes"
	"context"
	"encoding/binary"
	"fmt"
	"os"
	"strings"
	"sync"

	"github.com/holiman/uint256"

	"github.com/erigontech/erigon-lib/common"
	"github.com/erigontech/erigon-lib/common/dbg"
	"github.com/erigontech/erigon-lib/common/length"
	"github.com/erigontech/erigon-lib/log/v3"
	"github.com/erigontech/erigon-lib/metrics"
	"github.com/erigontech/erigon/db/kv"
	"github.com/erigontech/erigon/db/rawdb"
	dbstate "github.com/erigontech/erigon/db/state"
	"github.com/erigontech/erigon/eth/ethconfig"
	etrie "github.com/erigontech/erigon/execution/trie"
	"github.com/erigontech/erigon/execution/types"
	"github.com/erigontech/erigon/execution/types/accounts"
	"github.com/erigontech/erigon/turbo/shards"
)

var execTxsDone = metrics.NewCounter(`exec_txs_done`)
var mdbxMigrateReceiptsDebug = receiptDebugEnabled()
var mdbxMigrateReceiptsDebugBlockRaw, mdbxMigrateReceiptsDebugBlock = receiptDebugBlockEnv()
var mdbxMigrateReceiptsDebugBlockSet = mdbxMigrateReceiptsDebugBlockRaw != ""
var mdbxMigrateDebugWriteSet = os.Getenv("ERIGON_MDBX_MIGRATE_DEBUG_WRITESET") != "" || os.Getenv("MDBX_MIGRATE_DEBUG_WRITESET") != ""
var mdbxMigrateKeyTrace = dbg.EnvBool("ERIGON_MDBX_MIGRATE_KEYTRACE", false) || dbg.EnvBool("ERIGON_BAD_ROOT_DEBUG", false)
var mdbxMigrateAccountTrace = dbg.EnvBool("ERIGON_MDBX_MIGRATE_ACCOUNTTRACE", false) || dbg.EnvBool("ERIGON_BAD_ROOT_DEBUG", false)
var mdbxMigrateStorageTrace = dbg.EnvBool("ERIGON_MDBX_MIGRATE_STORAGETRACE", false)
var mdbxMigrateStorageTraceBlockRaw = dbg.EnvString("ERIGON_MDBX_MIGRATE_STORAGETRACE_BLOCK", "")
var mdbxMigrateStorageTraceBlock = dbg.EnvUint("ERIGON_MDBX_MIGRATE_STORAGETRACE_BLOCK", 0)
var mdbxMigrateStorageTraceBlockSet = mdbxMigrateStorageTraceBlockRaw != ""
var mdbxMigrateStorageTraceTxIndexRaw = dbg.EnvString("ERIGON_MDBX_MIGRATE_STORAGETRACE_TX_INDEX", "")
var mdbxMigrateStorageTraceTxIndex = dbg.EnvInt("ERIGON_MDBX_MIGRATE_STORAGETRACE_TX_INDEX", 0)
var mdbxMigrateStorageTraceTxIndexSet = mdbxMigrateStorageTraceTxIndexRaw != ""
var mdbxMigrateFixEmptyRoot = dbg.EnvBool("ERIGON_MDBX_MIGRATE_FIX_EMPTY_ROOT", false) || dbg.EnvBool("ERIGON_BAD_ROOT_DEBUG", false)
var keepEmptyAccounts = dbg.EnvBool("ERIGON_MDBX_MIGRATE_KEEP_EMPTY_ACCOUNTS", false)
var keepEmptyAccountsList = loadKeepEmptyAccountsList()

// Preserve known Arbitrum marker accounts by default during both migration and runtime execution.
// This can be disabled explicitly via:
//
//	ERIGON_MDBX_MIGRATE_KEEP_EMPTY_ACCOUNTS_DEFAULT_ADDRS=false
//
// or:
//
//	ERIGON_KEEP_EMPTY_ACCOUNTS_DEFAULT_ADDRS=false
var keepEmptyAccountsDefaultAddrs = dbg.EnvBool(
	"ERIGON_MDBX_MIGRATE_KEEP_EMPTY_ACCOUNTS_DEFAULT_ADDRS",
	dbg.EnvBool("ERIGON_KEEP_EMPTY_ACCOUNTS_DEFAULT_ADDRS", true),
)
var mdbxMigrateSweepTombstones = dbg.EnvBool("ERIGON_MDBX_MIGRATE_SWEEP_TOMBSTONES", false)
var mdbxMigrateSweepTombstonesBlock = dbg.EnvUint("ERIGON_MDBX_MIGRATE_SWEEP_TOMBSTONES_BLOCK", 0)
var mdbxMigrateApplyTrace = dbg.EnvBool("ERIGON_MDBX_MIGRATE_APPLYTRACE", false) || dbg.EnvBool("ERIGON_BAD_ROOT_DEBUG", false)
var mdbxMigrateApplyTraceMinBlock = dbg.EnvUint("ERIGON_PATH_PROBE_MIN_BLOCK", 33)
var mdbxMigrateApplyTraceTxIndex = dbg.EnvInt("ERIGON_PATH_PROBE_TX_INDEX", -1)
var mdbxMigrateApplyTraceAccountProbe = common.HexToAddress(dbg.EnvString("ERIGON_ACCOUNT_PROBE_ADDR", "0xA4b000000000000000000073657175656e636572"))
var mdbxMigrateApplyTraceStorageProbeAddr = common.HexToAddress(dbg.EnvString("ERIGON_PATH_PROBE_ADDR", "0xA4b05FffffFffFFFFfFFfffFfffFFfffFfFfFFFf"))
var mdbxMigrateApplyTraceStorageProbeSlot = common.HexToHash(dbg.EnvString("ERIGON_PATH_PROBE_SLOT", "0x3c79da47f96b0f39664f73c0a1f350580be90742947dddfa21ba64d578dfe623"))
var repairTombstonesOnce sync.Once

func receiptDebugEnabled() bool {
	return dbg.EnvBool("ERIGON_MDBX_MIGRATE_DEBUG", false) ||
		dbg.EnvBool("MDBX_MIGRATE_DEBUG", false) ||
		dbg.EnvBool("ERIGON_BAD_ROOT_DEBUG", false)
}

func receiptDebugBlockEnv() (string, uint64) {
	if raw := dbg.EnvString("ERIGON_MDBX_MIGRATE_DEBUG_BLOCK", ""); raw != "" {
		return raw, dbg.EnvUint("ERIGON_MDBX_MIGRATE_DEBUG_BLOCK", 0)
	}
	raw := dbg.EnvString("MDBX_MIGRATE_DEBUG_BLOCK", "")
	return raw, dbg.EnvUint("MDBX_MIGRATE_DEBUG_BLOCK", 0)
}

// Keep-empty accounts list is driven by explicit env config to match Nitro state.
// Some chains have known empty accounts that must be preserved to match the source root.
var arbosKeepEmptyAccounts = map[common.Address]struct{}{
	common.HexToAddress("0x502ffdafd660aedf4ea7db3d758999e154102a6c"): {},
	common.HexToAddress("0xe5052b97618c9ff3025bdece4d9a5e9e229b64b3"): {},
	common.HexToAddress("0x8807ed26dbaae86b62d0b663d754ce66f9d373b8"): {},
	common.HexToAddress("0x571fb9e1003ebe9c99ad3c1a60797e19cb577e93"): {},
	common.HexToAddress("0xA4b000000000000000000073657175656e636572"): {},
	common.HexToAddress("0xA4b05FffffFffFFFFfFFfffFfffFFfffFfFfFFFf"): {},
}

func loadKeepEmptyAccountsList() map[common.Address]struct{} {
	raw := os.Getenv("ERIGON_MDBX_MIGRATE_KEEP_EMPTY_ACCOUNTS_ADDRS")
	if raw == "" {
		raw = os.Getenv("ERIGON_MDBX_MIGRATE_FORCE_EMPTY_ACCOUNTS")
	}
	if raw == "" {
		return nil
	}
	parts := strings.Split(raw, ",")
	out := make(map[common.Address]struct{}, len(parts))
	for _, part := range parts {
		part = strings.TrimSpace(part)
		if part == "" || !common.IsHexAddress(part) {
			continue
		}
		out[common.HexToAddress(part)] = struct{}{}
	}
	if len(out) == 0 {
		return nil
	}
	return out
}

func shouldKeepEmptyAccount(addr common.Address) bool {
	if keepEmptyAccountsDefaultAddrs {
		if _, ok := arbosKeepEmptyAccounts[addr]; ok {
			return true
		}
	}
	return shouldKeepEmptyAccountExplicitOnly(addr)
}

// Runtime execution must follow canonical empty-account deletion rules unless the
// operator explicitly forces preservation. The default migration-only address set
// is intentionally excluded here: some ArbOS marker accounts exist at older
// blocks but are later deleted on canonical Nitro chains.
func shouldKeepEmptyAccountExplicitOnly(addr common.Address) bool {
	if !keepEmptyAccounts && len(keepEmptyAccountsList) == 0 {
		return false
	}
	if len(keepEmptyAccountsList) == 0 {
		return true
	}
	_, ok := keepEmptyAccountsList[addr]
	return ok
}

func shouldKeepEmptyAccountBytes(key []byte) bool {
	if len(key) != length.Addr {
		if len(keepEmptyAccountsList) == 0 {
			return keepEmptyAccounts
		}
		return false
	}
	return shouldKeepEmptyAccount(common.BytesToAddress(key))
}

func shouldMdbxMigrateApplyTrace(txTask *TxTask) bool {
	if !mdbxMigrateApplyTrace || txTask == nil || txTask.TxIndex < 0 {
		return false
	}
	if txTask.BlockNum < mdbxMigrateApplyTraceMinBlock {
		return false
	}
	if mdbxMigrateApplyTraceTxIndex >= 0 && txTask.TxIndex != mdbxMigrateApplyTraceTxIndex {
		return false
	}
	return true
}

func shouldTraceApplyAccount(addr common.Address) bool {
	if isBadRootAccount(addr) {
		return true
	}
	if !mdbxMigrateApplyTrace {
		return false
	}
	return addr == mdbxMigrateApplyTraceAccountProbe ||
		addr == mdbxMigrateApplyTraceStorageProbeAddr ||
		addr == common.HexToAddress("0x28c18bc63069e3581870904f32Dd34D9e3332cce")
}

func readApplyTraceAccount(domains *dbstate.SharedDomains, tx kv.TemporalTx, addr common.Address, out *accounts.Account) (exists bool, enc []byte, step kv.Step, err error) {
	enc, step, err = domains.GetLatest(kv.AccountsDomain, tx, addr.Bytes())
	if err != nil {
		return false, nil, 0, err
	}
	if len(enc) == 0 || isAccountTombstone(enc) {
		return false, enc, step, nil
	}
	if out != nil {
		out.Reset()
		if err := accounts.DeserialiseV3(out, enc); err != nil {
			return false, enc, step, err
		}
	}
	return true, enc, step, nil
}

func spuriousDragonEnabledForTask(txTask *TxTask) bool {
	if txTask != nil && txTask.Rules != nil {
		return txTask.Rules.IsSpuriousDragon
	}
	if txTask != nil && txTask.Config != nil && txTask.Config.IsArbitrum() {
		// Arbitrum/Nitro applies Spurious Dragon semantics from genesis.
		// Keep EIP-161 empty-account deletion enabled even if Rules is not propagated.
		return true
	}
	return false
}

func hasPendingStorageWritesForAddr(txTask *TxTask, addrBytes []byte) bool {
	if txTask == nil || txTask.WriteLists == nil || len(addrBytes) == 0 {
		return false
	}
	list, ok := txTask.WriteLists[kv.StorageDomain.String()]
	if !ok || list == nil || len(list.Keys) == 0 {
		return false
	}
	for _, key := range list.Keys {
		// Storage keys are raw bytes; treat any entry (including deletes) as a pending write.
		if bytes.HasPrefix([]byte(key), addrBytes) {
			return true
		}
	}
	return false
}

func computeStorageRootFromLatest(domains *dbstate.SharedDomains, tx kv.Tx, addr common.Address) (common.Hash, int, error) {
	if domains == nil || tx == nil {
		return common.Hash{}, 0, fmt.Errorf("computeStorageRootFromLatest: missing domains or tx")
	}
	prefix := addr.Bytes()
	tr := etrie.New(common.Hash{})
	items := 0
	err := domains.IteratePrefix(kv.StorageDomain, prefix, tx, func(k []byte, v []byte, step kv.Step) (bool, error) {
		if len(v) == 0 {
			return true, nil
		}
		if len(k) < length.Addr {
			return false, fmt.Errorf("short storage key: %d bytes", len(k))
		}
		slot := k[length.Addr:]
		slotHash, _ := common.HashData(slot)
		tr.Update(slotHash.Bytes(), common.Copy(v))
		items++
		return true, nil
	})
	if err != nil {
		return common.Hash{}, items, err
	}
	return tr.Hash(), items, nil
}

type cursorTx interface {
	Cursor(bucket string) (kv.Cursor, error)
}

func hasStorageForAddr(tx cursorTx, addrBytes []byte) (bool, error) {
	if tx == nil || len(addrBytes) == 0 {
		return false, nil
	}
	c, err := tx.Cursor(kv.StorageDomain.String())
	if err != nil {
		return false, err
	}
	defer c.Close()

	k, _, err := c.Seek(addrBytes)
	if err != nil {
		return false, err
	}
	return len(k) > 0 && bytes.HasPrefix(k, addrBytes), nil
}

const (
	accountEncodingMinLen = 4
	accountValsPrefixLen  = 8
	accountValsMinLen     = accountValsPrefixLen + accountEncodingMinLen
)

var emptyAccountEncoding = []byte{0, 0, 0, 0}

func isAccountTombstone(val []byte) bool {
	if len(val) == 0 {
		return false
	}
	// Account encodings use 4+ bytes; 0xff indicates a tombstone marker.
	if val[0] == 0xff {
		return true
	}
	return len(val) < accountEncodingMinLen
}

func isAccountValsTombstone(val []byte) bool {
	if len(val) == 0 {
		return false
	}
	return len(val) < accountValsMinLen
}

func isEmptyAccountEncoding(val []byte) bool {
	return len(val) == accountEncodingMinLen && bytes.Equal(val, emptyAccountEncoding)
}

var mdbxMigrateTraceKeys = [][]byte{
	common.FromHex("0xa4b05fffffffffffffffffffffffffffffffffff3c79da47f96b0f39664f73c0a1f350580be90742947dddfa21ba64d578dfe600"),
	common.FromHex("0xa4b05fffffffffffffffffffffffffffffffffff33f46529933152e1782e51b69b5bebb0810705b1e56844f07ef4225ddbc0d700"),
	common.FromHex("0xa4b05fffffffffffffffffffffffffffffffffff1c2916348c6a2141e372f746967464575851d1fd7b468e88ffde720bb27f0f00"),
	// Extra/missing storage slots for A4B05... observed in debug diffs.
	common.FromHex("0xa4b05fffffffffffffffffffffffffffffffffffe54de2a4cdacc0a0059d2b6e16348103df8c4aff409c31e40ec73d11926c8204"),
	common.FromHex("0xa4b05fffffffffffffffffffffffffffffffffffa9f6f085d78d1d37c5819e5c16c9e03198bd14e08cd1f6f8191bc6207b9e9706"),
	common.FromHex("0xa4b05fffffffffffffffffffffffffffffffffffa9f6f085d78d1d37c5819e5c16c9e03198bd14e08cd1f6f8191bc6207b9e970b"),
	common.FromHex("0xa4b05fffffffffffffffffffffffffffffffffff9bb24c435cb08976b0c8b2e5f791f87329d2d1c9e87eded8fabaab40daa003ce"),
	common.FromHex("0xa4b05fffffffffffffffffffffffffffffffffffce2e0b807182ef818ba97a1345709a5d0e972ebfd9b11067e4dbd6c89415e1d8"),
	common.FromHex("0xa4b05fffffffffffffffffffffffffffffffffff92f35efc010991d7e9cf2cce605a23399f5aaa17d84c93eb9b94a11b14ed38f9"),
	common.FromHex("0xa4b05fffffffffffffffffffffffffffffffffff94b0ea710acc66b6ee178746922647c9a07d2e7b381b8404815a9bc2b44caeba"),
}
var mdbxMigrateTraceAccounts = loadMdbxMigrateTraceAccounts()

func isMdbxMigrateTraceKey(key []byte) bool {
	for _, want := range mdbxMigrateTraceKeys {
		if bytes.Equal(key, want) {
			return true
		}
	}
	return false
}

func loadMdbxMigrateTraceAccounts() []common.Address {
	raw := os.Getenv("ERIGON_MDBX_MIGRATE_ACCOUNTTRACE_ADDRS")
	if raw == "" {
		return []common.Address{
			common.HexToAddress("0x28c18bc63069e3581870904f32Dd34D9e3332cce"),
			common.HexToAddress("0x31c5a1C83265113bd089385d76dfe4D8A2577204"),
			common.HexToAddress("0xA4b000000000000000000073657175656e636572"),
			common.HexToAddress("0xA4B00000000000000000000000000000000000f6"),
			common.HexToAddress("0x00000000000000000000000000000000000A4B05"),
			common.HexToAddress("0xA4B05FFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFF"),
		}
	}

	parts := strings.Split(raw, ",")
	addrs := make([]common.Address, 0, len(parts))
	for _, part := range parts {
		part = strings.TrimSpace(part)
		if part == "" {
			continue
		}
		if !common.IsHexAddress(part) {
			continue
		}
		addrs = append(addrs, common.HexToAddress(part))
	}
	return addrs
}

func isMdbxMigrateTraceAccount(addr common.Address) bool {
	for _, want := range mdbxMigrateTraceAccounts {
		if addr == want {
			return true
		}
	}
	return false
}

func logMdbxMigrateAccountTrace(op string, txNum uint64, address common.Address, original, account *accounts.Account) {
	if !mdbxMigrateAccountTrace || !isMdbxMigrateTraceAccount(address) {
		return
	}
	fields := []interface{}{
		"op", op,
		"tx_num", txNum,
		"addr", address.Hex(),
	}
	if original != nil {
		origEmpty := original.Nonce == 0 && original.Balance.IsZero() && original.IsEmptyCodeHash()
		fields = append(fields,
			"orig_empty", origEmpty,
			"orig_nonce", original.Nonce,
			"orig_balance", original.Balance.ToBig().String(),
			"orig_incarnation", original.Incarnation,
			"orig_code_hash", original.CodeHash.Hex(),
			"orig_root", original.Root.Hex(),
		)
	}
	if account != nil {
		newEmpty := account.Nonce == 0 && account.Balance.IsZero() && account.IsEmptyCodeHash()
		enc := accounts.SerialiseV3(account)
		fields = append(fields,
			"new_empty", newEmpty,
			"new_nonce", account.Nonce,
			"new_balance", account.Balance.ToBig().String(),
			"new_incarnation", account.Incarnation,
			"new_code_hash", account.CodeHash.Hex(),
			"new_root", account.Root.Hex(),
			"new_enc_len", len(enc),
			"new_enc", hexPreviewBytes(enc, 64),
		)
	}
	log.Info("mdbx-migrate accounttrace", fields...)
}

func decodeAccountV3(enc []byte) (*accounts.Account, error) {
	if len(enc) == 0 || isAccountTombstone(enc) {
		return nil, nil
	}
	var acc accounts.Account
	acc.Reset()
	if err := accounts.DeserialiseV3(&acc, enc); err != nil {
		return nil, err
	}
	out := acc
	return &out, nil
}

func logApplyAccountDomainSnapshot(stage string, domains *dbstate.SharedDomains, tx kv.TemporalTx, txTask *TxTask, keyBytes []byte, writeVal []byte) {
	if len(keyBytes) != length.Addr || txTask == nil {
		return
	}
	addr := common.BytesToAddress(keyBytes)
	if !shouldTraceApplyAccount(addr) {
		return
	}

	op := "put"
	if writeVal == nil {
		op = "del"
	}

	prevEnc, prevStep, prevErr := domains.GetLatest(kv.AccountsDomain, tx, keyBytes)
	var (
		prevAcc       *accounts.Account
		prevDecodeErr error
	)
	if prevErr == nil {
		prevAcc, prevDecodeErr = decodeAccountV3(prevEnc)
	}

	asofEnc, asofOk, asofErr := tx.GetAsOf(kv.AccountsDomain, keyBytes, txTask.TxNum)
	var (
		asofAcc       *accounts.Account
		asofDecodeErr error
	)
	if asofErr == nil && asofOk {
		asofAcc, asofDecodeErr = decodeAccountV3(asofEnc)
	}

	var (
		writeAcc       *accounts.Account
		writeDecodeErr error
	)
	if writeVal != nil {
		writeAcc, writeDecodeErr = decodeAccountV3(writeVal)
	}

	hasStoragePrefix := false
	hasStoragePrefixErr := ""
	if txWithCursor, ok := tx.(cursorTx); ok {
		okPrefix, err := hasStorageForAddr(txWithCursor, keyBytes)
		if err != nil {
			hasStoragePrefixErr = err.Error()
		} else {
			hasStoragePrefix = okPrefix
		}
	} else {
		hasStoragePrefixErr = "tx_has_no_cursor"
	}

	storageRoot := common.Hash{}
	storageItems := 0
	storageRootErr := ""
	if tx != nil {
		root, items, err := computeStorageRootFromLatest(domains, tx, addr)
		if err != nil {
			storageRootErr = err.Error()
		} else {
			storageRoot = root
			storageItems = items
		}
	} else {
		storageRootErr = "nil_tx"
	}

	fields := []interface{}{
		"block", txTask.BlockNum,
		"tx_index", txTask.TxIndex,
		"tx_num", txTask.TxNum,
		"stage", stage,
		"op", op,
		"addr", addr.Hex(),
		"write_len", len(writeVal),
		"write_tombstone", isAccountTombstone(writeVal),
		"write_empty_encoding", isEmptyAccountEncoding(writeVal),
		"write_decode_err", errToString(writeDecodeErr),
		"pre_len", len(prevEnc),
		"pre_tombstone", isAccountTombstone(prevEnc),
		"pre_step", prevStep,
		"pre_read_err", errToString(prevErr),
		"pre_decode_err", errToString(prevDecodeErr),
		"asof_ok", asofOk,
		"asof_len", len(asofEnc),
		"asof_tombstone", isAccountTombstone(asofEnc),
		"asof_read_err", errToString(asofErr),
		"asof_decode_err", errToString(asofDecodeErr),
		"has_storage_prefix", hasStoragePrefix,
		"has_storage_prefix_err", hasStoragePrefixErr,
		"storage_items", storageItems,
		"storage_root", storageRoot.Hex(),
		"storage_root_err", storageRootErr,
	}
	if prevAcc != nil {
		fields = append(fields,
			"pre_nonce", prevAcc.Nonce,
			"pre_balance", prevAcc.Balance.ToBig().String(),
			"pre_code_hash", prevAcc.CodeHash.Hex(),
			"pre_root", prevAcc.Root.Hex(),
			"pre_empty", prevAcc.Nonce == 0 && prevAcc.Balance.IsZero() && prevAcc.IsEmptyCodeHash(),
		)
	}
	if writeAcc != nil {
		fields = append(fields,
			"write_nonce", writeAcc.Nonce,
			"write_balance", writeAcc.Balance.ToBig().String(),
			"write_code_hash", writeAcc.CodeHash.Hex(),
			"write_root", writeAcc.Root.Hex(),
			"write_empty", writeAcc.Nonce == 0 && writeAcc.Balance.IsZero() && writeAcc.IsEmptyCodeHash(),
		)
	}
	if asofAcc != nil {
		fields = append(fields,
			"asof_nonce", asofAcc.Nonce,
			"asof_balance", asofAcc.Balance.ToBig().String(),
			"asof_code_hash", asofAcc.CodeHash.Hex(),
			"asof_root", asofAcc.Root.Hex(),
			"asof_empty", asofAcc.Nonce == 0 && asofAcc.Balance.IsZero() && asofAcc.IsEmptyCodeHash(),
		)
	}
	log.Warn("state apply account snapshot", fields...)
}

func errToString(err error) string {
	if err == nil {
		return ""
	}
	return err.Error()
}

func logMdbxMigrateAccountDrop(reason string, txTask *TxTask, address common.Address, val []byte) {
	if !mdbxMigrateAccountTrace || !isMdbxMigrateTraceAccount(address) {
		return
	}
	log.Info("mdbx-migrate accountdrop",
		"reason", reason,
		"tx_num", txTask.TxNum,
		"block", txTask.BlockNum,
		"tx_index", txTask.TxIndex,
		"addr", address.Hex(),
		"val_len", len(val),
		"val", hexPreviewBytes(val, 64),
	)
}

func shouldMdbxMigrateStorageTrace(blockNum uint64, txIndex int) bool {
	if !mdbxMigrateStorageTrace {
		return false
	}
	if mdbxMigrateStorageTraceBlockSet && blockNum != mdbxMigrateStorageTraceBlock {
		return false
	}
	if mdbxMigrateStorageTraceTxIndexSet && txIndex != mdbxMigrateStorageTraceTxIndex {
		return false
	}
	return true
}

func hexPreviewBytes(raw []byte, max int) string {
	if len(raw) == 0 || max <= 0 {
		return ""
	}
	if len(raw) <= max {
		return fmt.Sprintf("%x", raw)
	}
	return fmt.Sprintf("%x...len=%d", raw[:max], len(raw))
}

func codeHashForLog(code []byte) string {
	if len(code) == 0 {
		return ""
	}
	hash, err := common.HashData(code)
	if err != nil {
		return "error:" + err.Error()
	}
	return hash.Hex()
}

func logFixedSenderAccountCompare(site string, domains *dbstate.SharedDomains, tx kv.TemporalTx, txTask *TxTask, addr common.Address) {
	if txTask == nil {
		return
	}
	if addr != common.HexToAddress("0x28c18bc63069e3581870904f32Dd34D9e3332cce") {
		return
	}
	addrBytes := addr.Bytes()
	latestVal, latestStep, latestErr := domains.GetLatest(kv.AccountsDomain, tx, addrBytes)
	asofVal, asofOk, asofErr := tx.GetAsOf(kv.AccountsDomain, addrBytes, txTask.TxNum)
	fields := []interface{}{
		"site", site,
		"block", txTask.BlockNum,
		"tx_index", txTask.TxIndex,
		"tx_num", txTask.TxNum,
		"addr", addr.Hex(),
		"latest_len", len(latestVal),
		"latest_step", latestStep,
		"latest_preview", hexPreviewBytes(latestVal, 32),
		"latest_err", errToString(latestErr),
		"asof_ok", asofOk,
		"asof_len", len(asofVal),
		"asof_preview", hexPreviewBytes(asofVal, 32),
		"asof_err", errToString(asofErr),
	}
	if acc, err := decodeAccountV3(latestVal); err == nil && acc != nil {
		fields = append(fields, "latest_nonce", acc.Nonce)
	}
	if acc, err := decodeAccountV3(asofVal); err == nil && acc != nil {
		fields = append(fields, "asof_nonce", acc.Nonce)
	}
	log.Warn("state fixed sender account compare", fields...)
}

// ParallelExecutionState - mainly designed for parallel transactions execution. It does separate:
//   - execution
//   - re-try execution if conflict-resolution
//   - collect state changes for conflict-resolution
//   - apply state-changes independently from execution and even in another goroutine (by ApplyState func)
//   - track which txNums state-changes was applied
type ParallelExecutionState struct {
	domains      *dbstate.SharedDomains
	tx           kv.TemporalTx
	triggerLock  sync.Mutex
	triggers     map[uint64]*TxTask
	senderTxNums map[common.Address]uint64

	isBor bool

	logger log.Logger

	syncCfg ethconfig.Sync
	trace   bool
}

func mdbxMigrateShouldLogReceipts(blockNum uint64) bool {
	if !mdbxMigrateReceiptsDebug {
		return false
	}
	if mdbxMigrateReceiptsDebugBlockSet && blockNum != mdbxMigrateReceiptsDebugBlock {
		return false
	}
	return true
}

func NewParallelExecutionState(domains *dbstate.SharedDomains, tx kv.Tx, syncCfg ethconfig.Sync, isBor bool, logger log.Logger) *ParallelExecutionState {
	return &ParallelExecutionState{
		domains:      domains,
		tx:           tx.(kv.TemporalTx),
		triggers:     map[uint64]*TxTask{},
		senderTxNums: map[common.Address]uint64{},
		logger:       logger,
		syncCfg:      syncCfg,
		isBor:        isBor,
		//trace: true,
	}
}

func (rs *ParallelExecutionState) ReTry(txTask *TxTask, in *QueueWithRetry) {
	txTask.Reset()
	in.ReTry(txTask)
}
func (rs *ParallelExecutionState) AddWork(ctx context.Context, txTask *TxTask, in *QueueWithRetry) {
	txTask.Reset()
	in.Add(ctx, txTask)
}

func (rs *ParallelExecutionState) RegisterSender(txTask *TxTask) bool {
	//TODO: it deadlocks on panic, fix it
	defer func() {
		rec := recover()
		if rec != nil {
			fmt.Printf("panic?: %s,%s\n", rec, dbg.Stack())
		}
	}()
	rs.triggerLock.Lock()
	defer rs.triggerLock.Unlock()
	lastTxNum, deferral := rs.senderTxNums[*txTask.Sender()]
	if deferral {
		// Transactions with the same sender have obvious data dependency, no point running it before lastTxNum
		// So we add this data dependency as a trigger
		//fmt.Printf("trigger[%d] sender [%x]<=%x\n", lastTxNum, *txTask.Sender, txTask.Tx.Hash())
		rs.triggers[lastTxNum] = txTask
	}
	//fmt.Printf("senderTxNums[%x]=%d\n", *txTask.Sender, txTask.TxNum)
	rs.senderTxNums[*txTask.Sender()] = txTask.TxNum
	return !deferral
}

func (rs *ParallelExecutionState) CommitTxNum(sender *common.Address, txNum uint64, in *QueueWithRetry) (count int) {
	execTxsDone.Inc()

	rs.triggerLock.Lock()
	defer rs.triggerLock.Unlock()
	if triggered, ok := rs.triggers[txNum]; ok {
		in.ReTry(triggered)
		count++
		delete(rs.triggers, txNum)
	}
	if sender != nil {
		if lastTxNum, ok := rs.senderTxNums[*sender]; ok && lastTxNum == txNum {
			// This is the last transaction so far with this sender, remove
			delete(rs.senderTxNums, *sender)
		}
	}
	return count
}

func (rs *ParallelExecutionState) applyState(txTask *TxTask, domains *dbstate.SharedDomains) error {
	var acc accounts.Account
	type touchedContractState struct {
		codeTouched    bool
		storageTouched bool
		codeWriteVal   []byte
	}
	touchedContractStates := make(map[common.Address]touchedContractState)
	var fixEmptyRootAddrs map[common.Address]struct{}
	traceApply := shouldMdbxMigrateApplyTrace(txTask)
	if mdbxMigrateFixEmptyRoot {
		fixEmptyRootAddrs = make(map[common.Address]struct{})
		for addr := range badRootAccountsSet {
			fixEmptyRootAddrs[addr] = struct{}{}
		}
	}
	if traceApply {
		accountWrites := 0
		codeWrites := 0
		storageWrites := 0
		if txTask.WriteLists != nil {
			if list := txTask.WriteLists[kv.AccountsDomain.String()]; list != nil {
				accountWrites = len(list.Keys)
			}
			if list := txTask.WriteLists[kv.CodeDomain.String()]; list != nil {
				codeWrites = len(list.Keys)
			}
			if list := txTask.WriteLists[kv.StorageDomain.String()]; list != nil {
				storageWrites = len(list.Keys)
			}
		}
		log.Warn("state apply start",
			"block", txTask.BlockNum,
			"tx_index", txTask.TxIndex,
			"tx_num", txTask.TxNum,
			"account_writes", accountWrites,
			"code_writes", codeWrites,
			"storage_writes", storageWrites,
			"balance_increase_count", len(txTask.BalanceIncreaseSet),
			"account_probe", mdbxMigrateApplyTraceAccountProbe.Hex(),
			"path_probe_addr", mdbxMigrateApplyTraceStorageProbeAddr.Hex(),
			"path_probe_slot", mdbxMigrateApplyTraceStorageProbeSlot.Hex(),
		)
	}
	deletePlainAccount := func(key []byte, force bool) {
		if rwTx, ok := rs.tx.(kv.RwTx); ok {
			keep := keepEmptyAccounts
			if keepEmptyAccounts {
				keep = shouldKeepEmptyAccountBytes(key)
			}
			wantLog := false
			var addr common.Address
			if mdbxMigrateAccountTrace && len(key) == length.Addr {
				addr = common.BytesToAddress(key)
				wantLog = isMdbxMigrateTraceAccount(addr)
			}
			var cur []byte
			if (keep && !force) || wantLog {
				cur, _ = rwTx.GetOne(kv.TblAccountVals, key)
			}
			// When keeping empty accounts, only drop obvious tombstones/garbage.
			if keep && !force {
				if !isAccountValsTombstone(cur) {
					if wantLog {
						log.Info("mdbx-migrate accountdrop",
							"reason", "plain-keep",
							"tx_num", txTask.TxNum,
							"block", txTask.BlockNum,
							"tx_index", txTask.TxIndex,
							"addr", addr.Hex(),
							"force", force,
							"keep", keep,
							"val_len", len(cur),
							"val", hexPreviewBytes(cur, 64),
						)
					}
					return
				}
				force = true
			}
			if force || !keep {
				if wantLog {
					log.Info("mdbx-migrate accountdrop",
						"reason", "plain-delete",
						"tx_num", txTask.TxNum,
						"block", txTask.BlockNum,
						"tx_index", txTask.TxIndex,
						"addr", addr.Hex(),
						"force", force,
						"keep", keep,
						"val_len", len(cur),
						"val", hexPreviewBytes(cur, 64),
					)
				}
				_ = rwTx.Delete(kv.TblAccountVals, key)
			}
		}
	}

	// One-time sweep: clean up account tombstones that may have been left behind by history import.
	// Runs only when explicitly requested, to avoid mutating healthy states (e.g. L3 local chains).
	if mdbxMigrateSweepTombstones && (mdbxMigrateSweepTombstonesBlock == 0 || txTask.BlockNum >= mdbxMigrateSweepTombstonesBlock) {
		var tombstoneErr error
		repairTombstonesOnce.Do(func() {
			if rwTx, ok := rs.tx.(kv.RwTx); ok {
				if c, err := rwTx.Cursor(kv.TblAccountVals); err == nil {
					defer c.Close()
					for k, v, err := c.First(); k != nil; k, v, err = c.Next() {
						if err != nil {
							tombstoneErr = err
							return
						}
						if isAccountValsTombstone(v) {
							if err := rwTx.Delete(kv.TblAccountVals, k); err != nil {
								tombstoneErr = err
								return
							}
						}
					}
				} else {
					tombstoneErr = err
					return
				}
			}
			_ = domains.IteratePrefix(kv.AccountsDomain, nil, rs.tx, func(k, v []byte, step kv.Step) (bool, error) {
				if isAccountTombstone(v) {
					if len(k) == length.Addr {
						addr := common.BytesToAddress(k)
						logMdbxMigrateAccountDrop("tombstone-sweep", txTask, addr, v)
					}
					// Purge plain-state tombstones/obviously short records so account existence matches source.
					_ = domains.DomainDel(kv.AccountsDomain, rs.tx, k, txTask.TxNum, v, step)
					deletePlainAccount(k, true)
				}
				return true, nil
			})
		})
		if tombstoneErr != nil {
			return tombstoneErr
		}
	}

	//maps are unordered in Go! don't iterate over it. SharedDomains.deleteAccount will call GetLatest(Code) and expecting it not been delete yet
	if txTask.WriteLists != nil {
		for _, domain := range []kv.Domain{kv.AccountsDomain, kv.CodeDomain, kv.StorageDomain} {
			list, ok := txTask.WriteLists[domain.String()]
			if !ok {
				continue
			}

			for i, key := range list.Keys {
				keyBytes := []byte(key)
				if len(keyBytes) >= length.Addr {
					addr := common.BytesToAddress(keyBytes[:length.Addr])
					state := touchedContractStates[addr]
					if domain == kv.CodeDomain {
						state.codeTouched = true
						if val := list.Vals[i]; len(val) > 0 {
							state.codeWriteVal = append(state.codeWriteVal[:0], val...)
						}
					}
					if domain == kv.StorageDomain {
						state.storageTouched = true
					}
					touchedContractStates[addr] = state
				}
				if traceApply {
					if domain == kv.AccountsDomain && len(keyBytes) == length.Addr {
						addr := common.BytesToAddress(keyBytes)
						if shouldTraceApplyAccount(addr) {
							op := "put"
							if list.Vals[i] == nil {
								op = "del"
							}
							fields := []interface{}{
								"block", txTask.BlockNum,
								"tx_index", txTask.TxIndex,
								"tx_num", txTask.TxNum,
								"domain", domain.String(),
								"op", op,
								"addr", addr.Hex(),
								"val_len", len(list.Vals[i]),
								"is_tombstone", isAccountTombstone(list.Vals[i]),
								"is_empty_encoding", isEmptyAccountEncoding(list.Vals[i]),
							}
							if acc, err := decodeAccountV3(list.Vals[i]); err == nil && acc != nil {
								fields = append(fields,
									"val_nonce", acc.Nonce,
									"val_balance", acc.Balance.ToBig().String(),
									"val_root", acc.Root.Hex(),
								)
							}
							log.Warn("state apply account write-list op", fields...)
						}
					}
					if domain == kv.StorageDomain && len(keyBytes) >= length.Addr+length.Hash {
						addr := common.BytesToAddress(keyBytes[:length.Addr])
						if addr == mdbxMigrateApplyTraceStorageProbeAddr {
							slotBytes := keyBytes[length.Addr : length.Addr+length.Hash]
							slotMatchesProbe := bytes.Equal(slotBytes, mdbxMigrateApplyTraceStorageProbeSlot.Bytes())
							prevVal, prevStep, prevErr := domains.GetLatest(kv.StorageDomain, rs.tx, keyBytes)
							op := "put"
							if list.Vals[i] == nil {
								op = "del"
							}
							prevMatchesWrite := prevErr == nil && bytes.Equal(prevVal, list.Vals[i])
							log.Warn("state apply storage write-list op",
								"block", txTask.BlockNum,
								"tx_index", txTask.TxIndex,
								"tx_num", txTask.TxNum,
								"domain", domain.String(),
								"op", op,
								"addr", addr.Hex(),
								"slot", fmt.Sprintf("0x%x", slotBytes),
								"slot_matches_probe", slotMatchesProbe,
								"prev_step", prevStep,
								"prev_len", len(prevVal),
								"prev_preview", hexPreviewBytes(prevVal, 64),
								"prev_err", prevErr,
								"prev_matches_write", prevMatchesWrite,
								"val_len", len(list.Vals[i]),
								"val_preview", hexPreviewBytes(list.Vals[i], 64),
							)
						}
					}
				}
				if mdbxMigrateFixEmptyRoot {
					if domain == kv.AccountsDomain && len(keyBytes) == length.Addr {
						fixEmptyRootAddrs[common.BytesToAddress(keyBytes)] = struct{}{}
					} else if domain == kv.StorageDomain && len(keyBytes) >= length.Addr {
						fixEmptyRootAddrs[common.BytesToAddress(keyBytes[:length.Addr])] = struct{}{}
					}
				}
				if mdbxMigrateKeyTrace && domain == kv.StorageDomain && isMdbxMigrateTraceKey(keyBytes) {
					val := list.Vals[i]
					op := "put"
					if val == nil {
						op = "del"
					}
					log.Info("mdbx-migrate keytrace",
						"op", op,
						"domain", domain.String(),
						"tx_num", txTask.TxNum,
						"block", txTask.BlockNum,
						"tx_index", txTask.TxIndex,
						"key", fmt.Sprintf("0x%x", keyBytes),
						"val_len", len(val),
						"val", hexPreviewBytes(val, 64),
					)
				}
				if domain == kv.StorageDomain && shouldMdbxMigrateStorageTrace(txTask.BlockNum, txTask.TxIndex) {
					val := list.Vals[i]
					op := "put"
					if val == nil {
						op = "del"
					}
					log.Info("mdbx-migrate storagetrace",
						"op", op,
						"tx_num", txTask.TxNum,
						"block", txTask.BlockNum,
						"tx_index", txTask.TxIndex,
						"key_len", len(keyBytes),
						"key", fmt.Sprintf("0x%x", keyBytes),
						"val_len", len(val),
						"val", hexPreviewBytes(val, 64),
					)
				}
				if mdbxMigrateAccountTrace && domain == kv.AccountsDomain && len(keyBytes) == length.Addr {
					addr := common.BytesToAddress(keyBytes)
					if isMdbxMigrateTraceAccount(addr) {
						enc0, _, err := domains.GetLatest(kv.AccountsDomain, rs.tx, keyBytes)
						if err != nil {
							return err
						}
						var origAcc *accounts.Account
						if len(enc0) > 0 {
							acc.Reset()
							if err := accounts.DeserialiseV3(&acc, enc0); err != nil {
								return err
							}
							orig := acc
							origAcc = &orig
						}
						if list.Vals[i] == nil {
							logMdbxMigrateAccountTrace("apply_del", txTask.TxNum, addr, origAcc, nil)
						} else {
							acc.Reset()
							if err := accounts.DeserialiseV3(&acc, list.Vals[i]); err != nil {
								return err
							}
							newAcc := acc
							logMdbxMigrateAccountTrace("apply_put", txTask.TxNum, addr, origAcc, &newAcc)
						}
					}
				}
				// Treat account tombstones (0xff...) and obviously short encodings as deletes.
				if domain == kv.AccountsDomain && list.Vals[i] != nil {
					if isAccountTombstone(list.Vals[i]) {
						if len(keyBytes) == length.Addr {
							addr := common.BytesToAddress(keyBytes)
							logMdbxMigrateAccountDrop("tombstone", txTask, addr, list.Vals[i])
						}
						// Drop tombstone/garbage writes entirely and make sure the plain state is cleared.
						deletePlainAccount(keyBytes, true)
						list.Vals[i] = nil
					} else if isEmptyAccountEncoding(list.Vals[i]) && !shouldKeepEmptyAccountBytes(keyBytes) {
						// EIP-161: touched empty accounts should be deleted unless explicitly kept.
						// Guard: keep empty account encoding if any storage exists for the address.
						if len(keyBytes) == length.Addr {
							addr := common.BytesToAddress(keyBytes)
							// If we cannot check storage, keep the account to avoid dropping a storage-backed account.
							hasStorage := true
							if rs.tx != nil {
								var err error
								_, _, hasStorage, err = rs.tx.HasPrefix(kv.StorageDomain, keyBytes)
								if err != nil {
									return err
								}
							}
							hasPendingStorage := hasPendingStorageWritesForAddr(txTask, keyBytes)
							if hasStorage || hasPendingStorage {
								reason := "empty-encoding-with-storage"
								if hasPendingStorage && !hasStorage {
									reason = "empty-encoding-with-pending-storage"
								}
								logMdbxMigrateAccountDrop(reason, txTask, addr, list.Vals[i])
								// Replace empty encoding with the latest persisted account encoding when storage exists.
								// This preserves the correct storage root instead of keeping an empty-root account.
								enc, _, err := domains.GetLatest(kv.AccountsDomain, rs.tx, keyBytes)
								if err != nil {
									return err
								}
								if len(enc) > 0 && !isAccountTombstone(enc) {
									list.Vals[i] = enc
									if isBadRootAccount(addr) {
										log.Warn("state account replace empty-encoding due to storage (bad root watch)",
											"tx_num", txTask.TxNum,
											"block", txTask.BlockNum,
											"tx_index", txTask.TxIndex,
											"addr", addr.Hex(),
											"val_len", len(enc),
											"val", hexPreviewBytes(enc, 64),
										)
									}
								} else if isBadRootAccount(addr) {
									log.Warn("state account keep empty-encoding due to storage but no prior encoding (bad root watch)",
										"tx_num", txTask.TxNum,
										"block", txTask.BlockNum,
										"tx_index", txTask.TxIndex,
										"addr", addr.Hex(),
									)
								}
								if isBadRootAccount(addr) {
									log.Warn("state account keep empty-encoding due to storage (bad root watch)",
										"tx_num", txTask.TxNum,
										"block", txTask.BlockNum,
										"tx_index", txTask.TxIndex,
										"addr", addr.Hex(),
									)
								}
							} else if spuriousDragonEnabledForTask(txTask) {
								logMdbxMigrateAccountDrop("empty-encoding", txTask, addr, list.Vals[i])
								if isBadRootAccount(addr) {
									log.Warn("state account drop empty-encoding (bad root watch)",
										"tx_num", txTask.TxNum,
										"block", txTask.BlockNum,
										"tx_index", txTask.TxIndex,
										"addr", addr.Hex(),
									)
								}
								list.Vals[i] = nil
							}
						} else if spuriousDragonEnabledForTask(txTask) {
							list.Vals[i] = nil
						}
					}
				}

				if domain == kv.AccountsDomain && len(keyBytes) == length.Addr && list.Vals[i] != nil && mdbxMigrateFixEmptyRoot {
					addr := common.BytesToAddress(keyBytes)
					if _, watch := fixEmptyRootAddrs[addr]; watch {
						acc.Reset()
						if err := accounts.DeserialiseV3(&acc, list.Vals[i]); err != nil {
							return err
						}
						if acc.IsEmptyRoot() {
							storageRoot, items, err := computeStorageRootFromLatest(domains, rs.tx, addr)
							if err != nil {
								return err
							}
							if items > 0 && storageRoot != acc.Root {
								acc.Root = storageRoot
								list.Vals[i] = accounts.SerialiseV3(&acc)
								if isBadRootAccount(addr) {
									log.Warn("state account patched empty root before apply",
										"tx_num", txTask.TxNum,
										"block", txTask.BlockNum,
										"tx_index", txTask.TxIndex,
										"addr", addr.Hex(),
										"storage_items", items,
										"storage_root", storageRoot,
										"val_len", len(list.Vals[i]),
										"val", hexPreviewBytes(list.Vals[i], 64),
									)
								}
							}
							if domain == kv.CodeDomain && len(keyBytes) == length.Addr {
								addr := common.BytesToAddress(keyBytes)
								if shouldTraceApplyAccount(addr) {
									op := "put"
									if list.Vals[i] == nil {
										op = "del"
									}
									var codeHash common.Hash
									var hashErr error
									if len(list.Vals[i]) > 0 {
										codeHash, hashErr = common.HashData(list.Vals[i])
									}
									prevVal, prevStep, prevErr := domains.GetLatest(kv.CodeDomain, rs.tx, keyBytes)
									log.Warn("state apply code write-list op",
										"block", txTask.BlockNum,
										"tx_index", txTask.TxIndex,
										"tx_num", txTask.TxNum,
										"domain", domain.String(),
										"op", op,
										"addr", addr.Hex(),
										"prev_step", prevStep,
										"prev_len", len(prevVal),
										"prev_hash", codeHashForLog(prevVal),
										"prev_err", prevErr,
										"val_len", len(list.Vals[i]),
										"val_hash", codeHash.Hex(),
										"val_hash_err", hashErr,
										"val_preview", hexPreviewBytes(list.Vals[i], 32),
									)
								}
							}
						}
					}
				}

				if domain == kv.AccountsDomain && len(keyBytes) == length.Addr {
					logApplyAccountDomainSnapshot("pre-apply", domains, rs.tx, txTask, keyBytes, list.Vals[i])
				}

				if list.Vals[i] == nil {
					traceDelete := false
					traceDeleteAddr := common.Address{}
					if domain == kv.AccountsDomain && len(keyBytes) == length.Addr {
						traceDeleteAddr = common.BytesToAddress(keyBytes)
						traceDelete = shouldTraceApplyAccount(traceDeleteAddr)
					}
					// Guard: avoid dropping accounts that still have storage (or pending storage writes).
					// This preserves the correct storage root even when a delete/empty encoding shows up.
					if domain == kv.AccountsDomain && len(keyBytes) == length.Addr {
						keepEmpty := shouldKeepEmptyAccount(traceDeleteAddr)
						// If we cannot check storage, keep the account to avoid dropping a storage-backed account.
						hasStorage := true
						hasStorageChecked := false
						if rs.tx != nil {
							var err error
							hasStorageChecked = true
							_, _, hasStorage, err = rs.tx.HasPrefix(kv.StorageDomain, keyBytes)
							if err != nil {
								return err
							}
						}
						hasPendingStorage := hasPendingStorageWritesForAddr(txTask, keyBytes)
						if traceDelete {
							log.Warn("state apply account delete guard",
								"block", txTask.BlockNum,
								"tx_index", txTask.TxIndex,
								"tx_num", txTask.TxNum,
								"addr", traceDeleteAddr.Hex(),
								"keep_empty", keepEmpty,
								"has_storage_checked", hasStorageChecked,
								"has_storage", hasStorage,
								"has_pending_storage", hasPendingStorage,
							)
						}
						if hasStorage || hasPendingStorage {
							enc, encStep, err := domains.GetLatest(kv.AccountsDomain, rs.tx, keyBytes)
							if err != nil {
								return err
							}
							if len(enc) > 0 && !isAccountTombstone(enc) {
								if traceDelete {
									log.Warn("state apply account delete decision",
										"block", txTask.BlockNum,
										"tx_index", txTask.TxIndex,
										"tx_num", txTask.TxNum,
										"addr", traceDeleteAddr.Hex(),
										"action", "keep-put",
										"keep_empty", keepEmpty,
										"has_storage", hasStorage,
										"has_pending_storage", hasPendingStorage,
										"enc_len", len(enc),
										"enc_step", encStep,
										"enc_tombstone", isAccountTombstone(enc),
									)
								}
								if err := domains.DomainPut(kv.AccountsDomain, rs.tx, keyBytes, enc, txTask.TxNum, nil, 0); err != nil {
									return err
								}
								logApplyAccountDomainSnapshot("post-keep-put", domains, rs.tx, txTask, keyBytes, enc)
								continue
							}
							if traceDelete {
								log.Warn("state apply account delete decision",
									"block", txTask.BlockNum,
									"tx_index", txTask.TxIndex,
									"tx_num", txTask.TxNum,
									"addr", traceDeleteAddr.Hex(),
									"action", "keep-skip",
									"reason", "storage-present-no-prior-encoding",
									"keep_empty", keepEmpty,
									"has_storage", hasStorage,
									"has_pending_storage", hasPendingStorage,
									"enc_len", len(enc),
									"enc_step", encStep,
									"enc_tombstone", isAccountTombstone(enc),
								)
							}
							if isBadRootAccount(common.BytesToAddress(keyBytes)) {
								log.Warn("state account skip delete due to storage but no prior encoding (bad root watch)",
									"tx_num", txTask.TxNum,
									"block", txTask.BlockNum,
									"tx_index", txTask.TxIndex,
									"addr", common.BytesToAddress(keyBytes).Hex(),
								)
							}
							logApplyAccountDomainSnapshot("post-keep-skip", domains, rs.tx, txTask, keyBytes, nil)
							continue
						}
					}
					if domain == kv.AccountsDomain && mdbxMigrateAccountTrace && len(keyBytes) == length.Addr {
						addr := common.BytesToAddress(keyBytes)
						if isMdbxMigrateTraceAccount(addr) {
							prev, _, err := domains.GetLatest(kv.AccountsDomain, rs.tx, keyBytes)
							if err != nil {
								return err
							}
							log.Info("mdbx-migrate accountdrop",
								"reason", "domain-del",
								"tx_num", txTask.TxNum,
								"block", txTask.BlockNum,
								"tx_index", txTask.TxIndex,
								"addr", addr.Hex(),
								"val_len", len(prev),
								"val", hexPreviewBytes(prev, 64),
							)
						}
					}
					if domain == kv.AccountsDomain && traceDelete {
						log.Warn("state apply account delete decision",
							"block", txTask.BlockNum,
							"tx_index", txTask.TxIndex,
							"tx_num", txTask.TxNum,
							"addr", traceDeleteAddr.Hex(),
							"action", "domain-del",
						)
					}
					if err := domains.DomainDel(domain, rs.tx, keyBytes, txTask.TxNum, nil, 0); err != nil {
						return err
					}
					if domain == kv.AccountsDomain {
						deletePlainAccount(keyBytes, false)
						logApplyAccountDomainSnapshot("post-del", domains, rs.tx, txTask, keyBytes, nil)
						if traceDelete {
							existsAfter, encAfter, stepAfter, err := readApplyTraceAccount(domains, rs.tx, traceDeleteAddr, nil)
							if err != nil {
								log.Warn("state apply account delete post-check failed",
									"block", txTask.BlockNum,
									"tx_index", txTask.TxIndex,
									"tx_num", txTask.TxNum,
									"addr", traceDeleteAddr.Hex(),
									"err", err,
								)
							} else {
								log.Warn("state apply account delete post-check",
									"block", txTask.BlockNum,
									"tx_index", txTask.TxIndex,
									"tx_num", txTask.TxNum,
									"addr", traceDeleteAddr.Hex(),
									"exists_after", existsAfter,
									"enc_after_len", len(encAfter),
									"step_after", stepAfter,
								)
							}
						}
					}
				} else {
					if err := domains.DomainPut(domain, rs.tx, keyBytes, list.Vals[i], txTask.TxNum, nil, 0); err != nil {
						return err
					}
					if traceApply && domain == kv.CodeDomain && len(keyBytes) == length.Addr {
						addr := common.BytesToAddress(keyBytes)
						if shouldTraceApplyAccount(addr) {
							domsVal, domsStep, domsErr := domains.GetLatest(kv.CodeDomain, rs.tx, keyBytes)
							txVal, txStep, txErr := rs.tx.GetLatest(kv.CodeDomain, keyBytes)
							log.Warn("state apply code post-put check",
								"block", txTask.BlockNum,
								"tx_index", txTask.TxIndex,
								"tx_num", txTask.TxNum,
								"domain", domain.String(),
								"addr", addr.Hex(),
								"write_len", len(list.Vals[i]),
								"write_hash", codeHashForLog(list.Vals[i]),
								"doms_len", len(domsVal),
								"doms_step", domsStep,
								"doms_hash", codeHashForLog(domsVal),
								"doms_err", domsErr,
								"doms_matches_write", domsErr == nil && bytes.Equal(domsVal, list.Vals[i]),
								"tx_len", len(txVal),
								"tx_step", txStep,
								"tx_hash", codeHashForLog(txVal),
								"tx_err", txErr,
								"tx_matches_write", txErr == nil && bytes.Equal(txVal, list.Vals[i]),
							)
						}
					}
					if traceApply && domain == kv.StorageDomain && len(keyBytes) >= length.Addr+length.Hash {
						addr := common.BytesToAddress(keyBytes[:length.Addr])
						if addr == mdbxMigrateApplyTraceStorageProbeAddr {
							slotBytes := keyBytes[length.Addr : length.Addr+length.Hash]
							slotMatchesProbe := bytes.Equal(slotBytes, mdbxMigrateApplyTraceStorageProbeSlot.Bytes())

							domsVal, domsStep, domsErr := domains.GetLatest(kv.StorageDomain, rs.tx, keyBytes)
							txVal, txStep, txErr := rs.tx.GetLatest(kv.StorageDomain, keyBytes)

							domsMatchesWrite := domsErr == nil && bytes.Equal(domsVal, list.Vals[i])
							txMatchesWrite := txErr == nil && bytes.Equal(txVal, list.Vals[i])
							domsVsTxMatch := domsErr == nil && txErr == nil && bytes.Equal(domsVal, txVal)

							log.Warn("state apply storage post-put check",
								"block", txTask.BlockNum,
								"tx_index", txTask.TxIndex,
								"tx_num", txTask.TxNum,
								"domain", domain.String(),
								"addr", addr.Hex(),
								"slot", fmt.Sprintf("0x%x", slotBytes),
								"slot_matches_probe", slotMatchesProbe,
								"write_len", len(list.Vals[i]),
								"write_preview", hexPreviewBytes(list.Vals[i], 64),
								"doms_len", len(domsVal),
								"doms_step", domsStep,
								"doms_preview", hexPreviewBytes(domsVal, 64),
								"doms_err", domsErr,
								"doms_matches_write", domsMatchesWrite,
								"tx_len", len(txVal),
								"tx_step", txStep,
								"tx_preview", hexPreviewBytes(txVal, 64),
								"tx_err", txErr,
								"tx_matches_write", txMatchesWrite,
								"doms_vs_tx_match", domsVsTxMatch,
							)
						}
					}
					if domain == kv.AccountsDomain && len(keyBytes) == length.Addr {
						logApplyAccountDomainSnapshot("post-put", domains, rs.tx, txTask, keyBytes, list.Vals[i])
					}
				}
			}
		}
	}

	for addr, increase := range txTask.BalanceIncreaseSet {
		increase := increase
		if mdbxMigrateFixEmptyRoot {
			fixEmptyRootAddrs[addr] = struct{}{}
		}
		emptyRemoval := spuriousDragonEnabledForTask(txTask) && !increase.IsEscrow
		if shouldKeepEmptyAccount(addr) {
			emptyRemoval = false
		}
		addrBytes := addr.Bytes()
		logFixedSenderAccountCompare("balance_increase_pre", domains, rs.tx, txTask, addr)
		enc0, step0, err := domains.GetLatest(kv.AccountsDomain, rs.tx, addrBytes)
		if err != nil {
			return err
		}
		acc.Reset()
		if len(enc0) > 0 {
			if err := accounts.DeserialiseV3(&acc, enc0); err != nil {
				return err
			}
		}
		if traceApply {
			exists := len(enc0) > 0 && !isAccountTombstone(enc0)
			log.Warn("state apply balance increase entry",
				"block", txTask.BlockNum,
				"tx_index", txTask.TxIndex,
				"tx_num", txTask.TxNum,
				"addr", addr.Hex(),
				"exists", exists,
				"enc0_len", len(enc0),
				"step0", step0,
				"amount", increase.Amount.ToBig().String(),
				"is_escrow", increase.IsEscrow,
				"empty_removal", emptyRemoval,
				"before_nonce", acc.Nonce,
				"before_balance", acc.Balance.ToBig().String(),
				"before_code_hash", acc.CodeHash.Hex(),
				"before_root", acc.Root.Hex(),
			)
		}
		var origAcc *accounts.Account
		if mdbxMigrateAccountTrace && isMdbxMigrateTraceAccount(addr) {
			orig := acc
			origAcc = &orig
		}
		acc.Balance.Add(&acc.Balance, &increase.Amount)
		if traceApply {
			log.Warn("state apply balance increase after add",
				"block", txTask.BlockNum,
				"tx_index", txTask.TxIndex,
				"tx_num", txTask.TxNum,
				"addr", addr.Hex(),
				"after_nonce", acc.Nonce,
				"after_balance", acc.Balance.ToBig().String(),
				"after_code_hash", acc.CodeHash.Hex(),
				"after_root", acc.Root.Hex(),
			)
		}
		if origAcc != nil {
			newAcc := acc
			logMdbxMigrateAccountTrace("balance_increase", txTask.TxNum, addr, origAcc, &newAcc)
		}
		if addr == common.HexToAddress("0x571fb9e1003ebe9c99ad3c1a60797e19cb577e93") {
			log.Info("mdbx-migrate escrow debug balance_increase",
				"tx_num", txTask.TxNum,
				"addr", addr.Hex(),
				"is_escrow", increase.IsEscrow,
				"empty_removal", emptyRemoval,
				"nonce", acc.Nonce,
				"balance", acc.Balance.String(),
				"code_hash", fmt.Sprintf("0x%x", acc.CodeHash.Bytes()),
				"enc0_len", len(enc0),
				"step0", step0,
			)
		}
		if !increase.IsEscrow && emptyRemoval && acc.Nonce == 0 && acc.Balance.IsZero() && acc.IsEmptyCodeHash() {
			if isBadRootAccount(addr) {
				log.Warn("state account drop empty-removal (bad root watch)",
					"tx_num", txTask.TxNum,
					"block", txTask.BlockNum,
					"tx_index", txTask.TxIndex,
					"addr", addr.Hex(),
					"is_escrow", increase.IsEscrow,
					"empty_removal", emptyRemoval,
				)
			}
			if addr == common.HexToAddress("0x571fb9e1003ebe9c99ad3c1a60797e19cb577e93") {
				log.Info("mdbx-migrate escrow debug domain_del",
					"tx_num", txTask.TxNum,
					"addr", addr.Hex(),
					"is_escrow", increase.IsEscrow,
					"empty_removal", emptyRemoval,
				)
			}
			if err := domains.DomainDel(kv.AccountsDomain, rs.tx, addrBytes, txTask.TxNum, enc0, step0); err != nil {
				return err
			}
			if traceApply {
				log.Warn("state apply balance increase domain del",
					"block", txTask.BlockNum,
					"tx_index", txTask.TxIndex,
					"tx_num", txTask.TxNum,
					"addr", addr.Hex(),
					"empty_removal", emptyRemoval,
					"is_escrow", increase.IsEscrow,
				)
			}
		} else {
			enc1 := accounts.SerialiseV3(&acc)
			if addr == common.HexToAddress("0x571fb9e1003ebe9c99ad3c1a60797e19cb577e93") {
				log.Info("mdbx-migrate escrow debug domain_put",
					"tx_num", txTask.TxNum,
					"addr", addr.Hex(),
					"is_escrow", increase.IsEscrow,
					"empty_removal", emptyRemoval,
					"enc1_len", len(enc1),
				)
			}
			if err := domains.DomainPut(kv.AccountsDomain, rs.tx, addrBytes, enc1, txTask.TxNum, enc0, step0); err != nil {
				return err
			}
			if traceApply {
				log.Warn("state apply balance increase domain put",
					"block", txTask.BlockNum,
					"tx_index", txTask.TxIndex,
					"tx_num", txTask.TxNum,
					"addr", addr.Hex(),
					"enc1_len", len(enc1),
					"nonce", acc.Nonce,
					"balance", acc.Balance.ToBig().String(),
					"root", acc.Root.Hex(),
				)
			}
		}
	}
	// Safety net: if code/storage changed for an address but account encoding is absent,
	// synthesize a minimal account so commitment computation includes the contract leaf.
	for addr, touched := range touchedContractStates {
		if !touched.codeTouched && !touched.storageTouched {
			continue
		}
		addrBytes := addr.Bytes()
		logFixedSenderAccountCompare("touched_contract_pre", domains, rs.tx, txTask, addr)
		enc0, step0, err := domains.GetLatest(kv.AccountsDomain, rs.tx, addrBytes)
		if err != nil {
			return err
		}
		exists := len(enc0) > 0 && !isAccountTombstone(enc0)
		var nextAcc accounts.Account
		nextAcc.Reset()
		if exists {
			if err := accounts.DeserialiseV3(&nextAcc, enc0); err != nil {
				return err
			}
		}

		needsPut := false
		if touched.codeTouched {
			codeVal, _, err := domains.GetLatest(kv.CodeDomain, rs.tx, addrBytes)
			if err != nil {
				return err
			}
			if len(codeVal) == 0 && len(touched.codeWriteVal) > 0 {
				prevCode, prevCodeStep, err := domains.GetLatest(kv.CodeDomain, rs.tx, addrBytes)
				if err != nil {
					return err
				}
				if err := domains.DomainPut(kv.CodeDomain, rs.tx, addrBytes, touched.codeWriteVal, txTask.TxNum, prevCode, prevCodeStep); err != nil {
					return err
				}
				codeVal = touched.codeWriteVal
				if traceApply {
					log.Warn("state apply restored code from write-list fallback",
						"block", txTask.BlockNum,
						"tx_index", txTask.TxIndex,
						"tx_num", txTask.TxNum,
						"addr", addr.Hex(),
						"code_len", len(codeVal),
					)
				}
			}
			if len(codeVal) > 0 {
				codeHash, err := common.HashData(codeVal)
				if err != nil {
					return err
				}
				if nextAcc.CodeHash != codeHash {
					nextAcc.CodeHash = codeHash
					needsPut = true
				}
				// EVM-created contracts start at nonce=1; recover this when account encoding is absent
				// or was persisted as a touched-empty placeholder.
				if nextAcc.Nonce == 0 {
					nextAcc.Nonce = 1
					needsPut = true
				}
			}
		}
		if !exists && !needsPut {
			continue
		}
		if needsPut {
			enc1 := accounts.SerialiseV3(&nextAcc)
			if err := domains.DomainPut(kv.AccountsDomain, rs.tx, addrBytes, enc1, txTask.TxNum, enc0, step0); err != nil {
				return err
			}
			if traceApply || isBadRootAccount(addr) {
				log.Warn("state apply synthesized account for touched contract state",
					"block", txTask.BlockNum,
					"tx_index", txTask.TxIndex,
					"tx_num", txTask.TxNum,
					"addr", addr.Hex(),
					"account_previously_present", exists,
					"code_touched", touched.codeTouched,
					"storage_touched", touched.storageTouched,
					"nonce", nextAcc.Nonce,
					"balance", nextAcc.Balance.ToBig().String(),
					"code_hash", nextAcc.CodeHash.Hex(),
					"root", nextAcc.Root.Hex(),
				)
			}
		}
	}

	if traceApply {
		for _, addr := range []common.Address{mdbxMigrateApplyTraceAccountProbe, mdbxMigrateApplyTraceStorageProbeAddr} {
			var finalAcc accounts.Account
			exists, enc, step, err := readApplyTraceAccount(domains, rs.tx, addr, &finalAcc)
			if err != nil {
				log.Warn("state apply final account read failed",
					"block", txTask.BlockNum,
					"tx_index", txTask.TxIndex,
					"tx_num", txTask.TxNum,
					"addr", addr.Hex(),
					"err", err,
				)
				continue
			}
			if !exists {
				log.Warn("state apply final account missing",
					"block", txTask.BlockNum,
					"tx_index", txTask.TxIndex,
					"tx_num", txTask.TxNum,
					"addr", addr.Hex(),
					"enc_len", len(enc),
					"step", step,
				)
			} else {
				log.Warn("state apply final account",
					"block", txTask.BlockNum,
					"tx_index", txTask.TxIndex,
					"tx_num", txTask.TxNum,
					"addr", addr.Hex(),
					"enc_len", len(enc),
					"step", step,
					"nonce", finalAcc.Nonce,
					"balance", finalAcc.Balance.ToBig().String(),
					"code_hash", finalAcc.CodeHash.Hex(),
					"root", finalAcc.Root.Hex(),
				)
			}
			if addr == mdbxMigrateApplyTraceStorageProbeAddr {
				storageRoot, items, err := computeStorageRootFromLatest(domains, rs.tx, addr)
				if err != nil {
					log.Warn("state apply final storage root read failed",
						"block", txTask.BlockNum,
						"tx_index", txTask.TxIndex,
						"tx_num", txTask.TxNum,
						"addr", addr.Hex(),
						"err", err,
					)
				} else {
					log.Warn("state apply final storage root",
						"block", txTask.BlockNum,
						"tx_index", txTask.TxIndex,
						"tx_num", txTask.TxNum,
						"addr", addr.Hex(),
						"storage_items", items,
						"storage_root", storageRoot.Hex(),
					)
				}
			}
		}
	}
	if mdbxMigrateFixEmptyRoot && len(fixEmptyRootAddrs) > 0 {
		for addr := range fixEmptyRootAddrs {
			addrBytes := addr.Bytes()
			logFixedSenderAccountCompare("fix_empty_root_pre", domains, rs.tx, txTask, addr)
			enc0, step0, err := domains.GetLatest(kv.AccountsDomain, rs.tx, addrBytes)
			if err != nil {
				return err
			}
			if len(enc0) == 0 || isAccountTombstone(enc0) {
				continue
			}
			acc.Reset()
			if err := accounts.DeserialiseV3(&acc, enc0); err != nil {
				return err
			}
			if !acc.IsEmptyRoot() {
				continue
			}
			storageRoot, items, err := computeStorageRootFromLatest(domains, rs.tx, addr)
			if err != nil {
				return err
			}
			if items == 0 || storageRoot == acc.Root {
				continue
			}
			acc.Root = storageRoot
			enc1 := accounts.SerialiseV3(&acc)
			if err := domains.DomainPut(kv.AccountsDomain, rs.tx, addrBytes, enc1, txTask.TxNum, enc0, step0); err != nil {
				return err
			}
			if isBadRootAccount(addr) {
				log.Warn("state account fixed empty storage root (bad root watch)",
					"tx_num", txTask.TxNum,
					"block", txTask.BlockNum,
					"tx_index", txTask.TxIndex,
					"addr", addr.Hex(),
					"storage_items", items,
					"storage_root", storageRoot,
					"val_len", len(enc1),
					"val", hexPreviewBytes(enc1, 64),
				)
			}
		}
	}
	if mdbxMigrateKeyTrace && shouldMdbxMigrateStorageTrace(txTask.BlockNum, txTask.TxIndex) {
		for _, key := range mdbxMigrateTraceKeys {
			val, step, err := domains.GetLatest(kv.StorageDomain, rs.tx, key)
			if err != nil {
				log.Warn("mdbx-migrate keytrace final read failed",
					"block", txTask.BlockNum,
					"tx_index", txTask.TxIndex,
					"tx_num", txTask.TxNum,
					"key", fmt.Sprintf("0x%x", key),
					"err", err,
				)
				continue
			}
			log.Info("mdbx-migrate keytrace final",
				"block", txTask.BlockNum,
				"tx_index", txTask.TxIndex,
				"tx_num", txTask.TxNum,
				"key", fmt.Sprintf("0x%x", key),
				"val_len", len(val),
				"val", hexPreviewBytes(val, 64),
				"step", step,
			)
		}
	}
	return nil
}

func (rs *ParallelExecutionState) Domains() *dbstate.SharedDomains {
	return rs.domains
}

func (rs *ParallelExecutionState) TemporalGetter() kv.TemporalGetter {
	return rs.domains.AsGetter(rs.tx)
}

func (rs *ParallelExecutionState) TemporalPutDel() kv.TemporalPutDel {
	return rs.domains.AsPutDel(rs.tx)
}

func (rs *ParallelExecutionState) SetTxNum(txNum, blockNum uint64) {
	rs.domains.SetTxNum(txNum)
	rs.domains.SetBlockNum(blockNum)
}

func (rs *ParallelExecutionState) ApplyState(ctx context.Context, txTask *TxTask) error {
	if txTask.HistoryExecution {
		return nil
	}
	//defer rs.domains.BatchHistoryWriteStart().BatchHistoryWriteEnd()

	if err := rs.applyState(txTask, rs.domains); err != nil {
		return fmt.Errorf("ParallelExecutionState.ApplyState: %w", err)
	}
	returnReadList(txTask.ReadLists)
	returnWriteList(txTask.WriteLists)

	if err := rs.ApplyLogsAndTraces(txTask, rs.domains); err != nil {
		return fmt.Errorf("ParallelExecutionState.ApplyLogsAndTraces: %w", err)
	}

	if (txTask.TxNum+1)%rs.domains.StepSize() == 0 /*&& txTask.TxNum > 0 */ {
		// We do not update txNum before commitment cuz otherwise committed state will be in the beginning of next file, not in the latest.
		// That's why we need to make txnum++ on SeekCommitment to get exact txNum for the latest committed state.
		//fmt.Printf("[commitment] running due to txNum reached aggregation step %d\n", txNum/rs.domains.StepSize())
		_, err := rs.domains.ComputeCommitment(ctx, true, txTask.BlockNum, txTask.TxNum, fmt.Sprintf("applying step %d", txTask.TxNum/rs.domains.StepSize()))
		if err != nil {
			return fmt.Errorf("ParallelExecutionState.ComputeCommitment: %w", err)
		}
	}

	txTask.ReadLists, txTask.WriteLists = nil, nil
	return nil
}

func (rs *ParallelExecutionState) ApplyLogsAndTraces(txTask *TxTask, domains *dbstate.SharedDomains) error {
	shouldLogReceipts := mdbxMigrateShouldLogReceipts(txTask.BlockNum)
	traceApply := shouldMdbxMigrateApplyTrace(txTask)
	for addr := range txTask.TraceFroms {
		if err := domains.IndexAdd(kv.TracesFromIdx, addr[:], txTask.TxNum); err != nil {
			return err
		}
	}

	for addr := range txTask.TraceTos {
		if err := domains.IndexAdd(kv.TracesToIdx, addr[:], txTask.TxNum); err != nil {
			return err
		}
	}

	for _, lg := range txTask.Logs {
		if err := domains.IndexAdd(kv.LogAddrIdx, lg.Address[:], txTask.TxNum); err != nil {
			return err
		}
		for _, topic := range lg.Topics {
			if err := domains.IndexAdd(kv.LogTopicIdx, topic[:], txTask.TxNum); err != nil {
				return err
			}
		}
	}

	if txTask.TxIndex == 0 && strings.EqualFold(os.Getenv("ERIGON_BAD_ROOT_DEBUG"), "true") {
		log.Warn("exec3 receipts cache state",
			"block_number", txTask.BlockNum,
			"txs_in_block", len(txTask.BlockReceipts),
			"persist_rcache", rs.syncCfg.PersistReceiptsCacheV2,
			"should_log_receipts", shouldLogReceipts,
			"tx_num", txTask.TxNum,
		)
	}

	if shouldLogReceipts && !rs.syncCfg.PersistReceiptsCacheV2 && txTask.TxIndex == 0 {
		log.Info("mdbx-migrate receipts cache disabled",
			"block_number", txTask.BlockNum,
			"tx_num", txTask.TxNum,
		)
	}

	if rs.syncCfg.PersistReceiptsCacheV2 {
		var receipt *types.Receipt
		receiptIndexValid := txTask.TxIndex >= 0 && txTask.TxIndex < len(txTask.BlockReceipts)
		if txTask.TxIndex >= 0 && txTask.TxIndex < len(txTask.BlockReceipts) {
			receipt = txTask.BlockReceipts[txTask.TxIndex]
		}
		if traceApply {
			log.Warn("state apply receipts trace",
				"block_number", txTask.BlockNum,
				"tx_index", txTask.TxIndex,
				"tx_num", txTask.TxNum,
				"receipt_index_valid", receiptIndexValid,
				"receipt_nil", receipt == nil,
				"block_receipts_len", len(txTask.BlockReceipts),
				"logs_len", len(txTask.Logs),
			)
		}
		if shouldLogReceipts {
			logsLen := 0
			cumGasUsed := uint64(0)
			firstLogIndex := uint32(0)
			receiptBlockNum := uint64(0)
			receiptTxIndex := uint(0)
			if receipt != nil {
				logsLen = len(receipt.Logs)
				cumGasUsed = receipt.CumulativeGasUsed
				firstLogIndex = receipt.FirstLogIndexWithinBlock
				if receipt.BlockNumber != nil {
					receiptBlockNum = receipt.BlockNumber.Uint64()
				}
				receiptTxIndex = receipt.TransactionIndex
			}
			log.Warn("mdbx-migrate receipts cache write attempt",
				"block_number", txTask.BlockNum,
				"tx_index", txTask.TxIndex,
				"tx_num", txTask.TxNum,
				"receipt_index_valid", receiptIndexValid,
				"receipt_nil", receipt == nil,
				"receipt_block_number", receiptBlockNum,
				"receipt_tx_index", receiptTxIndex,
				"receipt_logs", logsLen,
				"receipt_cum_gas_used", cumGasUsed,
				"receipt_first_log_index", firstLogIndex,
			)
		}
		if err := rawdb.WriteReceiptCacheV2(domains.AsPutDel(rs.tx), receipt, txTask.TxNum); err != nil {
			return err
		}
		if shouldLogReceipts {
			log.Warn("mdbx-migrate receipts cache write done",
				"block_number", txTask.BlockNum,
				"tx_index", txTask.TxIndex,
				"tx_num", txTask.TxNum,
			)
			if txTask.Tx != nil && txTask.TxIndex >= 0 {
				query := rawdb.RCacheV2Query{
					BlockNum:      txTask.BlockNum,
					BlockHash:     txTask.BlockHash,
					TxnHash:       txTask.Tx.Hash(),
					TxNum:         txTask.TxNum,
					DontCalcBloom: true,
				}
				readBackHist, readBackHistOK, readBackHistErr := rawdb.ReadReceiptCacheV2(rs.tx, query)
				readBackLatest, readBackLatestOK, readBackLatestErr := rawdb.ReadReceiptCacheV2Latest(domains.AsGetter(rs.tx), query)
				readBack := readBackHist
				readBackOK := readBackHistOK
				readBackErr := readBackHistErr
				if !readBackOK && readBackLatestOK {
					readBack = readBackLatest
					readBackOK = true
					readBackErr = nil
				}
				readBackLogs := 0
				readBackStatus := uint64(0)
				readBackGasUsed := uint64(0)
				readBackTxIndex := uint(0)
				if readBack != nil {
					readBackLogs = len(readBack.Logs)
					readBackStatus = readBack.Status
					readBackGasUsed = readBack.GasUsed
					readBackTxIndex = readBack.TransactionIndex
				}
				expectedStatus := uint64(0)
				expectedGasUsed := uint64(0)
				expectedLogs := 0
				expectedTxIndex := uint(0)
				if receipt != nil {
					expectedStatus = receipt.Status
					expectedGasUsed = receipt.GasUsed
					expectedLogs = len(receipt.Logs)
					expectedTxIndex = receipt.TransactionIndex
				}
				log.Warn("mdbx-migrate receipts cache write readback",
					"block_number", txTask.BlockNum,
					"tx_index", txTask.TxIndex,
					"tx_num", txTask.TxNum,
					"tx_hash", txTask.Tx.Hash(),
					"readback_ok", readBackOK,
					"readback_err", readBackErr,
					"history_readback_ok", readBackHistOK,
					"history_readback_err", readBackHistErr,
					"history_readback_nil", readBackHist == nil,
					"latest_readback_ok", readBackLatestOK,
					"latest_readback_err", readBackLatestErr,
					"latest_readback_nil", readBackLatest == nil,
					"expected_nil", receipt == nil,
					"readback_nil", readBack == nil,
					"expected_status", expectedStatus,
					"readback_status", readBackStatus,
					"expected_gas_used", expectedGasUsed,
					"readback_gas_used", readBackGasUsed,
					"expected_logs", expectedLogs,
					"readback_logs", readBackLogs,
					"expected_tx_index", expectedTxIndex,
					"readback_tx_index", readBackTxIndex,
				)
			} else {
				log.Warn("mdbx-migrate receipts cache write readback skipped",
					"block_number", txTask.BlockNum,
					"tx_index", txTask.TxIndex,
					"tx_num", txTask.TxNum,
					"tx_nil", txTask.Tx == nil,
				)
			}
		}
	}

	return nil
}

func (rs *ParallelExecutionState) DoneCount() uint64 {
	return execTxsDone.GetValueUint64()
}

func (rs *ParallelExecutionState) SizeEstimate() (r uint64) {
	if rs.domains != nil {
		r += rs.domains.SizeEstimate()
	}
	return r
}

func (rs *ParallelExecutionState) ReadsValid(readLists map[string]*dbstate.KvList) bool {
	return false
}

// StateWriterBufferedV3 - used by parallel workers to accumulate updates and then send them to conflict-resolution.
type StateWriterBufferedV3 struct {
	rs           *ParallelExecutionState
	trace        bool
	writeLists   map[string]*dbstate.KvList
	accountPrevs map[string][]byte
	accountDels  map[string]*accounts.Account
	storagePrevs map[string][]byte
	codePrevs    map[string]uint64
	accumulator  *shards.Accumulator
	txNum        uint64
}

func NewStateWriterBufferedV3(rs *ParallelExecutionState, accumulator *shards.Accumulator) *StateWriterBufferedV3 {
	return &StateWriterBufferedV3{
		rs:          rs,
		writeLists:  newWriteList(),
		accumulator: accumulator,
		//trace:      true,
	}
}

func (w *StateWriterBufferedV3) SetTxNum(txNum uint64) {
	w.txNum = txNum
	w.rs.domains.SetTxNum(txNum)
}
func (w *StateWriterBufferedV3) SetTx(tx kv.Tx) {}

func (w *StateWriterBufferedV3) ResetWriteSet() {
	w.writeLists = newWriteList()
	w.accountPrevs = nil
	w.accountDels = nil
	w.storagePrevs = nil
	w.codePrevs = nil
}

func (w *StateWriterBufferedV3) WriteSet() map[string]*dbstate.KvList {
	return w.writeLists
}

func (w *StateWriterBufferedV3) PrevAndDels() (map[string][]byte, map[string]*accounts.Account, map[string][]byte, map[string]uint64) {
	return w.accountPrevs, w.accountDels, w.storagePrevs, w.codePrevs
}

func (w *StateWriterBufferedV3) UpdateAccountData(address common.Address, original, account *accounts.Account) error {
	logMdbxMigrateAccountTrace("put", w.txNum, address, original, account)
	if shouldTraceApplyAccount(address) {
		fields := []interface{}{
			"tx_num", w.txNum,
			"addr", address.Hex(),
		}
		if original != nil {
			fields = append(fields,
				"orig_nonce", original.Nonce,
				"orig_balance", original.Balance.ToBig().String(),
				"orig_root", original.Root.Hex(),
			)
		}
		if account != nil {
			fields = append(fields,
				"new_nonce", account.Nonce,
				"new_balance", account.Balance.ToBig().String(),
				"new_root", account.Root.Hex(),
			)
		}
		log.Warn("state writer buffered updateAccountData", fields...)
	}
	if w.trace {
		fmt.Printf("acc %x: {Balance: %d, Nonce: %d, Inc: %d, CodeHash: %x}\n", address, &account.Balance, account.Nonce, account.Incarnation, account.CodeHash)
	}
	if original.Incarnation > account.Incarnation {
		//del, before create: to clanup code/storage
		if err := w.rs.domains.DomainDel(kv.CodeDomain, w.rs.tx, address[:], w.txNum, nil, 0); err != nil {
			return err
		}

		if err := w.rs.domains.IteratePrefix(kv.StorageDomain, address[:], w.rs.tx, func(k, v []byte, step kv.Step) (bool, error) {
			w.writeLists[kv.StorageDomain.String()].Push(string(k), nil)
			return true, nil
		}); err != nil {
			return err
		}
	}
	value := accounts.SerialiseV3(account)
	if w.accumulator != nil {
		w.accumulator.ChangeAccount(address, account.Incarnation, value)
	}
	w.writeLists[kv.AccountsDomain.String()].Push(string(address[:]), value)

	return nil
}

func (w *StateWriterBufferedV3) UpdateAccountCode(address common.Address, incarnation uint64, codeHash common.Hash, code []byte) error {
	if w.trace {
		fmt.Printf("code: %x, %x, valLen: %d\n", address.Bytes(), codeHash, len(code))
	}
	if w.accumulator != nil {
		w.accumulator.ChangeCode(address, incarnation, code)
	}
	w.writeLists[kv.CodeDomain.String()].Push(string(address[:]), code)
	return nil
}

func (w *StateWriterBufferedV3) DeleteAccount(address common.Address, original *accounts.Account) error {
	keepEmptyRuntime := shouldKeepEmptyAccount(address)
	if shouldTraceApplyAccount(address) {
		_, keepDefaultHit := arbosKeepEmptyAccounts[address]
		_, keepListHit := keepEmptyAccountsList[address]
		fields := []interface{}{
			"tx_num", w.txNum,
			"addr", address.Hex(),
			"keep_empty", shouldKeepEmptyAccount(address),
			"keep_empty_explicit_only", keepEmptyRuntime,
			"keep_empty_global", keepEmptyAccounts,
			"keep_empty_default_addrs", keepEmptyAccountsDefaultAddrs,
			"keep_empty_default_hit", keepDefaultHit,
			"keep_empty_list_len", len(keepEmptyAccountsList),
			"keep_empty_list_hit", keepListHit,
		}
		if original != nil {
			fields = append(fields,
				"orig_nonce", original.Nonce,
				"orig_balance", original.Balance.ToBig().String(),
				"orig_incarnation", original.Incarnation,
				"orig_code_hash", original.CodeHash.Hex(),
				"orig_root", original.Root.Hex(),
				"orig_empty", original.Nonce == 0 && original.Balance.IsZero() && original.IsEmptyCodeHash(),
			)
		} else {
			fields = append(fields, "orig_nil", true)
		}
		log.Warn("state writer deleteAccount request", fields...)
	}
	if keepEmptyRuntime && (original == nil || (original.Nonce == 0 && original.Balance.IsZero() && original.IsEmptyCodeHash())) {
		// Keep-empty behavior follows runtime + migration keep-empty configuration.
		// Important: when the account did not previously exist, a no-op here would keep it
		// absent and diverge from Nitro on chains that require touched-empty marker accounts.
		// Persist canonical empty-account encoding instead of dropping to nil.
		keepVal := common.Copy(emptyAccountEncoding)
		if w.accumulator != nil {
			w.accumulator.ChangeAccount(address, 0, keepVal)
		}
		w.writeLists[kv.AccountsDomain.String()].Push(string(address[:]), keepVal)
		if mdbxMigrateAccountTrace && isMdbxMigrateTraceAccount(address) {
			fields := []interface{}{
				"action", "put_keep_empty",
				"tx_num", w.txNum,
				"addr", address.Hex(),
				"val_len", len(keepVal),
			}
			if original != nil {
				fields = append(fields,
					"orig_nonce", original.Nonce,
					"orig_balance", original.Balance.ToBig().String(),
					"orig_incarnation", original.Incarnation,
					"orig_code_hash", original.CodeHash.Hex(),
					"orig_root", original.Root.Hex(),
				)
			}
			log.Info("mdbx-migrate accountdelete", fields...)
		}
		return nil
	}
	logMdbxMigrateAccountTrace("del", w.txNum, address, original, nil)
	if w.trace {
		fmt.Printf("del acc: %x\n", address)
	}
	if w.accumulator != nil {
		w.accumulator.DeleteAccount(address)
	}
	w.writeLists[kv.AccountsDomain.String()].Push(string(address.Bytes()), nil)

	//if err := w.rs.domains.DomainDelPrefix(kv.StorageDomain, address[:]); err != nil {
	//	return err
	//}
	//commitment delete already has been applied via account
	//if err := w.rs.domains.DomainDel(kv.CodeDomain, address[:], nil, nil, 0); err != nil {
	//	return err
	//}

	return nil
}

func (w *StateWriterBufferedV3) WriteAccountStorage(address common.Address, incarnation uint64, key common.Hash, original, value uint256.Int) error {
	if original == value {
		return nil
	}
	composite := append(address[:], key.Bytes()...)
	if mdbxMigrateKeyTrace && isMdbxMigrateTraceKey(composite) {
		v := value.Bytes()
		op := "put"
		if len(v) == 0 {
			op = "del"
		}
		log.Info("mdbx-migrate keytrace",
			"op", op,
			"domain", kv.StorageDomain.String(),
			"tx_num", w.rs.domains.TxNum(),
			"key", fmt.Sprintf("0x%x", composite),
			"val_len", len(v),
			"val", hexPreviewBytes(v, 64),
		)
	}
	compositeS := string(composite)
	w.writeLists[kv.StorageDomain.String()].Push(compositeS, value.Bytes())
	if w.trace {
		fmt.Printf("storage: %x,%x,%x\n", address, key, value.Bytes())
	}
	if w.accumulator != nil {
		v := value.Bytes()
		w.accumulator.ChangeStorage(address, incarnation, key, v)
	}
	return nil
}

func (w *StateWriterBufferedV3) CreateContract(address common.Address) error {
	if w.trace {
		fmt.Printf("create contract: %x\n", address)
	}
	if fastCreate {
		return nil
	}
	// Keep buffered writer semantics aligned with Writer.CreateContract():
	// contract creation must start from clean storage/code even if dangling rows
	// exist without a corresponding account record.
	if err := w.rs.domains.IteratePrefix(kv.StorageDomain, address[:], w.rs.tx, func(k, v []byte, step kv.Step) (bool, error) {
		w.writeLists[kv.StorageDomain.String()].Push(string(common.Copy(k)), nil)
		return true, nil
	}); err != nil {
		return err
	}
	w.writeLists[kv.CodeDomain.String()].Push(string(address[:]), nil)
	return nil
}

// Writer - used by parallel workers to accumulate updates and then send them to conflict-resolution.
type Writer struct {
	tx          kv.TemporalPutDel
	trace       bool
	accumulator *shards.Accumulator
	txNum       uint64
	writeLists  map[string]*dbstate.KvList
}

func NewWriter(tx kv.TemporalPutDel, accumulator *shards.Accumulator, txNum uint64) *Writer {
	writer := &Writer{
		tx:          tx,
		accumulator: accumulator,
		txNum:       txNum,
		//trace: true,
	}
	if mdbxMigrateDebugWriteSet {
		writer.writeLists = newWriteList()
	}
	return writer
}

func (w *Writer) SetTxNum(v uint64) { w.txNum = v }
func (w *Writer) ResetWriteSet() {
	if w.writeLists != nil {
		w.writeLists = newWriteList()
	}
}

func (w *Writer) WriteSet() map[string]*dbstate.KvList {
	return w.writeLists
}

func (w *Writer) PrevAndDels() (map[string][]byte, map[string]*accounts.Account, map[string][]byte, map[string]uint64) {
	return nil, nil, nil, nil
}

func (w *Writer) UpdateAccountData(address common.Address, original, account *accounts.Account) error {
	logMdbxMigrateAccountTrace("put", w.txNum, address, original, account)
	if shouldTraceApplyAccount(address) {
		fields := []interface{}{
			"tx_num", w.txNum,
			"addr", address.Hex(),
		}
		if original != nil {
			fields = append(fields,
				"orig_nonce", original.Nonce,
				"orig_balance", original.Balance.ToBig().String(),
				"orig_root", original.Root.Hex(),
			)
		}
		if account != nil {
			fields = append(fields,
				"new_nonce", account.Nonce,
				"new_balance", account.Balance.ToBig().String(),
				"new_root", account.Root.Hex(),
			)
		}
		log.Warn("state writer direct updateAccountData", fields...)
	}
	if w.trace {
		fmt.Printf("acc %x: {Balance: %d, Nonce: %d, Inc: %d, CodeHash: %x}\n", address, &account.Balance, account.Nonce, account.Incarnation, account.CodeHash)
	}
	if original.Incarnation > account.Incarnation {
		//del, before create: to clanup code/storage
		if err := w.tx.DomainDel(kv.CodeDomain, address[:], w.txNum, nil, 0); err != nil {
			return err
		}
		if w.writeLists != nil {
			w.writeLists[kv.CodeDomain.String()].Push(string(address[:]), nil)
		}
		if err := w.tx.DomainDelPrefix(kv.StorageDomain, address[:], w.txNum); err != nil {
			return err
		}
		if w.writeLists != nil {
			w.writeLists[kv.StorageDomain.String()].Push(string(address[:]), nil)
		}
	}
	value := accounts.SerialiseV3(account)
	if w.accumulator != nil {
		w.accumulator.ChangeAccount(address, account.Incarnation, value)
	}

	if err := w.tx.DomainPut(kv.AccountsDomain, address[:], value, w.txNum, nil, 0); err != nil {
		return err
	}
	if w.writeLists != nil {
		w.writeLists[kv.AccountsDomain.String()].Push(string(address[:]), value)
	}
	return nil
}

func (w *Writer) UpdateAccountCode(address common.Address, incarnation uint64, codeHash common.Hash, code []byte) error {
	if w.trace {
		fmt.Printf("code: %x, %x, valLen: %d\n", address.Bytes(), codeHash, len(code))
	}
	if err := w.tx.DomainPut(kv.CodeDomain, address[:], code, w.txNum, nil, 0); err != nil {
		return err
	}
	if w.writeLists != nil {
		w.writeLists[kv.CodeDomain.String()].Push(string(address[:]), code)
	}
	if w.accumulator != nil {
		w.accumulator.ChangeCode(address, incarnation, code)
	}
	return nil
}

func (w *Writer) DeleteAccount(address common.Address, original *accounts.Account) error {
	keepEmptyRuntime := shouldKeepEmptyAccount(address)
	if shouldTraceApplyAccount(address) {
		_, keepDefaultHit := arbosKeepEmptyAccounts[address]
		_, keepListHit := keepEmptyAccountsList[address]
		fields := []interface{}{
			"tx_num", w.txNum,
			"addr", address.Hex(),
			"keep_empty", shouldKeepEmptyAccount(address),
			"keep_empty_explicit_only", keepEmptyRuntime,
			"keep_empty_global", keepEmptyAccounts,
			"keep_empty_default_addrs", keepEmptyAccountsDefaultAddrs,
			"keep_empty_default_hit", keepDefaultHit,
			"keep_empty_list_len", len(keepEmptyAccountsList),
			"keep_empty_list_hit", keepListHit,
		}
		if original != nil {
			fields = append(fields,
				"orig_nonce", original.Nonce,
				"orig_balance", original.Balance.ToBig().String(),
				"orig_incarnation", original.Incarnation,
				"orig_code_hash", original.CodeHash.Hex(),
				"orig_root", original.Root.Hex(),
				"orig_empty", original.Nonce == 0 && original.Balance.IsZero() && original.IsEmptyCodeHash(),
			)
		} else {
			fields = append(fields, "orig_nil", true)
		}
		log.Warn("state writer deleteAccount request", fields...)
	}
	if keepEmptyRuntime && (original == nil || (original.Nonce == 0 && original.Balance.IsZero() && original.IsEmptyCodeHash())) {
		// Keep-empty behavior follows runtime + migration keep-empty configuration.
		// Important: when the account did not previously exist, a no-op here would keep it
		// absent and diverge from Nitro on chains that require touched-empty marker accounts.
		// Persist canonical empty-account encoding instead of deleting.
		keepVal := common.Copy(emptyAccountEncoding)
		if err := w.tx.DomainPut(kv.AccountsDomain, address[:], keepVal, w.txNum, nil, 0); err != nil {
			return err
		}
		if w.writeLists != nil {
			w.writeLists[kv.AccountsDomain.String()].Push(string(address[:]), keepVal)
		}
		if w.accumulator != nil {
			w.accumulator.ChangeAccount(address, 0, keepVal)
		}
		if mdbxMigrateAccountTrace && isMdbxMigrateTraceAccount(address) {
			fields := []interface{}{
				"action", "put_keep_empty",
				"tx_num", w.txNum,
				"addr", address.Hex(),
				"val_len", len(keepVal),
			}
			if original != nil {
				fields = append(fields,
					"orig_nonce", original.Nonce,
					"orig_balance", original.Balance.ToBig().String(),
					"orig_incarnation", original.Incarnation,
					"orig_code_hash", original.CodeHash.Hex(),
					"orig_root", original.Root.Hex(),
				)
			}
			log.Info("mdbx-migrate accountdelete", fields...)
		}
		return nil
	}
	logMdbxMigrateAccountTrace("del", w.txNum, address, original, nil)
	if w.trace {
		fmt.Printf("del acc: %x\n", address)
	}
	//TODO: move logic from SD
	//if err := w.tx.DomainDelPrefix(kv.StorageDomain, address[:]); err != nil {
	//	return err
	//}
	//if err := w.tx.DomainDel(kv.CodeDomain, address[:], nil, 0); err != nil {
	//	return err
	//}
	if err := w.tx.DomainDel(kv.AccountsDomain, address[:], w.txNum, nil, 0); err != nil {
		return err
	}
	if w.writeLists != nil {
		w.writeLists[kv.AccountsDomain.String()].Push(string(address[:]), nil)
	}
	// if w.accumulator != nil { TODO: investigate later. basically this will always panic. keeping this out should be fine anyway.
	// 	w.accumulator.DeleteAccount(address)
	// }
	return nil
}

func (w *Writer) WriteAccountStorage(address common.Address, incarnation uint64, key common.Hash, original, value uint256.Int) error {
	if original == value {
		return nil
	}
	composite := append(address[:], key.Bytes()...)
	v := value.Bytes()
	if mdbxMigrateKeyTrace && isMdbxMigrateTraceKey(composite) {
		op := "put"
		if len(v) == 0 {
			op = "del"
		}
		log.Info("mdbx-migrate keytrace",
			"op", op,
			"domain", kv.StorageDomain.String(),
			"tx_num", w.txNum,
			"key", fmt.Sprintf("0x%x", composite),
			"val_len", len(v),
			"val", hexPreviewBytes(v, 64),
		)
	}
	if w.trace {
		fmt.Printf("storage: %x,%x,%x\n", address, key, v)
	}
	if len(v) == 0 {
		if err := w.tx.DomainDel(kv.StorageDomain, composite, w.txNum, nil, 0); err != nil {
			return err
		}
		if w.writeLists != nil {
			w.writeLists[kv.StorageDomain.String()].Push(string(composite), nil)
		}
		return nil
	}
	if w.accumulator != nil {
		w.accumulator.ChangeStorage(address, incarnation, key, v)
	}

	if err := w.tx.DomainPut(kv.StorageDomain, composite, v, w.txNum, nil, 0); err != nil {
		return err
	}
	if w.writeLists != nil {
		w.writeLists[kv.StorageDomain.String()].Push(string(composite), v)
	}
	return nil
}

var fastCreate = dbg.EnvBool("FAST_CREATE", false)

func (w *Writer) CreateContract(address common.Address) error {
	if w.trace {
		fmt.Printf("create contract: %x\n", address)
	}
	if fastCreate {
		return nil
	}
	if err := w.tx.DomainDelPrefix(kv.StorageDomain, address[:], w.txNum); err != nil {
		return err
	}
	if w.writeLists != nil {
		w.writeLists[kv.StorageDomain.String()].Push(string(address[:]), nil)
	}
	return nil
}

type ReaderV3 struct {
	txNum     uint64
	trace     bool
	tx        kv.TemporalGetter
	composite []byte
}

func NewReaderV3(tx kv.TemporalGetter) *ReaderV3 {
	return &ReaderV3{
		tx:        tx,
		composite: make([]byte, 20+32),
	}
}

func (r *ReaderV3) DiscardReadList()                    {}
func (r *ReaderV3) SetTxNum(txNum uint64)               { r.txNum = txNum }
func (r *ReaderV3) SetTx(tx kv.TemporalTx)              {}
func (r *ReaderV3) ReadSet() map[string]*dbstate.KvList { return nil }
func (r *ReaderV3) SetTrace(trace bool)                 { r.trace = trace }
func (r *ReaderV3) ResetReadSet()                       {}

func (r *ReaderV3) HasStorage(address common.Address) (bool, error) {
	if r.tx != nil {
		if txWithCursor, ok := r.tx.(cursorTx); ok {
			hasStorage, err := hasStorageForAddr(txWithCursor, address[:])
			if err != nil {
				return false, err
			}
			return hasStorage, nil
		}
		_, _, hasStorage, err := r.tx.HasPrefix(kv.StorageDomain, address[:])
		if err != nil {
			return false, err
		}
		return hasStorage, nil
	}
	return false, nil
}

func (r *ReaderV3) ReadAccountData(address common.Address) (*accounts.Account, error) {
	enc, _, err := r.tx.GetLatest(kv.AccountsDomain, address[:])
	if err != nil {
		return nil, err
	}
	if len(enc) == 0 {
		if r.trace {
			fmt.Printf("ReadAccountData [%x] => [empty], txNum: %d\n", address, r.txNum)
		}
		return nil, nil
	}

	var acc accounts.Account
	if err := accounts.DeserialiseV3(&acc, enc); err != nil {
		return nil, err
	}
	if r.trace {
		fmt.Printf("ReadAccountData [%x] => [nonce: %d, balance: %d, codeHash: %x], txNum: %d\n", address, acc.Nonce, &acc.Balance, acc.CodeHash, r.txNum)
	}
	return &acc, nil
}

func (r *ReaderV3) ReadAccountDataForDebug(address common.Address) (*accounts.Account, error) {
	return r.ReadAccountData(address)
}

func (r *ReaderV3) ReadAccountStorage(address common.Address, key common.Hash) (uint256.Int, bool, error) {
	r.composite = append(append(r.composite[:0], address[:]...), key[:]...)
	enc, _, err := r.tx.GetLatest(kv.StorageDomain, r.composite)
	var res uint256.Int

	if err != nil {
		return res, false, err
	}
	if r.trace {
		if enc == nil {
			fmt.Printf("ReadAccountStorage [%x] => [empty], txNum: %d\n", r.composite, r.txNum)
		} else {
			fmt.Printf("ReadAccountStorage [%x] => [%x], txNum: %d\n", r.composite, enc, r.txNum)
		}
	}

	ok := enc != nil
	if ok {
		(&res).SetBytes(enc)
	}
	return res, ok, err
}

func (r *ReaderV3) ReadAccountCode(address common.Address) ([]byte, error) {
	enc, _, err := r.tx.GetLatest(kv.CodeDomain, address[:])
	if err != nil {
		return nil, err
	}
	if r.trace {
		fmt.Printf("ReadAccountCode [%x] => [%x], txNum: %d\n", address, enc, r.txNum)
	}
	return enc, nil
}

func (r *ReaderV3) ReadAccountCodeSize(address common.Address) (int, error) {
	enc, _, err := r.tx.GetLatest(kv.CodeDomain, address[:])
	if err != nil {
		return 0, err
	}
	size := len(enc)
	if r.trace {
		fmt.Printf("ReadAccountCodeSize [%x] => [%d], txNum: %d\n", address, size, r.txNum)
	}
	return size, nil
}

func (r *ReaderV3) ReadAccountIncarnation(address common.Address) (uint64, error) {
	return 0, nil
}

type ReaderParallelV3 struct {
	txNum     uint64
	trace     bool
	sd        *dbstate.SharedDomains
	tx        kv.TemporalTx
	composite []byte

	discardReadList bool
	readLists       map[string]*dbstate.KvList
}

func NewReaderParallelV3(sd *dbstate.SharedDomains) *ReaderParallelV3 {
	return &ReaderParallelV3{
		//trace:     true,
		sd:        sd,
		readLists: newReadList(),
		composite: make([]byte, 20+32),
	}
}

func (r *ReaderParallelV3) DiscardReadList()                    { r.discardReadList = true }
func (r *ReaderParallelV3) SetTxNum(txNum uint64)               { r.txNum = txNum }
func (r *ReaderParallelV3) SetTx(tx kv.TemporalTx)              { r.tx = tx }
func (r *ReaderParallelV3) ReadSet() map[string]*dbstate.KvList { return r.readLists }
func (r *ReaderParallelV3) SetTrace(trace bool)                 { r.trace = trace }
func (r *ReaderParallelV3) ResetReadSet()                       { r.readLists = newReadList() }

func (r *ReaderParallelV3) HasStorage(address common.Address) (bool, error) {
	if r.tx == nil {
		return false, nil
	}
	if txWithCursor, ok := r.tx.(cursorTx); ok {
		return hasStorageForAddr(txWithCursor, address[:])
	}
	firstK, firstV, hasStorage, err := r.sd.HasPrefix(kv.StorageDomain, address[:], r.tx)
	if err != nil {
		return false, err
	}
	if !r.discardReadList {
		r.readLists[kv.StorageDomain.String()].Push(string(firstK), firstV)
	}
	return hasStorage, nil
}

func (r *ReaderParallelV3) ReadAccountData(address common.Address) (*accounts.Account, error) {
	enc, _, err := r.sd.GetLatest(kv.AccountsDomain, r.tx, address[:])
	if err != nil {
		return nil, err
	}
	if !r.discardReadList {
		// lifecycle of `r.readList` is less than lifecycle of `r.rs` and `r.tx`, also `r.rs` and `r.tx` do store data immutable way
		r.readLists[kv.AccountsDomain.String()].Push(string(address[:]), enc)
	}
	if len(enc) == 0 {
		if r.trace {
			fmt.Printf("ReadAccountData [%x] => [empty], txNum: %d\n", address, r.txNum)
		}
		return nil, nil
	}

	var acc accounts.Account
	if err := accounts.DeserialiseV3(&acc, enc); err != nil {
		return nil, err
	}
	if r.trace {
		fmt.Printf("ReadAccountData [%x] => [nonce: %d, balance: %d, codeHash: %x], txNum: %d\n", address, acc.Nonce, &acc.Balance, acc.CodeHash, r.txNum)
	}
	return &acc, nil
}

// ReadAccountDataForDebug - is like ReadAccountData, but without adding key to `readList`.
// Used to get `prev` account balance
func (r *ReaderParallelV3) ReadAccountDataForDebug(address common.Address) (*accounts.Account, error) {
	enc, _, err := r.sd.GetLatest(kv.AccountsDomain, r.tx, address[:])
	if err != nil {
		return nil, err
	}
	if len(enc) == 0 {
		if r.trace {
			fmt.Printf("ReadAccountData [%x] => [empty], txNum: %d\n", address, r.txNum)
		}
		return nil, nil
	}

	var acc accounts.Account
	if err := accounts.DeserialiseV3(&acc, enc); err != nil {
		return nil, err
	}
	if r.trace {
		fmt.Printf("ReadAccountData [%x] => [nonce: %d, balance: %d, codeHash: %x], txNum: %d\n", address, acc.Nonce, &acc.Balance, acc.CodeHash, r.txNum)
	}
	return &acc, nil
}

func (r *ReaderParallelV3) ReadAccountStorage(address common.Address, key common.Hash) (uint256.Int, bool, error) {
	r.composite = append(append(r.composite[:0], address[:]...), key[:]...)
	enc, _, err := r.sd.GetLatest(kv.StorageDomain, r.tx, r.composite)
	if err != nil {
		return uint256.Int{}, false, err
	}
	if !r.discardReadList {
		r.readLists[kv.StorageDomain.String()].Push(string(r.composite), enc)
	}
	if r.trace {
		if enc == nil {
			fmt.Printf("ReadAccountStorage [%x] => [empty], txNum: %d\n", r.composite, r.txNum)
		} else {
			fmt.Printf("ReadAccountStorage [%x] => [%x], txNum: %d\n", r.composite, enc, r.txNum)
		}
	}
	var res uint256.Int
	(&res).SetBytes(enc)
	return res, true, nil
}

func (r *ReaderParallelV3) ReadAccountCode(address common.Address) ([]byte, error) {
	enc, _, err := r.sd.GetLatest(kv.CodeDomain, r.tx, address[:])
	if err != nil {
		return nil, err
	}

	if !r.discardReadList {
		r.readLists[kv.CodeDomain.String()].Push(string(address[:]), enc)
	}
	if r.trace {
		fmt.Printf("ReadAccountCode [%x] => [%x], txNum: %d\n", address, enc, r.txNum)
	}
	return enc, nil
}

func (r *ReaderParallelV3) ReadAccountCodeSize(address common.Address) (int, error) {
	enc, _, err := r.sd.GetLatest(kv.CodeDomain, r.tx, address[:])
	if err != nil {
		return 0, err
	}
	if !r.discardReadList {
		var sizebuf [8]byte
		binary.BigEndian.PutUint64(sizebuf[:], uint64(len(enc)))
		r.readLists[dbstate.CodeSizeTableFake].Push(string(address[:]), sizebuf[:])
	}
	size := len(enc)
	if r.trace {
		fmt.Printf("ReadAccountCodeSize [%x] => [%d], txNum: %d\n", address, size, r.txNum)
	}
	return size, nil
}

func (r *ReaderParallelV3) ReadAccountIncarnation(address common.Address) (uint64, error) {
	return 0, nil
}

var writeListPool = sync.Pool{
	New: func() any {
		return map[string]*dbstate.KvList{
			kv.AccountsDomain.String(): {},
			kv.StorageDomain.String():  {},
			kv.CodeDomain.String():     {},
		}
	},
}

func newWriteList() map[string]*dbstate.KvList {
	v := writeListPool.Get().(map[string]*dbstate.KvList)
	for _, tbl := range v {
		tbl.Keys, tbl.Vals = tbl.Keys[:0], tbl.Vals[:0]
	}
	return v
	//return writeListPool.Get().(map[string]*dbstate.KvList)
}
func returnWriteList(v map[string]*dbstate.KvList) {
	if v == nil {
		return
	}
	//for _, tbl := range v {
	//	clear(tbl.Keys)
	//	clear(tbl.Vals)
	//	tbl.Keys, tbl.Vals = tbl.Keys[:0], tbl.Vals[:0]
	//}
	writeListPool.Put(v)
}

var readListPool = sync.Pool{
	New: func() any {
		return map[string]*dbstate.KvList{
			kv.AccountsDomain.String(): {},
			kv.CodeDomain.String():     {},
			dbstate.CodeSizeTableFake:  {},
			kv.StorageDomain.String():  {},
		}
	},
}

func newReadList() map[string]*dbstate.KvList {
	v := readListPool.Get().(map[string]*dbstate.KvList)
	for _, tbl := range v {
		tbl.Keys, tbl.Vals = tbl.Keys[:0], tbl.Vals[:0]
	}
	return v
	//return readListPool.Get().(map[string]*dbstate.KvList)
}
func returnReadList(v map[string]*dbstate.KvList) {
	if v == nil {
		return
	}
	//for _, tbl := range v {
	//	clear(tbl.Keys)
	//	clear(tbl.Vals)
	//	tbl.Keys, tbl.Vals = tbl.Keys[:0], tbl.Vals[:0]
	//}
	readListPool.Put(v)
}
