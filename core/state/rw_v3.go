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
	"github.com/erigontech/erigon/execution/types"
	"github.com/erigontech/erigon/execution/types/accounts"
	"github.com/erigontech/erigon/turbo/shards"
)

var execTxsDone = metrics.NewCounter(`exec_txs_done`)
var mdbxMigrateReceiptsDebug = dbg.EnvBool("MDBX_MIGRATE_DEBUG", false)
var mdbxMigrateReceiptsDebugBlockRaw = dbg.EnvString("MDBX_MIGRATE_DEBUG_BLOCK", "")
var mdbxMigrateReceiptsDebugBlock = dbg.EnvUint("MDBX_MIGRATE_DEBUG_BLOCK", 0)
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
var mdbxMigrateTraceKeys = [][]byte{
	common.FromHex("0xa4b05fffffffffffffffffffffffffffffffffff3c79da47f96b0f39664f73c0a1f350580be90742947dddfa21ba64d578dfe600"),
	common.FromHex("0xa4b05fffffffffffffffffffffffffffffffffff33f46529933152e1782e51b69b5bebb0810705b1e56844f07ef4225ddbc0d700"),
	common.FromHex("0xa4b05fffffffffffffffffffffffffffffffffff1c2916348c6a2141e372f746967464575851d1fd7b468e88ffde720bb27f0f00"),
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
		fields = append(fields,
			"orig_nonce", original.Nonce,
			"orig_balance", original.Balance.ToBig().String(),
			"orig_incarnation", original.Incarnation,
			"orig_code_hash", original.CodeHash.Hex(),
			"orig_root", original.Root.Hex(),
		)
	}
	if account != nil {
		fields = append(fields,
			"new_nonce", account.Nonce,
			"new_balance", account.Balance.ToBig().String(),
			"new_incarnation", account.Incarnation,
			"new_code_hash", account.CodeHash.Hex(),
			"new_root", account.Root.Hex(),
		)
	}
	log.Info("mdbx-migrate accounttrace", fields...)
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

	//maps are unordered in Go! don't iterate over it. SharedDomains.deleteAccount will call GetLatest(Code) and expecting it not been delete yet
	if txTask.WriteLists != nil {
		for _, domain := range []kv.Domain{kv.AccountsDomain, kv.CodeDomain, kv.StorageDomain} {
			list, ok := txTask.WriteLists[domain.String()]
			if !ok {
				continue
			}

			for i, key := range list.Keys {
				keyBytes := []byte(key)
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
				if list.Vals[i] == nil {
					if err := domains.DomainDel(domain, rs.tx, keyBytes, txTask.TxNum, nil, 0); err != nil {
						return err
					}
				} else {
					if err := domains.DomainPut(domain, rs.tx, keyBytes, list.Vals[i], txTask.TxNum, nil, 0); err != nil {
						return err
					}
				}
			}
		}
	}

	for addr, increase := range txTask.BalanceIncreaseSet {
		increase := increase
		emptyRemoval := txTask.Rules.IsSpuriousDragon && !increase.IsEscrow
		addrBytes := addr.Bytes()
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
		var origAcc *accounts.Account
		if mdbxMigrateAccountTrace && isMdbxMigrateTraceAccount(addr) {
			orig := acc
			origAcc = &orig
		}
		acc.Balance.Add(&acc.Balance, &increase.Amount)
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
			log.Info("mdbx-migrate receipts cache write",
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

func (w *StateWriterBufferedV3) SetTxNum(ctx context.Context, txNum uint64) {
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

	//seems don't need delete code here - tests starting fail
	//err := w.rs.domains.IteratePrefix(kv.StorageDomain, address[:], func(k, v []byte) error {
	//	w.writeLists[string(kv.StorageDomain)].Push(string(k), nil)
	//	return nil
	//})
	//if err != nil {
	//	return err
	//}
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
	_, _, hasStorage, err := r.tx.HasPrefix(kv.StorageDomain, address[:])
	return hasStorage, err
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
