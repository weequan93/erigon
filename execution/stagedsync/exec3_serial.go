package stagedsync

import (
	"context"
	"errors"
	"fmt"
	"os"
	"strconv"
	"time"

	"github.com/erigontech/erigon-lib/log/v3"
	"github.com/erigontech/erigon/core"
	"github.com/erigontech/erigon/core/state"
	"github.com/erigontech/erigon/db/kv"
	"github.com/erigontech/erigon/db/rawdb/rawtemporaldb"
	dbstate "github.com/erigontech/erigon/db/state"
	"github.com/erigontech/erigon/execution/consensus"
	"github.com/erigontech/erigon/execution/tests/chaos_monkey"
	"github.com/erigontech/erigon/execution/types"
)

type serialExecutor struct {
	txExecutor
	skipPostEvaluation bool
	// outputs
	txCount     uint64
	gasUsed     uint64
	blobGasUsed uint64
}

var (
	mdbxMigrateDebug                                            = envBoolPrefer("ERIGON_MDBX_MIGRATE_DEBUG", "MDBX_MIGRATE_DEBUG")
	mdbxMigrateDebugBlock, mdbxMigrateDebugBlockSet             = parseEnvUintPrefer("ERIGON_MDBX_MIGRATE_DEBUG_BLOCK", "MDBX_MIGRATE_DEBUG_BLOCK")
	mdbxMigrateDebugTxIndex, mdbxMigrateDebugTxSet              = parseEnvIntPrefer("ERIGON_MDBX_MIGRATE_DEBUG_TX_INDEX", "MDBX_MIGRATE_DEBUG_TX_INDEX")
	mdbxMigrateDebugTxData                                      = envBoolPrefer("ERIGON_MDBX_MIGRATE_DEBUG_TX_DATA", "MDBX_MIGRATE_DEBUG_TX_DATA")
	mdbxMigrateDebugWriteSet                                    = envBoolPrefer("ERIGON_MDBX_MIGRATE_DEBUG_WRITESET", "MDBX_MIGRATE_DEBUG_WRITESET")
	mdbxMigrateDebugWriteSetMax, mdbxMigrateDebugWriteSetMaxSet = parseEnvIntPrefer("ERIGON_MDBX_MIGRATE_DEBUG_WRITESET_MAX", "MDBX_MIGRATE_DEBUG_WRITESET_MAX")
)

func parseEnvUint(name string) (uint64, bool) {
	value := os.Getenv(name)
	if value == "" {
		return 0, false
	}
	parsed, err := strconv.ParseUint(value, 10, 64)
	if err != nil {
		log.Warn("mdbx-migrate debug: invalid uint env", "name", name, "value", value, "err", err)
		return 0, false
	}
	return parsed, true
}

func parseEnvUintPrefer(primary, fallback string) (uint64, bool) {
	value := os.Getenv(primary)
	if value == "" {
		return parseEnvUint(fallback)
	}
	parsed, err := strconv.ParseUint(value, 10, 64)
	if err != nil {
		log.Warn("mdbx-migrate debug: invalid uint env", "name", primary, "value", value, "err", err)
		return 0, false
	}
	return parsed, true
}

func parseEnvInt(name string) (int, bool) {
	value := os.Getenv(name)
	if value == "" {
		return 0, false
	}
	parsed, err := strconv.Atoi(value)
	if err != nil {
		log.Warn("mdbx-migrate debug: invalid int env", "name", name, "value", value, "err", err)
		return 0, false
	}
	return parsed, true
}

func parseEnvIntPrefer(primary, fallback string) (int, bool) {
	value := os.Getenv(primary)
	if value == "" {
		return parseEnvInt(fallback)
	}
	parsed, err := strconv.Atoi(value)
	if err != nil {
		log.Warn("mdbx-migrate debug: invalid int env", "name", primary, "value", value, "err", err)
		return 0, false
	}
	return parsed, true
}

func envBoolPrefer(primary, fallback string) bool {
	if os.Getenv(primary) != "" {
		return true
	}
	return os.Getenv(fallback) != ""
}

func mdbxMigrateShouldLog(blockNum uint64, txIndex int) bool {
	if !mdbxMigrateDebug {
		return false
	}
	if mdbxMigrateDebugBlockSet && blockNum != mdbxMigrateDebugBlock {
		return false
	}
	if mdbxMigrateDebugTxSet && txIndex != mdbxMigrateDebugTxIndex {
		return false
	}
	return true
}

func hexPreview(raw []byte, max int) string {
	if len(raw) == 0 || max <= 0 {
		return ""
	}
	if len(raw) <= max {
		return fmt.Sprintf("%x", raw)
	}
	return fmt.Sprintf("%x...len=%d", raw[:max], len(raw))
}

func logMdbxMigrateWriteSet(txTask *state.TxTask, maxEntries int, maxEntriesSet bool) {
	if txTask == nil {
		return
	}
	if txTask.WriteLists == nil && len(txTask.BalanceIncreaseSet) == 0 {
		return
	}

	limit := 50
	if maxEntriesSet && maxEntries > 0 {
		limit = maxEntries
	}

	log.Info("mdbx-migrate writeset",
		"block", txTask.BlockNum,
		"tx_index", txTask.TxIndex,
		"tx_num", txTask.TxNum,
		"limit", limit,
	)

	for _, domain := range []kv.Domain{kv.AccountsDomain, kv.CodeDomain, kv.StorageDomain} {
		list, ok := txTask.WriteLists[domain.String()]
		if !ok || list == nil || list.Len() == 0 {
			continue
		}
		log.Info("mdbx-migrate writeset domain",
			"block", txTask.BlockNum,
			"tx_index", txTask.TxIndex,
			"domain", domain.String(),
			"entries", list.Len(),
		)
		entries := list.Len()
		if entries > limit {
			entries = limit
		}
		for i := 0; i < entries; i++ {
			key := []byte(list.Keys[i])
			val := list.Vals[i]
			log.Info("mdbx-migrate writeset entry",
				"block", txTask.BlockNum,
				"tx_index", txTask.TxIndex,
				"domain", domain.String(),
				"idx", i,
				"key_len", len(key),
				"key", hexPreview(key, 64),
				"val_len", len(val),
				"val", hexPreview(val, 64),
				"delete", val == nil,
			)
		}
		if list.Len() > entries {
			log.Info("mdbx-migrate writeset truncated",
				"block", txTask.BlockNum,
				"tx_index", txTask.TxIndex,
				"domain", domain.String(),
				"entries", list.Len(),
				"logged", entries,
			)
		}
	}

	if len(txTask.BalanceIncreaseSet) > 0 {
		log.Info("mdbx-migrate balance increases",
			"block", txTask.BlockNum,
			"tx_index", txTask.TxIndex,
			"entries", len(txTask.BalanceIncreaseSet),
		)
		count := 0
		for addr, entry := range txTask.BalanceIncreaseSet {
			log.Info("mdbx-migrate balance increase",
				"block", txTask.BlockNum,
				"tx_index", txTask.TxIndex,
				"address", addr,
				"amount", entry.Amount.ToBig().String(),
				"escrow", entry.IsEscrow,
			)
			count++
			if count >= limit {
				if len(txTask.BalanceIncreaseSet) > count {
					log.Info("mdbx-migrate balance increase truncated",
						"block", txTask.BlockNum,
						"tx_index", txTask.TxIndex,
						"entries", len(txTask.BalanceIncreaseSet),
						"logged", count,
					)
				}
				break
			}
		}
	}
}

func kvListCounts(lists map[string]*dbstate.KvList) (domains int, entries int) {
	for _, list := range lists {
		if list == nil {
			continue
		}
		domains++
		entries += list.Len()
	}
	return domains, entries
}

func (se *serialExecutor) wait() error {
	return nil
}

func (se *serialExecutor) status(ctx context.Context, commitThreshold uint64) error {
	return nil
}

func (se *serialExecutor) execute(ctx context.Context, tasks []*state.TxTask, gp *core.GasPool) (cont bool, err error) {
	for _, txTask := range tasks {
		if txTask.Error != nil {
			return false, nil
		}
		if gp != nil {
			se.applyWorker.SetGaspool(gp)
		}
		se.applyWorker.SetArbitrumWasmDB(se.cfg.arbitrumWasmDB)
		shouldLog := mdbxMigrateShouldLog(txTask.BlockNum, txTask.TxIndex)
		if shouldLog {
			log.Info("mdbx-migrate tx task",
				"block", txTask.BlockNum,
				"tx_index", txTask.TxIndex,
				"tx_num", txTask.TxNum,
				"final", txTask.Final,
				"tx_nil", txTask.Tx == nil,
			)
		}
		se.applyWorker.RunTxTaskNoLock(txTask, se.isMining, se.skipPostEvaluation)
		if shouldLog {
			if txTask.Tx == nil {
				log.Info("mdbx-migrate tx",
					"block", txTask.BlockNum,
					"tx_index", txTask.TxIndex,
					"tx_num", txTask.TxNum,
					"gas_used", txTask.GasUsed,
					"failed", txTask.Failed,
					"tx_nil", true,
				)
			} else {
				from := "<unknown>"
				if sender := txTask.Sender(); sender != nil {
					from = sender.Hex()
				}
				to := "<nil>"
				if toAddr := txTask.Tx.GetTo(); toAddr != nil {
					to = toAddr.Hex()
				}
				value := "<nil>"
				if txValue := txTask.Tx.GetValue(); txValue != nil {
					value = txValue.ToBig().String()
				}
				data := txTask.Tx.GetData()
				dataSig := ""
				if len(data) >= 4 {
					dataSig = fmt.Sprintf("0x%x", data[:4])
				} else if len(data) > 0 {
					dataSig = fmt.Sprintf("0x%x", data)
				}
				writeDomains, writeEntries := kvListCounts(txTask.WriteLists)
				readDomains, readEntries := kvListCounts(txTask.ReadLists)
				log.Info("mdbx-migrate tx",
					"block", txTask.BlockNum,
					"tx_index", txTask.TxIndex,
					"tx_num", txTask.TxNum,
					"hash", txTask.Tx.Hash(),
					"type", txTask.Tx.Type(),
					"from", from,
					"to", to,
					"nonce", txTask.Tx.GetNonce(),
					"gas_limit", txTask.Tx.GetGasLimit(),
					"gas_used", txTask.GasUsed,
					"failed", txTask.Failed,
					"value", value,
					"data_len", len(data),
					"data_sig", dataSig,
					"write_domains", writeDomains,
					"write_entries", writeEntries,
					"read_domains", readDomains,
					"read_entries", readEntries,
				)
				if mdbxMigrateDebugTxData {
					log.Info("mdbx-migrate tx data",
						"block", txTask.BlockNum,
						"tx_index", txTask.TxIndex,
						"tx_num", txTask.TxNum,
						"data_len", len(data),
						"data", fmt.Sprintf("0x%x", data),
					)
				}
			}
			if mdbxMigrateDebugWriteSet {
				logMdbxMigrateWriteSet(txTask, mdbxMigrateDebugWriteSetMax, mdbxMigrateDebugWriteSetMaxSet)
			}
			if txTask.Error == nil && se.doms != nil {
				if sdc := se.doms.GetCommitmentContext(); sdc != nil {
					root, rootErr := sdc.DebugRootHash(ctx, se.execStage.LogPrefix())
					if rootErr != nil {
						log.Warn("mdbx-migrate tx root failed",
							"block", txTask.BlockNum,
							"tx_index", txTask.TxIndex,
							"tx_num", txTask.TxNum,
							"err", rootErr,
						)
					} else {
						log.Info("mdbx-migrate tx root",
							"block", txTask.BlockNum,
							"tx_index", txTask.TxIndex,
							"tx_num", txTask.TxNum,
							"updates", sdc.KeysCount(),
							"root", fmt.Sprintf("0x%x", root),
						)
					}
				}
			}
		}
		if err := func() error {
			if errors.Is(txTask.Error, context.Canceled) {
				return txTask.Error
			}
			if txTask.Error != nil {
				return fmt.Errorf("%w, txnIdx=%d, %v", consensus.ErrInvalidBlock, txTask.TxIndex, txTask.Error) //same as in stage_exec.go
			}

			se.txCount++
			se.gasUsed += txTask.GasUsed
			mxExecGas.Add(float64(txTask.GasUsed))
			mxExecTransactions.Add(1)

			if txTask.Tx != nil {
				se.blobGasUsed += txTask.Tx.GetBlobGas()
			}

			if txTask.Final {
				if !se.isMining && !se.skipPostEvaluation && !se.execStage.CurrentSyncCycle.IsInitialCycle {
					// note this assumes the bloach reciepts is a fixed array shared by
					// all tasks - if that changes this will need to change - robably need to
					// add this to the executor
					if se.cfg.notifications != nil && se.cfg.notifications.RecentLogs != nil {
						se.cfg.notifications.RecentLogs.Add(txTask.BlockReceipts)
					}
				}
				// TODO arbitrum enable receipt checking
				checkReceipts := false //!se.cfg.vmConfig.StatelessExec && se.cfg.chainConfig.IsByzantium(txTask.BlockNum) && !se.cfg.vmConfig.NoReceipts && !se.isMining

				if txTask.BlockNum > 0 && !se.skipPostEvaluation { //Disable check for genesis. Maybe need somehow improve it in future - to satisfy TestExecutionSpec
					if err := core.BlockPostValidation(se.gasUsed, se.blobGasUsed, checkReceipts, txTask.BlockReceipts, txTask.Header, se.isMining, txTask.Txs, se.cfg.chainConfig, se.logger); err != nil {
						return fmt.Errorf("%w, txnIdx=%d, %v", consensus.ErrInvalidBlock, txTask.TxIndex, err) //same as in stage_exec.go
					}
				}

				se.outputBlockNum.SetUint64(txTask.BlockNum)
			}
			if se.cfg.syncCfg.ChaosMonkey {
				chaosErr := chaos_monkey.ThrowRandomConsensusError(se.execStage.CurrentSyncCycle.IsInitialCycle, txTask.TxIndex, se.cfg.badBlockHalt, txTask.Error)
				if chaosErr != nil {
					log.Warn("Monkey in a consensus")
					return chaosErr
				}
			}
			return nil
		}(); err != nil {
			if errors.Is(err, context.Canceled) {
				return false, err
			}
			se.logger.Warn(fmt.Sprintf("[%s] Execution failed", se.execStage.LogPrefix()),
				"block", txTask.BlockNum, "txNum", txTask.TxNum, "header-hash", txTask.Header.Hash().String(), "err", err, "inMem", se.inMemExec)
			if se.cfg.hd != nil && se.cfg.hd.POSSync() && errors.Is(err, consensus.ErrInvalidBlock) {
				se.cfg.hd.ReportBadHeaderPoS(txTask.Header.Hash(), txTask.Header.ParentHash)
			}
			if se.cfg.badBlockHalt {
				return false, err
			}
			if errors.Is(err, consensus.ErrInvalidBlock) {
				if se.u != nil {
					if err := se.u.UnwindTo(txTask.BlockNum-1, BadBlock(txTask.Header.Hash(), err), se.applyTx); err != nil {
						return false, err
					}
				}
			} else {
				if se.u != nil {
					if err := se.u.UnwindTo(txTask.BlockNum-1, ExecUnwind, se.applyTx); err != nil {
						return false, err
					}
				}
			}
			return false, nil
		}

		var logIndexAfterTx uint32
		var cumGasUsed uint64
		if !txTask.Final {
			if txTask.TxIndex >= 0 {
				receipt := txTask.BlockReceipts[txTask.TxIndex]
				if receipt != nil {
					logIndexAfterTx = receipt.FirstLogIndexWithinBlock + uint32(len(txTask.Logs))
					cumGasUsed = receipt.CumulativeGasUsed
				}
			}
		} else {
			if se.cfg.chainConfig.Bor != nil && txTask.TxIndex >= 1 {
				// get last receipt and store the last log index + 1
				lastReceipt := txTask.BlockReceipts[txTask.TxIndex-1]
				if lastReceipt == nil {
					if se.skipPostEvaluation {
						// if we're in the startup block and the last tx has been skilled we'll
						// need to run it as a historic tx to recover its logs
						prevTask := *txTask
						prevTask.TxNum = txTask.TxNum - 1
						prevTask.TxIndex = txTask.TxIndex - 1
						prevTask.Tx = prevTask.Txs[prevTask.TxIndex]
						signer := *types.MakeSigner(se.cfg.chainConfig, prevTask.BlockNum, prevTask.Header.Time)
						prevTask.TxAsMessage, err = prevTask.Tx.AsMessage(signer, prevTask.Header.BaseFee, txTask.Rules)
						if err != nil {
							return false, err
						}
						prevTask.Final = false
						prevTask.HistoryExecution = true
						se.applyWorker.RunTxTaskNoLock(&prevTask, se.isMining, se.skipPostEvaluation)
						if prevTask.Error != nil {
							return false, fmt.Errorf("error while finding last receipt: %w", prevTask.Error)
						}
						prevTask.CreateReceipt(se.applyTx.(kv.TemporalTx))
						lastReceipt = txTask.BlockReceipts[txTask.TxIndex-1]
					} else {
						return false, fmt.Errorf("receipt is nil but should be populated, txIndex=%d, block=%d", txTask.TxIndex-1, txTask.BlockNum)
					}
				}
				if len(lastReceipt.Logs) > 0 {
					firstIndex := lastReceipt.Logs[len(lastReceipt.Logs)-1].Index + 1
					logIndexAfterTx = uint32(firstIndex) + uint32(len(txTask.Logs))
					cumGasUsed = lastReceipt.CumulativeGasUsed
				}
			}
		}
		if !txTask.HistoryExecution {
			if rawtemporaldb.ReceiptStoresFirstLogIdx(se.applyTx.(kv.TemporalTx)) {
				logIndexAfterTx -= uint32(len(txTask.Logs))
			}
			if err := rawtemporaldb.AppendReceipt(se.doms.AsPutDel(se.applyTx.(kv.TemporalTx)), logIndexAfterTx, cumGasUsed, se.blobGasUsed, txTask.TxNum); err != nil {
				return false, err
			}
		}

		// MA applystate
		if err := se.rs.ApplyState(ctx, txTask); err != nil {
			return false, err
		}

		se.outputTxNum.Add(1)
	}

	return true, nil
}

func (se *serialExecutor) commit(ctx context.Context, txNum uint64, blockNum uint64, useExternalTx bool) (t2 time.Duration, err error) {
	se.doms.Close()
	if err = se.execStage.Update(se.applyTx, blockNum); err != nil {
		return 0, err
	}

	se.applyTx.CollectMetrics()

	if !useExternalTx {
		tt := time.Now()
		if err = se.applyTx.Commit(); err != nil {
			return 0, err
		}

		t2 = time.Since(tt)
		se.agg.BuildFilesInBackground(se.outputTxNum.Load())

		se.applyTx, err = se.cfg.db.BeginRw(context.Background()) //nolint
		if err != nil {
			return t2, err
		}
	}
	temporalTx, ok := se.applyTx.(kv.TemporalTx)
	if !ok {
		return t2, errors.New("tx is not a temporal tx")
	}
	se.doms, err = dbstate.NewSharedDomains(temporalTx, se.logger)
	if err != nil {
		return t2, err
	}
	se.doms.SetTxNum(txNum)
	se.rs = state.NewParallelExecutionState(se.doms, se.applyTx, se.cfg.syncCfg, se.cfg.chainConfig.Bor != nil, se.logger)

	se.applyWorker.ResetTx(se.applyTx)
	se.applyWorker.ResetState(se.rs, se.accumulator)

	return t2, nil
}
