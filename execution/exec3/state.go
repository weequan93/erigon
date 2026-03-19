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

package exec3

import (
	"bytes"
	"context"
	"errors"
	"fmt"
	"sync"

	"github.com/holiman/uint256"
	"golang.org/x/sync/errgroup"

	"github.com/offchainlabs/nitro/arbos"
	"github.com/offchainlabs/nitro/arbos/arbosState"
	offchainArbosState "github.com/offchainlabs/nitro/arbos/arbosState"
	"github.com/offchainlabs/nitro/gethhook"

	"github.com/erigontech/erigon-lib/common"
	"github.com/erigontech/erigon-lib/common/dbg"
	"github.com/erigontech/erigon-lib/log/v3"
	"github.com/erigontech/erigon/arb/ethdb/wasmdb"
	"github.com/erigontech/erigon/core"
	"github.com/erigontech/erigon/core/genesiswrite"
	"github.com/erigontech/erigon/core/state"
	"github.com/erigontech/erigon/core/tracing"
	"github.com/erigontech/erigon/core/vm"
	"github.com/erigontech/erigon/core/vm/evmtypes"
	"github.com/erigontech/erigon/db/datadir"
	"github.com/erigontech/erigon/db/kv"
	"github.com/erigontech/erigon/eth/consensuschain"
	"github.com/erigontech/erigon/execution/aa"
	"github.com/erigontech/erigon/execution/chain"
	"github.com/erigontech/erigon/execution/consensus"
	"github.com/erigontech/erigon/execution/exec3/calltracer"
	"github.com/erigontech/erigon/execution/types"
	"github.com/erigontech/erigon/execution/types/accounts"
	"github.com/erigontech/erigon/turbo/services"
	"github.com/erigontech/erigon/turbo/shards"
)

var (
	arbTrace         bool
	badRootDebug     bool
	pathProbeAddr    = common.HexToAddress(dbg.EnvString("ERIGON_PATH_PROBE_ADDR", "0xA4b05FffffFffFFFFfFFfffFfffFFfffFfFfFFFf"))
	accountProbeAddr = common.HexToAddress(dbg.EnvString("ERIGON_ACCOUNT_PROBE_ADDR", "0xA4b000000000000000000073657175656e636572"))
	pathProbeSlot    = common.HexToHash(dbg.EnvString("ERIGON_PATH_PROBE_SLOT", "0x3c79da47f96b0f39664f73c0a1f350580be90742947dddfa21ba64d578dfe623"))
	pathProbeMin     = dbg.EnvUint("ERIGON_PATH_PROBE_MIN_BLOCK", 33)
	pathProbeTxi     = dbg.EnvInt("ERIGON_PATH_PROBE_TX_INDEX", -1)
)

func init() {
	gethhook.RequireHookedGeth()
	arbTrace = dbg.EnvBool("ARB_TRACE", false)
	badRootDebug = dbg.EnvBool("ERIGON_BAD_ROOT_DEBUG", false)
}

type pathProbeReader interface {
	ReadAccountStorage(address common.Address, key common.Hash) (uint256.Int, bool, error)
	ReadAccountDataForDebug(address common.Address) (*accounts.Account, error)
}

func shouldLogRuntimePathProbe(txTask *state.TxTask) bool {
	if !badRootDebug || txTask == nil || txTask.Tx == nil || txTask.TxIndex < 0 || txTask.BlockNum < pathProbeMin {
		return false
	}
	if pathProbeTxi >= 0 && txTask.TxIndex != pathProbeTxi {
		return false
	}
	return true
}

func runtimeHexPreview(raw []byte, max int) string {
	if len(raw) == 0 {
		return "0x"
	}
	if max <= 0 || len(raw) <= max {
		return fmt.Sprintf("0x%x", raw)
	}
	return fmt.Sprintf("0x%x...(+%d bytes)", raw[:max], len(raw)-max)
}

func runtimeDecodeAccountPayload(raw []byte) (nonce uint64, balance string, codeHash string, decodeErr string) {
	if len(raw) == 0 {
		return 0, "0", "0x", ""
	}
	var acc accounts.Account
	acc.Reset()
	if err := accounts.DeserialiseV3(&acc, raw); err != nil {
		return 0, "0", "0x", err.Error()
	}
	return acc.Nonce, acc.Balance.ToBig().String(), acc.CodeHash.Hex(), ""
}

func runtimeDomainsTxNum(rs *state.ParallelExecutionState) uint64 {
	if rs == nil || rs.Domains() == nil {
		return 0
	}
	return rs.Domains().TxNum()
}

func logRuntimeTxBoundary(logger log.Logger, phase string, txTask *state.TxTask, reader state.ResettableStateReader, historyMode bool, domainsTxNum uint64) {
	if logger == nil || !shouldLogRuntimePathProbe(txTask) {
		return
	}
	logger.Warn(
		"exec3: tx boundary",
		"phase", phase,
		"block", txTask.BlockNum,
		"txnum", txTask.TxNum,
		"tx_index", txTask.TxIndex,
		"tx_hash", txTask.Tx.Hash(),
		"history_execution", txTask.HistoryExecution,
		"history_mode", historyMode,
		"doms_txnum", domainsTxNum,
		"reader", fmt.Sprintf("%T", reader),
	)
}

func logRuntimePathProbe(logger log.Logger, phase string, txTask *state.TxTask, reader state.ResettableStateReader, _ *state.IntraBlockState, historyMode bool, domainsTxNum uint64) {
	if logger == nil || !shouldLogRuntimePathProbe(txTask) {
		return
	}
	probeReader, ok := reader.(pathProbeReader)
	if !ok {
		return
	}

	probeVal, probeOK, err := probeReader.ReadAccountStorage(pathProbeAddr, pathProbeSlot)
	if err != nil {
		logger.Warn(
			"exec3: path probe read failed",
			"phase", phase,
			"block", txTask.BlockNum,
			"txnum", txTask.TxNum,
			"tx_index", txTask.TxIndex,
			"tx_hash", txTask.Tx.Hash(),
			"history_mode", historyMode,
			"doms_txnum", domainsTxNum,
			"reader", fmt.Sprintf("%T", reader),
			"probe_addr", pathProbeAddr,
			"probe_slot", pathProbeSlot,
			"err", err,
		)
		return
	}

	probeValHex := "0x"
	if probeOK {
		probeValHex = fmt.Sprintf("0x%x", probeVal.Bytes())
	}

	logger.Warn(
		"exec3: path probe",
		"phase", phase,
		"block", txTask.BlockNum,
		"txnum", txTask.TxNum,
		"tx_index", txTask.TxIndex,
		"tx_hash", txTask.Tx.Hash(),
		"history_mode", historyMode,
		"doms_txnum", domainsTxNum,
		"reader", fmt.Sprintf("%T", reader),
		"probe_addr", pathProbeAddr,
		"probe_slot", pathProbeSlot,
		"probe_ok", probeOK,
		"probe_val", probeValHex,
	)

	accountData, accErr := probeReader.ReadAccountDataForDebug(accountProbeAddr)
	if accErr != nil {
		logger.Warn(
			"exec3: account probe read failed",
			"phase", phase,
			"block", txTask.BlockNum,
			"txnum", txTask.TxNum,
			"tx_index", txTask.TxIndex,
			"tx_hash", txTask.Tx.Hash(),
			"history_mode", historyMode,
			"doms_txnum", domainsTxNum,
			"reader", fmt.Sprintf("%T", reader),
			"probe_addr", accountProbeAddr,
			"err", accErr,
		)
		return
	}

	readerExists := accountData != nil
	readerNonce := uint64(0)
	readerBalance := "0"
	readerInc := uint64(0)
	readerCodeHash := "0x"
	readerRoot := "0x"
	if accountData != nil {
		readerNonce = accountData.Nonce
		readerBalance = accountData.Balance.ToBig().String()
		readerInc = accountData.Incarnation
		readerCodeHash = accountData.CodeHash.Hex()
		readerRoot = accountData.Root.Hex()
	}

	logger.Warn(
		"exec3: account probe",
		"phase", phase,
		"block", txTask.BlockNum,
		"txnum", txTask.TxNum,
		"tx_index", txTask.TxIndex,
		"tx_hash", txTask.Tx.Hash(),
		"history_mode", historyMode,
		"doms_txnum", domainsTxNum,
		"probe_addr", accountProbeAddr,
		"reader_exists", readerExists,
		"reader_nonce", readerNonce,
		"reader_balance", readerBalance,
		"reader_incarnation", readerInc,
		"reader_code_hash", readerCodeHash,
		"reader_root", readerRoot,
	)
}

func logRuntimeBalanceIncreaseBoundary(logger log.Logger, phase string, txTask *state.TxTask, domainsTxNum uint64) {
	if logger == nil || !shouldLogRuntimePathProbe(txTask) {
		return
	}
	logger.Warn(
		"exec3: balance increase boundary",
		"phase", phase,
		"block", txTask.BlockNum,
		"txnum", txTask.TxNum,
		"tx_index", txTask.TxIndex,
		"tx_hash", txTask.Tx.Hash(),
		"doms_txnum", domainsTxNum,
		"count", len(txTask.BalanceIncreaseSet),
	)
	for addr, increase := range txTask.BalanceIncreaseSet {
		logger.Warn(
			"exec3: balance increase entry",
			"phase", phase,
			"block", txTask.BlockNum,
			"txnum", txTask.TxNum,
			"tx_index", txTask.TxIndex,
			"tx_hash", txTask.Tx.Hash(),
			"doms_txnum", domainsTxNum,
			"addr", addr,
			"amount", increase.Amount.ToBig().String(),
			"is_escrow", increase.IsEscrow,
		)
	}
}

func logRuntimeWriteSetProbe(logger log.Logger, txTask *state.TxTask, domainsTxNum uint64) {
	if logger == nil || !shouldLogRuntimePathProbe(txTask) {
		return
	}

	accountProbeOps := 0
	storageProbeOps := 0

	accountList, hasAccountList := txTask.WriteLists[kv.AccountsDomain.String()]
	if hasAccountList && accountList != nil {
		for i, key := range accountList.Keys {
			keyBytes := []byte(key)
			if len(keyBytes) != len(accountProbeAddr) {
				continue
			}
			if !bytes.Equal(keyBytes, accountProbeAddr.Bytes()) {
				continue
			}
			val := accountList.Vals[i]
			op := "put"
			if val == nil {
				op = "del"
			}
			nonce, balance, codeHash, decodeErr := runtimeDecodeAccountPayload(val)
			logger.Warn(
				"exec3: write-set account probe",
				"block", txTask.BlockNum,
				"txnum", txTask.TxNum,
				"tx_index", txTask.TxIndex,
				"tx_hash", txTask.Tx.Hash(),
				"doms_txnum", domainsTxNum,
				"op", op,
				"addr", accountProbeAddr,
				"val_len", len(val),
				"val_preview", runtimeHexPreview(val, 64),
				"val_nonce", nonce,
				"val_balance", balance,
				"val_code_hash", codeHash,
				"val_decode_err", decodeErr,
			)
			accountProbeOps++
		}
	}

	storageList, hasStorageList := txTask.WriteLists[kv.StorageDomain.String()]
	if hasStorageList && storageList != nil {
		addrLen := len(pathProbeAddr)
		slotLen := len(pathProbeSlot)
		for i, key := range storageList.Keys {
			keyBytes := []byte(key)
			if len(keyBytes) < addrLen+slotLen {
				continue
			}
			if !bytes.Equal(keyBytes[:addrLen], pathProbeAddr.Bytes()) {
				continue
			}
			val := storageList.Vals[i]
			op := "put"
			if val == nil {
				op = "del"
			}
			slotBytes := keyBytes[addrLen : addrLen+slotLen]
			slotMatches := bytes.Equal(slotBytes, pathProbeSlot.Bytes())
			logger.Warn(
				"exec3: write-set storage probe",
				"block", txTask.BlockNum,
				"txnum", txTask.TxNum,
				"tx_index", txTask.TxIndex,
				"tx_hash", txTask.Tx.Hash(),
				"doms_txnum", domainsTxNum,
				"op", op,
				"key_len", len(keyBytes),
				"slot", fmt.Sprintf("0x%x", slotBytes),
				"slot_matches_probe", slotMatches,
				"val_len", len(val),
				"val_preview", runtimeHexPreview(val, 64),
			)
			storageProbeOps++
		}
	}

	logger.Warn(
		"exec3: write-set probe summary",
		"block", txTask.BlockNum,
		"txnum", txTask.TxNum,
		"tx_index", txTask.TxIndex,
		"tx_hash", txTask.Tx.Hash(),
		"doms_txnum", domainsTxNum,
		"account_probe_ops", accountProbeOps,
		"storage_probe_ops", storageProbeOps,
		"write_lists", len(txTask.WriteLists),
		"balance_increase_count", len(txTask.BalanceIncreaseSet),
	)
}

func logRuntimeIbsSummary(logger log.Logger, phase string, txTask *state.TxTask, ibs *state.IntraBlockState, domainsTxNum uint64) {
	if logger == nil || ibs == nil || !shouldLogRuntimePathProbe(txTask) {
		return
	}
	journalEntries, journalDirties, journalDirtyForProbe, stateObjects, stateObjectsDirty, balanceIncreases, hasStateObject, stateObjectDirty :=
		ibs.DebugDirtySummary(accountProbeAddr)
	logger.Warn(
		"exec3: ibs summary",
		"phase", phase,
		"block", txTask.BlockNum,
		"txnum", txTask.TxNum,
		"tx_index", txTask.TxIndex,
		"tx_hash", txTask.Tx.Hash(),
		"doms_txnum", domainsTxNum,
		"journal_entries", journalEntries,
		"journal_dirties", journalDirties,
		"journal_dirty_for_probe", journalDirtyForProbe,
		"state_objects", stateObjects,
		"state_objects_dirty", stateObjectsDirty,
		"balance_increases", balanceIncreases,
		"probe_has_state_object", hasStateObject,
		"probe_state_object_dirty", stateObjectDirty,
		"probe_addr", accountProbeAddr,
	)
}

var noop = state.NewNoopWriter()

type Worker struct {
	lock        sync.Locker
	logger      log.Logger
	chainDb     kv.RoDB
	chainTx     kv.TemporalTx
	background  bool // if true - worker does manage RoTx (begin/rollback) in .ResetTx()
	blockReader services.FullBlockReader
	in          *state.QueueWithRetry
	rs          *state.ParallelExecutionState
	stateWriter *state.StateWriterBufferedV3
	stateReader state.ResettableStateReader
	historyMode bool // if true - stateReader is HistoryReaderV3, otherwise it's state reader
	chainConfig *chain.Config

	ctx      context.Context
	engine   consensus.Engine
	genesis  *types.Genesis
	resultCh *state.ResultsQueue
	chain    consensus.ChainReader

	callTracer  *calltracer.CallTracer
	taskGasPool *core.GasPool
	hooks       *tracing.Hooks

	evm   *vm.EVM
	ibs   *state.IntraBlockState
	vmCfg vm.Config

	dirs datadir.Dirs

	isMining bool

	escrowTouched map[common.Address]struct{}
	escrowBlock   uint64
}

func NewWorker(lock sync.Locker, logger log.Logger, hooks *tracing.Hooks, ctx context.Context, background bool, chainDb kv.RoDB, in *state.QueueWithRetry, blockReader services.FullBlockReader, chainConfig *chain.Config, genesis *types.Genesis, results *state.ResultsQueue, engine consensus.Engine, dirs datadir.Dirs, isMining bool) *Worker {
	w := &Worker{
		lock:    lock,
		chainDb: chainDb,
		in:      in,

		logger: logger,
		ctx:    ctx,

		background:  background,
		blockReader: blockReader,

		chainConfig: chainConfig,
		genesis:     genesis,
		resultCh:    results,
		engine:      engine,

		evm:         vm.NewEVM(evmtypes.BlockContext{}, evmtypes.TxContext{}, nil, chainConfig, vm.Config{}),
		callTracer:  calltracer.NewCallTracer(hooks),
		taskGasPool: new(core.GasPool),
		hooks:       hooks,

		dirs: dirs,

		isMining: isMining,
	}
	w.vmCfg = vm.Config{Tracer: w.callTracer.Tracer().Hooks, NoBaseFee: true}
	w.evm = vm.NewEVM(evmtypes.BlockContext{}, evmtypes.TxContext{}, nil, chainConfig, w.vmCfg)
	arbOSVersion := w.evm.Context.ArbOSVersion
	w.taskGasPool.AddBlobGas(chainConfig.GetMaxBlobGasPerBlock(0, arbOSVersion))
	w.ibs = state.New(w.stateReader)
	return w
}

func (rw *Worker) LogLRUStats() { rw.evm.Config().JumpDestCache.LogStats() }

func (rw *Worker) ResetState(rs *state.ParallelExecutionState, accumulator *shards.Accumulator) {
	rw.rs = rs
	if rw.background {
		rw.SetReader(state.NewReaderParallelV3(rs.Domains()))
	} else {
		rw.SetReader(state.NewReaderV3(rs.TemporalGetter()))
	}
	rw.stateWriter = state.NewStateWriterBufferedV3(rs, accumulator)
}

func (rw *Worker) SetGaspool(gp *core.GasPool) {
	rw.taskGasPool = gp
}

func (rw *Worker) Tx() kv.TemporalTx { return rw.chainTx }
func (rw *Worker) DiscardReadList()  { rw.stateReader.DiscardReadList() }
func (rw *Worker) ResetTx(chainTx kv.Tx) {
	if rw.background && rw.chainTx != nil {
		rw.chainTx.Rollback()
		rw.chainTx = nil
	}
	if chainTx != nil {
		rw.chainTx = chainTx.(kv.TemporalTx)
		rw.stateReader.SetTx(rw.chainTx)
		rw.chain = consensuschain.NewReader(rw.chainConfig, rw.chainTx, rw.blockReader, rw.logger)
	}
}

func (rw *Worker) Run() (err error) {
	defer func() { // convert panic to err - because it's background workers
		if rec := recover(); rec != nil {
			err = fmt.Errorf("exec3.Worker panic: %s, %s", rec, dbg.Stack())
		}
	}()

	for txTask, ok := rw.in.Next(rw.ctx); ok; txTask, ok = rw.in.Next(rw.ctx) {
		//fmt.Println("RTX", txTask.BlockNum, txTask.TxIndex, txTask.TxNum, txTask.Final)
		rw.RunTxTask(txTask, rw.isMining)
		if err := rw.resultCh.Add(rw.ctx, txTask); err != nil {
			return err
		}
	}
	return nil
}

func (rw *Worker) RunTxTask(txTask *state.TxTask, isMining bool) {
	rw.lock.Lock()
	defer rw.lock.Unlock()
	rw.RunTxTaskNoLock(txTask, isMining, false)
}

// Needed to set history reader when need to offset few txs from block beginning and does not break processing,
// like compute gas used for block and then to set state reader to continue processing on latest data.
func (rw *Worker) SetReader(reader state.ResettableStateReader) {
	rw.stateReader = reader
	rw.stateReader.SetTx(rw.Tx())
	rw.ibs.Reset()
	rw.ibs = state.New(rw.stateReader)

	switch reader.(type) {
	case *state.HistoryReaderV3:
		rw.historyMode = true
	case *state.ReaderV3:
		rw.historyMode = false
	default:
		rw.historyMode = false
		//fmt.Printf("[worker] unknown reader %T: historyMode is set to disabled\n", reader)
	}
}

func (rw *Worker) SetArbitrumWasmDB(wasmDB wasmdb.WasmIface) {
	if rw.chainConfig.IsArbitrum() {
		rw.ibs.SetWasmDB(wasmDB)
	}
}

func (rw *Worker) RunTxTaskNoLock(txTask *state.TxTask, isMining, skipPostEvaluation bool) {
	if txTask.HistoryExecution && !rw.historyMode {
		// in case if we cancelled execution and commitment happened in the middle of the block, we have to process block
		// from the beginning until committed txNum and only then disable history mode.
		// Needed to correctly evaluate spent gas and other things.
		rw.SetReader(state.NewHistoryReaderV3())
	} else if !txTask.HistoryExecution && rw.historyMode {
		if rw.background {
			rw.SetReader(state.NewReaderParallelV3(rw.rs.Domains()))
		} else {
			rw.SetReader(state.NewReaderV3(rw.rs.TemporalGetter()))
		}
	}
	if rw.background && rw.chainTx == nil {
		var err error
		if rw.chainTx, err = rw.chainDb.(kv.TemporalRoDB).BeginTemporalRo(rw.ctx); err != nil {
			panic(err)
		}
		rw.stateReader.SetTx(rw.chainTx)
		rw.chain = consensuschain.NewReader(rw.chainConfig, rw.chainTx, rw.blockReader, rw.logger)
	}
	if txTask.BlockNum != rw.escrowBlock {
		rw.escrowBlock = txTask.BlockNum
		rw.escrowTouched = nil
	}
	txTask.Error = nil

	logRuntimeTxBoundary(rw.logger, "before-set-txnum", txTask, rw.stateReader, rw.historyMode, runtimeDomainsTxNum(rw.rs))
	rw.stateReader.SetTxNum(txTask.TxNum)
	rw.stateWriter.SetTxNum(txTask.TxNum)
	rw.rs.Domains().SetTxNum(txTask.TxNum)
	rw.stateReader.ResetReadSet()
	rw.stateWriter.ResetWriteSet()
	rw.ibs.Reset()
	if len(rw.escrowTouched) > 0 {
		rw.ibs.RestoreEscrowTouched(rw.escrowTouched)
	}
	ibs, hooks, cc := rw.ibs, rw.hooks, rw.chainConfig
	rw.ibs.SetTrace(arbTrace)
	ibs.SetHooks(hooks)
	logRuntimeTxBoundary(rw.logger, "after-set-txnum", txTask, rw.stateReader, rw.historyMode, runtimeDomainsTxNum(rw.rs))
	logRuntimePathProbe(rw.logger, "after-set-txnum", txTask, rw.stateReader, ibs, rw.historyMode, runtimeDomainsTxNum(rw.rs))

	var err error
	rules, header := txTask.Rules, txTask.Header
	if arbTrace {
		fmt.Printf("txNum=%d blockNum=%d history=%t\n", txTask.TxNum, txTask.BlockNum, txTask.HistoryExecution)
	}
	if badRootDebug && txTask.TxIndex == 0 && txTask.Tx != nil {
		log.Warn("exec3 tx task",
			"block_number", txTask.BlockNum,
			"tx_index", txTask.TxIndex,
			"tx_num", txTask.TxNum,
			"tx_hash", txTask.Tx.Hash(),
			"tx_type", txTask.Tx.Type(),
		)
	}

	switch {
	case txTask.TxIndex == -1:
		if txTask.BlockNum == 0 {

			//fmt.Printf("txNum=%d, blockNum=%d, Genesis\n", txTask.TxNum, txTask.BlockNum)
			_, ibs, err = genesiswrite.GenesisToBlock(nil, rw.genesis, rw.dirs, rw.logger)
			if err != nil {
				panic(err)
			}
			// For Genesis, rules should be empty, so that empty accounts can be included
			rules = &chain.Rules{}

			if rw.chainConfig.IsArbitrum() { // initialize arbos once
				// GenesisToBlock uses a temporary DB; use the execution IBS so ArbOS writes persist.
				ibsa := state.NewArbitrum(rw.ibs)
				accountsPerSync := uint(100000) // const for sep-rollup
				stateRoot, err := initializeArbosGenesis(ibsa, rw.rs.Domains(), rw.rs.TemporalPutDel(), rw.chainConfig, rw.evm.Context.Time, accountsPerSync)
				if err != nil {
					if errors.Is(err, arbosState.ErrAlreadyInitialized) || errors.Is(err, offchainArbosState.ErrAlreadyInitialized) {
						rw.logger.Info("ArbOS already initialized at genesis, skipping")
						break
					}
					rw.logger.Error("Failed to init ArbOS", "err", err)
					return
				}
				_ = stateRoot
				rw.logger.Info("ArbOS initialized", "stateRoot", stateRoot) // todo this produces invalid state isnt it?
			}
			break
		}

		// Block initialisation
		//fmt.Printf("txNum=%d, blockNum=%d, initialisation of the block\n", txTask.TxNum, txTask.BlockNum)
		syscall := func(contract common.Address, data []byte, ibs *state.IntraBlockState, header *types.Header, constCall bool) ([]byte, error) {
			ret, err := core.SysCallContract(contract, data, cc, ibs, header, rw.engine, constCall /* constCall */, rw.vmCfg)
			return ret, err
		}
		rw.engine.Initialize(cc, rw.chain, header, ibs, syscall, rw.logger, hooks)
		txTask.Error = ibs.FinalizeTx(rules, noop)
	case txTask.Final:
		if txTask.BlockNum == 0 {
			break
		}

		if arbTrace {
			fmt.Printf("txNum=%d, blockNum=%d, finalisation of the block\n", txTask.TxNum, txTask.BlockNum)
		}
		rw.callTracer.Reset()
		ibs.SetTxContext(txTask.BlockNum, txTask.TxIndex)

		// End of block transaction in a block
		syscall := func(contract common.Address, data []byte) ([]byte, error) {
			ret, err := core.SysCallContract(contract, data, cc, ibs, header, rw.engine, false /* constCall */, rw.vmCfg)
			txTask.Logs = append(txTask.Logs, ibs.GetRawLogs(txTask.TxIndex)...)
			return ret, err
		}

		if isMining {
			_, _, err = rw.engine.FinalizeAndAssemble(cc, types.CopyHeader(header), ibs, txTask.Txs, txTask.Uncles, txTask.BlockReceipts, txTask.Withdrawals, rw.chain, syscall, nil, rw.logger)
		} else {
			_, err = rw.engine.Finalize(cc, types.CopyHeader(header), ibs, txTask.Txs, txTask.Uncles, txTask.BlockReceipts, txTask.Withdrawals, rw.chain, syscall, skipPostEvaluation, rw.logger)
		}
		if err != nil {
			txTask.Error = err
		} else {
			txTask.TraceFroms = rw.callTracer.Froms()
			txTask.TraceTos = rw.callTracer.Tos()
			if txTask.TraceFroms == nil {
				txTask.TraceFroms = map[common.Address]struct{}{}
			}
			if txTask.TraceTos == nil {
				txTask.TraceTos = map[common.Address]struct{}{}
			}
			txTask.TraceTos[txTask.Coinbase] = struct{}{}
			for _, uncle := range txTask.Uncles {
				txTask.TraceTos[uncle.Coinbase] = struct{}{}
			}
		}
	default:
		if badRootDebug {
			log.Warn("exec3 tx start",
				"block_number", txTask.BlockNum,
				"tx_index", txTask.TxIndex,
				"tx_hash", txTask.Tx.Hash(),
				"tx_type", txTask.Tx.Type(),
				"header_root", txTask.Header.Root,
				"parent_hash", txTask.Header.ParentHash,
			)
		}
		rw.taskGasPool.Reset(txTask.Tx.GetGasLimit(), rw.chainConfig.GetMaxBlobGasPerBlock(header.Time, rules.ArbOSVersion)) // ARBITRUM only

		rw.callTracer.Reset()
		ibs.SetTxContext(txTask.BlockNum, txTask.TxIndex)
		txn := txTask.Tx

		if txTask.Tx.Type() == types.AccountAbstractionTxType {
			if !cc.AllowAA {
				txTask.Error = errors.New("account abstraction transactions are not allowed")
				break
			}

			msg, err := txn.AsMessage(types.Signer{}, nil, nil)
			if err != nil {
				txTask.Error = err
				break
			}

			rw.evm.ResetBetweenBlocks(txTask.EvmBlockContext, core.NewEVMTxContext(msg), ibs, rw.vmCfg, rules)
			rw.updateArbosHook(txTask.BlockNum, msg)
			rw.execAATxn(txTask)
			break
		}

		msg := txTask.TxAsMessage
		rw.evm.ResetBetweenBlocks(txTask.EvmBlockContext, core.NewEVMTxContext(msg), ibs, rw.vmCfg, rules)
		rw.updateArbosHook(txTask.BlockNum, msg)
		if badRootDebug && txTask.TxIndex == 1 && txTask.Tx != nil {
			baseFee := "<nil>"
			if rw.evm.Context.BaseFee != nil {
				baseFee = rw.evm.Context.BaseFee.ToBig().String()
			}
			baseFeeInBlock := "<nil>"
			if rw.evm.Context.BaseFeeInBlock != nil {
				baseFeeInBlock = rw.evm.Context.BaseFeeInBlock.ToBig().String()
			}
			toAddr := "<nil>"
			if msg.To() != nil {
				toAddr = msg.To().Hex()
			}
			log.Warn("exec3 tx msg",
				"block_number", txTask.BlockNum,
				"tx_index", txTask.TxIndex,
				"tx_hash", txTask.Tx.Hash(),
				"from", msg.From().Hex(),
				"to", toAddr,
				"value", msg.Value().ToBig().String(),
				"gas_limit", msg.Gas(),
				"gas_price", msg.GasPrice().ToBig().String(),
				"fee_cap", msg.FeeCap().ToBig().String(),
				"tip_cap", msg.TipCap().ToBig().String(),
				"skip_l1_charging", msg.SkipL1Charging,
				"coinbase", rw.evm.Context.Coinbase,
				"base_fee", baseFee,
				"base_fee_in_block", baseFeeInBlock,
			)
		}

		if hooks != nil && hooks.OnTxStart != nil {
			hooks.OnTxStart(rw.evm.GetVMContext(), txn, msg.From())
		}
		logRuntimeTxBoundary(rw.logger, "before-apply", txTask, rw.stateReader, rw.historyMode, runtimeDomainsTxNum(rw.rs))
		logRuntimePathProbe(rw.logger, "before-apply", txTask, rw.stateReader, ibs, rw.historyMode, runtimeDomainsTxNum(rw.rs))
		logRuntimeIbsSummary(rw.logger, "before-apply", txTask, ibs, runtimeDomainsTxNum(rw.rs))
		// MA applytx
		applyRes, err := core.ApplyMessage(rw.evm, msg, rw.taskGasPool, true /* refunds */, false /* gasBailout */, rw.engine)
		if err != nil {
			txTask.Error = err
			if hooks != nil && hooks.OnTxEnd != nil {
				hooks.OnTxEnd(nil, err)
			}
			if badRootDebug {
				log.Warn("exec3 applymessage error",
					"block_number", txTask.BlockNum,
					"tx_index", txTask.TxIndex,
					"tx_hash", txTask.Tx.Hash(),
					"err", err,
				)
			}
		} else {
			txTask.Failed = applyRes.Failed()
			txTask.GasUsed = applyRes.GasUsed
			ibs.SoftFinalise()
			logRuntimePathProbe(rw.logger, "after-soft-finalise", txTask, rw.stateReader, ibs, rw.historyMode, runtimeDomainsTxNum(rw.rs))
			logRuntimeIbsSummary(rw.logger, "after-soft-finalise", txTask, ibs, runtimeDomainsTxNum(rw.rs))
			if badRootDebug {
				root := ibs.IntermediateRoot(true)
				log.Warn("exec3 intermediate root",
					"block_number", txTask.BlockNum,
					"tx_index", txTask.TxIndex,
					"root", root,
				)
			}
			txTask.Logs = ibs.GetRawLogs(txTask.TxIndex)
			txTask.TraceFroms = rw.callTracer.Froms()
			txTask.TraceTos = rw.callTracer.Tos()

			txTask.CreateReceipt(rw.Tx())
			logRuntimePathProbe(rw.logger, "after-receipt", txTask, rw.stateReader, ibs, rw.historyMode, runtimeDomainsTxNum(rw.rs))
			logRuntimeTxBoundary(rw.logger, "after-receipt", txTask, rw.stateReader, rw.historyMode, runtimeDomainsTxNum(rw.rs))
			if hooks != nil && hooks.OnTxEnd != nil {
				hooks.OnTxEnd(txTask.BlockReceipts[txTask.TxIndex], nil)
			}
			if badRootDebug {
				log.Warn("exec3 tx after apply",
					"block_number", txTask.BlockNum,
					"tx_index", txTask.TxIndex,
					"tx_hash", txTask.Tx.Hash(),
					"gas_used", txTask.GasUsed,
					"failed", txTask.Failed,
					"logs_len", len(txTask.Logs),
					"receipts_len", len(txTask.BlockReceipts),
				)
			}
		}
	}
	if arbTrace {
		fmt.Printf("---- txnIdx %d block %d DONE------\n", txTask.TxIndex, txTask.BlockNum)
	}
	// Prepare read set, write set and balanceIncrease set and send for serialisation
	if txTask.Error == nil {
		txTask.BalanceIncreaseSet = ibs.BalanceIncreaseSet()
		logRuntimeBalanceIncreaseBoundary(rw.logger, "after-capture", txTask, runtimeDomainsTxNum(rw.rs))
		if snapshot := ibs.EscrowTouchedSnapshot(); len(snapshot) > 0 {
			if rw.escrowTouched == nil {
				rw.escrowTouched = make(map[common.Address]struct{}, len(snapshot))
			}
			for addr := range snapshot {
				rw.escrowTouched[addr] = struct{}{}
			}
		}
		if arbTrace {
			for addr, bal := range txTask.BalanceIncreaseSet {
				fmt.Printf("BalanceIncreaseSet [%x]=>[%d]\n", addr, &(bal.Amount))
			}
		}
		logRuntimeTxBoundary(rw.logger, "before-make-write-set", txTask, rw.stateReader, rw.historyMode, runtimeDomainsTxNum(rw.rs))
		logRuntimePathProbe(rw.logger, "before-make-write-set", txTask, rw.stateReader, ibs, rw.historyMode, runtimeDomainsTxNum(rw.rs))
		logRuntimeIbsSummary(rw.logger, "before-make-write-set", txTask, ibs, runtimeDomainsTxNum(rw.rs))
		if err = ibs.MakeWriteSet(rules, rw.stateWriter); err != nil {
			panic(err)
		}
		txTask.ReadLists = rw.stateReader.ReadSet()
		txTask.WriteLists = rw.stateWriter.WriteSet()
		txTask.AccountPrevs, txTask.AccountDels, txTask.StoragePrevs, txTask.CodePrevs = rw.stateWriter.PrevAndDels()
		if shouldLogRuntimePathProbe(txTask) {
			rw.logger.Warn(
				"exec3: rw set boundary",
				"phase", "after-make-write-set",
				"block", txTask.BlockNum,
				"txnum", txTask.TxNum,
				"tx_index", txTask.TxIndex,
				"tx_hash", txTask.Tx.Hash(),
				"history_mode", rw.historyMode,
				"doms_txnum", runtimeDomainsTxNum(rw.rs),
				"read_lists", len(txTask.ReadLists),
				"write_lists", len(txTask.WriteLists),
				"account_prevs", len(txTask.AccountPrevs),
				"account_dels", len(txTask.AccountDels),
				"storage_prevs", len(txTask.StoragePrevs),
				"code_prevs", len(txTask.CodePrevs),
			)
		}
		logRuntimeIbsSummary(rw.logger, "after-make-write-set", txTask, ibs, runtimeDomainsTxNum(rw.rs))
		logRuntimeWriteSetProbe(rw.logger, txTask, runtimeDomainsTxNum(rw.rs))
	}
}

func (rw *Worker) updateArbosHook(blockNum uint64, msg *types.Message) {
	if msg == nil || blockNum == 0 || !rw.chainConfig.IsArbitrum() {
		return
	}

	arbState := state.NewArbitrum(rw.ibs)
	if rw.evm.ProcessingHookSet.CompareAndSwap(false, true) {
		rw.evm.ProcessingHook = arbos.NewTxProcessorIBS(rw.evm, arbState, msg)
	} else {
		rw.evm.ProcessingHook.SetMessage(msg, arbState)
	}
}

func (rw *Worker) execAATxn(txTask *state.TxTask) {
	if !txTask.InBatch {
		// this is the first transaction in an AA transaction batch, run all validation frames, then execute execution frames in its own txtask
		startIdx := uint64(txTask.TxIndex)
		endIdx := startIdx + txTask.AAValidationBatchSize

		validationResults := make([]state.AAValidationResult, txTask.AAValidationBatchSize+1)
		log.Info("🕵️‍♂️[aa] found AA bundle", "startIdx", startIdx, "endIdx", endIdx)

		var outerErr error
		for i := startIdx; i <= endIdx; i++ {
			rw.evm.ResetBetweenBlocks(txTask.EvmBlockContext, core.NewEVMTxContext(txTask.TxAsMessage), rw.ibs, rw.vmCfg, txTask.Rules)
			rw.updateArbosHook(txTask.BlockNum, txTask.TxAsMessage)
			// check if next n transactions are AA transactions and run validation
			if txTask.Txs[i].Type() == types.AccountAbstractionTxType {
				aaTxn, ok := txTask.Txs[i].(*types.AccountAbstractionTransaction)
				if !ok {
					outerErr = fmt.Errorf("invalid transaction type, expected AccountAbstractionTx, got %T", txTask.Tx)
					break
				}

				paymasterContext, validationGasUsed, err := aa.ValidateAATransaction(aaTxn, rw.ibs, rw.taskGasPool, txTask.Header, rw.evm, rw.chainConfig)
				if err != nil {
					outerErr = err
					break
				}

				validationResults[i-startIdx] = state.AAValidationResult{
					PaymasterContext: paymasterContext,
					GasUsed:          validationGasUsed,
				}
			} else {
				outerErr = fmt.Errorf("invalid txcount, expected txn %d to be type %d", i, types.AccountAbstractionTxType)
				break
			}
		}

		if outerErr != nil {
			txTask.Error = outerErr
			return
		}
		log.Info("✅[aa] validated AA bundle", "len", endIdx-startIdx+1)

		txTask.ValidationResults = validationResults
	}

	if len(txTask.ValidationResults) == 0 {
		txTask.Error = fmt.Errorf("found RIP-7560 but no remaining validation results, txIndex %d", txTask.TxIndex)
		return
	}

	aaTxn := txTask.Tx.(*types.AccountAbstractionTransaction) // type cast checked earlier
	validationRes := txTask.ValidationResults[0]
	txTask.ValidationResults = txTask.ValidationResults[1:]

	rw.evm.ResetBetweenBlocks(txTask.EvmBlockContext, core.NewEVMTxContext(txTask.TxAsMessage), rw.ibs, rw.vmCfg, txTask.Rules)
	rw.updateArbosHook(txTask.BlockNum, txTask.TxAsMessage)
	status, gasUsed, err := aa.ExecuteAATransaction(aaTxn, validationRes.PaymasterContext, validationRes.GasUsed, rw.taskGasPool, rw.evm, txTask.Header, rw.ibs)
	if err != nil {
		txTask.Error = err
		return
	}

	txTask.Failed = status != 0
	txTask.GasUsed = gasUsed
	// Update the state with pending changes
	rw.ibs.SoftFinalise()
	txTask.Logs = rw.ibs.GetLogs(txTask.TxIndex, txTask.Tx.Hash(), txTask.BlockNum, txTask.BlockHash)
	txTask.TraceFroms = rw.callTracer.Froms()
	txTask.TraceTos = rw.callTracer.Tos()
	txTask.CreateReceipt(rw.Tx())

	log.Info("🚀[aa] executed AA bundle transaction", "txIndex", txTask.TxIndex, "status", status, "gasUsed", gasUsed)
}

func NewWorkersPool(lock sync.Locker, accumulator *shards.Accumulator, logger log.Logger, hooks *tracing.Hooks, ctx context.Context, background bool, chainDb kv.RoDB, rs *state.ParallelExecutionState, in *state.QueueWithRetry, blockReader services.FullBlockReader, chainConfig *chain.Config, genesis *types.Genesis, engine consensus.Engine, workerCount int, dirs datadir.Dirs, isMining bool) (reconWorkers []*Worker, applyWorker *Worker, rws *state.ResultsQueue, clear func(), wait func()) {
	reconWorkers = make([]*Worker, workerCount)

	resultChSize := workerCount * 8
	rws = state.NewResultsQueue(resultChSize, workerCount) // workerCount * 4
	{
		// we all errors in background workers (except ctx.Cancel), because applyLoop will detect this error anyway.
		// and in applyLoop all errors are critical
		ctx, cancel := context.WithCancel(ctx)
		g, ctx := errgroup.WithContext(ctx)
		for i := 0; i < workerCount; i++ {
			reconWorkers[i] = NewWorker(lock, logger, hooks, ctx, background, chainDb, in, blockReader, chainConfig, genesis, rws, engine, dirs, isMining)
			reconWorkers[i].ResetState(rs, accumulator)
		}
		if background {
			for i := 0; i < workerCount; i++ {
				i := i
				g.Go(func() error {
					return reconWorkers[i].Run()
				})
			}
			wait = func() { g.Wait() }
		}

		var clearDone bool
		clear = func() {
			if clearDone {
				return
			}
			clearDone = true
			cancel()
			g.Wait()
			for _, w := range reconWorkers {
				w.ResetTx(nil)
			}
			//applyWorker.ResetTx(nil)
		}
	}
	applyWorker = NewWorker(lock, logger, hooks, ctx, false, chainDb, in, blockReader, chainConfig, genesis, rws, engine, dirs, isMining)

	return reconWorkers, applyWorker, rws, clear, wait
}
