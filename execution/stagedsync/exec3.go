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

package stagedsync

import (
	"bytes"
	"context"
	"crypto/sha256"
	"encoding/binary"
	"encoding/hex"
	"errors"
	"fmt"
	"runtime"
	"sort"
	"strings"
	"sync"
	"sync/atomic"
	"time"

	"github.com/erigontech/erigon-lib/common"
	"github.com/erigontech/erigon-lib/common/cmp"
	"github.com/erigontech/erigon-lib/common/dbg"
	"github.com/erigontech/erigon-lib/estimate"
	"github.com/erigontech/erigon-lib/log/v3"
	"github.com/erigontech/erigon-lib/metrics"
	"github.com/erigontech/erigon/core"
	"github.com/erigontech/erigon/core/state"
	"github.com/erigontech/erigon/core/tracing"
	"github.com/erigontech/erigon/db/config3"
	"github.com/erigontech/erigon/db/kv"
	"github.com/erigontech/erigon/db/kv/order"
	"github.com/erigontech/erigon/db/kv/rawdbv3"
	"github.com/erigontech/erigon/db/rawdb"
	"github.com/erigontech/erigon/db/rawdb/rawdbhelpers"
	"github.com/erigontech/erigon/db/rawdb/rawtemporaldb"
	dbstate "github.com/erigontech/erigon/db/state"
	changeset2 "github.com/erigontech/erigon/db/state/changeset"
	"github.com/erigontech/erigon/db/wrap"
	"github.com/erigontech/erigon/execution/commitment/commitmentdb"
	"github.com/erigontech/erigon/execution/consensus"
	"github.com/erigontech/erigon/execution/exec3"
	"github.com/erigontech/erigon/execution/stagedsync/stages"
	etrie "github.com/erigontech/erigon/execution/trie"
	"github.com/erigontech/erigon/execution/types"
	"github.com/erigontech/erigon/execution/types/accounts"
	"github.com/erigontech/erigon/turbo/services"
	"github.com/erigontech/erigon/turbo/shards"
	"github.com/offchainlabs/nitro/arbos"
	arbosutil "github.com/offchainlabs/nitro/arbos/util"
)

var (
	mxExecStepsInDB    = metrics.NewGauge(`exec_steps_in_db`) //nolint
	mxExecRepeats      = metrics.NewCounter(`exec_repeats`)   //nolint
	mxExecTriggers     = metrics.NewCounter(`exec_triggers`)  //nolint
	mxExecTransactions = metrics.NewCounter(`exec_txns`)
	mxExecGas          = metrics.NewCounter(`exec_gas`)
	mxExecBlocks       = metrics.NewGauge("exec_blocks")

	mxMgas = metrics.NewGauge(`exec_mgas`)
)

const (
	maxUnwindJumpAllowance = 1000 // Maximum number of blocks we are allowed to unwind
)

func NewProgress(prevOutputBlockNum, commitThreshold uint64, workersCount int, logPrefix string, logger log.Logger) *Progress {
	return &Progress{prevTime: time.Now(), prevOutputBlockNum: prevOutputBlockNum, commitThreshold: commitThreshold, workersCount: workersCount, logPrefix: logPrefix, logger: logger}
}

type Progress struct {
	prevTime           time.Time
	prevTxCount        uint64
	prevGasUsed        uint64
	prevOutputBlockNum uint64
	prevRepeatCount    uint64
	commitThreshold    uint64

	workersCount int
	logPrefix    string
	logger       log.Logger
}

func (p *Progress) Log(suffix string, rs *state.ParallelExecutionState, in *state.QueueWithRetry, rws *state.ResultsQueue, txCount uint64, gas uint64, inputBlockNum uint64, outputBlockNum uint64, outTxNum uint64, repeatCount uint64, idxStepsAmountInDB float64, commitEveryBlock bool, inMemExec bool) {
	mxExecStepsInDB.Set(idxStepsAmountInDB * 100)
	var m runtime.MemStats
	dbg.ReadMemStats(&m)
	sizeEstimate := rs.SizeEstimate()
	currentTime := time.Now()
	interval := currentTime.Sub(p.prevTime)
	//var repeatRatio float64
	//if doneCount > p.prevCount {
	//	repeatRatio = 100.0 * float64(repeatCount-p.prevRepeatCount) / float64(doneCount-p.prevCount)
	//}

	if len(suffix) > 0 {
		suffix = " " + suffix
	}

	if commitEveryBlock {
		suffix += " Commit every block"
	}

	gasSec := uint64(float64(gas-p.prevGasUsed) / interval.Seconds())
	txSec := uint64(float64(txCount-p.prevTxCount) / interval.Seconds())
	diffBlocks := max(int(outputBlockNum)-int(p.prevOutputBlockNum)+1, 0)

	p.logger.Info(fmt.Sprintf("[%s]"+suffix, p.logPrefix),
		"blk", outputBlockNum,
		"blks", diffBlocks,
		"blk/s", fmt.Sprintf("%.1f", float64(diffBlocks)/interval.Seconds()),
		"txs", txCount-p.prevTxCount,
		"tx/s", common.PrettyCounter(txSec),
		"gas/s", common.PrettyCounter(gasSec),
		//"pipe", fmt.Sprintf("(%d+%d)->%d/%d->%d/%d", in.NewTasksLen(), in.RetriesLen(), rws.ResultChLen(), rws.ResultChCap(), rws.Len(), rws.Limit()),
		//"repeatRatio", fmt.Sprintf("%.2f%%", repeatRatio),
		//"workers", p.workersCount,
		"buf", fmt.Sprintf("%s/%s", common.ByteCount(sizeEstimate), common.ByteCount(p.commitThreshold)),
		"stepsInDB", fmt.Sprintf("%.2f", idxStepsAmountInDB),
		"step", fmt.Sprintf("%.1f", float64(outTxNum)/float64(config3.DefaultStepSize)),
		"inMem", inMemExec,
		"alloc", common.ByteCount(m.Alloc), "sys", common.ByteCount(m.Sys),
	)

	p.prevTime = currentTime
	p.prevTxCount = txCount
	p.prevGasUsed = gas
	p.prevOutputBlockNum = outputBlockNum
	p.prevRepeatCount = repeatCount
}

// Cases:
//  1. Snapshots > ExecutionStage: snapshots can have half-block data `10.4`. Get right txNum from SharedDomains (after SeekCommitment)
//  2. ExecutionStage > Snapshots: no half-block data possible. Rely on DB.
func restoreTxNum(ctx context.Context, cfg *ExecuteBlockCfg, applyTx kv.Tx, doms *dbstate.SharedDomains, maxBlockNum uint64) (
	inputTxNum uint64, maxTxNum uint64, offsetFromBlockBeginning uint64, err error) {

	txNumsReader := cfg.blockReader.TxnumReader(ctx)

	inputTxNum = doms.TxNum()

	if nothing, err := nothingToExec(applyTx, txNumsReader, inputTxNum); err != nil {
		return 0, 0, 0, err
	} else if nothing {
		return 0, 0, 0, err
	}

	maxTxNum, err = txNumsReader.Max(applyTx, maxBlockNum)
	if err != nil {
		return 0, 0, 0, err
	}

	_blockNum, ok, err := txNumsReader.FindBlockNum(applyTx, doms.TxNum())
	if err != nil {
		return 0, 0, 0, err
	}
	if !ok {
		_lb, _lt, _ := txNumsReader.Last(applyTx)
		_fb, _ft, _ := txNumsReader.First(applyTx)
		return 0, 0, 0, fmt.Errorf("seems broken TxNums index not filled. can't find blockNum of txNum=%d; in db: (%d-%d, %d-%d)", inputTxNum, _fb, _lb, _ft, _lt)
	}
	{
		_max, _ := txNumsReader.Max(applyTx, _blockNum)
		if doms.TxNum() == _max {
			_blockNum++
		}
	}

	_min, err := txNumsReader.Min(applyTx, _blockNum)
	if err != nil {
		return 0, 0, 0, err
	}

	if doms.TxNum() > _min {
		// if stopped in the middle of the block: start from beginning of block.
		// first part will be executed in HistoryExecution mode
		offsetFromBlockBeginning = doms.TxNum() - _min
	}

	inputTxNum = _min

	//_max, _ := txNumsReader.Max(applyTx, blockNum)
	//fmt.Printf("[commitment] found domain.txn %d, inputTxn %d, offset %d. DB found block %d {%d, %d}\n", doms.TxNum(), inputTxNum, offsetFromBlockBeginning, blockNum, _min, _max)
	doms.SetBlockNum(_blockNum)
	doms.SetTxNum(inputTxNum)
	return inputTxNum, maxTxNum, offsetFromBlockBeginning, nil
}

func nothingToExec(applyTx kv.Tx, txNumsReader rawdbv3.TxNumsReader, inputTxNum uint64) (bool, error) {
	_, lastTxNum, err := txNumsReader.Last(applyTx)
	if err != nil {
		return false, err
	}
	return lastTxNum == inputTxNum, nil
}

func ExecV3(ctx context.Context,
	execStage *StageState, u Unwinder, workerCount int, cfg ExecuteBlockCfg, txc wrap.TxContainer,
	parallel bool, //nolint
	maxBlockNum uint64,
	logger log.Logger,
	hooks *tracing.Hooks,
	initialCycle bool,
	isMining bool,
) (execErr error) {
	inMemExec := txc.Doms != nil
	// TODO: e35 doesn't support parallel-exec yet
	parallel = false //nolint

	blockReader := cfg.blockReader
	chainConfig := cfg.chainConfig
	totalGasUsed := uint64(0)
	start := time.Now()
	defer func() {
		if totalGasUsed > 0 {
			mxMgas.Set((float64(totalGasUsed) / 1e6) / time.Since(start).Seconds())
		}
	}()

	applyTx := txc.Tx
	useExternalTx := applyTx != nil
	if !useExternalTx {
		if !parallel {
			var err error
			applyTx, err = cfg.db.BeginRw(ctx) //nolint
			if err != nil {
				return err
			}
			defer func() { // need callback - because tx may be committed
				applyTx.Rollback()
			}()
		}
	}

	chainReader := NewChainReaderImpl(cfg.chainConfig, applyTx, blockReader, logger)
	agg := cfg.db.(dbstate.HasAgg).Agg().(*dbstate.Aggregator)
	if ERIGON_STOP_AT_BLOCK > 0 && maxBlockNum > ERIGON_STOP_AT_BLOCK {
		logger.Warn("Execution stop block enabled", "stop_block", ERIGON_STOP_AT_BLOCK, "max_block", maxBlockNum)
		maxBlockNum = ERIGON_STOP_AT_BLOCK
	}
	if !inMemExec && !isMining {
		if initialCycle {
			agg.SetCollateAndBuildWorkers(min(2, estimate.StateV3Collate.Workers()))
			agg.SetMergeWorkers(min(1, estimate.StateV3Collate.Workers()))
			agg.SetCompressWorkers(estimate.CompressSnapshot.Workers())
		} else {
			agg.SetCollateAndBuildWorkers(1)
			agg.SetMergeWorkers(1)
			agg.SetCompressWorkers(1)
		}
	}

	var err error
	var doms *dbstate.SharedDomains
	if inMemExec {
		doms = txc.Doms
	} else {
		var err error
		temporalTx, ok := applyTx.(kv.TemporalTx)
		if !ok {
			return errors.New("applyTx is not a temporal transaction")
		}
		doms, err = dbstate.NewSharedDomains(temporalTx, log.New())
		// if we are behind the commitment, we can't execute anything
		// this can heppen if progress in domain is higher than progress in blocks
		if errors.Is(err, commitmentdb.ErrBehindCommitment) {
			return nil
		}
		if err != nil {
			return err
		}
		defer doms.Close()
	}
	txNumInDB := doms.TxNum()

	var (
		inputTxNum               = doms.TxNum()
		stageProgress            = execStage.BlockNumber
		outputTxNum              = atomic.Uint64{}
		blockComplete            = atomic.Bool{}
		outputBlockNum           = stages.SyncMetrics[stages.Execution]
		inputBlockNum            = &atomic.Uint64{}
		offsetFromBlockBeginning uint64
		blockNum, maxTxNum       uint64
	)

	blockNum = doms.BlockNum()
	outputTxNum.Store(doms.TxNum())

	if maxBlockNum < blockNum {
		return nil
	}

	if maxBlockNum > blockNum+16 {
		log.Info(fmt.Sprintf("[%s] starting", execStage.LogPrefix()),
			"from", blockNum, "to", maxBlockNum, "fromTxNum", doms.TxNum(), "offsetFromBlockBeginning", offsetFromBlockBeginning, "initialCycle", initialCycle, "useExternalTx", useExternalTx, "inMem", inMemExec)
	}

	logSnapshotBuildCallsite(logger, "exec3.preloop", outputTxNum.Load(), blockNum, maxBlockNum)
	agg.BuildFilesInBackground(outputTxNum.Load())

	var count uint64

	shouldReportToTxPool := cfg.notifications != nil && !isMining && maxBlockNum <= blockNum+64
	var accumulator *shards.Accumulator
	if shouldReportToTxPool {
		accumulator = cfg.notifications.Accumulator
		if accumulator == nil {
			accumulator = shards.NewAccumulator()
		}
	}
	rs := state.NewParallelExecutionState(doms, applyTx, cfg.syncCfg, cfg.chainConfig.Bor != nil, logger)

	////TODO: owner of `resultCh` is main goroutine, but owner of `retryQueue` is applyLoop.
	// Now rwLoop closing both (because applyLoop we completely restart)
	// Maybe need split channels? Maybe don't exit from ApplyLoop? Maybe current way is also ok?

	if applyTx != nil {
		if inputTxNum, maxTxNum, offsetFromBlockBeginning, err = restoreTxNum(ctx, &cfg, applyTx, doms, maxBlockNum); err != nil {
			return err
		}
	} else {
		if err := cfg.db.View(ctx, func(tx kv.Tx) (err error) {
			inputTxNum, maxTxNum, offsetFromBlockBeginning, err = restoreTxNum(ctx, &cfg, tx, doms, maxBlockNum)
			return err
		}); err != nil {
			return err
		}
	}

	if maxTxNum == 0 {
		return nil
	}

	applyWorker := cfg.applyWorker
	if isMining {
		applyWorker = cfg.applyWorkerMining
	}
	defer applyWorker.LogLRUStats()

	applyWorker.ResetState(rs, accumulator)

	commitThreshold := cfg.batchSize.Bytes()

	// TODO are these dups ?
	progress := NewProgress(blockNum, commitThreshold, workerCount, execStage.LogPrefix(), logger)

	logEvery := time.NewTicker(20 * time.Second)
	defer logEvery.Stop()
	pruneEvery := time.NewTicker(2 * time.Second)
	defer pruneEvery.Stop()

	var logGas uint64
	var stepsInDB float64
	var executor executor

	if parallel {
		pe := &parallelExecutor{
			txExecutor: txExecutor{
				cfg:            cfg,
				execStage:      execStage,
				rs:             rs,
				doms:           doms,
				agg:            agg,
				accumulator:    accumulator,
				isMining:       isMining,
				inMemExec:      inMemExec,
				initialCycle:   initialCycle,
				applyTx:        applyTx,
				applyWorker:    applyWorker,
				inputBlockNum:  inputBlockNum,
				maxBlockNum:    maxBlockNum,
				outputTxNum:    &outputTxNum,
				outputBlockNum: stages.SyncMetrics[stages.Execution],
				logger:         logger,
			},
			workerCount: workerCount,
			pruneEvery:  pruneEvery,
			logEvery:    logEvery,
			progress:    progress,
		}

		executorCancel := pe.run(ctx, maxTxNum, logger)
		defer executorCancel()

		defer func() {
			progress.Log("Done", executor.readState(), nil, pe.rws, 0 /*txCount - TODO*/, logGas, inputBlockNum.Load(), outputBlockNum.GetValueUint64(), outputTxNum.Load(), mxExecRepeats.GetValueUint64(), stepsInDB, pe.shouldGenerateChangeSets(), inMemExec)
		}()

		executor = pe
	} else {
		applyWorker.ResetTx(applyTx)

		se := &serialExecutor{
			txExecutor: txExecutor{
				cfg:            cfg,
				execStage:      execStage,
				rs:             rs,
				doms:           doms,
				agg:            agg,
				u:              u,
				isMining:       isMining,
				inMemExec:      inMemExec,
				initialCycle:   initialCycle,
				applyTx:        applyTx,
				applyWorker:    applyWorker,
				inputBlockNum:  inputBlockNum,
				maxBlockNum:    maxBlockNum,
				outputTxNum:    &outputTxNum,
				outputBlockNum: stages.SyncMetrics[stages.Execution],
				logger:         logger,
			},
		}

		defer func() {
			progress.Log("Done", executor.readState(), nil, nil, se.txCount, logGas, inputBlockNum.Load(), outputBlockNum.GetValueUint64(), outputTxNum.Load(), mxExecRepeats.GetValueUint64(), stepsInDB, se.shouldGenerateChangeSets() || cfg.syncCfg.KeepExecutionProofs, inMemExec)
		}()

		executor = se
	}

	blockComplete.Store(true)

	computeCommitmentDuration := time.Duration(0)
	blockNum = executor.domains().BlockNum()
	outputTxNum.Store(executor.domains().TxNum())

	if maxBlockNum < blockNum {
		return nil
	}

	if maxBlockNum > blockNum+16 {
		log.Info(fmt.Sprintf("[%s] starting", execStage.LogPrefix()),
			"from", blockNum, "to", maxBlockNum, "fromTxNum", executor.domains().TxNum(), "offsetFromBlockBeginning", offsetFromBlockBeginning, "initialCycle", initialCycle, "useExternalTx", useExternalTx)
	}

	logSnapshotBuildCallsite(logger, "exec3.loop.setup", outputTxNum.Load(), blockNum, maxBlockNum)
	agg.BuildFilesInBackground(outputTxNum.Load())

	var readAhead chan uint64
	if !isMining && !inMemExec && execStage.CurrentSyncCycle.IsInitialCycle {
		// snapshots are often stored on chaper drives. don't expect low-read-latency and manually read-ahead.
		// can't use OS-level ReadAhead - because Data >> RAM
		// it also warmsup state a bit - by touching senders/coninbase accounts and code
		var clean func()

		readAhead, clean = exec3.BlocksReadAhead(ctx, 2, cfg.db, cfg.engine, cfg.blockReader)
		defer clean()
	}

	var b *types.Block
	startBlockNum := blockNum
	blockLimit := uint64(cfg.syncCfg.LoopBlockLimit)
	var errExhausted *ErrLoopExhausted

Loop:
	for ; blockNum <= maxBlockNum; blockNum++ {
		if ERIGON_STOP_AT_BLOCK > 0 && blockNum > ERIGON_STOP_AT_BLOCK {
			errExhausted = &ErrLoopExhausted{From: startBlockNum, To: blockNum - 1, Reason: "stop block reached"}
			logger.Warn("Execution stop block reached", "stop_block", ERIGON_STOP_AT_BLOCK, "last_block", blockNum-1)
			break
		}
		shouldGenerateChangesets := shouldGenerateChangeSets(cfg, blockNum, maxBlockNum, initialCycle)
		changeSet := &changeset2.StateChangeSet{}
		if shouldGenerateChangesets && blockNum > 0 {
			executor.domains().SetChangesetAccumulator(changeSet)
		}
		if !parallel {
			select {
			case readAhead <- blockNum:
			default:
			}
		}
		inputBlockNum.Store(blockNum)
		executor.domains().SetBlockNum(blockNum)

		b, err = blockWithSenders(ctx, cfg.db, executor.tx(), blockReader, blockNum)
		if err != nil {
			return err
		}
		if b == nil {
			// TODO: panic here and see that overall process deadlock
			return fmt.Errorf("nil block %d", blockNum)
		}

		if b.NumberU64() == 0 {
			if hooks != nil && hooks.OnGenesisBlock != nil {
				hooks.OnGenesisBlock(b, cfg.genesis.Alloc)
			}
		} else {
			if hooks != nil && hooks.OnBlockStart != nil {
				hooks.OnBlockStart(tracing.BlockEvent{
					Block:     b,
					TD:        chainReader.GetTd(b.ParentHash(), b.NumberU64()-1),
					Finalized: chainReader.CurrentFinalizedHeader(),
					Safe:      chainReader.CurrentSafeHeader(),
				})
			}
		}

		txs := b.Transactions()
		header := b.HeaderNoCopy()

		var arbosv uint64
		signer := *types.LatestSignerForChainID(chainConfig.ChainID)
		if chainConfig.IsArbitrum() {
			arbosv = types.GetArbOSVersion(header, chainConfig)
			signer = *types.MakeSignerArb(chainConfig, blockNum, header.Time, arbosv)
		}

		getHashFnMute := &sync.Mutex{}
		getHashFn := core.GetHashFn(header, func(hash common.Hash, number uint64) (*types.Header, error) {
			getHashFnMute.Lock()
			defer getHashFnMute.Unlock()
			return executor.getHeader(ctx, hash, number)
		})
		totalGasUsed += b.GasUsed()
		blockContext := core.NewEVMBlockContext(header, getHashFn, cfg.engine, cfg.author /* author */, chainConfig)
		gp := new(core.GasPool).AddGas(header.GasLimit).AddBlobGas(chainConfig.GetMaxBlobGasPerBlock(b.Time(), arbosv))

		// print type of engine
		if parallel {
			if err := executor.status(ctx, commitThreshold); err != nil {
				if b.NumberU64() > 0 && hooks != nil && hooks.OnBlockEnd != nil {
					hooks.OnBlockEnd(err)
				}
				return err
			}
		} else if accumulator != nil {
			txs, err := blockReader.RawTransactions(context.Background(), executor.tx(), b.NumberU64(), b.NumberU64())
			if err != nil {
				if b.NumberU64() > 0 && hooks != nil && hooks.OnBlockEnd != nil {
					hooks.OnBlockEnd(err)
				}
				return err
			}
			accumulator.StartChange(header, txs, false)
		}

		rules := blockContext.Rules(chainConfig)
		blockReceipts := make(types.Receipts, len(txs))
		// During the first block execution, we may have half-block data in the snapshots.
		// Thus, we need to skip the first txs in the block, however, this causes the GasUsed to be incorrect.
		// So we skip that check for the first block, if we find half-executed data.
		skipPostEvaluation := false
		var gasUsed uint64
		var txTasks []*state.TxTask
		var validationResults []state.AAValidationResult
		for txIndex := -1; txIndex <= len(txs); txIndex++ {
			// Do not oversend, wait for the result heap to go under certain size
			txTask := &state.TxTask{
				BlockNum:        blockNum,
				Header:          header,
				Coinbase:        b.Coinbase(),
				Uncles:          b.Uncles(),
				Rules:           rules,
				Txs:             txs,
				TxNum:           inputTxNum,
				TxIndex:         txIndex,
				BlockHash:       b.Hash(),
				Final:           txIndex == len(txs),
				GetHashFn:       getHashFn,
				EvmBlockContext: blockContext,
				Withdrawals:     b.Withdrawals(),
				TxAsMessage:     &types.Message{},

				// use history reader instead of state reader to catch up to the tx where we left off
				HistoryExecution: offsetFromBlockBeginning > 0 && txIndex < int(offsetFromBlockBeginning),

				BlockReceipts: blockReceipts,

				Config: chainConfig,

				ValidationResults: validationResults,
			}
			if txTask.HistoryExecution && gasUsed == 0 {
				gasUsed, _, _, err = rawtemporaldb.ReceiptAsOf(executor.tx().(kv.TemporalTx), txTask.TxNum)
				if err != nil {
					if b.NumberU64() > 0 && hooks != nil && hooks.OnBlockEnd != nil {
						hooks.OnBlockEnd(err)
					}
					return err
				}
			}

			if cfg.genesis != nil {
				txTask.Config = cfg.genesis.Config
			}

			// When resuming from the middle of a block, we must replay the skipped prefix
			// in history mode. If we short-circuit by txNum here, we can end up executing
			// only the final synthetic task, which diverges state/receipts.
			if offsetFromBlockBeginning == 0 && txTask.TxNum <= txNumInDB && txTask.TxNum > 0 && !cfg.blockProduction {
				inputTxNum++
				skipPostEvaluation = true
				continue
			}
			executor.domains().SetTxNum(txTask.TxNum)
			executor.domains().SetBlockNum(txTask.BlockNum)

			if txIndex >= 0 && txIndex < len(txs) {
				txTask.Tx = txs[txIndex]

				txTask.TxAsMessage, err = txTask.Tx.AsMessage(signer, header.BaseFee, txTask.Rules)
				if err != nil {
					if b.NumberU64() > 0 && hooks != nil && hooks.OnBlockEnd != nil {
						hooks.OnBlockEnd(err)
					}
					return fmt.Errorf("%w: %w", consensus.ErrInvalidBlock, err) // new payload can contain invalid txs
				}
			}

			txTasks = append(txTasks, txTask)
			stageProgress = blockNum
			inputTxNum++
		}
		if ERIGON_BAD_ROOT_DEBUG && blockNum >= 33 {
			plan := make([]string, 0, len(txTasks))
			for _, task := range txTasks {
				if task == nil {
					continue
				}
				taskKind := "real"
				if task.TxIndex < 0 {
					taskKind = "pre"
				} else if task.TxIndex >= len(txs) {
					taskKind = "final"
				}
				txHash := "nil"
				if task.Tx != nil {
					txHash = task.Tx.Hash().Hex()
				}
				plan = append(plan, fmt.Sprintf("%s[idx=%d txnum=%d hist=%t tx=%s]", taskKind, task.TxIndex, task.TxNum, task.HistoryExecution, txHash))
			}
			logger.Warn("exec3: block task plan",
				"block", blockNum,
				"txs", len(txs),
				"tasks", len(txTasks),
				"input_txnum_after_plan", inputTxNum,
				"domains_txnum_after_plan", executor.domains().TxNum(),
				"plan", strings.Join(plan, " "),
			)
		}

		// check for consecutive RIP-7560 sequence
		var isAASequence bool
		for _, txTask := range txTasks {
			txIndex := txTask.TxIndex
			if txIndex < 0 || txIndex > len(txs)-1 {
				continue
			}

			if txTask.Tx.Type() != types.AccountAbstractionTxType {
				isAASequence = false
				continue
			}
			if isAASequence {
				continue
			}

			aaBatchSize := uint64(0)
			for _, tt := range txTasks {
				if tt.TxIndex > txIndex && tt.Tx != nil && tt.Tx.Type() == types.AccountAbstractionTxType {
					aaBatchSize++
					tt.InBatch = true
				} else {
					break
				}
			}

			txTask.AAValidationBatchSize = aaBatchSize
			isAASequence = true
		}

		if parallel {
			_, err := executor.execute(ctx, txTasks, nil /*gasPool*/) // For now don't use block's gas pool for parallel
			if b.NumberU64() > 0 && hooks != nil && hooks.OnBlockEnd != nil {
				hooks.OnBlockEnd(err)
			}
			if err != nil {
				return err
			}

			logSnapshotBuildCallsite(logger, "exec3.loop.parallel", outputTxNum.Load(), blockNum, maxBlockNum)
			agg.BuildFilesInBackground(outputTxNum.Load())
		} else {
			se := executor.(*serialExecutor)

			se.skipPostEvaluation = skipPostEvaluation

			continueLoop, err := se.execute(ctx, txTasks, gp)
			if b.NumberU64() > 0 && hooks != nil && hooks.OnBlockEnd != nil {
				hooks.OnBlockEnd(err)
			}
			if err != nil {
				return err
			}

			count += uint64(len(txTasks))
			logGas += se.gasUsed

			se.gasUsed = 0
			se.blobGasUsed = 0

			if !continueLoop {
				break Loop
			}
		}

		mxExecBlocks.Add(1)

		if ERIGON_COMMIT_EACH_BLOCK || shouldGenerateChangesets || cfg.syncCfg.KeepExecutionProofs {
			start := time.Now()
			if blockNum == 0 {
				executor.domains().GetCommitmentContext().Trie().SetTrace(true)
			} else {
				executor.domains().GetCommitmentContext().Trie().SetTrace(false)
			}
			commitTxNum := inputTxNum
			commitTxNumSource := "stage_cursor_minus_one"
			if commitTxNum > 0 {
				// Anchor to the stage cursor (last txnum in the block range).
				commitTxNum--
			}
			realTxCount := 0
			realTxMin := uint64(0)
			realTxMax := uint64(0)
			for _, task := range txTasks {
				if task == nil || task.TxIndex < 0 || task.TxIndex >= len(txs) {
					continue
				}
				if realTxCount == 0 {
					realTxMin = task.TxNum
					realTxMax = task.TxNum
				} else {
					if task.TxNum < realTxMin {
						realTxMin = task.TxNum
					}
					if task.TxNum > realTxMax {
						realTxMax = task.TxNum
					}
				}
				realTxCount++
			}
			// Arbitrum exec tasks include synthetic pre/final tasks. State root in
			// the canonical header is anchored to the last real tx, not the final
			// synthetic task txnum.
			if realTxCount > 0 {
				commitTxNum = realTxMax
				commitTxNumSource = "last_real_tx"
			}

			commitmentCtx := executor.domains().GetCommitmentContext()
			restoredState := false
			restoredStateBlock := uint64(0)
			restoredStateTxNum := uint64(0)
			restoredStateRoot := common.Hash{}
			restoreSkipped := true
			restoreSkipReason := "disabled to preserve current block commitment updates"
			preRestoreCtxTxNum := uint64(0)
			preRestoreCtxReadable := false
			if commitmentCtx != nil {
				preRestoreCtxTxNum, _, _, preRestoreCtxReadable = commitmentCtx.DebugReadContext()
			}
			if ERIGON_BAD_ROOT_DEBUG && blockNum >= 33 {
				logger.Warn("exec3: per-block commitment txnum",
					"block", blockNum,
					"input_txnum", inputTxNum,
					"commit_txnum", commitTxNum,
					"commit_txnum_source", commitTxNumSource,
					"domains_txnum", executor.domains().TxNum(),
					"real_tx_count", realTxCount,
					"real_tx_min", realTxMin,
					"real_tx_max", realTxMax,
					"restore_skipped", restoreSkipped,
					"restore_skip_reason", restoreSkipReason,
					"ctx_txnum_before_restore", preRestoreCtxTxNum,
					"ctx_readable_before_restore", preRestoreCtxReadable,
					"state_restored", restoredState,
					"state_restored_block", restoredStateBlock,
					"state_restored_txnum", restoredStateTxNum,
					"state_restored_root", restoredStateRoot,
				)
			}
			domsTxNumBefore := executor.domains().TxNum()
			ctxTxNumBefore := uint64(0)
			ctxLimitReadAsOfTxNum := uint64(0)
			ctxWithHistory := false
			ctxReadable := false
			if commitmentCtx != nil {
				ctxTxNumBefore, ctxLimitReadAsOfTxNum, ctxWithHistory, ctxReadable = commitmentCtx.DebugReadContext()
			}
			ctxAdjusted := false
			if ctxReadable && commitmentCtx != nil && ctxTxNumBefore != commitTxNum {
				commitmentCtx.SetTxNum(commitTxNum)
				ctxAdjusted = true
			}
			if ERIGON_BAD_ROOT_DEBUG && blockNum >= 33 {
				logger.Warn("exec3: commitment ctx align",
					"block", blockNum,
					"commit_txnum", commitTxNum,
					"ctx_readable", ctxReadable,
					"ctx_txnum_before", ctxTxNumBefore,
					"ctx_limit_read_as_of_txnum", ctxLimitReadAsOfTxNum,
					"ctx_with_history", ctxWithHistory,
					"ctx_adjusted", ctxAdjusted,
					"domains_txnum_before", domsTxNumBefore,
				)
			}
			domsAdjusted := false
			if domsTxNumBefore != commitTxNum {
				executor.domains().SetTxNum(commitTxNum)
				domsAdjusted = true
			}
			if ERIGON_BAD_ROOT_DEBUG && blockNum >= 33 {
				logger.Warn("exec3: commitment domains align",
					"block", blockNum,
					"commit_txnum", commitTxNum,
					"domains_txnum_before", domsTxNumBefore,
					"domains_adjusted", domsAdjusted,
					"domains_txnum_after", executor.domains().TxNum(),
				)
			}
			if ERIGON_BAD_ROOT_DEBUG && blockNum >= 33 && commitmentCtx != nil {
				ctxTxBeforeProbe := ctxTxNumBefore
				if !ctxReadable {
					if txNum, _, _, ok := commitmentCtx.DebugReadContext(); ok {
						ctxTxBeforeProbe = txNum
					}
				}
				logger.Warn("exec3: commitment txnum probe restore",
					"block", blockNum,
					"ctx_txnum_before_probe", ctxTxBeforeProbe,
					"ctx_txnum_for_compute", commitTxNum,
					"state_restore_after_probe_skipped", true,
					"probe_disabled_reason", "avoid mutating commitment context before compute",
				)
			}
			rh, err := executor.domains().ComputeCommitment(ctx, true, blockNum, commitTxNum, execStage.LogPrefix())
			if domsAdjusted {
				executor.domains().SetTxNum(domsTxNumBefore)
				if ERIGON_BAD_ROOT_DEBUG && blockNum >= 33 {
					logger.Warn("exec3: commitment domains restore",
						"block", blockNum,
						"commit_txnum", commitTxNum,
						"domains_txnum_restored", domsTxNumBefore,
					)
				}
			}
			if ctxAdjusted && commitmentCtx != nil {
				commitmentCtx.SetTxNum(ctxTxNumBefore)
				if ERIGON_BAD_ROOT_DEBUG && blockNum >= 33 {
					logger.Warn("exec3: commitment ctx restore",
						"block", blockNum,
						"commit_txnum", commitTxNum,
						"ctx_txnum_restored", ctxTxNumBefore,
					)
				}
			}
			if ERIGON_BAD_ROOT_DEBUG && blockNum >= 33 {
				headerRoot := common.Hash{}
				if b != nil && b.HeaderNoCopy() != nil {
					headerRoot = b.HeaderNoCopy().Root
				}
				logger.Warn("exec3: per-block commitment result",
					"block", blockNum,
					"commit_txnum", commitTxNum,
					"domains_txnum", executor.domains().TxNum(),
					"computed_root", common.BytesToHash(rh),
					"header_root", headerRoot,
					"matches_header", len(rh) > 0 && common.BytesToHash(rh) == headerRoot,
				)
				logCommitmentAnchorProbe("per_block_after_compute", blockNum, executor.domains(), executor.tx(), rh, logger)
			}
			if err != nil {
				return err
			}

			if ERIGON_COMMIT_EACH_BLOCK {
				if !bytes.Equal(rh, header.Root.Bytes()) {
					logger.Error(fmt.Sprintf("[%s] Wrong trie root of block %d: %x, expected (from header): %x. Block hash: %x", execStage.LogPrefix(), header.Number.Uint64(), rh, header.Root.Bytes(), header.Hash()))
					return errors.New("wrong trie root")
				}
			}

			computeCommitmentDuration += time.Since(start)
			if shouldGenerateChangesets {
				executor.domains().SavePastChangesetAccumulator(b.Hash(), blockNum, changeSet)
				if !inMemExec {
					if err := changeset2.WriteDiffSet(executor.tx(), blockNum, b.Hash(), changeSet); err != nil {
						return err
					}
				}
			}
			executor.domains().SetChangesetAccumulator(nil)
		}

		mxExecBlocks.Add(1)

		if offsetFromBlockBeginning > 0 {
			// after history execution no offset will be required
			offsetFromBlockBeginning = 0
		}

		// MA commitTx
		if !parallel {
			select {
			case <-logEvery.C:
				if inMemExec || isMining {
					break
				}

				stepsInDB := rawdbhelpers.IdxStepsCountV3(executor.tx())
				progress.Log("", executor.readState(), nil, nil, count, logGas, inputBlockNum.Load(), outputBlockNum.GetValueUint64(), outputTxNum.Load(), mxExecRepeats.GetValueUint64(), stepsInDB, shouldGenerateChangesets, inMemExec)

				//TODO: https://github.com/erigontech/erigon/issues/10724
				//if executor.tx().(dbstate.HasAggTx).AggTx().(*dbstate.AggregatorRoTx).CanPrune(executor.tx(), outputTxNum.Load()) {
				//	//small prune cause MDBX_TXN_FULL
				//	if _, err := executor.tx().(dbstate.HasAggTx).AggTx().(*dbstate.AggregatorRoTx).PruneSmallBatches(ctx, 10*time.Hour, executor.tx()); err != nil {
				//		return err
				//	}
				//}

				aggregatorRo := dbstate.AggTx(executor.tx())

				isBatchFull := executor.readState().SizeEstimate() >= commitThreshold
				canPrune := aggregatorRo.CanPrune(executor.tx(), outputTxNum.Load())
				needCalcRoot := isBatchFull ||
					skipPostEvaluation || // If we skip post evaluation, then we should compute root hash ASAP for fail-fast
					canPrune // if have something to prune - better prune ASAP to keep chaindata smaller
				if !needCalcRoot {
					break
				}

				var (
					commitStart = time.Now()

					pruneDuration time.Duration
				)
				ok, times, err := flushAndCheckCommitmentV3(ctx, b.HeaderNoCopy(), executor.tx(), executor.domains(), cfg, execStage, stageProgress, parallel, logger, u, inMemExec)
				if err != nil {
					return err
				} else if !ok {
					break Loop
				}

				computeCommitmentDuration += times.ComputeCommitment
				flushDuration := times.Flush

				timeStart := time.Now()

				// allow greedy prune on non-chain-tip
				pruneTimeout := 250 * time.Millisecond
				if initialCycle {
					pruneTimeout = 10 * time.Hour

					if err = executor.tx().(kv.TemporalRwTx).GreedyPruneHistory(ctx, kv.CommitmentDomain); err != nil {
						return err
					}
				}

				if _, err := aggregatorRo.PruneSmallBatches(ctx, pruneTimeout, executor.tx()); err != nil {
					return err
				}
				pruneDuration = time.Since(timeStart)

				commitDuration, err := executor.(*serialExecutor).commit(ctx, inputTxNum, outputBlockNum.GetValueUint64(), useExternalTx)
				if err != nil {
					return err
				}

				// on chain-tip: if batch is full then stop execution - to allow stages commit
				if !initialCycle && isBatchFull {
					errExhausted = &ErrLoopExhausted{From: startBlockNum, To: blockNum, Reason: "block batch is full"}
					break Loop
				}
				if !initialCycle && canPrune {
					errExhausted = &ErrLoopExhausted{From: startBlockNum, To: blockNum, Reason: "block batch can be pruned"}
					break Loop
				}
				if initialCycle {
					logger.Info("Committed", "time", time.Since(commitStart),
						"block", outputBlockNum.GetValueUint64(), "txNum", inputTxNum,
						"step", fmt.Sprintf("%.1f", float64(inputTxNum)/float64(agg.StepSize())),
						"flush", flushDuration, "compute commitment", computeCommitmentDuration, "tx.commit", commitDuration, "prune", pruneDuration)
				}
			default:
			}
		}

		if blockLimit > 0 && blockNum-startBlockNum+1 >= blockLimit {
			errExhausted = &ErrLoopExhausted{From: startBlockNum, To: blockNum, Reason: "block limit reached"}
			break
		}

		select {
		case <-ctx.Done():
			return ctx.Err()
		default:
		}
	}

	//log.Info("Executed", "blocks", inputBlockNum.Load(), "txs", outputTxNum.Load(), "repeats", mxExecRepeats.GetValueUint64())

	//fmt.Println("WAIT")
	executor.wait()

	if u != nil && !u.HasUnwindPoint() {
		if b != nil {
			_, _, err = flushAndCheckCommitmentV3(ctx, b.HeaderNoCopy(), executor.tx(), executor.domains(), cfg, execStage, stageProgress, parallel, logger, u, inMemExec)
			if err != nil {
				return err
			}
		} else {
			fmt.Printf("[dbg] mmmm... do we need action here????\n")
		}
	}

	//dumpPlainStateDebug(executor.tx(), executor.domains())

	if !useExternalTx && executor.tx() != nil {
		if err = executor.tx().Commit(); err != nil {
			return err
		}
		logger.Info("Committed", "blocks", inputBlockNum.Load())
	}

	logSnapshotBuildCallsite(logger, "exec3.final", outputTxNum.Load(), blockNum, maxBlockNum)
	agg.BuildFilesInBackground(outputTxNum.Load())

	if errExhausted != nil && blockNum < maxBlockNum {
		// special err allows the loop to continue, caller will call us again to continue from where we left off
		// only return it if we haven't reached the maxBlockNum
		return errExhausted
	}

	if !shouldReportToTxPool && cfg.notifications != nil && cfg.notifications.Accumulator != nil && !isMining && b != nil {
		// No reporting to the txn pool has been done since we are not within the "state-stream" window.
		// However, we should still at the very least report the last block number to it, so it can update its block progress.
		// Otherwise, we can get in a deadlock situation when there is a block building request in environments where
		// the Erigon process is the only block builder (e.g. some Hive tests, kurtosis testnets with one erigon block builder, etc.)
		cfg.notifications.Accumulator.StartChange(b.HeaderNoCopy(), nil, false /* unwind */)
	}

	return nil
}

var ERIGON_COMMIT_EACH_BLOCK = dbg.EnvBool("ERIGON_COMMIT_EACH_BLOCK", false)
var ERIGON_STOP_AT_BLOCK = dbg.EnvUint("ERIGON_STOP_AT_BLOCK", 0)
var ERIGON_BAD_ROOT_DEBUG = dbg.EnvBool("ERIGON_BAD_ROOT_DEBUG", false)
var ERIGON_SNAPSHOT_CALLSITE_DEBUG = dbg.EnvBool("ERIGON_SNAPSHOT_BUILD_DEBUG", false)
var ERIGON_BAD_ROOT_DUMP_STATE = dbg.EnvBool("ERIGON_BAD_ROOT_DUMP_STATE", false)
var ERIGON_BAD_ROOT_ACCOUNTS = dbg.EnvStrings("ERIGON_BAD_ROOT_ACCOUNTS", ",", nil)
var ERIGON_BAD_ROOT_DUMP_TOUCHED_ACCOUNTS = dbg.EnvBool("ERIGON_BAD_ROOT_DUMP_TOUCHED_ACCOUNTS", false)
var ERIGON_BAD_ROOT_DUMP_TOUCHED_ACCOUNTS_MAX = dbg.EnvInt("ERIGON_BAD_ROOT_DUMP_TOUCHED_ACCOUNTS_MAX", 200)
var ERIGON_BAD_ROOT_STORAGE_DIFF_TIMELINE_MAX = dbg.EnvInt("ERIGON_BAD_ROOT_STORAGE_DIFF_TIMELINE_MAX", 10)
var ERIGON_BAD_ROOT_PROBE_STORAGE_KEY = dbg.EnvString("ERIGON_BAD_ROOT_PROBE_STORAGE_KEY", "")
var ERIGON_MDBX_MIGRATE_FLUSH_ON_BAD_ROOT = dbg.EnvBool("ERIGON_MDBX_MIGRATE_FLUSH_ON_BAD_ROOT", false)
var ERIGON_MDBX_MIGRATE_SKIP_UNWIND_ON_BAD_ROOT = dbg.EnvBool("ERIGON_MDBX_MIGRATE_SKIP_UNWIND_ON_BAD_ROOT", false)

func logSnapshotBuildCallsite(logger log.Logger, where string, txNum uint64, blockNum uint64, maxBlockNum uint64) {
	if !ERIGON_SNAPSHOT_CALLSITE_DEBUG {
		return
	}
	logger.Info(
		"[snapshots] build callsite",
		"where", where,
		"txnum", txNum,
		"block", blockNum,
		"max_block", maxBlockNum,
	)
}

// nolint
func dumpPlainStateDebug(tx kv.TemporalRwTx, doms *dbstate.SharedDomains) {
	if doms != nil {
		doms.Flush(context.Background(), tx)
	}
	{
		it, err := tx.Debug().RangeLatest(kv.AccountsDomain, nil, nil, -1)
		if err != nil {
			panic(err)
		}
		for it.HasNext() {
			k, v, err := it.Next()
			if err != nil {
				panic(err)
			}
			a := accounts.NewAccount()
			accounts.DeserialiseV3(&a, v)
			fmt.Printf("%x, %d, %d, %d, %x\n", k, &a.Balance, a.Nonce, a.Incarnation, a.CodeHash)
		}
	}
	{
		it, err := tx.Debug().RangeLatest(kv.StorageDomain, nil, nil, -1)
		if err != nil {
			panic(1)
		}
		for it.HasNext() {
			k, v, err := it.Next()
			if err != nil {
				panic(err)
			}
			fmt.Printf("%x, %x\n", k, v)
		}
	}
	{
		it, err := tx.Debug().RangeLatest(kv.CommitmentDomain, nil, nil, -1)
		if err != nil {
			panic(1)
		}
		for it.HasNext() {
			k, v, err := it.Next()
			if err != nil {
				panic(err)
			}
			fmt.Printf("%x, %x\n", k, v)
			if bytes.Equal(k, []byte("state")) {
				fmt.Printf("state: t=%d b=%d\n", binary.BigEndian.Uint64(v[:8]), binary.BigEndian.Uint64(v[8:]))
			}
		}
	}
}

func badRootAccountList(header *types.Header, logger log.Logger) []common.Address {
	if header == nil {
		return nil
	}
	out := make([]common.Address, 0, len(ERIGON_BAD_ROOT_ACCOUNTS)+1)
	seen := make(map[common.Address]struct{}, len(ERIGON_BAD_ROOT_ACCOUNTS)+1)
	add := func(addr common.Address) {
		if _, ok := seen[addr]; ok {
			return
		}
		seen[addr] = struct{}{}
		out = append(out, addr)
	}

	add(header.Coinbase)
	for _, raw := range ERIGON_BAD_ROOT_ACCOUNTS {
		raw = strings.TrimSpace(raw)
		if raw == "" {
			continue
		}
		if !common.IsHexAddress(raw) {
			logger.Warn("Bad state root account address invalid", "value", raw)
			continue
		}
		add(common.HexToAddress(raw))
	}
	return out
}

func logBadRootAccounts(header *types.Header, applyTx kv.Tx, doms *dbstate.SharedDomains, logger log.Logger) {
	if header == nil {
		return
	}
	temporalTx, ok := applyTx.(kv.TemporalTx)
	if !ok {
		logger.Warn("Bad state root account log skipped", "reason", "non-temporal tx")
		return
	}
	addrs := badRootAccountList(header, logger)
	addrStrs := make([]string, 0, len(addrs))
	for _, addr := range addrs {
		addrStrs = append(addrStrs, addr.Hex())
	}
	logger.Warn("Bad state root account dump start",
		"block", header.Number.Uint64(),
		"count", len(addrs),
		"coinbase", header.Coinbase,
		"addrs", addrStrs,
	)
	if len(addrs) == 0 {
		return
	}
	if doms == nil {
		logger.Warn("Bad state root account log skipped", "reason", "missing domains")
		return
	}
	txNum := doms.TxNum()
	for _, addr := range addrs {
		val, step, err := doms.GetLatest(kv.AccountsDomain, temporalTx, addr[:])
		if err != nil {
			logger.Warn("Bad state root account read failed", "block", header.Number.Uint64(), "address", addr, "err", err)
			continue
		}
		storageRoot, storageItems, storageDigest, storageErr := computeStorageRootFromDomainWithDigest(temporalTx, addr, txNum)
		if storageErr != nil {
			logger.Warn("Bad state root storage root read failed", "block", header.Number.Uint64(), "address", addr, "tx_num", txNum, "err", storageErr)
		}
		latestRoot, latestItems, latestDigest, latestErr := computeStorageRootFromSharedLatestWithDigest(doms, temporalTx, addr)
		if latestErr != nil {
			logger.Warn("Bad state root storage latest root read failed", "block", header.Number.Uint64(), "address", addr, "tx_num", txNum, "err", latestErr)
		}
		if storageErr == nil && latestErr == nil {
			rootMatch := storageRoot == latestRoot
			itemsMatch := storageItems == latestItems
			digestMatch := storageDigest == latestDigest
			logger.Warn("Bad state root storage root compare",
				"block", header.Number.Uint64(),
				"address", addr,
				"tx_num", txNum,
				"asof_root", storageRoot,
				"asof_items", storageItems,
				"asof_digest", storageDigest,
				"latest_root", latestRoot,
				"latest_items", latestItems,
				"latest_digest", latestDigest,
				"root_match", rootMatch,
				"items_match", itemsMatch,
				"digest_match", digestMatch,
			)
			if !rootMatch || !itemsMatch || !digestMatch {
				asOfBySlot, asOfErr := collectStorageAsOfBySlot(temporalTx, addr, txNum)
				latestBySlot, latestMapErr := collectStorageLatestBySlot(doms, temporalTx, addr)
				if asOfErr != nil || latestMapErr != nil {
					logger.Warn("Bad state root storage slot diff unavailable",
						"block", header.Number.Uint64(),
						"address", addr,
						"tx_num", txNum,
						"asof_err", asOfErr,
						"latest_err", latestMapErr,
					)
				} else {
					onlyAsOf, onlyLatest, valueMismatch, samples := storageDiffSamples(asOfBySlot, latestBySlot, 10)
					logger.Warn("Bad state root storage slot diff summary",
						"block", header.Number.Uint64(),
						"address", addr,
						"tx_num", txNum,
						"asof_slots", len(asOfBySlot),
						"latest_slots", len(latestBySlot),
						"only_asof", onlyAsOf,
						"only_latest", onlyLatest,
						"value_mismatch", valueMismatch,
						"sample_count", len(samples),
					)
					for i, sample := range samples {
						logger.Warn("Bad state root storage slot diff sample",
							"block", header.Number.Uint64(),
							"address", addr,
							"tx_num", txNum,
							"idx", i,
							"sample", sample,
						)
					}
					diffSlots := storageDiffSlots(asOfBySlot, latestBySlot, ERIGON_BAD_ROOT_STORAGE_DIFF_TIMELINE_MAX)
					logStorageDiffTxTimeline("account_dump", header.Number.Uint64(), temporalTx, doms, addr, txNum, diffSlots, logger)
				}
			}
		}
		if len(val) == 0 {
			logger.Warn("Bad state root account missing",
				"block", header.Number.Uint64(),
				"address", addr,
				"step", step,
				"tx_num", txNum,
				"storage_root", storageRoot,
				"storage_items", storageItems,
				"storage_digest", storageDigest,
			)
			continue
		}
		acc := accounts.NewAccount()
		if err := accounts.DeserialiseV3(&acc, val); err != nil {
			logger.Warn("Bad state root account decode failed", "block", header.Number.Uint64(), "address", addr, "err", err)
			continue
		}
		logger.Warn("Bad state root account",
			"block", header.Number.Uint64(),
			"address", addr,
			"nonce", acc.Nonce,
			"balance", acc.Balance.String(),
			"incarnation", acc.Incarnation,
			"code_hash", acc.CodeHash,
			"root", acc.Root,
			"step", step,
			"tx_num", txNum,
			"storage_root", storageRoot,
			"storage_items", storageItems,
			"storage_digest", storageDigest,
		)
	}
}

func computeStorageRootFromDomainWithDigest(ttx kv.TemporalTx, addr common.Address, txNum uint64) (common.Hash, int, string, error) {
	to, ok := kv.NextSubtree(addr[:])
	if !ok {
		to = nil
	}
	it, err := ttx.RangeAsOf(kv.StorageDomain, addr[:], to, txNum, order.Asc, kv.Unlim)
	if err != nil {
		return common.Hash{}, 0, "", err
	}
	defer it.Close()

	tr := etrie.New(common.Hash{})
	digest := sha256.New()
	items := 0
	for it.HasNext() {
		k, v, err := it.Next()
		if err != nil {
			return common.Hash{}, items, "", err
		}
		if len(v) == 0 {
			continue
		}
		if len(k) < 20 {
			return common.Hash{}, items, "", fmt.Errorf("short storage key: %d bytes", len(k))
		}
		slot := k[20:]
		slotHash, _ := common.HashData(slot)
		tr.Update(slotHash.Bytes(), common.Copy(v))
		var lenBuf [8]byte
		binary.BigEndian.PutUint64(lenBuf[:], uint64(len(v)))
		digest.Write(slotHash.Bytes())
		digest.Write(lenBuf[:])
		digest.Write(v)
		items++
	}
	return tr.Hash(), items, hex.EncodeToString(digest.Sum(nil)), nil
}

func computeStorageRootFromDomain(ttx kv.TemporalTx, addr common.Address, txNum uint64) (common.Hash, int, error) {
	root, items, _, err := computeStorageRootFromDomainWithDigest(ttx, addr, txNum)
	return root, items, err
}

func computeStorageRootFromSharedLatestWithDigest(doms *dbstate.SharedDomains, tx kv.Tx, addr common.Address) (common.Hash, int, string, error) {
	if doms == nil || tx == nil {
		return common.Hash{}, 0, "", errors.New("missing domains or tx")
	}
	tr := etrie.New(common.Hash{})
	digest := sha256.New()
	items := 0
	err := doms.IteratePrefix(kv.StorageDomain, addr.Bytes(), tx, func(k []byte, v []byte, step kv.Step) (bool, error) {
		if len(v) == 0 {
			return true, nil
		}
		if len(k) < 20 {
			return false, fmt.Errorf("short storage key: %d bytes", len(k))
		}
		slot := k[20:]
		slotHash, _ := common.HashData(slot)
		tr.Update(slotHash.Bytes(), common.Copy(v))
		var lenBuf [8]byte
		binary.BigEndian.PutUint64(lenBuf[:], uint64(len(v)))
		digest.Write(slotHash.Bytes())
		digest.Write(lenBuf[:])
		digest.Write(v)
		items++
		return true, nil
	})
	if err != nil {
		return common.Hash{}, items, "", err
	}
	return tr.Hash(), items, hex.EncodeToString(digest.Sum(nil)), nil
}

func collectStorageAsOfBySlot(ttx kv.TemporalTx, addr common.Address, txNum uint64) (map[string][]byte, error) {
	to, ok := kv.NextSubtree(addr[:])
	if !ok {
		to = nil
	}
	it, err := ttx.RangeAsOf(kv.StorageDomain, addr[:], to, txNum, order.Asc, kv.Unlim)
	if err != nil {
		return nil, err
	}
	defer it.Close()

	entries := make(map[string][]byte)
	for it.HasNext() {
		k, v, err := it.Next()
		if err != nil {
			return nil, err
		}
		if len(v) == 0 || len(k) < 20 {
			continue
		}
		slotHex := hex.EncodeToString(k[20:])
		entries[slotHex] = common.Copy(v)
	}
	return entries, nil
}

func collectStorageLatestBySlot(doms *dbstate.SharedDomains, tx kv.Tx, addr common.Address) (map[string][]byte, error) {
	if doms == nil || tx == nil {
		return nil, errors.New("missing domains or tx")
	}
	entries := make(map[string][]byte)
	err := doms.IteratePrefix(kv.StorageDomain, addr[:], tx, func(k []byte, v []byte, step kv.Step) (bool, error) {
		if len(v) == 0 || len(k) < 20 {
			return true, nil
		}
		slotHex := hex.EncodeToString(k[20:])
		entries[slotHex] = common.Copy(v)
		return true, nil
	})
	if err != nil {
		return nil, err
	}
	return entries, nil
}

func storageDiffSamples(asOf, latest map[string][]byte, max int) (onlyAsOf int, onlyLatest int, valueMismatch int, samples []string) {
	if max <= 0 {
		max = 5
	}
	asOfKeys := make([]string, 0, len(asOf))
	for k := range asOf {
		asOfKeys = append(asOfKeys, k)
	}
	sort.Strings(asOfKeys)
	for _, slot := range asOfKeys {
		asVal := asOf[slot]
		latestVal, ok := latest[slot]
		if !ok {
			onlyAsOf++
			if len(samples) < max {
				samples = append(samples, fmt.Sprintf("only_asof slot=0x%s asof_val=0x%x", slot, asVal))
			}
			continue
		}
		if !bytes.Equal(asVal, latestVal) {
			valueMismatch++
			if len(samples) < max {
				samples = append(samples, fmt.Sprintf("value_mismatch slot=0x%s asof_val=0x%x latest_val=0x%x", slot, asVal, latestVal))
			}
		}
	}
	latestKeys := make([]string, 0, len(latest))
	for k := range latest {
		latestKeys = append(latestKeys, k)
	}
	sort.Strings(latestKeys)
	for _, slot := range latestKeys {
		if _, ok := asOf[slot]; ok {
			continue
		}
		onlyLatest++
		if len(samples) < max {
			samples = append(samples, fmt.Sprintf("only_latest slot=0x%s latest_val=0x%x", slot, latest[slot]))
		}
	}
	return onlyAsOf, onlyLatest, valueMismatch, samples
}

func storageDiffSlots(asOf, latest map[string][]byte, max int) []string {
	if max <= 0 {
		max = 10
	}
	out := make([]string, 0, max)
	appendSlot := func(slot string) {
		if len(out) >= max {
			return
		}
		out = append(out, slot)
	}

	asOfKeys := make([]string, 0, len(asOf))
	for k := range asOf {
		asOfKeys = append(asOfKeys, k)
	}
	sort.Strings(asOfKeys)
	for _, slot := range asOfKeys {
		asVal := asOf[slot]
		latestVal, ok := latest[slot]
		if !ok || !bytes.Equal(asVal, latestVal) {
			appendSlot(slot)
		}
	}

	if len(out) >= max {
		return out
	}

	latestKeys := make([]string, 0, len(latest))
	for k := range latest {
		latestKeys = append(latestKeys, k)
	}
	sort.Strings(latestKeys)
	for _, slot := range latestKeys {
		if _, ok := asOf[slot]; ok {
			continue
		}
		appendSlot(slot)
		if len(out) >= max {
			break
		}
	}

	return out
}

func storageValuePreview(v []byte) string {
	if len(v) == 0 {
		return "0x"
	}
	if len(v) <= 16 {
		return fmt.Sprintf("0x%x", v)
	}
	return fmt.Sprintf("0x%x...(+%d bytes)", v[:16], len(v)-16)
}

func logStorageDiffTxTimeline(source string, blockNum uint64, temporalTx kv.TemporalTx, doms *dbstate.SharedDomains, addr common.Address, txNum uint64, slots []string, logger log.Logger) {
	if len(slots) == 0 || temporalTx == nil || doms == nil || logger == nil {
		return
	}
	for idx, slotHex := range slots {
		slot, err := hex.DecodeString(slotHex)
		if err != nil {
			logger.Warn("Bad state root storage slot timeline decode failed",
				"source", source,
				"block", blockNum,
				"address", addr,
				"slot", slotHex,
				"err", err,
			)
			continue
		}
		key := make([]byte, 20+len(slot))
		copy(key[:20], addr[:])
		copy(key[20:], slot)

		var (
			asOfPrev    []byte
			asOfPrevOk  bool
			asOfPrevErr error
			prevTxNum   uint64
		)
		if txNum > 0 {
			prevTxNum = txNum - 1
			asOfPrev, asOfPrevOk, asOfPrevErr = temporalTx.GetAsOf(kv.StorageDomain, key, prevTxNum)
		}
		asOfNow, asOfNowOk, asOfNowErr := temporalTx.GetAsOf(kv.StorageDomain, key, txNum)

		nextTxNum := txNum
		if txNum < ^uint64(0) {
			nextTxNum = txNum + 1
		}
		asOfNext, asOfNextOk, asOfNextErr := temporalTx.GetAsOf(kv.StorageDomain, key, nextTxNum)

		memLatest, memStep, memOK := doms.DebugGetLatestFromMem(kv.StorageDomain, key)
		domsLatest, domsStep, domsErr := doms.GetLatest(kv.StorageDomain, temporalTx, key)
		dbLatest, dbStep, dbErr := temporalTx.GetLatest(kv.StorageDomain, key)

		logger.Warn("Bad state root storage slot timeline",
			"source", source,
			"block", blockNum,
			"address", addr,
			"tx_num", txNum,
			"idx", idx,
			"slot", "0x"+slotHex,
			"asof_prev_tx", prevTxNum,
			"asof_prev_ok", asOfPrevOk,
			"asof_prev_err", asOfPrevErr,
			"asof_prev_len", len(asOfPrev),
			"asof_prev_preview", storageValuePreview(asOfPrev),
			"asof_now_ok", asOfNowOk,
			"asof_now_err", asOfNowErr,
			"asof_now_len", len(asOfNow),
			"asof_now_preview", storageValuePreview(asOfNow),
			"asof_next_tx", nextTxNum,
			"asof_next_ok", asOfNextOk,
			"asof_next_err", asOfNextErr,
			"asof_next_len", len(asOfNext),
			"asof_next_preview", storageValuePreview(asOfNext),
			"mem_latest_ok", memOK,
			"mem_latest_step", memStep,
			"mem_latest_len", len(memLatest),
			"mem_latest_preview", storageValuePreview(memLatest),
			"doms_latest_step", domsStep,
			"doms_latest_err", domsErr,
			"doms_latest_len", len(domsLatest),
			"doms_latest_preview", storageValuePreview(domsLatest),
			"db_latest_step", dbStep,
			"db_latest_err", dbErr,
			"db_latest_len", len(dbLatest),
			"db_latest_preview", storageValuePreview(dbLatest),
			"doms_vs_mem_match", bytes.Equal(domsLatest, memLatest),
			"db_vs_mem_match", bytes.Equal(dbLatest, memLatest),
			"doms_vs_db_match", bytes.Equal(domsLatest, dbLatest),
		)
	}
}

func logBadRootTouchedAccounts(header *types.Header, applyTx kv.Tx, doms *dbstate.SharedDomains, touchedPlainKeys [][]byte, logger log.Logger) {
	if header == nil || doms == nil {
		return
	}
	if !ERIGON_BAD_ROOT_DUMP_TOUCHED_ACCOUNTS {
		return
	}
	temporalTx, ok := applyTx.(kv.TemporalTx)
	if !ok {
		logger.Warn("Bad state root touched account log skipped", "reason", "non-temporal tx")
		return
	}
	keys := touchedPlainKeys
	if len(keys) == 0 {
		commitCtx := doms.GetCommitmentContext()
		if commitCtx == nil {
			logger.Warn("Bad state root touched account log skipped", "reason", "missing commitment context")
			return
		}
		keys = commitCtx.DebugLastPlainKeys()
		if len(keys) == 0 {
			keys = commitCtx.DebugPlainKeys()
		}
	}
	if len(keys) == 0 {
		logger.Warn("Bad state root touched account log skipped", "reason", "no touched keys")
		return
	}
	txNum, err := rawdbv3.TxNums.Max(temporalTx, header.Number.Uint64())
	if err != nil {
		logger.Warn("Bad state root touched account txnum read failed", "block", header.Number.Uint64(), "err", err)
		return
	}

	addrSet := make(map[string]struct{}, len(keys))
	for _, key := range keys {
		if len(key) < 20 {
			continue
		}
		addrSet[string(key[:20])] = struct{}{}
	}
	if len(addrSet) == 0 {
		logger.Warn("Bad state root touched account log skipped", "reason", "no addresses")
		return
	}

	addrs := make([]string, 0, len(addrSet))
	for addr := range addrSet {
		addrs = append(addrs, addr)
	}
	sort.Slice(addrs, func(i, j int) bool {
		return bytes.Compare([]byte(addrs[i]), []byte(addrs[j])) < 0
	})

	max := ERIGON_BAD_ROOT_DUMP_TOUCHED_ACCOUNTS_MAX
	if max <= 0 || max > len(addrs) {
		max = len(addrs)
	}

	logger.Warn("Bad state root touched accounts summary",
		"block", header.Number.Uint64(),
		"count", len(addrs),
		"max", max,
	)
	for i := 0; i < max; i++ {
		addr := common.BytesToAddress([]byte(addrs[i]))
		val, step, err := doms.GetLatest(kv.AccountsDomain, temporalTx, addr[:])
		if err != nil {
			logger.Warn("Bad state root touched account read failed", "block", header.Number.Uint64(), "address", addr, "err", err)
			continue
		}

		root, items, digest, err := computeStorageRootFromDomainWithDigest(temporalTx, addr, txNum)
		if err != nil {
			logger.Warn("Bad state root touched account storage root failed", "block", header.Number.Uint64(), "address", addr, "err", err)
			continue
		}
		latestRoot, latestItems, latestDigest, latestErr := computeStorageRootFromSharedLatestWithDigest(doms, temporalTx, addr)
		if latestErr != nil {
			logger.Warn("Bad state root touched account latest storage root failed", "block", header.Number.Uint64(), "address", addr, "err", latestErr)
		} else {
			rootMatch := root == latestRoot
			itemsMatch := items == latestItems
			digestMatch := digest == latestDigest
			logger.Warn("Bad state root touched account storage compare",
				"block", header.Number.Uint64(),
				"address", addr,
				"tx_num", txNum,
				"asof_root", root,
				"asof_items", items,
				"asof_digest", digest,
				"latest_root", latestRoot,
				"latest_items", latestItems,
				"latest_digest", latestDigest,
				"root_match", rootMatch,
				"items_match", itemsMatch,
				"digest_match", digestMatch,
			)
			if !rootMatch || !itemsMatch || !digestMatch {
				asOfBySlot, asOfErr := collectStorageAsOfBySlot(temporalTx, addr, txNum)
				latestBySlot, latestMapErr := collectStorageLatestBySlot(doms, temporalTx, addr)
				if asOfErr != nil || latestMapErr != nil {
					logger.Warn("Bad state root touched account storage diff unavailable",
						"block", header.Number.Uint64(),
						"address", addr,
						"tx_num", txNum,
						"asof_err", asOfErr,
						"latest_err", latestMapErr,
					)
				} else {
					onlyAsOf, onlyLatest, valueMismatch, samples := storageDiffSamples(asOfBySlot, latestBySlot, 10)
					logger.Warn("Bad state root touched account storage diff summary",
						"block", header.Number.Uint64(),
						"address", addr,
						"tx_num", txNum,
						"asof_slots", len(asOfBySlot),
						"latest_slots", len(latestBySlot),
						"only_asof", onlyAsOf,
						"only_latest", onlyLatest,
						"value_mismatch", valueMismatch,
						"sample_count", len(samples),
					)
					for i, sample := range samples {
						logger.Warn("Bad state root touched account storage diff sample",
							"block", header.Number.Uint64(),
							"address", addr,
							"tx_num", txNum,
							"idx", i,
							"sample", sample,
						)
					}
					diffSlots := storageDiffSlots(asOfBySlot, latestBySlot, ERIGON_BAD_ROOT_STORAGE_DIFF_TIMELINE_MAX)
					logStorageDiffTxTimeline("touched_accounts", header.Number.Uint64(), temporalTx, doms, addr, txNum, diffSlots, logger)
				}
			}
		}

		if len(val) == 0 {
			logger.Warn("Bad state root touched account missing",
				"block", header.Number.Uint64(),
				"address", addr,
				"storage_root", root,
				"storage_items", items,
				"storage_digest", digest,
				"step", step,
			)
			continue
		}

		acc := accounts.NewAccount()
		if err := accounts.DeserialiseV3(&acc, val); err != nil {
			logger.Warn("Bad state root touched account decode failed", "block", header.Number.Uint64(), "address", addr, "err", err)
			continue
		}
		logger.Warn("Bad state root touched account",
			"block", header.Number.Uint64(),
			"address", addr,
			"nonce", acc.Nonce,
			"balance", acc.Balance.String(),
			"incarnation", acc.Incarnation,
			"code_hash", acc.CodeHash,
			"account_root", acc.Root,
			"root", root,
			"storage_items", items,
			"storage_digest", digest,
			"step", step,
		)
	}
}

func logBadRootTxNumScan(ctx context.Context, header *types.Header, computedRootHash []byte, applyTx kv.Tx, doms *dbstate.SharedDomains, logPrefix string, logger log.Logger) {
	if header == nil || applyTx == nil || doms == nil || logger == nil {
		return
	}
	if header.Number == nil {
		return
	}
	temporalTx, ok := applyTx.(kv.TemporalTx)
	if !ok {
		logger.Warn("Bad state root txnum scan skipped", "reason", "non-temporal tx")
		return
	}

	blockNum := header.Number.Uint64()
	domsTxNum := doms.TxNum()
	expectedRoot := header.Root
	computedRoot := common.BytesToHash(computedRootHash)

	minTxNum, minErr := rawdbv3.TxNums.Min(temporalTx, blockNum)
	maxTxNum, maxErr := rawdbv3.TxNums.Max(temporalTx, blockNum)
	var parentMaxTxNum uint64
	parentMaxSet := false
	var parentErr error
	if blockNum > 0 {
		parentMaxTxNum, parentErr = rawdbv3.TxNums.Max(temporalTx, blockNum-1)
		parentMaxSet = parentErr == nil
	}

	logger.Warn("Bad state root txnum context",
		"block", blockNum,
		"doms_txnum", domsTxNum,
		"txnums_min", minTxNum,
		"txnums_max", maxTxNum,
		"txnums_min_err", minErr,
		"txnums_max_err", maxErr,
		"parent_max_txnum", parentMaxTxNum,
		"parent_max_set", parentMaxSet,
		"parent_max_err", parentErr,
		"expected_root", expectedRoot,
		"computed_root", computedRoot,
	)

	candidates := make(map[uint64]struct{}, 16)
	addCandidate := func(txNum uint64) {
		candidates[txNum] = struct{}{}
	}

	addCandidate(domsTxNum)
	if minErr == nil {
		addCandidate(minTxNum)
	}
	if maxErr == nil {
		addCandidate(maxTxNum)
	}
	if parentMaxSet {
		addCandidate(parentMaxTxNum)
		if parentMaxTxNum < ^uint64(0) {
			addCandidate(parentMaxTxNum + 1)
		}
	}
	for delta := uint64(1); delta <= 4; delta++ {
		if domsTxNum >= delta {
			addCandidate(domsTxNum - delta)
		}
		addCandidate(domsTxNum + delta)
	}

	ordered := make([]uint64, 0, len(candidates))
	for txNum := range candidates {
		ordered = append(ordered, txNum)
	}
	sort.Slice(ordered, func(i, j int) bool { return ordered[i] < ordered[j] })

	for _, txNum := range ordered {
		root, err := doms.ComputeCommitment(ctx, true, blockNum, txNum, logPrefix)
		if err != nil {
			logger.Warn("Bad state root txnum scan",
				"block", blockNum,
				"tx_num", txNum,
				"err", err,
			)
			continue
		}
		rootHash := common.BytesToHash(root)
		inBlockRange := minErr == nil && maxErr == nil && txNum >= minTxNum && txNum <= maxTxNum
		logger.Warn("Bad state root txnum scan",
			"block", blockNum,
			"tx_num", txNum,
			"root", rootHash,
			"matches_expected_header", rootHash == expectedRoot,
			"matches_computed_root", rootHash == computedRoot,
			"in_block_txnum_range", inBlockRange,
			"is_parent_max", parentMaxSet && txNum == parentMaxTxNum,
			"is_first_after_parent", parentMaxSet && txNum == parentMaxTxNum+1,
			"is_doms_txnum", txNum == domsTxNum,
		)
	}
}

func logCommitmentAnchorProbe(phase string, blockNum uint64, doms *dbstate.SharedDomains, applyTx kv.Tx, computedRoot []byte, logger log.Logger) {
	if !ERIGON_BAD_ROOT_DEBUG || blockNum < 33 {
		return
	}
	if logger == nil || doms == nil || applyTx == nil {
		return
	}

	temporalTx, ok := applyTx.(kv.TemporalTx)
	if !ok {
		logger.Warn("commitment anchor probe skipped", "phase", phase, "block", blockNum, "reason", "non-temporal tx")
		return
	}

	stateVal, stateStep, err := temporalTx.GetLatest(kv.CommitmentDomain, commitmentdb.KeyCommitmentState)
	if err != nil {
		logger.Warn("commitment anchor probe read failed", "phase", phase, "block", blockNum, "err", err)
		return
	}

	var stateTxNum uint64
	var stateBlockNum uint64
	stateDecoded := false
	if len(stateVal) >= 16 {
		stateTxNum = binary.BigEndian.Uint64(stateVal[:8])
		stateBlockNum = binary.BigEndian.Uint64(stateVal[8:16])
		stateDecoded = true
	}

	lastPlainKeys := 0
	ctxHasTrie := false
	ctxTxNum := uint64(0)
	ctxLimitReadAsOfTxNum := uint64(0)
	ctxWithHistory := false
	liveTrieRoot := common.Hash{}
	liveTrieRootErr := ""
	encodedStateRoot := common.Hash{}
	encodedStateRootErr := ""
	encodedStateBlockNum := uint64(0)
	encodedStateTxNum := uint64(0)
	commitCtx := doms.GetCommitmentContext()
	if commitCtx != nil {
		lastPlainKeys = len(commitCtx.DebugLastPlainKeys())
		ctxTxNum, ctxLimitReadAsOfTxNum, ctxWithHistory, ctxHasTrie = commitCtx.DebugReadContext()
		if liveRoot, err := commitCtx.DebugCurrentRootHash(); err != nil {
			liveTrieRootErr = err.Error()
		} else if len(liveRoot) > 0 {
			liveTrieRoot = common.BytesToHash(liveRoot)
		}
		if len(stateVal) > 0 {
			stateBlock, stateTx, stateRoot, err := commitCtx.DebugStateRootFromEncoded(stateVal)
			if err != nil {
				encodedStateRootErr = err.Error()
			} else {
				encodedStateBlockNum = stateBlock
				encodedStateTxNum = stateTx
				if len(stateRoot) > 0 {
					encodedStateRoot = common.BytesToHash(stateRoot)
				}
			}
		}
	}

	probeStorageKey := strings.TrimSpace(ERIGON_BAD_ROOT_PROBE_STORAGE_KEY)
	probeStorageKeyLen := 0
	probeStorageStep := kv.Step(0)
	probeStorageValLen := 0
	probeStorageVal := common.Hash{}
	probeStorageReadErr := ""
	probeStorageAsOfStateOk := false
	probeStorageAsOfStateLen := 0
	probeStorageAsOfStateVal := common.Hash{}
	probeStorageAsOfStateErr := ""
	probeStorageAsOfDomsOk := false
	probeStorageAsOfDomsLen := 0
	probeStorageAsOfDomsVal := common.Hash{}
	probeStorageAsOfDomsErr := ""
	probeAccountAddr := ""
	probeAccountStep := kv.Step(0)
	probeAccountValLen := 0
	probeAccountVal := common.Hash{}
	probeAccountReadErr := ""
	probeAccountAsOfStateOk := false
	probeAccountAsOfStateLen := 0
	probeAccountAsOfStateVal := common.Hash{}
	probeAccountAsOfStateErr := ""
	probeAccountAsOfDomsOk := false
	probeAccountAsOfDomsLen := 0
	probeAccountAsOfDomsVal := common.Hash{}
	probeAccountAsOfDomsErr := ""
	if probeStorageKey != "" {
		plainStorageKey := common.FromHex(probeStorageKey)
		probeStorageKeyLen = len(plainStorageKey)
		if len(plainStorageKey) == 0 {
			probeStorageReadErr = "invalid ERIGON_BAD_ROOT_PROBE_STORAGE_KEY"
		} else {
			val, step, readErr := doms.GetLatest(kv.StorageDomain, temporalTx, plainStorageKey)
			if readErr != nil {
				probeStorageReadErr = readErr.Error()
			} else {
				probeStorageStep = step
				probeStorageValLen = len(val)
				if len(val) > 0 {
					probeStorageVal = common.BytesToHash(val)
				}
			}

			if stateDecoded {
				asOfState, ok, asOfErr := temporalTx.GetAsOf(kv.StorageDomain, plainStorageKey, stateTxNum)
				probeStorageAsOfStateOk = ok
				if asOfErr != nil {
					probeStorageAsOfStateErr = asOfErr.Error()
				} else if ok {
					probeStorageAsOfStateLen = len(asOfState)
					if len(asOfState) > 0 {
						probeStorageAsOfStateVal = common.BytesToHash(asOfState)
					}
				}
			}

			asOfDoms, okDoms, asOfDomsErr := temporalTx.GetAsOf(kv.StorageDomain, plainStorageKey, doms.TxNum())
			probeStorageAsOfDomsOk = okDoms
			if asOfDomsErr != nil {
				probeStorageAsOfDomsErr = asOfDomsErr.Error()
			} else if okDoms {
				probeStorageAsOfDomsLen = len(asOfDoms)
				if len(asOfDoms) > 0 {
					probeStorageAsOfDomsVal = common.BytesToHash(asOfDoms)
				}
			}

			if len(plainStorageKey) >= 20 {
				accountKey := plainStorageKey[:20]
				probeAccountAddr = common.BytesToAddress(accountKey).Hex()

				accountVal, accountStep, accountErr := doms.GetLatest(kv.AccountsDomain, temporalTx, accountKey)
				if accountErr != nil {
					probeAccountReadErr = accountErr.Error()
				} else {
					probeAccountStep = accountStep
					probeAccountValLen = len(accountVal)
					if len(accountVal) > 0 {
						probeAccountVal = common.BytesToHash(accountVal)
					}
				}

				if stateDecoded {
					accountAsOfState, ok, accountAsOfStateErr := temporalTx.GetAsOf(kv.AccountsDomain, accountKey, stateTxNum)
					probeAccountAsOfStateOk = ok
					if accountAsOfStateErr != nil {
						probeAccountAsOfStateErr = accountAsOfStateErr.Error()
					} else if ok {
						probeAccountAsOfStateLen = len(accountAsOfState)
						if len(accountAsOfState) > 0 {
							probeAccountAsOfStateVal = common.BytesToHash(accountAsOfState)
						}
					}
				}

				accountAsOfDoms, ok, accountAsOfDomsErr := temporalTx.GetAsOf(kv.AccountsDomain, accountKey, doms.TxNum())
				probeAccountAsOfDomsOk = ok
				if accountAsOfDomsErr != nil {
					probeAccountAsOfDomsErr = accountAsOfDomsErr.Error()
				} else if ok {
					probeAccountAsOfDomsLen = len(accountAsOfDoms)
					if len(accountAsOfDoms) > 0 {
						probeAccountAsOfDomsVal = common.BytesToHash(accountAsOfDoms)
					}
				}
			}
		}
	}

	computed := common.Hash{}
	if len(computedRoot) > 0 {
		computed = common.BytesToHash(computedRoot)
	}

	logger.Warn("commitment anchor probe",
		"phase", phase,
		"block", blockNum,
		"doms_block", doms.BlockNum(),
		"doms_txnum", doms.TxNum(),
		"state_val_len", len(stateVal),
		"state_step", stateStep,
		"state_decoded", stateDecoded,
		"state_txnum", stateTxNum,
		"state_block", stateBlockNum,
		"last_plain_keys", lastPlainKeys,
		"ctx_has_trie", ctxHasTrie,
		"ctx_txnum", ctxTxNum,
		"ctx_limit_read_as_of_txnum", ctxLimitReadAsOfTxNum,
		"ctx_with_history", ctxWithHistory,
		"live_trie_root", liveTrieRoot,
		"live_trie_root_err", liveTrieRootErr,
		"encoded_state_root", encodedStateRoot,
		"encoded_state_root_err", encodedStateRootErr,
		"encoded_state_block", encodedStateBlockNum,
		"encoded_state_txnum", encodedStateTxNum,
		"live_matches_encoded", liveTrieRoot == encodedStateRoot && liveTrieRootErr == "" && encodedStateRootErr == "",
		"encoded_matches_computed", len(computedRoot) > 0 && encodedStateRoot == common.BytesToHash(computedRoot) && encodedStateRootErr == "",
		"probe_storage_key", probeStorageKey,
		"probe_storage_key_len", probeStorageKeyLen,
		"probe_storage_step", probeStorageStep,
		"probe_storage_val_len", probeStorageValLen,
		"probe_storage_val", probeStorageVal,
		"probe_storage_read_err", probeStorageReadErr,
		"probe_storage_asof_state_ok", probeStorageAsOfStateOk,
		"probe_storage_asof_state_len", probeStorageAsOfStateLen,
		"probe_storage_asof_state_val", probeStorageAsOfStateVal,
		"probe_storage_asof_state_err", probeStorageAsOfStateErr,
		"probe_storage_asof_doms_ok", probeStorageAsOfDomsOk,
		"probe_storage_asof_doms_len", probeStorageAsOfDomsLen,
		"probe_storage_asof_doms_val", probeStorageAsOfDomsVal,
		"probe_storage_asof_doms_err", probeStorageAsOfDomsErr,
		"probe_account_addr", probeAccountAddr,
		"probe_account_step", probeAccountStep,
		"probe_account_val_len", probeAccountValLen,
		"probe_account_val", probeAccountVal,
		"probe_account_read_err", probeAccountReadErr,
		"probe_account_asof_state_ok", probeAccountAsOfStateOk,
		"probe_account_asof_state_len", probeAccountAsOfStateLen,
		"probe_account_asof_state_val", probeAccountAsOfStateVal,
		"probe_account_asof_state_err", probeAccountAsOfStateErr,
		"probe_account_asof_doms_ok", probeAccountAsOfDomsOk,
		"probe_account_asof_doms_len", probeAccountAsOfDomsLen,
		"probe_account_asof_doms_val", probeAccountAsOfDomsVal,
		"probe_account_asof_doms_err", probeAccountAsOfDomsErr,
		"computed_root", computed,
	)
}

func logBadRootDetails(ctx context.Context, header *types.Header, computedRootHash []byte, applyTx kv.Tx, doms *dbstate.SharedDomains, touchedPlainKeys [][]byte, cfg ExecuteBlockCfg, e *StageState, maxBlockNum uint64, logger log.Logger) {
	if header == nil {
		logger.Warn("Bad state root details: missing header")
		return
	}
	if header.Number == nil {
		logger.Warn("Bad state root details: missing header number", "hash", header.Hash())
		return
	}

	chainID := "<nil>"
	if cfg.chainConfig != nil && cfg.chainConfig.ChainID != nil {
		chainID = cfg.chainConfig.ChainID.String()
	}

	logger.Warn("Bad state root details",
		"block", header.Number.Uint64(),
		"hash", header.Hash(),
		"parent_hash", header.ParentHash,
		"expected_root", header.Root,
		"computed_root", common.BytesToHash(computedRootHash),
		"chain_id", chainID,
		"tx_root", header.TxHash,
		"receipt_root", header.ReceiptHash,
		"withdrawals_root", header.WithdrawalsHash,
		"gas_used", header.GasUsed,
		"gas_limit", header.GasLimit,
		"time", header.Time,
		"base_fee", header.BaseFee,
		"difficulty", header.Difficulty,
		"coinbase", header.Coinbase,
		"extra_len", len(header.Extra),
		"aura_step", header.AuRaStep,
		"aura_seal_len", len(header.AuRaSeal),
		"blob_gas_used", header.BlobGasUsed,
		"excess_blob_gas", header.ExcessBlobGas,
		"parent_beacon_root", header.ParentBeaconBlockRoot,
		"requests_hash", header.RequestsHash,
	)
	if ERIGON_BAD_ROOT_DEBUG {
		logBadRootTxNumScan(ctx, header, computedRootHash, applyTx, doms, e.LogPrefix(), logger)
	}

	if doms != nil {
		logger.Warn("Bad state root progress",
			"domains_block", doms.BlockNum(),
			"domains_txnum", doms.TxNum(),
			"stage_block", e.BlockNumber,
			"target_block", maxBlockNum,
		)
	} else {
		logger.Warn("Bad state root progress", "stage_block", e.BlockNumber, "target_block", maxBlockNum)
	}

	if ERIGON_BAD_ROOT_DEBUG {
		logBlockDetails := func(source string, b *types.Block) {
			txs := b.Transactions()
			computedTxRoot := types.DeriveSha(txs)
			logger.Warn("Bad state root block info",
				"source", source,
				"txs", len(txs),
				"uncles", len(b.Uncles()),
				"withdrawals", len(b.Withdrawals()),
				"size", b.Size(),
				"tx_root_header", header.TxHash,
				"tx_root_computed", computedTxRoot,
				"tx_root_match", computedTxRoot == header.TxHash,
			)
			if len(txs) > 0 {
				logger.Warn("Bad state root tx sample",
					"source", source,
					"first", txs[0].Hash(),
					"last", txs[len(txs)-1].Hash(),
				)
				if itx, ok := txs[0].Unwrap().(*types.ArbitrumInternalTx); ok {
					selector := "<short>"
					if len(itx.Data) >= 4 {
						selector = fmt.Sprintf("%x", itx.Data[:4])
					}
					if len(itx.Data) >= 4 && *(*[4]byte)(itx.Data[:4]) == arbos.InternalTxStartBlockMethodID {
						inputs, err := arbosutil.UnpackInternalTxDataStartBlock(itx.Data)
						if err != nil {
							logger.Warn("Bad state root internal tx decode failed",
								"source", source,
								"block", b.NumberU64(),
								"tx_hash", txs[0].Hash(),
								"selector", selector,
								"err", err,
							)
						} else {
							l1BlockNumber, _ := inputs["l1BlockNumber"].(uint64)
							l2BlockNumber, _ := inputs["l2BlockNumber"].(uint64)
							timePassed, _ := inputs["timePassed"].(uint64)
							l1BaseFee := inputs["l1BaseFee"]
							headerInfo := types.DeserializeHeaderExtraInformation(header)
							logger.Warn("Bad state root internal tx startblock",
								"source", source,
								"block", b.NumberU64(),
								"header_number", header.Number.Uint64(),
								"header_time", header.Time,
								"header_base_fee", header.BaseFee,
								"header_l1_block_number", headerInfo.L1BlockNumber,
								"header_send_count", headerInfo.SendCount,
								"header_arbos_format_version", headerInfo.ArbOSFormatVersion,
								"l1_base_fee", l1BaseFee,
								"tx_hash", txs[0].Hash(),
								"data_len", len(itx.Data),
								"selector", selector,
								"l1_block_number", l1BlockNumber,
								"l2_block_number", l2BlockNumber,
								"time_passed", timePassed,
							)
						}
					} else {
						logger.Warn("Bad state root internal tx unknown selector",
							"source", source,
							"block", b.NumberU64(),
							"tx_hash", txs[0].Hash(),
							"data_len", len(itx.Data),
							"selector", selector,
						)
					}
				}
			}
			if wd := b.Withdrawals(); wd != nil {
				computedWithdrawalsRoot := types.DeriveSha(types.Withdrawals(wd))
				logger.Warn("Bad state root withdrawals",
					"source", source,
					"withdrawals_root_header", header.WithdrawalsHash,
					"withdrawals_root_computed", computedWithdrawalsRoot,
				)
			}
			if temporalTx, ok := applyTx.(kv.TemporalTx); ok {
				txNumReader := rawdbv3.TxNums
				if cfg.blockReader != nil {
					txNumReader = cfg.blockReader.TxnumReader(ctx)
				}
				txNumMin, minErr := txNumReader.Min(temporalTx, b.NumberU64())
				txNumMax, maxErr := txNumReader.Max(temporalTx, b.NumberU64())
				txNumCount := uint64(0)
				if minErr == nil && maxErr == nil && txNumMax >= txNumMin {
					txNumCount = txNumMax - txNumMin + 1
				}
				logger.Warn("Bad state root receipts txnum context",
					"source", source,
					"block", b.NumberU64(),
					"txs", len(txs),
					"txnum_min", txNumMin,
					"txnum_max", txNumMax,
					"txnum_count", txNumCount,
					"txnum_min_err", minErr,
					"txnum_max_err", maxErr,
				)

				receipts, err := rawdb.ReadReceiptsCacheV2(temporalTx, b, txNumReader)
				if err != nil {
					logger.Warn("Bad state root receipts read failed", "source", source, "err", err)
				} else {
					computedReceiptRoot := types.DeriveSha(receipts)
					receiptRootMatch := computedReceiptRoot == header.ReceiptHash
					logger.Warn("Bad state root receipts",
						"source", source,
						"receipts", len(receipts),
						"receipt_root_header", header.ReceiptHash,
						"receipt_root_computed", computedReceiptRoot,
						"receipt_root_match", receiptRootMatch,
					)
					if (!receiptRootMatch || len(receipts) != len(txs)) && minErr == nil && maxErr == nil && txNumMax >= txNumMin {
						maxProbe := len(txs)
						if maxProbe > 8 {
							maxProbe = 8
						}
						for i := 0; i < maxProbe; i++ {
							tx := txs[i]
							txNum := txNumMin + uint64(i)
							if txNum > txNumMax {
								logger.Warn("Bad state root receipt probe out-of-range",
									"source", source,
									"tx_index", i,
									"tx_hash", tx.Hash(),
									"txnum", txNum,
									"txnum_max", txNumMax,
								)
								break
							}
							probeReceipt := func(label string, probeTxNum uint64) {
								receipt, ok, probeErr := rawdb.ReadReceiptCacheV2(temporalTx, rawdb.RCacheV2Query{
									BlockNum:      b.NumberU64(),
									BlockHash:     b.Hash(),
									TxnHash:       tx.Hash(),
									TxNum:         probeTxNum,
									DontCalcBloom: true,
								})
								if probeErr != nil {
									logger.Warn("Bad state root receipt probe error",
										"source", source,
										"tx_index", i,
										"tx_hash", tx.Hash(),
										"probe", label,
										"txnum", probeTxNum,
										"err", probeErr,
									)
									return
								}
								if !ok || receipt == nil {
									logger.Warn("Bad state root receipt probe miss",
										"source", source,
										"tx_index", i,
										"tx_hash", tx.Hash(),
										"probe", label,
										"txnum", probeTxNum,
									)
									return
								}
								logger.Warn("Bad state root receipt probe hit",
									"source", source,
									"tx_index", i,
									"tx_hash", tx.Hash(),
									"probe", label,
									"txnum", probeTxNum,
									"receipt_tx_index", receipt.TransactionIndex,
									"status", receipt.Status,
									"gas_used", receipt.GasUsed,
									"logs", len(receipt.Logs),
									"receipt_block", receipt.BlockNumber,
									"receipt_hash", receipt.BlockHash,
								)
							}

							probeReceipt("exact", txNum)
							if txNum > 0 {
								probeReceipt("minus1", txNum-1)
							}
							probeReceipt("plus1", txNum+1)

							// When txnum assignment drifts from the naive tx-index mapping,
							// scan the entire txnum window for this tx hash to pinpoint placement.
							scanUpper := txNumMax
							if scanUpper > txNumMin+63 {
								scanUpper = txNumMin + 63
							}
							scanHits := 0
							for probeTxNum := txNumMin; probeTxNum <= scanUpper; probeTxNum++ {
								receiptAtNum, okAtNum, errAtNum := rawdb.ReadReceiptCacheV2(temporalTx, rawdb.RCacheV2Query{
									BlockNum:      b.NumberU64(),
									BlockHash:     b.Hash(),
									TxnHash:       tx.Hash(),
									TxNum:         probeTxNum,
									DontCalcBloom: true,
								})
								if errAtNum != nil {
									logger.Warn("Bad state root receipt scan error",
										"source", source,
										"tx_index", i,
										"tx_hash", tx.Hash(),
										"txnum", probeTxNum,
										"err", errAtNum,
									)
									continue
								}
								if !okAtNum || receiptAtNum == nil {
									continue
								}
								scanHits++
								logger.Warn("Bad state root receipt scan hit",
									"source", source,
									"tx_index", i,
									"tx_hash", tx.Hash(),
									"txnum", probeTxNum,
									"receipt_tx_index", receiptAtNum.TransactionIndex,
									"status", receiptAtNum.Status,
									"gas_used", receiptAtNum.GasUsed,
									"logs", len(receiptAtNum.Logs),
									"receipt_block", receiptAtNum.BlockNumber,
									"receipt_hash", receiptAtNum.BlockHash,
								)
							}
							if scanHits == 0 {
								logger.Warn("Bad state root receipt scan no hits",
									"source", source,
									"tx_index", i,
									"tx_hash", tx.Hash(),
									"scan_from", txNumMin,
									"scan_to", scanUpper,
									"txnum_min", txNumMin,
									"txnum_max", txNumMax,
								)
							}
						}
					}
				}
			} else {
				logger.Warn("Bad state root receipts skipped", "source", source, "reason", "non-temporal tx")
			}
			for i, tx := range txs {
				from := "<unknown>"
				if sender, ok := tx.GetSender(); ok {
					from = sender.Hex()
				}
				to := "<contract>"
				if tx.GetTo() != nil {
					to = tx.GetTo().Hex()
				}
				logger.Warn("Bad state root tx",
					"source", source,
					"idx", i,
					"hash", tx.Hash(),
					"type", tx.Type(),
					"from", from,
					"to", to,
					"nonce", tx.GetNonce(),
					"gas_limit", tx.GetGasLimit(),
					"blob_gas", tx.GetBlobGas(),
					"value", tx.GetValue(),
					"tip_cap", tx.GetTipCap(),
					"fee_cap", tx.GetFeeCap(),
					"chain_id", tx.GetChainID(),
					"data_len", len(tx.GetData()),
					"access_list_len", len(tx.GetAccessList()),
					"auth_len", len(tx.GetAuthorizations()),
					"timeboosted", tx.IsTimeBoosted(),
				)
			}
		}

		if header.Number.Uint64() > 0 && applyTx != nil {
			parent := rawdb.ReadHeader(applyTx, header.ParentHash, header.Number.Uint64()-1)
			if parent != nil {
				logger.Warn("Bad state root parent",
					"number", parent.Number.Uint64(),
					"hash", parent.Hash(),
					"state_root", parent.Root,
					"tx_root", parent.TxHash,
					"receipt_root", parent.ReceiptHash,
				)
			}
		}

		if applyTx == nil {
			logger.Warn("Bad state root: missing tx for block inspection")
		} else {
			loggedBlock := false
			if cfg.blockReader == nil {
				logger.Warn("Bad state root: block reader is nil")
			} else {
				b, err := blockWithSenders(ctx, cfg.db, applyTx, cfg.blockReader, header.Number.Uint64())
				if err != nil {
					logger.Warn("Bad state root block read failed", "source", "block_reader", "err", err)
				} else if b == nil {
					logger.Warn("Bad state root block read returned nil", "source", "block_reader")
				} else {
					logBlockDetails("block_reader", b)
					loggedBlock = true
				}
			}
			if !loggedBlock {
				b, senders, err := rawdb.ReadBlockWithSenders(applyTx, header.Hash(), header.Number.Uint64())
				if err != nil {
					logger.Warn("Bad state root block read failed", "source", "db", "err", err)
				} else if b == nil {
					logger.Warn("Bad state root block read returned nil", "source", "db")
				} else {
					if len(senders) > 0 && len(senders) != b.Transactions().Len() {
						logger.Warn("Bad state root senders mismatch", "source", "db", "senders", len(senders), "txs", len(b.Transactions()))
					}
					logBlockDetails("db", b)
				}
			}
		}
		logBadRootAccounts(header, applyTx, doms, logger)
		logBadRootTouchedAccounts(header, applyTx, doms, touchedPlainKeys, logger)
	}

	if ERIGON_BAD_ROOT_DUMP_STATE {
		temporalTx, ok := applyTx.(kv.TemporalRwTx)
		if !ok {
			logger.Warn("Bad state root: cannot dump state, tx is not temporal")
			return
		}
		dumpPlainStateDebug(temporalTx, doms)
	}
}

func handleIncorrectRootHashError(header *types.Header, applyTx kv.TemporalRwTx, cfg ExecuteBlockCfg, e *StageState, maxBlockNum uint64, logger log.Logger, u Unwinder) (bool, error) {
	if ERIGON_MDBX_MIGRATE_SKIP_UNWIND_ON_BAD_ROOT {
		logger.Warn("Skipping unwind due to incorrect root hash (debug)", "block", header.Number.Uint64())
		return false, nil
	}
	if cfg.badBlockHalt {
		return false, fmt.Errorf("%w: wrong trie root", consensus.ErrInvalidBlock)
	}
	if cfg.hd != nil && cfg.hd.POSSync() {
		cfg.hd.ReportBadHeaderPoS(header.Hash(), header.ParentHash)
	}
	minBlockNum := e.BlockNumber
	if maxBlockNum <= minBlockNum {
		return false, nil
	}

	unwindToLimit, err := rawtemporaldb.CanUnwindToBlockNum(applyTx)
	if err != nil {
		return false, err
	}
	minBlockNum = max(minBlockNum, unwindToLimit)

	// Binary search, but not too deep
	jump := cmp.InRange(1, maxUnwindJumpAllowance, (maxBlockNum-minBlockNum)/2)
	unwindTo := maxBlockNum - jump

	// protect from too far unwind
	allowedUnwindTo, ok, err := rawtemporaldb.CanUnwindBeforeBlockNum(unwindTo, applyTx)
	if err != nil {
		return false, err
	}
	if !ok {
		return false, fmt.Errorf("%w: requested=%d, minAllowed=%d", ErrTooDeepUnwind, unwindTo, allowedUnwindTo)
	}
	logger.Warn("Bad state root unwind decision",
		"block", header.Number.Uint64(),
		"stage_block", e.BlockNumber,
		"target_block", maxBlockNum,
		"min_block", minBlockNum,
		"unwind_limit", unwindToLimit,
		"jump", jump,
		"requested_unwind_to", unwindTo,
		"allowed_unwind_to", allowedUnwindTo,
	)
	logger.Warn("Unwinding due to incorrect root hash", "to", unwindTo)
	if u != nil {
		if err := u.UnwindTo(allowedUnwindTo, BadBlock(header.Hash(), ErrInvalidStateRootHash), applyTx); err != nil {
			return false, err
		}
	}
	return false, nil
}

type FlushAndComputeCommitmentTimes struct {
	Flush             time.Duration
	ComputeCommitment time.Duration
}

// flushAndCheckCommitmentV3 - does write state to db and then check commitment
func flushAndCheckCommitmentV3(ctx context.Context, header *types.Header, applyTx kv.RwTx, doms *dbstate.SharedDomains, cfg ExecuteBlockCfg, e *StageState, maxBlockNum uint64, parallel bool, logger log.Logger, u Unwinder, inMemExec bool) (ok bool, times FlushAndComputeCommitmentTimes, err error) {
	start := time.Now()
	var touchedPlainKeys [][]byte
	// E2 state root check was in another stage - means we did flush state even if state root will not match
	// And Unwind expecting it
	if !parallel {
		if err := e.Update(applyTx, maxBlockNum); err != nil {
			return false, times, err
		}
		if _, err := rawdb.IncrementStateVersion(applyTx); err != nil {
			return false, times, fmt.Errorf("writing plain state version: %w", err)
		}
	}

	if header == nil {
		return false, times, errors.New("header is nil")
	}

	if dbg.DiscardCommitment() {
		return true, times, nil
	}
	if doms.BlockNum() != header.Number.Uint64() {
		panic(fmt.Errorf("%d != %d", doms.BlockNum(), header.Number.Uint64()))
	}

	if ERIGON_BAD_ROOT_DEBUG && ERIGON_BAD_ROOT_DUMP_TOUCHED_ACCOUNTS {
		if commitCtx := doms.GetCommitmentContext(); commitCtx != nil {
			touchedPlainKeys = commitCtx.DebugPlainKeys()
		}
	}

	// Do not restore commitment state here: per-block execution already computes
	// and stores the current block commitment in this same in-flight context.
	// Restoring from persisted DB state at flush-time can move the trie back to
	// the previous block and make the final check compare against a stale root.

	logCommitmentAnchorProbe("before_compute", header.Number.Uint64(), doms, applyTx, nil, logger)

	computedRootHash, err := doms.ComputeCommitment(ctx, true, header.Number.Uint64(), doms.TxNum(), e.LogPrefix())
	times.ComputeCommitment = time.Since(start)
	if err != nil {
		return false, times, fmt.Errorf("ParallelExecutionState.Apply: %w", err)
	}
	logCommitmentAnchorProbe("after_compute", header.Number.Uint64(), doms, applyTx, computedRootHash, logger)

	if cfg.blockProduction {
		header.Root = common.BytesToHash(computedRootHash)
		return true, times, nil
	}
	if !bytes.Equal(computedRootHash, header.Root.Bytes()) {
		// Fallback for fast-path commitment divergence:
		// rebuild as-of current txnum from touched keys and full latest scan.
		// If fallback matches header root, treat it as authoritative and proceed.
		fallbackTried := false
		fallbackMatched := false
		var fallbackErr error
		var fallbackRootHash []byte
		if temporalTx, ok := applyTx.(kv.TemporalTx); ok {
			if commitmentCtx := doms.GetCommitmentContext(); commitmentCtx != nil {
				fallbackTried = true
				fallbackRootHash, fallbackErr = commitmentCtx.RebuildCommitmentAsOfTxNumFullScan(ctx, temporalTx, header.Number.Uint64(), doms.TxNum())
				if fallbackErr == nil {
					fallbackMatched = bytes.Equal(fallbackRootHash, header.Root.Bytes())
					if fallbackMatched {
						computedRootHash = fallbackRootHash
					}
				}
				logger.Warn("Bad state root fallback rebuild",
					"block", header.Number.Uint64(),
					"doms_txnum", doms.TxNum(),
					"fallback_err", fallbackErr,
					"fallback_root", common.BytesToHash(fallbackRootHash),
					"header_root", header.Root,
					"matches_header", fallbackMatched,
				)
			}
		}
		if fallbackTried && fallbackMatched {
			logger.Warn("Bad state root resolved by fallback rebuild",
				"block", header.Number.Uint64(),
				"root", common.BytesToHash(computedRootHash),
				"txnum", doms.TxNum(),
			)
			if !inMemExec {
				flushStart := time.Now()
				if err := doms.Flush(ctx, applyTx); err != nil {
					return false, times, err
				}
				times.Flush = time.Since(flushStart)
			}
			return true, times, nil
		}

		minTxNum, minTxErr := rawdbv3.TxNums.Min(applyTx, header.Number.Uint64())
		maxTxNum, maxTxErr := rawdbv3.TxNums.Max(applyTx, header.Number.Uint64())
		logger.Warn("Bad state root mismatch checkpoint",
			"block", header.Number.Uint64(),
			"hash", header.Hash(),
			"parent_hash", header.ParentHash,
			"doms_block", doms.BlockNum(),
			"doms_txnum", doms.TxNum(),
			"txnums_min", minTxNum,
			"txnums_max", maxTxNum,
			"txnums_min_err", minTxErr,
			"txnums_max_err", maxTxErr,
			"stage_block", e.BlockNumber,
			"target_block", maxBlockNum,
			"parallel", parallel,
			"in_mem_exec", inMemExec,
			"bad_block_halt", cfg.badBlockHalt,
			"workers", cfg.syncCfg.ExecWorkerCount,
			"log_prefix", e.LogPrefix(),
		)
		logger.Warn(fmt.Sprintf("[%s] Wrong trie root of block %d: %x, expected (from header): %x. Block hash: %x", e.LogPrefix(), header.Number.Uint64(), computedRootHash, header.Root.Bytes(), header.Hash()))
		if ERIGON_MDBX_MIGRATE_FLUSH_ON_BAD_ROOT && !inMemExec {
			flushStart := time.Now()
			if err := doms.Flush(ctx, applyTx); err != nil {
				return false, times, err
			}
			times.Flush = time.Since(flushStart)
		}
		logBadRootDetails(ctx, header, computedRootHash, applyTx, doms, touchedPlainKeys, cfg, e, maxBlockNum, logger)
		ok, err = handleIncorrectRootHashError(header, applyTx.(kv.TemporalRwTx), cfg, e, maxBlockNum, logger, u)
		return ok, times, err
	}
	if !inMemExec {
		start = time.Now()
		err := doms.Flush(ctx, applyTx)
		times.Flush = time.Since(start)
		if err != nil {
			return false, times, err
		}
	}
	return true, times, nil

}

func blockWithSenders(ctx context.Context, db kv.RoDB, tx kv.Tx, blockReader services.BlockReader, blockNum uint64) (b *types.Block, err error) {
	if tx == nil {
		tx, err = db.BeginRo(ctx)
		if err != nil {
			return nil, err
		}
		defer tx.Rollback()
	}
	b, err = blockReader.BlockByNumber(ctx, tx, blockNum)
	if err != nil {
		return nil, err
	}
	if b == nil {
		return nil, nil
	}
	if mdbxMigrateDebug && (!mdbxMigrateDebugBlockSet || blockNum == mdbxMigrateDebugBlock) {
		log.Info("mdbx-migrate block read",
			"block", blockNum,
			"hash", b.Hash(),
			"txs", len(b.Transactions()),
			"uncles", len(b.Uncles()),
			"size", b.Size(),
		)
	}
	if ERIGON_BAD_ROOT_DEBUG && (!mdbxMigrateDebugBlockSet || blockNum == mdbxMigrateDebugBlock) {
		canonicalHash, canonErr := rawdb.ReadCanonicalHash(tx, blockNum)
		if canonErr != nil {
			log.Warn("Bad state root canonical hash read failed", "block", blockNum, "err", canonErr)
		} else if canonicalHash == (common.Hash{}) {
			log.Warn("Bad state root canonical hash missing", "block", blockNum, "reader_hash", b.Hash())
		} else {
			canonHeader := rawdb.ReadHeader(tx, canonicalHash, blockNum)
			if canonHeader == nil {
				log.Warn("Bad state root canonical header missing",
					"block", blockNum,
					"canonical_hash", canonicalHash,
					"reader_hash", b.Hash(),
				)
			} else {
				readerHeader := b.HeaderNoCopy()
				log.Warn("Bad state root header source compare",
					"block", blockNum,
					"reader_hash", b.Hash(),
					"reader_parent_hash", readerHeader.ParentHash,
					"reader_state_root", readerHeader.Root,
					"reader_tx_root", readerHeader.TxHash,
					"reader_receipt_root", readerHeader.ReceiptHash,
					"canonical_hash", canonicalHash,
					"canonical_parent_hash", canonHeader.ParentHash,
					"canonical_state_root", canonHeader.Root,
					"canonical_tx_root", canonHeader.TxHash,
					"canonical_receipt_root", canonHeader.ReceiptHash,
					"hash_match", b.Hash() == canonicalHash,
					"parent_hash_match", readerHeader.ParentHash == canonHeader.ParentHash,
					"state_root_match", readerHeader.Root == canonHeader.Root,
					"tx_root_match", readerHeader.TxHash == canonHeader.TxHash,
					"receipt_root_match", readerHeader.ReceiptHash == canonHeader.ReceiptHash,
				)
			}
		}
	}
	return b, err
}

func shouldGenerateChangeSets(cfg ExecuteBlockCfg, blockNum, maxBlockNum uint64, initialCycle bool) bool {
	if cfg.syncCfg.AlwaysGenerateChangesets {
		return true
	}
	if blockNum < cfg.blockReader.FrozenBlocks() {
		return false
	}
	if initialCycle {
		return false
	}
	// once past the initial cycle, make sure to generate changesets for the last blocks that fall in the reorg window
	return blockNum+cfg.syncCfg.MaxReorgDepth >= maxBlockNum
}

// sweepAccountTombstonesPlain removes plain-state account rows that are clearly
// delete markers (e.g. values shorter than the 8-byte prefix + account encoding).
// Leaving these in AccountVals causes the commitment trie
// to think the account exists, leading to state-root mismatches during
// migration (seen at block 13).
func sweepAccountTombstonesPlain(tx kv.Tx, doms *dbstate.SharedDomains, logger log.Logger) {
	if tx == nil {
		return
	}
	const accountValsMinLen = 8 + 4
	rwTx, ok := tx.(kv.RwTx)
	if !ok {
		return
	}
	c, err := rwTx.Cursor(kv.TblAccountVals)
	if err != nil {
		logger.Warn("sweepAccountTombstonesPlain: open cursor failed", "err", err)
		return
	}
	defer c.Close()

	for k, v, err := c.First(); k != nil; k, v, err = c.Next() {
		if err != nil {
			logger.Warn("sweepAccountTombstonesPlain: cursor next failed", "err", err)
			break
		}
		if len(v) > 0 && len(v) < accountValsMinLen {
			if err := rwTx.Delete(kv.TblAccountVals, k); err != nil {
				logger.Warn("sweepAccountTombstonesPlain: delete failed", "err", err, "addr", fmt.Sprintf("0x%x", k))
			}
		}
	}

	// Also purge from the hashed/temporal Accounts domain so the commitment trie
	// doesn't see the tombstone as a live account.
	if doms == nil {
		return
	}
	temporalTx, ok := tx.(kv.TemporalTx)
	if !ok {
		return
	}
	keys, err := temporalTx.Debug().RangeLatest(kv.AccountsDomain, nil, nil, -1)
	if err != nil {
		logger.Warn("sweepAccountTombstonesPlain: range hashed failed", "err", err)
		return
	}
	defer keys.Close()

	for keys.HasNext() {
		k, v, err := keys.Next()
		if err != nil {
			logger.Warn("sweepAccountTombstonesPlain: hashed next failed", "err", err)
			break
		}
		if len(v) > 0 && (len(v) < 4 || v[0] == 0xff) {
			if err := doms.DomainDel(kv.AccountsDomain, temporalTx, k, doms.TxNum(), v, 0); err != nil {
				logger.Warn("sweepAccountTombstonesPlain: hashed delete failed", "err", err, "addr", fmt.Sprintf("0x%x", k))
			}
		}
	}
}
