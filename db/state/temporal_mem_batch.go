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
	"sort"
	"sync"
	"time"
	"unsafe"

	btree2 "github.com/tidwall/btree"

	"github.com/erigontech/erigon-lib/common"
	"github.com/erigontech/erigon-lib/common/dbg"
	"github.com/erigontech/erigon-lib/log/v3"
	"github.com/erigontech/erigon/db/kv"
	"github.com/erigontech/erigon/db/kv/order"
	"github.com/erigontech/erigon/db/kv/rawdbv3"
	"github.com/erigontech/erigon/db/state/changeset"
)

type dataWithPrevStep struct {
	data     []byte
	prevStep kv.Step
}

// TemporalMemBatch - temporal read-write interface - which storing updates in RAM. Don't forget to call `.Flush()`
type TemporalMemBatch struct {
	stepSize uint64

	estSize int

	latestStateLock sync.RWMutex
	domains         [kv.DomainLen]map[string]dataWithPrevStep
	storage         *btree2.Map[string, dataWithPrevStep] // TODO: replace hardcoded domain name to per-config configuration of available Guarantees/AccessMethods (range vs get)

	domainWriters [kv.DomainLen]*DomainBufferedWriter
	iiWriters     []*InvertedIndexBufferedWriter

	currentChangesAccumulator *changeset.StateChangeSet
	pastChangesAccumulator    map[string]*changeset.StateChangeSet
}

var fixedSenderDiffTraceAddrBytes = common.HexToAddress("0x28c18bc63069e3581870904f32Dd34D9e3332cce").Bytes()
var traceDiffsetSource = dbg.EnvBool("ERIGON_MDBX_MIGRATE_DIFFSET_TRACE", false) || dbg.EnvBool("ERIGON_BAD_ROOT_DEBUG", false)
var traceTemporalFlush = dbg.EnvBool("ERIGON_TEMPORAL_FLUSH_TRACE", false) || dbg.EnvBool("ERIGON_EXEC_LOOP_TRACE", false)

func newTemporalMemBatch(tx kv.TemporalTx) *TemporalMemBatch {
	sd := &TemporalMemBatch{
		storage: btree2.NewMap[string, dataWithPrevStep](128),
	}
	aggTx := AggTx(tx)
	sd.stepSize = aggTx.StepSize()

	sd.iiWriters = make([]*InvertedIndexBufferedWriter, len(aggTx.iis))

	for id, ii := range aggTx.iis {
		sd.iiWriters[id] = ii.NewWriter()
	}

	for id, d := range aggTx.d {
		sd.domains[id] = map[string]dataWithPrevStep{}
		sd.domainWriters[id] = d.NewWriter()
	}
	if aw := sd.domainWriters[kv.AccountsDomain]; aw != nil {
		log.Info("escrow trace mem_new",
			"mem", fmt.Sprintf("%p", sd),
			"writer", fmt.Sprintf("%p", aw),
			"values", fmt.Sprintf("%p", aw.values),
		)
	}

	return sd
}

func (sd *TemporalMemBatch) DomainPut(domain kv.Domain, k string, v []byte, txNum uint64, preval []byte, prevStep kv.Step) error {
	sd.putLatest(domain, k, v, txNum)
	return sd.putHistory(domain, toBytesZeroCopy(k), v, txNum, preval, prevStep)
}

func (sd *TemporalMemBatch) DomainDel(domain kv.Domain, k string, txNum uint64, preval []byte, prevStep kv.Step) error {
	sd.putLatest(domain, k, nil, txNum)
	return sd.putHistory(domain, toBytesZeroCopy(k), nil, txNum, preval, prevStep)
}

func (sd *TemporalMemBatch) putHistory(domain kv.Domain, k, v []byte, txNum uint64, preval []byte, prevStep kv.Step) error {
	if domain == kv.AccountsDomain && bytes.Equal(k, escrowTraceAddrBytes) {
		w := sd.domainWriters[domain]
		log.Info("escrow trace mem_put",
			"mem", fmt.Sprintf("%p", sd),
			"writer", fmt.Sprintf("%p", w),
			"values", fmt.Sprintf("%p", w.values),
			"tx_num", txNum,
			"val_len", len(v),
			"prev_len", len(preval),
		)
	}
	if len(v) == 0 {
		return sd.domainWriters[domain].DeleteWithPrev(k, txNum, preval, prevStep)
	}
	return sd.domainWriters[domain].PutWithPrev(k, v, txNum, preval, prevStep)
}

func (sd *TemporalMemBatch) putLatest(domain kv.Domain, key string, val []byte, txNum uint64) {
	sd.latestStateLock.Lock()
	defer sd.latestStateLock.Unlock()
	// Keep latest cache immutable against caller buffer reuse.
	// Execution paths reuse backing buffers aggressively; storing references here
	// can make "latest" drift from what was actually written for this tx.
	var valCopy []byte
	if val != nil {
		valCopy = common.Copy(val)
	}
	valWithPrevStep := dataWithPrevStep{data: valCopy, prevStep: kv.Step(txNum / sd.stepSize)}
	if domain == kv.StorageDomain {
		if old, ok := sd.storage.Set(key, valWithPrevStep); ok {
			sd.estSize += len(valCopy) - len(old.data)
		} else {
			sd.estSize += len(key) + len(valCopy)
		}
		return
	}

	if old, ok := sd.domains[domain][key]; ok {
		sd.estSize += len(valCopy) - len(old.data)
	} else {
		sd.estSize += len(key) + len(valCopy)
	}
	sd.domains[domain][key] = valWithPrevStep
}

func (sd *TemporalMemBatch) GetLatest(table kv.Domain, key []byte) (v []byte, prevStep kv.Step, ok bool) {
	sd.latestStateLock.RLock()
	defer sd.latestStateLock.RUnlock()

	keyS := toStringZeroCopy(key)
	var dataWithPrevStep dataWithPrevStep
	if table == kv.StorageDomain {
		dataWithPrevStep, ok = sd.storage.Get(keyS)
		return dataWithPrevStep.data, dataWithPrevStep.prevStep, ok

	}

	dataWithPrevStep, ok = sd.domains[table][keyS]
	return dataWithPrevStep.data, dataWithPrevStep.prevStep, ok
}

func (sd *TemporalMemBatch) SizeEstimate() uint64 {
	sd.latestStateLock.RLock()
	defer sd.latestStateLock.RUnlock()

	// multiply 2: to cover data-structures overhead (and keep accounting cheap)
	// and muliply 2 more: for Commitment calculation when batch is full
	return uint64(sd.estSize) * 4
}

func (sd *TemporalMemBatch) ClearRam() {
	sd.latestStateLock.Lock()
	defer sd.latestStateLock.Unlock()
	for i := range sd.domains {
		sd.domains[i] = map[string]dataWithPrevStep{}
	}

	sd.storage = btree2.NewMap[string, dataWithPrevStep](128)
	sd.estSize = 0
	sd.currentChangesAccumulator = nil
	sd.pastChangesAccumulator = nil
	for i := range sd.domainWriters {
		if sd.domainWriters[i] != nil {
			sd.domainWriters[i].SetDiff(nil)
		}
	}
}

func (sd *TemporalMemBatch) IteratePrefix(domain kv.Domain, prefix []byte, roTx kv.Tx, it func(k []byte, v []byte, step kv.Step) (cont bool, err error)) error {
	sd.latestStateLock.RLock()
	defer sd.latestStateLock.RUnlock()
	var ramIter btree2.MapIter[string, dataWithPrevStep]
	if domain == kv.StorageDomain {
		ramIter = sd.storage.Iter()
	}

	return AggTx(roTx).d[domain].debugIteratePrefixLatest(prefix, ramIter, it, roTx)
}

func (sd *TemporalMemBatch) SetChangesetAccumulator(acc *changeset.StateChangeSet) {
	sd.currentChangesAccumulator = acc
	for idx := range sd.domainWriters {
		if sd.currentChangesAccumulator == nil {
			sd.domainWriters[idx].SetDiff(nil)
		} else {
			sd.domainWriters[idx].SetDiff(&sd.currentChangesAccumulator.Diffs[idx])
		}
	}
}
func (sd *TemporalMemBatch) SavePastChangesetAccumulator(blockHash common.Hash, blockNumber uint64, acc *changeset.StateChangeSet) {
	if sd.pastChangesAccumulator == nil {
		sd.pastChangesAccumulator = make(map[string]*changeset.StateChangeSet)
	}
	key := make([]byte, 40)
	binary.BigEndian.PutUint64(key[:8], blockNumber)
	copy(key[8:], blockHash[:])
	sd.pastChangesAccumulator[toStringZeroCopy(key)] = acc
}

func (sd *TemporalMemBatch) GetDiffset(tx kv.RwTx, blockHash common.Hash, blockNumber uint64) ([kv.DomainLen][]kv.DomainEntryDiff, bool, error) {
	var key [40]byte
	binary.BigEndian.PutUint64(key[:8], blockNumber)
	copy(key[8:], blockHash[:])
	if changeset, ok := sd.pastChangesAccumulator[toStringZeroCopy(key[:])]; ok {
		diffs := [kv.DomainLen][]kv.DomainEntryDiff{
			changeset.Diffs[kv.AccountsDomain].GetDiffSet(),
			changeset.Diffs[kv.StorageDomain].GetDiffSet(),
			changeset.Diffs[kv.CodeDomain].GetDiffSet(),
			changeset.Diffs[kv.CommitmentDomain].GetDiffSet(),
		}
		logDiffsetSource("mem", blockNumber, blockHash, diffs)
		return diffs, true, nil
	}
	diffs, ok, err := changeset.ReadDiffSet(tx, blockNumber, blockHash)
	if err == nil && ok && len(diffs[kv.AccountsDomain]) == 0 {
		if synthesized, synthOK, synthErr := synthesizeAccountDiffsetFromHistory(tx, blockNumber); synthErr != nil {
			log.Warn("state diffset history fallback failed", "block", blockNumber, "block_hash", blockHash, "err", synthErr)
		} else if synthOK && len(synthesized) > 0 {
			diffs[kv.AccountsDomain] = synthesized
			log.Warn("state diffset history fallback",
				"block", blockNumber,
				"block_hash", blockHash,
				"accounts_len", len(synthesized),
			)
		}
	}
	if err == nil && ok && len(diffs[kv.StorageDomain]) == 0 {
		if synthesized, synthOK, synthErr := synthesizeStorageDiffsetFromHistory(tx, blockNumber); synthErr != nil {
			log.Warn("state storage diffset history fallback failed", "block", blockNumber, "block_hash", blockHash, "err", synthErr)
		} else if synthOK && len(synthesized) > 0 {
			diffs[kv.StorageDomain] = synthesized
			log.Warn("state storage diffset history fallback",
				"block", blockNumber,
				"block_hash", blockHash,
				"storage_len", len(synthesized),
			)
		}
	}
	if err == nil && ok && len(diffs[kv.CodeDomain]) == 0 {
		if synthesized, synthOK, synthErr := synthesizeCodeDiffsetFromHistory(tx, blockNumber); synthErr != nil {
			log.Warn("state code diffset history fallback failed", "block", blockNumber, "block_hash", blockHash, "err", synthErr)
		} else if synthOK && len(synthesized) > 0 {
			diffs[kv.CodeDomain] = synthesized
			log.Warn("state code diffset history fallback",
				"block", blockNumber,
				"block_hash", blockHash,
				"code_len", len(synthesized),
			)
		}
	}
	if err == nil {
		logDiffsetSource("db", blockNumber, blockHash, diffs)
	}
	return diffs, ok, err
}

func synthesizeAccountDiffsetFromHistory(tx kv.RwTx, blockNumber uint64) ([]kv.DomainEntryDiff, bool, error) {
	ttx, ok := tx.(kv.TemporalTx)
	if !ok {
		return nil, false, nil
	}
	startTxNum, err := rawdbv3.TxNums.Min(tx, blockNumber)
	if err != nil {
		return nil, false, err
	}
	endTxNum, err := rawdbv3.TxNums.Max(tx, blockNumber)
	if err != nil {
		return nil, false, err
	}
	if endTxNum == 0 && blockNumber != 0 {
		return nil, false, nil
	}
	it, err := ttx.HistoryRange(kv.AccountsDomain, int(startTxNum), int(endTxNum+1), order.Asc, kv.Unlim)
	if err != nil {
		return nil, false, err
	}
	defer it.Close()

	diffs := make([]kv.DomainEntryDiff, 0, 16)
	prevStepBytes := make([]byte, 8)
	currentStepBytes := make([]byte, 8)
	for it.HasNext() {
		k, _, err := it.Next()
		if err != nil {
			return nil, false, err
		}
		restoreVal, restoreOK, err := ttx.HistorySeek(kv.AccountsDomain, k, startTxNum)
		if err != nil {
			return nil, false, err
		}
		if !restoreOK {
			continue
		}
		if bytes.Equal(k, fixedSenderDiffTraceAddrBytes) {
			log.Warn("state account history restore probe",
				"mode", "fallback",
				"block", blockNumber,
				"start_txnum", startTxNum,
				"end_txnum", endTxNum,
				"key", common.BytesToAddress(k),
				"restore_len", len(restoreVal),
				"restore_preview", badRootValuePreview(restoreVal),
			)
		}
		step := kv.Step(0)
		if _, latestStep, latestErr := ttx.GetLatest(kv.AccountsDomain, k); latestErr == nil {
			step = latestStep
		}
		binary.BigEndian.PutUint64(prevStepBytes, ^uint64(step))
		binary.BigEndian.PutUint64(currentStepBytes, ^uint64(step))
		valsKey := append(append(make([]byte, 0, len(k)+8), k...), currentStepBytes...)
		diffs = append(diffs, kv.DomainEntryDiff{
			Key:           toStringZeroCopy(valsKey),
			Value:         common.Copy(restoreVal),
			PrevStepBytes: common.Copy(prevStepBytes),
		})
	}
	return diffs, len(diffs) > 0, nil
}

func rewriteAccountDiffsetFromHistory(tx kv.RwTx, blockNumber uint64, existing []kv.DomainEntryDiff) ([]kv.DomainEntryDiff, bool, error) {
	ttx, ok := tx.(kv.TemporalTx)
	if !ok {
		return existing, false, nil
	}
	startTxNum, err := rawdbv3.TxNums.Min(tx, blockNumber)
	if err != nil {
		return nil, false, err
	}
	endTxNum, err := rawdbv3.TxNums.Max(tx, blockNumber)
	if err != nil {
		return nil, false, err
	}
	if endTxNum == 0 && blockNumber != 0 {
		return existing, false, nil
	}
	it, err := ttx.HistoryRange(kv.AccountsDomain, int(startTxNum), int(endTxNum+1), order.Asc, kv.Unlim)
	if err != nil {
		return nil, false, err
	}
	defer it.Close()

	rewritten := make(map[string]kv.DomainEntryDiff, len(existing)+8)
	for i := range existing {
		entry := existing[i]
		rewritten[entry.Key] = kv.DomainEntryDiff{
			Key:           entry.Key,
			Value:         common.Copy(entry.Value),
			PrevStepBytes: common.Copy(entry.PrevStepBytes),
		}
	}

	prevStepBytes := make([]byte, 8)
	currentStepBytes := make([]byte, 8)
	changed := false
	// Some persisted diffsets already contain the affected account key, but
	// HistoryRange over the block span may not enumerate it in this replay path.
	// For those entries, prefer the raw AccountVals row identified by the diff's
	// PrevStepBytes. That is the value unwind will restore, and it avoids the
	// marker-like HistorySeek/GetAsOf payloads observed on poster rewind.
	for i := range existing {
		logicalKey := accountLogicalKey(toBytesZeroCopy(existing[i].Key))
		if len(logicalKey) == 0 || !bytes.Equal(logicalKey, fixedSenderDiffTraceAddrBytes) {
			continue
		}
		restoreVal, restoreOK, err := ttx.HistorySeek(kv.AccountsDomain, logicalKey, startTxNum)
		if err != nil {
			return nil, false, err
		}
		asOfVal, asOfOK, asOfErr := ttx.GetAsOf(kv.AccountsDomain, logicalKey, startTxNum)
		asOfNextVal, asOfNextOK, asOfNextErr := ttx.GetAsOf(kv.AccountsDomain, logicalKey, startTxNum+1)
		prevStepVal, prevStepOK, prevStepErr := lookupAccountValueByPrevStep(tx, logicalKey, existing[i].PrevStepBytes)
		log.Warn("state account history restore probe",
			"mode", "rewrite-existing-probe",
			"block", blockNumber,
			"start_txnum", startTxNum,
			"end_txnum", endTxNum,
			"key", common.BytesToAddress(logicalKey),
			"existing_len", len(existing[i].Value),
			"existing_preview", badRootValuePreview(existing[i].Value),
			"restore_len", len(restoreVal),
			"restore_preview", badRootValuePreview(restoreVal),
			"restore_ok", restoreOK,
			"asof_ok", asOfOK,
			"asof_preview", badRootValuePreview(asOfVal),
			"asof_err", errString(asOfErr),
			"asof_next_ok", asOfNextOK,
			"asof_next_preview", badRootValuePreview(asOfNextVal),
			"asof_next_err", errString(asOfNextErr),
			"prev_step_lookup_ok", prevStepOK,
			"prev_step_lookup_preview", badRootValuePreview(prevStepVal),
			"prev_step_lookup_err", errString(prevStepErr),
		)
		if prevStepOK {
			log.Warn("state account history restore probe",
				"mode", "rewrite-existing-candidate",
				"block", blockNumber,
				"key", common.BytesToAddress(logicalKey),
				"candidate_preview", badRootValuePreview(prevStepVal),
			)
		}
	}
	for it.HasNext() {
		k, _, err := it.Next()
		if err != nil {
			return nil, false, err
		}
		restoreVal, restoreOK, err := ttx.HistorySeek(kv.AccountsDomain, k, startTxNum)
		if err != nil {
			return nil, false, err
		}
		if !restoreOK {
			continue
		}
		if bytes.Equal(k, fixedSenderDiffTraceAddrBytes) {
			log.Warn("state account history restore probe",
				"mode", "rewrite",
				"block", blockNumber,
				"start_txnum", startTxNum,
				"end_txnum", endTxNum,
				"key", common.BytesToAddress(k),
				"restore_len", len(restoreVal),
				"restore_preview", badRootValuePreview(restoreVal),
			)
		}
		step := kv.Step(0)
		if _, latestStep, latestErr := ttx.GetLatest(kv.AccountsDomain, k); latestErr == nil {
			step = latestStep
		}
		binary.BigEndian.PutUint64(prevStepBytes, ^uint64(step))
		binary.BigEndian.PutUint64(currentStepBytes, ^uint64(step))
		valsKey := append(append(make([]byte, 0, len(k)+8), k...), currentStepBytes...)
		key := toStringZeroCopy(valsKey)
		rewritten[key] = kv.DomainEntryDiff{
			Key:           key,
			Value:         common.Copy(restoreVal),
			PrevStepBytes: common.Copy(prevStepBytes),
		}
		changed = true
	}
	if !changed {
		return existing, false, nil
	}
	out := make([]kv.DomainEntryDiff, 0, len(rewritten))
	for _, entry := range rewritten {
		out = append(out, entry)
	}
	sort.Slice(out, func(i, j int) bool {
		return out[i].Key < out[j].Key
	})
	return out, true, nil
}

func synthesizeStorageDiffsetFromHistory(tx kv.RwTx, blockNumber uint64) ([]kv.DomainEntryDiff, bool, error) {
	ttx, ok := tx.(kv.TemporalTx)
	if !ok {
		return nil, false, nil
	}
	startTxNum, err := rawdbv3.TxNums.Min(tx, blockNumber)
	if err != nil {
		return nil, false, err
	}
	endTxNum, err := rawdbv3.TxNums.Max(tx, blockNumber)
	if err != nil {
		return nil, false, err
	}
	if endTxNum == 0 && blockNumber != 0 {
		return nil, false, nil
	}
	it, err := ttx.HistoryRange(kv.StorageDomain, int(startTxNum), int(endTxNum+1), order.Asc, kv.Unlim)
	if err != nil {
		return nil, false, err
	}
	defer it.Close()

	diffs := make([]kv.DomainEntryDiff, 0, 32)
	prevStepBytes := make([]byte, 8)
	currentStepBytes := make([]byte, 8)
	for it.HasNext() {
		k, _, err := it.Next()
		if err != nil {
			return nil, false, err
		}
		restoreVal, restoreOK, err := ttx.HistorySeek(kv.StorageDomain, k, startTxNum)
		if err != nil {
			return nil, false, err
		}
		if !restoreOK {
			continue
		}
		step := kv.Step(0)
		if _, latestStep, latestErr := ttx.GetLatest(kv.StorageDomain, k); latestErr == nil {
			step = latestStep
		}
		binary.BigEndian.PutUint64(prevStepBytes, ^uint64(step))
		binary.BigEndian.PutUint64(currentStepBytes, ^uint64(step))
		valsKey := append(append(make([]byte, 0, len(k)+8), k...), currentStepBytes...)
		diffs = append(diffs, kv.DomainEntryDiff{
			Key:           toStringZeroCopy(valsKey),
			Value:         common.Copy(restoreVal),
			PrevStepBytes: common.Copy(prevStepBytes),
		})
	}
	return diffs, len(diffs) > 0, nil
}

func rewriteStorageDiffsetFromHistory(tx kv.RwTx, blockNumber uint64, existing []kv.DomainEntryDiff) ([]kv.DomainEntryDiff, bool, error) {
	ttx, ok := tx.(kv.TemporalTx)
	if !ok {
		return existing, false, nil
	}
	startTxNum, err := rawdbv3.TxNums.Min(tx, blockNumber)
	if err != nil {
		return nil, false, err
	}
	endTxNum, err := rawdbv3.TxNums.Max(tx, blockNumber)
	if err != nil {
		return nil, false, err
	}
	if endTxNum == 0 && blockNumber != 0 {
		return existing, false, nil
	}
	it, err := ttx.HistoryRange(kv.StorageDomain, int(startTxNum), int(endTxNum+1), order.Asc, kv.Unlim)
	if err != nil {
		return nil, false, err
	}
	defer it.Close()

	rewritten := make(map[string]kv.DomainEntryDiff, len(existing)+16)
	for i := range existing {
		entry := existing[i]
		rewritten[entry.Key] = kv.DomainEntryDiff{
			Key:           entry.Key,
			Value:         common.Copy(entry.Value),
			PrevStepBytes: common.Copy(entry.PrevStepBytes),
		}
	}

	prevStepBytes := make([]byte, 8)
	currentStepBytes := make([]byte, 8)
	changed := false
	for it.HasNext() {
		k, _, err := it.Next()
		if err != nil {
			return nil, false, err
		}
		restoreVal, restoreOK, err := ttx.HistorySeek(kv.StorageDomain, k, startTxNum)
		if err != nil {
			return nil, false, err
		}
		if !restoreOK {
			continue
		}
		step := kv.Step(0)
		if _, latestStep, latestErr := ttx.GetLatest(kv.StorageDomain, k); latestErr == nil {
			step = latestStep
		}
		binary.BigEndian.PutUint64(prevStepBytes, ^uint64(step))
		binary.BigEndian.PutUint64(currentStepBytes, ^uint64(step))
		valsKey := append(append(make([]byte, 0, len(k)+8), k...), currentStepBytes...)
		key := toStringZeroCopy(valsKey)
		rewritten[key] = kv.DomainEntryDiff{
			Key:           key,
			Value:         common.Copy(restoreVal),
			PrevStepBytes: common.Copy(prevStepBytes),
		}
		changed = true
	}
	if !changed {
		return existing, false, nil
	}
	out := make([]kv.DomainEntryDiff, 0, len(rewritten))
	for _, entry := range rewritten {
		out = append(out, entry)
	}
	sort.Slice(out, func(i, j int) bool {
		return out[i].Key < out[j].Key
	})
	return out, true, nil
}

func synthesizeCodeDiffsetFromHistory(tx kv.RwTx, blockNumber uint64) ([]kv.DomainEntryDiff, bool, error) {
	ttx, ok := tx.(kv.TemporalTx)
	if !ok {
		return nil, false, nil
	}
	startTxNum, err := rawdbv3.TxNums.Min(tx, blockNumber)
	if err != nil {
		return nil, false, err
	}
	endTxNum, err := rawdbv3.TxNums.Max(tx, blockNumber)
	if err != nil {
		return nil, false, err
	}
	if endTxNum == 0 && blockNumber != 0 {
		return nil, false, nil
	}
	it, err := ttx.HistoryRange(kv.CodeDomain, int(startTxNum), int(endTxNum+1), order.Asc, kv.Unlim)
	if err != nil {
		return nil, false, err
	}
	defer it.Close()

	diffs := make([]kv.DomainEntryDiff, 0, 8)
	prevStepBytes := make([]byte, 8)
	currentStepBytes := make([]byte, 8)
	for it.HasNext() {
		k, _, err := it.Next()
		if err != nil {
			return nil, false, err
		}
		restoreVal, restoreOK, err := ttx.HistorySeek(kv.CodeDomain, k, startTxNum)
		if err != nil {
			return nil, false, err
		}
		if !restoreOK {
			continue
		}
		step := kv.Step(0)
		if _, latestStep, latestErr := ttx.GetLatest(kv.CodeDomain, k); latestErr == nil {
			step = latestStep
		}
		binary.BigEndian.PutUint64(prevStepBytes, ^uint64(step))
		binary.BigEndian.PutUint64(currentStepBytes, ^uint64(step))
		valsKey := append(append(make([]byte, 0, len(k)+8), k...), currentStepBytes...)
		diffs = append(diffs, kv.DomainEntryDiff{
			Key:           toStringZeroCopy(valsKey),
			Value:         common.Copy(restoreVal),
			PrevStepBytes: common.Copy(prevStepBytes),
		})
	}
	return diffs, len(diffs) > 0, nil
}

func logDiffsetSource(source string, blockNumber uint64, blockHash common.Hash, diffs [kv.DomainLen][]kv.DomainEntryDiff) {
	if !traceDiffsetSource {
		return
	}
	if sender := findDomainDiff(diffs[kv.AccountsDomain], fixedSenderDiffTraceAddrBytes); sender != nil {
		log.Warn("state diffset source trace",
			"source", source,
			"block", blockNumber,
			"block_hash", blockHash,
			"sender", common.BytesToAddress(fixedSenderDiffTraceAddrBytes),
			"value_len", len(sender.Value),
			"value_preview", badRootValuePreview(sender.Value),
			"prev_step", fmt.Sprintf("%x", sender.PrevStepBytes),
			"accounts_len", len(diffs[kv.AccountsDomain]),
		)
		return
	}
	log.Warn("state diffset source trace",
		"source", source,
		"block", blockNumber,
		"block_hash", blockHash,
		"sender", common.BytesToAddress(fixedSenderDiffTraceAddrBytes),
		"value_len", 0,
		"value_preview", "missing",
		"accounts_len", len(diffs[kv.AccountsDomain]),
	)
}

func findDomainDiff(diffs []kv.DomainEntryDiff, key []byte) *kv.DomainEntryDiff {
	for i := range diffs {
		diffKey := toBytesZeroCopy(diffs[i].Key)
		if bytes.Equal(diffKey, key) {
			return &diffs[i]
		}
		if len(diffKey) > len(key) && bytes.Equal(diffKey[:len(key)], key) {
			return &diffs[i]
		}
	}
	return nil
}

func errString(err error) string {
	if err == nil {
		return ""
	}
	return err.Error()
}

func lookupAccountValueByPrevStep(tx kv.Tx, logicalKey []byte, prevStepBytes []byte) ([]byte, bool, error) {
	if len(logicalKey) == 0 || len(prevStepBytes) != 8 {
		return nil, false, nil
	}
	c, err := tx.CursorDupSort(kv.TblAccountVals)
	if err != nil {
		return nil, false, err
	}
	defer c.Close()
	dup, err := c.SeekBothRange(logicalKey, prevStepBytes)
	if err != nil {
		return nil, false, err
	}
	if dup == nil || len(dup) < 8 || !bytes.Equal(dup[:8], prevStepBytes) {
		return nil, false, nil
	}
	return common.Copy(dup[8:]), true, nil
}

func accountLogicalKey(diffKey []byte) []byte {
	if len(diffKey) == 0 {
		return nil
	}
	if len(diffKey) >= 20+8 {
		return common.Copy(diffKey[:20])
	}
	if len(diffKey) >= 20 {
		return common.Copy(diffKey[:20])
	}
	return common.Copy(diffKey)
}

func (sd *TemporalMemBatch) IndexAdd(table kv.InvertedIdx, key []byte, txNum uint64) (err error) {
	for _, writer := range sd.iiWriters {
		if writer.name == table {
			return writer.Add(key, txNum)
		}
	}
	panic(fmt.Errorf("unknown index %s", table))
}

func (sd *TemporalMemBatch) Close() {
	for _, d := range sd.domainWriters {
		d.Close()
	}
	for _, iiWriter := range sd.iiWriters {
		iiWriter.close()
	}
}
func (sd *TemporalMemBatch) Flush(ctx context.Context, tx kv.RwTx) error {
	defer mxFlushTook.ObserveDuration(time.Now())
	start := time.Now()
	if traceTemporalFlush {
		log.Warn("temporal flush trace", "phase", "flush_start", "diffsets", len(sd.pastChangesAccumulator))
	}
	if err := sd.flushDiffSet(ctx, tx); err != nil {
		return err
	}
	sd.pastChangesAccumulator = make(map[string]*changeset.StateChangeSet)
	if err := sd.flushWriters(ctx, tx); err != nil {
		return err
	}
	if traceTemporalFlush {
		log.Warn("temporal flush trace", "phase", "flush_done", "elapsed", time.Since(start))
	}
	return nil
}

func (sd *TemporalMemBatch) flushDiffSet(ctx context.Context, tx kv.RwTx) error {
	start := time.Now()
	if traceTemporalFlush {
		log.Warn("temporal flush trace", "phase", "diffset_start", "diffsets", len(sd.pastChangesAccumulator))
	}
	written := 0
	for key, changeSet := range sd.pastChangesAccumulator {
		if len(key) < 40 {
			return fmt.Errorf("unexpected diffset key len %d", len(key))
		}
		blockNum := binary.BigEndian.Uint64(toBytesZeroCopy(key[:8]))
		blockHash := common.BytesToHash(toBytesZeroCopy(key[8:]))
		if traceTemporalFlush && (written == 0 || written%1000 == 0) {
			log.Warn("temporal flush trace", "phase", "diffset_write", "written", written, "diffset_block", blockNum, "diffset_hash", blockHash)
		}
		if err := changeset.WriteDiffSet(tx, blockNum, blockHash, changeSet); err != nil {
			return err
		}
		written++
	}
	if traceTemporalFlush {
		log.Warn("temporal flush trace", "phase", "diffset_done", "written", written, "elapsed", time.Since(start))
	}
	return nil
}

func (sd *TemporalMemBatch) flushWriters(ctx context.Context, tx kv.RwTx) error {
	aggTx := AggTx(tx)
	for di, w := range sd.domainWriters {
		if w == nil {
			continue
		}
		start := time.Now()
		if traceTemporalFlush {
			log.Warn("temporal flush trace", "phase", "domain_writer_start", "domain", kv.Domain(di).String())
		}
		if kv.Domain(di) == kv.AccountsDomain {
			log.Info("escrow trace mem_flush",
				"mem", fmt.Sprintf("%p", sd),
				"writer", fmt.Sprintf("%p", w),
				"values", fmt.Sprintf("%p", w.values),
				"discard", w.discard,
				"large_vals", w.largeVals,
			)
		}
		if err := w.Flush(ctx, tx); err != nil {
			return err
		}
		if traceTemporalFlush {
			log.Warn("temporal flush trace", "phase", "domain_writer_done", "domain", kv.Domain(di).String(), "elapsed", time.Since(start))
		}
		aggTx.d[di].closeValsCursor() //TODO: why?
		w.Close()
	}
	for ii, w := range sd.iiWriters {
		if w == nil {
			continue
		}
		start := time.Now()
		if traceTemporalFlush {
			log.Warn("temporal flush trace", "phase", "ii_writer_start", "index", ii, "name", w.name, "filename", w.filenameBase)
		}
		if err := w.Flush(ctx, tx); err != nil {
			return err
		}
		if traceTemporalFlush {
			log.Warn("temporal flush trace", "phase", "ii_writer_done", "index", ii, "name", w.name, "filename", w.filenameBase, "elapsed", time.Since(start))
		}
		w.close()
	}
	return nil
}

func (sd *TemporalMemBatch) DiscardWrites(domain kv.Domain) {
	sd.domainWriters[domain].discard = true
	sd.domainWriters[domain].h.discard = true
}

func AggTx(tx kv.Tx) *AggregatorRoTx {
	if withAggTx, ok := tx.(interface{ AggTx() any }); ok {
		return withAggTx.AggTx().(*AggregatorRoTx)
	}

	return nil
}

func toStringZeroCopy(v []byte) string {
	if len(v) == 0 {
		return ""
	}
	return unsafe.String(&v[0], len(v))
}

func toBytesZeroCopy(s string) []byte { return unsafe.Slice(unsafe.StringData(s), len(s)) }
