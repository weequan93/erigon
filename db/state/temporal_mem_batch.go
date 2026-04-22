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
	} else if err == nil && ok && len(diffs[kv.AccountsDomain]) > 0 {
		if rewritten, changed, rewriteErr := rewriteAccountDiffsetFromHistory(tx, blockNumber, diffs[kv.AccountsDomain]); rewriteErr != nil {
			log.Warn("state diffset history rewrite failed", "block", blockNumber, "block_hash", blockHash, "err", rewriteErr)
		} else if changed {
			diffs[kv.AccountsDomain] = rewritten
			log.Warn("state diffset history rewrite",
				"block", blockNumber,
				"block_hash", blockHash,
				"accounts_len", len(rewritten),
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
	} else if err == nil && ok && len(diffs[kv.StorageDomain]) > 0 {
		if rewritten, changed, rewriteErr := rewriteStorageDiffsetFromHistory(tx, blockNumber, diffs[kv.StorageDomain]); rewriteErr != nil {
			log.Warn("state storage diffset history rewrite failed", "block", blockNumber, "block_hash", blockHash, "err", rewriteErr)
		} else if changed {
			diffs[kv.StorageDomain] = rewritten
			log.Warn("state storage diffset history rewrite",
				"block", blockNumber,
				"block_hash", blockHash,
				"storage_len", len(rewritten),
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
		restoreVal, _, err := ttx.HistorySeek(kv.AccountsDomain, k, startTxNum)
		if err != nil {
			return nil, false, err
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
	for it.HasNext() {
		k, _, err := it.Next()
		if err != nil {
			return nil, false, err
		}
		restoreVal, _, err := ttx.HistorySeek(kv.AccountsDomain, k, startTxNum)
		if err != nil {
			return nil, false, err
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
		restoreVal, _, err := ttx.HistorySeek(kv.StorageDomain, k, startTxNum)
		if err != nil {
			return nil, false, err
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
		restoreVal, _, err := ttx.HistorySeek(kv.StorageDomain, k, startTxNum)
		if err != nil {
			return nil, false, err
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

func logDiffsetSource(source string, blockNumber uint64, blockHash common.Hash, diffs [kv.DomainLen][]kv.DomainEntryDiff) {
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
	keyStr := toStringZeroCopy(key)
	for i := range diffs {
		if diffs[i].Key == keyStr {
			return &diffs[i]
		}
	}
	return nil
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
	if err := sd.flushDiffSet(ctx, tx); err != nil {
		return err
	}
	sd.pastChangesAccumulator = make(map[string]*changeset.StateChangeSet)
	if err := sd.flushWriters(ctx, tx); err != nil {
		return err
	}
	return nil
}

func (sd *TemporalMemBatch) flushDiffSet(ctx context.Context, tx kv.RwTx) error {
	for key, changeSet := range sd.pastChangesAccumulator {
		blockNum := binary.BigEndian.Uint64(toBytesZeroCopy(key[:8]))
		blockHash := common.BytesToHash(toBytesZeroCopy(key[8:]))
		if err := changeset.WriteDiffSet(tx, blockNum, blockHash, changeSet); err != nil {
			return err
		}
	}
	return nil
}

func (sd *TemporalMemBatch) flushWriters(ctx context.Context, tx kv.RwTx) error {
	aggTx := AggTx(tx)
	for di, w := range sd.domainWriters {
		if w == nil {
			continue
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
		aggTx.d[di].closeValsCursor() //TODO: why?
		w.Close()
	}
	for _, w := range sd.iiWriters {
		if w == nil {
			continue
		}
		if err := w.Flush(ctx, tx); err != nil {
			return err
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
