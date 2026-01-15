package mdbx

// ReadTxWaits is a compatibility stub for builds without MDBX wait counters.
func ReadTxWaits() uint64 {
	return 0
}

// TxnRestarts is a compatibility stub for builds without MDBX restart counters.
func TxnRestarts() uint64 {
	return 0
}
