//go:build erigon
// +build erigon

package exec3

import (
	"sync/atomic"

	"github.com/offchainlabs/nitro/arbos"
	"github.com/offchainlabs/nitro/arbos/arbostypes"
	"github.com/offchainlabs/nitro/statetransfer"

	ecommon "github.com/erigontech/erigon-lib/common"
	"github.com/erigontech/erigon/core/state"
	"github.com/erigontech/erigon/db/kv"
	dbstate "github.com/erigontech/erigon/db/state"
	"github.com/erigontech/erigon/execution/chain"
)

var arbitrumInitMessage atomic.Pointer[arbostypes.ParsedInitMessage]

// SetArbitrumInitMessage overrides the init message used during genesis initialization.
func SetArbitrumInitMessage(msg *arbostypes.ParsedInitMessage) {
	arbitrumInitMessage.Store(msg)
}

func getArbitrumInitMessage(chainCfg *chain.Config) (*arbostypes.ParsedInitMessage, error) {
	if msg := arbitrumInitMessage.Load(); msg != nil {
		return msg, nil
	}
	return arbos.BuildInitMessageFromChainConfig(chainCfg)
}

func initializeArbosGenesis(
	ibs state.IntraBlockStateArbitrum,
	domains *dbstate.SharedDomains,
	putDel kv.TemporalPutDel,
	chainCfg *chain.Config,
	timestamp uint64,
	accountsPerSync uint,
) (ecommon.Hash, error) {
	initMsg, err := getArbitrumInitMessage(chainCfg)
	if err != nil {
		return ecommon.Hash{}, err
	}

	initData := statetransfer.ArbosInitializationInfo{
		NextBlockNumber: 0,
	}
	initReader := statetransfer.NewMemoryInitDataReader(&initData)

	return arbos.InitializeArbosInDatabase(
		ibs,
		domains,
		putDel,
		initReader,
		chainCfg,
		initMsg,
		timestamp,
		accountsPerSync,
	)
}
