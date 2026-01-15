//go:build !erigon
// +build !erigon

package exec3

import (
	"errors"

	"github.com/offchainlabs/nitro/arbos/arbostypes"

	ecommon "github.com/erigontech/erigon-lib/common"
	"github.com/erigontech/erigon/core/state"
	"github.com/erigontech/erigon/db/kv"
	dbstate "github.com/erigontech/erigon/db/state"
	"github.com/erigontech/erigon/execution/chain"
)

// SetArbitrumInitMessage is a no-op when erigon integration is disabled.
func SetArbitrumInitMessage(_ *arbostypes.ParsedInitMessage) {}

func initializeArbosGenesis(
	_ state.IntraBlockStateArbitrum,
	_ *dbstate.SharedDomains,
	_ kv.TemporalPutDel,
	_ *chain.Config,
	_ uint64,
	_ uint,
) (ecommon.Hash, error) {
	return ecommon.Hash{}, errors.New("arbos initialization requires erigon build tag")
}
