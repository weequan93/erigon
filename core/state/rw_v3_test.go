package state

import (
	"testing"

	"github.com/erigontech/erigon/execution/chain"
)

func TestSpuriousDragonEnabledForTask(t *testing.T) {
	t.Run("uses rules when present", func(t *testing.T) {
		task := &TxTask{Rules: &chain.Rules{IsSpuriousDragon: false}}
		if spuriousDragonEnabledForTask(task) {
			t.Fatalf("expected false when rules disable spurious dragon")
		}
		task.Rules.IsSpuriousDragon = true
		if !spuriousDragonEnabledForTask(task) {
			t.Fatalf("expected true when rules enable spurious dragon")
		}
	})

	t.Run("arbitrum fallback when rules missing", func(t *testing.T) {
		task := &TxTask{
			Config: &chain.Config{
				ArbitrumChainParams: chain.ArbitrumChainParams{EnableArbOS: true},
			},
		}
		if !spuriousDragonEnabledForTask(task) {
			t.Fatalf("expected true for arbitrum when rules are missing")
		}
	})

	t.Run("non arbitrum without rules", func(t *testing.T) {
		task := &TxTask{Config: &chain.Config{}}
		if spuriousDragonEnabledForTask(task) {
			t.Fatalf("expected false without rules on non-arbitrum config")
		}
	})
}
