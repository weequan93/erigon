package state

import (
	"os"
	"strings"

	"github.com/erigontech/erigon-lib/common"
	"github.com/erigontech/erigon-lib/common/length"
)

var badRootAccountsSet = func() map[common.Address]struct{} {
	raw := os.Getenv("ERIGON_BAD_ROOT_ACCOUNTS")
	if raw == "" {
		return nil
	}
	parts := strings.Split(raw, ",")
	out := make(map[common.Address]struct{}, len(parts))
	for _, part := range parts {
		part = strings.TrimSpace(part)
		if part == "" || !common.IsHexAddress(part) {
			continue
		}
		out[common.HexToAddress(part)] = struct{}{}
	}
	if len(out) == 0 {
		return nil
	}
	return out
}()

func isBadRootAccount(addr common.Address) bool {
	if len(badRootAccountsSet) == 0 {
		return false
	}
	_, ok := badRootAccountsSet[addr]
	return ok
}

func isBadRootAccountBytes(key []byte) bool {
	if len(key) != length.Addr {
		return false
	}
	return isBadRootAccount(common.BytesToAddress(key))
}
