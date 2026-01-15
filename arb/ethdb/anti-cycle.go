package ethdb

import (
	gethethdb "github.com/ethereum/go-ethereum/ethdb"

	"github.com/erigontech/erigon/arb/ethdb/wasmdb"
)

const DefaultTargetDescriptionArm = "arm64-linux-unknown+neon"
const DefaultTargetDescriptionX86 = "x86_64-linux-unknown+sse4.2+lzcnt+bmi"

var SetWasmTarget func(name gethethdb.WasmTarget, description string, native bool) error

// InitializeLocalWasmTarget initializes the local WASM target based on the current arch.
func InitialiazeLocalWasmTarget() {
	if SetWasmTarget == nil {
		return
	}
	lt := wasmdb.LocalTarget()
	desc := "description unavailable"
	switch lt {
	case wasmdb.TargetAmd64:
		desc = DefaultTargetDescriptionX86
	case wasmdb.TargetArm64:
		desc = DefaultTargetDescriptionArm
	}

	SetWasmTarget(gethethdb.WasmTarget(lt), desc, true)
}
