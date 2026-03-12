// Copyright 2026 The Erigon Authors
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

package trie

import (
	"fmt"
	"sort"
	"strings"

	"github.com/erigontech/erigon-lib/common"
	"github.com/erigontech/erigon-lib/common/length"
	"github.com/erigontech/erigon-lib/crypto"
)

// CollectNodeRLPPreimages walks all expanded trie nodes and returns canonical
// RLP preimages keyed by Keccak256 hash.
//
// HashNode placeholders do not carry the underlying payload bytes and are not
// included in the result.
func (t *Trie) CollectNodeRLPPreimages() (map[common.Hash][]byte, error) {
	preimages := make(map[common.Hash][]byte)
	if t == nil || t.RootNode == nil {
		return preimages, nil
	}

	// Hashing can populate cached node references. Reset after collection so
	// callers keep deterministic behavior independent of diagnostics.
	defer t.Reset()

	hasher := newHasher(t.valueNodesRLPEncoded)
	defer returnHasherToPool(hasher)

	var walk func(Node) error
	walk = func(node Node) error {
		switch n := node.(type) {
		case nil:
			return nil
		case HashNode:
			return nil
		case *HashNode:
			return nil
		case ValueNode:
			return nil
		case CodeNode:
			return nil
		case *AccountNode:
			// Account payload is encoded by its parent short/full node. Here we
			// only recurse into materialized storage subtree.
			return walk(n.Storage)
		case *ShortNode, *FullNode, *DuoNode:
			nodeRLP, err := hasher.hashChildren(n, 0)
			if err != nil {
				return err
			}
			if len(nodeRLP) > 0 {
				nodeCopy := common.Copy(nodeRLP)
				preimages[crypto.Keccak256Hash(nodeCopy)] = nodeCopy
			}

			switch typed := n.(type) {
			case *ShortNode:
				return walk(typed.Val)
			case *DuoNode:
				if err := walk(typed.child1); err != nil {
					return err
				}
				return walk(typed.child2)
			case *FullNode:
				for i := range typed.Children {
					if err := walk(typed.Children[i]); err != nil {
						return err
					}
				}
				return nil
			default:
				return nil
			}
		default:
			return fmt.Errorf("unsupported trie node type %T", n)
		}
	}

	if err := walk(t.RootNode); err != nil {
		return nil, err
	}
	return preimages, nil
}

// CollectHashNodeReferences walks expanded trie nodes and returns hashes carried
// by HashNode placeholders. These references do not include node payload bytes
// and are useful only for diagnostics.
func (t *Trie) CollectHashNodeReferences() map[common.Hash]struct{} {
	refs := make(map[common.Hash]struct{})
	if t == nil || t.RootNode == nil {
		return refs
	}

	var walk func(Node)
	walk = func(node Node) {
		switch n := node.(type) {
		case nil:
			return
		case HashNode:
			if len(n.hash) == length.Hash {
				refs[common.BytesToHash(n.hash)] = struct{}{}
			}
			return
		case *HashNode:
			if n != nil && len(n.hash) == length.Hash {
				refs[common.BytesToHash(n.hash)] = struct{}{}
			}
			return
		case ValueNode:
			return
		case CodeNode:
			return
		case *AccountNode:
			walk(n.Storage)
			return
		case *ShortNode:
			walk(n.Val)
			return
		case *DuoNode:
			walk(n.child1)
			walk(n.child2)
			return
		case *FullNode:
			for i := range n.Children {
				walk(n.Children[i])
			}
			return
		default:
			return
		}
	}

	walk(t.RootNode)
	return refs
}

func encodeNibblePath(path []byte) string {
	if len(path) == 0 {
		return "<root>"
	}
	var b strings.Builder
	b.Grow(len(path) + 4)
	for _, nibble := range path {
		switch {
		case nibble < 16:
			b.WriteByte("0123456789abcdef"[nibble])
		case nibble == 16:
			b.WriteByte('|')
		default:
			b.WriteByte('?')
		}
	}
	return b.String()
}

// CollectHashNodeReferencesWithPaths walks expanded trie nodes and returns hash
// placeholders together with nibble paths where each reference appears.
func (t *Trie) CollectHashNodeReferencesWithPaths() map[common.Hash][]string {
	refs := make(map[common.Hash]map[string]struct{})
	if t == nil || t.RootNode == nil {
		return map[common.Hash][]string{}
	}

	addRef := func(hashBytes []byte, path []byte) {
		if len(hashBytes) != length.Hash {
			return
		}
		hash := common.BytesToHash(hashBytes)
		pathStr := encodeNibblePath(path)
		pathSet, ok := refs[hash]
		if !ok {
			pathSet = make(map[string]struct{}, 1)
			refs[hash] = pathSet
		}
		pathSet[pathStr] = struct{}{}
	}

	var walk func(Node, []byte)
	walk = func(node Node, path []byte) {
		switch n := node.(type) {
		case nil:
			return
		case HashNode:
			addRef(n.hash, path)
			return
		case *HashNode:
			if n != nil {
				addRef(n.hash, path)
			}
			return
		case ValueNode:
			return
		case CodeNode:
			return
		case *AccountNode:
			// Account node itself doesn't consume path nibbles. Continue into
			// materialized storage subtree.
			walk(n.Storage, path)
			return
		case *ShortNode:
			nextPath := append(common.Copy(path), n.Key...)
			walk(n.Val, nextPath)
			return
		case *DuoNode:
			i1, i2 := n.childrenIdx()
			path1 := append(common.Copy(path), i1)
			path2 := append(common.Copy(path), i2)
			walk(n.child1, path1)
			walk(n.child2, path2)
			return
		case *FullNode:
			for i := range n.Children {
				nextPath := append(common.Copy(path), byte(i))
				walk(n.Children[i], nextPath)
			}
			return
		default:
			return
		}
	}

	walk(t.RootNode, nil)

	out := make(map[common.Hash][]string, len(refs))
	for hash, pathSet := range refs {
		paths := make([]string, 0, len(pathSet))
		for pathStr := range pathSet {
			paths = append(paths, pathStr)
		}
		sort.Strings(paths)
		out[hash] = paths
	}
	return out
}
