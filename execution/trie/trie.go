// Copyright 2019 The go-ethereum Authors
// (original work)
// Copyright 2024 The Erigon Authors
// (modifications)
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

// Package trie implements Merkle Patricia Tries.
package trie

import (
	"bytes"
	"encoding/binary"
	"fmt"
	"os"
	"reflect"
	"strings"

	"github.com/erigontech/erigon-lib/common"
	"github.com/erigontech/erigon-lib/crypto"
	"github.com/erigontech/erigon/execution/types/accounts"
)

var (
	// EmptyRoot is the known root hash of an empty trie.
	// DESCRIBED: docs/programmers_guide/guide.md#root
	EmptyRoot = common.HexToHash("56e81f171bcc55a6ff8345e692c0f86e5b48e01b996cadc001622fb5e363b421")

	// emptyState is the known hash of an empty state trie entry.
	emptyState = crypto.Keccak256Hash(nil)

	// Keep merge relaxations opt-in. Enabling them implicitly via generic debug
	// flags can silently mutate witness shape and hide preimage gaps.
	mergeAllowHashnodeMismatch = strings.EqualFold(os.Getenv("ERIGON_TRIE_MERGE_ALLOW_HASHNODE_MISMATCH"), "true")
	mergePreferRhsOnHashnodeMismatch = !strings.EqualFold(os.Getenv("ERIGON_TRIE_MERGE_HASHNODE_POLICY"), "lhs")
	// Some witness reads can disagree on whether a ShortNode key carries the
	// terminal nibble (0x10) while still describing the same subtree. Allow
	// normalizing that representation mismatch when explicitly requested.
	mergeAllowShortTerminatorMismatch = strings.EqualFold(os.Getenv("ERIGON_TRIE_MERGE_ALLOW_SHORT_TERMINATOR_MISMATCH"), "true")
	// Witness materialization can also differ on whether a branch segment is
	// represented as FullNode or ShortNode; normalize only when requested.
	mergeAllowShortFullTypeNormalization = strings.EqualFold(os.Getenv("ERIGON_TRIE_MERGE_ALLOW_SHORT_FULL_NORMALIZATION"), "true")
	// Partial witness tries for different touched keys can legitimately diverge
	// inside compressed short-node segments. Allow normalizing this only when
	// explicitly requested by env flag.
	mergeAllowShortKeyDivergence = strings.EqualFold(os.Getenv("ERIGON_TRIE_MERGE_ALLOW_SHORT_KEY_DIVERGENCE"), "true")
)

// Trie is a Merkle Patricia Trie.
// The zero value is an empty trie with no database.
// Use New to create a trie that sits on top of a database.
//
// Trie is not safe for concurrent use.
// Deprecated
// use package turbo/trie
type Trie struct {
	RootNode             Node
	valueNodesRLPEncoded bool

	newHasherFunc func() *hasher
	strictHash    bool // if true, the trie will panic on a hash access
}

// New creates a trie with an existing root node from db.
//
// If root is the zero hash or the sha3 hash of an empty string, the
// trie is initially empty and does not require a database. Otherwise,
// New will panic if db is nil and returns a MissingNodeError if root does
// not exist in the database. Accessing the trie loads nodes from db on demand.
// Deprecated
// use package turbo/trie
func New(root common.Hash) *Trie {
	trie := &Trie{
		newHasherFunc: func() *hasher { return newHasher( /*valueNodesRlpEncoded = */ false) },
	}
	if (root != common.Hash{}) && root != EmptyRoot {
		trie.RootNode = &HashNode{hash: root[:]}
	}
	return trie
}

func NewInMemoryTrie(root Node) *Trie {
	trie := &Trie{
		newHasherFunc: func() *hasher { return newHasher( /*valueNodesRlpEncoded = */ false) },
		RootNode:      root,
	}
	return trie
}

func NewInMemoryTrieRLPEncoded(root Node) *Trie {
	trie := &Trie{
		newHasherFunc:        func() *hasher { return newHasher( /*valueNodesRlpEncoded = */ true) },
		RootNode:             root,
		valueNodesRLPEncoded: true,
	}
	return trie
}

// this will merge node2 into node1, returns a boolean mergeNecessary, if it was necessary to replace a child.
// If not, then the two full nodes are the same so no replacement was necessary
// This function also performs certain sanity checks which can result in an error if they fail
func mergePathAppend(path []byte, nibble byte) []byte {
	next := make([]byte, len(path)+1)
	copy(next, path)
	next[len(path)] = nibble
	return next
}

func mergePathAppendKey(path []byte, key []byte) []byte {
	next := make([]byte, len(path)+len(key))
	copy(next, path)
	copy(next[len(path):], key)
	return next
}

func formatMergePath(path []byte) string {
	if len(path) == 0 {
		return "<root>"
	}
	const hexChars = "0123456789abcdef"
	formatted := make([]byte, 0, len(path))
	for _, nibble := range path {
		if nibble < 16 {
			formatted = append(formatted, hexChars[nibble])
			continue
		}
		if nibble == 16 {
			formatted = append(formatted, '|')
			continue
		}
		formatted = append(formatted, '?')
	}
	return fmt.Sprintf("%s(raw=%x)", string(formatted), path)
}

func merge2FullNodes(node1, node2 *FullNode, path []byte) (bool, error) {
	furtherMergingNeeded := false
	for i := 0; i < len(node1.Children); i++ {
		child1 := node1.Children[i]
		child2 := node2.Children[i]
		// nil means "no information for this branch" in one partial trie. Keep/merge
		// whichever side has data.
		if child1 == nil {
			if child2 != nil {
				node1.Children[i] = child2
			}
			continue
		}
		if child2 == nil {
			continue
		}

		hashNode1, ok1 := child1.(*HashNode)
		hashNode2, ok2 := child2.(*HashNode)
		switch {
		case ok1 && ok2:
			// both are hash nodes
			if !bytes.Equal(hashNode1.hash, hashNode2.hash) {
				return false, fmt.Errorf(
					"children hashnodes have different hashes at path=%s nibble=%x hash1(%x)!=hash2(%x) parent1=%s parent2=%s child1=%s child2=%s",
					formatMergePath(path),
					i,
					hashNode1.hash,
					hashNode2.hash,
					describeFullNodeForMerge(node1),
					describeFullNodeForMerge(node2),
					describeNodeForMerge(node1.Children[i]),
					describeNodeForMerge(node2.Children[i]),
				)
			}
		case ok1 && !ok2:
			// child2 has the expanded node, prefer it
			node1.Children[i] = child2
		case !ok1 && ok2:
			// child1 is already expanded, keep it
		default:
			// both are expanded nodes: types must match and then recurse
			if reflect.TypeOf(child1) != reflect.TypeOf(child2) {
				return false, fmt.Errorf(
					"children have different types at path=%s index=%d: %T != %T child1=%s child2=%s",
					formatMergePath(path),
					i,
					child1,
					child2,
					describeNodeForMerge(child1),
					describeNodeForMerge(child2),
				)
			}
			furtherMergingNeeded = true
		}
	}
	return furtherMergingNeeded, nil
}

func merge2ShortNodes(node1, node2 *ShortNode, path []byte) (bool, error) {
	furtherMergingNeeded := false
	if !bytes.Equal(node1.Key, node2.Key) { // sanity check
		if canonical, ok := normalizeShortKeyMismatchForMerge(node1.Key, node2.Key); ok && mergeAllowShortTerminatorMismatch {
			node1.Key = canonical
			node2.Key = append([]byte(nil), canonical...)
		} else if mergeAllowShortKeyDivergence {
			expanded1 := expandShortNodeForMerge(node1)
			expanded2 := expandShortNodeForMerge(node2)
			merged, err := mergeNodesRecursive(expanded1, expanded2, path)
			if err != nil {
				return false, err
			}
			switch mergedNode := merged.(type) {
			case *ShortNode:
				node1.Key = append(node1.Key[:0], mergedNode.Key...)
				node1.Val = mergedNode.Val
				return false, nil
			default:
				// Caller should replace this node with the returned merged node.
				return true, nil
			}
		} else {
			return false, fmt.Errorf(
				"mismatch in the short node keys at path=%s node1.Key(%x)!=node2.Key(%x)",
				formatMergePath(path),
				node1.Key,
				node2.Key,
			)
		}
	}
	node1.Val = normalizeMergeNode(node1.Val)
	node2.Val = normalizeMergeNode(node2.Val)

	if node1.Val == nil {
		if node2.Val != nil {
			node1.Val = node2.Val
		}
		return false, nil
	}
	if node2.Val == nil {
		return false, nil
	}

	hashNode1, ok1 := node1.Val.(*HashNode)
	hashNode2, ok2 := node2.Val.(*HashNode)
	switch {
	case ok1 && ok2:
		if !bytes.Equal(hashNode1.hash, hashNode2.hash) {
			return false, fmt.Errorf(
				"hashnodes have different hashes at path=%s short_key=%x hash1(%x) != hash2(%x)",
				formatMergePath(path),
				node1.Key,
				hashNode1.hash,
				hashNode2.hash,
			)
		}
	case ok1 && !ok2:
		node1.Val = node2.Val
	case !ok1 && ok2:
		// node1.Val already expanded, keep it
	default:
		if reflect.TypeOf(node1.Val) != reflect.TypeOf(node2.Val) {
			return false, fmt.Errorf(
				"node1.Val and node2.Val have different types at path=%s: %T != %T short_key=%x node1_val=%s node2_val=%s",
				formatMergePath(path),
				node1.Val,
				node2.Val,
				node1.Key,
				describeNodeForMerge(node1.Val),
				describeNodeForMerge(node2.Val),
			)
		}
		furtherMergingNeeded = true
	}
	return furtherMergingNeeded, nil
}

func stripShortTerminatorForMerge(key []byte) []byte {
	if hasTerm(key) {
		return key[:len(key)-1]
	}
	return key
}

func normalizeShortKeyMismatchForMerge(key1, key2 []byte) (canonical []byte, ok bool) {
	base1 := stripShortTerminatorForMerge(key1)
	base2 := stripShortTerminatorForMerge(key2)
	if !bytes.Equal(base1, base2) {
		return nil, false
	}
	// Require an actual representation mismatch where one side carries 0x10 and
	// the other doesn't, then normalize both to the shared non-terminating key.
	hasTerm1 := hasTerm(key1)
	hasTerm2 := hasTerm(key2)
	if hasTerm1 == hasTerm2 {
		return nil, false
	}
	return append([]byte(nil), base1...), true
}

func expandShortNodeForMerge(sn *ShortNode) Node {
	if sn == nil {
		return nil
	}
	if len(sn.Key) == 0 {
		return sn.Val
	}
	idx := sn.Key[0]
	rest := sn.Key[1:]
	full := &FullNode{}
	if len(rest) == 0 {
		full.Children[idx] = sn.Val
		return full
	}
	full.Children[idx] = &ShortNode{Key: append([]byte(nil), rest...), Val: sn.Val}
	return full
}

func normalizeMergeNode(n Node) Node {
	// Some trie variants wrap account/value leaves in a terminal ShortNode {key=0x10,val=*AccountNode}.
	// For merge-equivalence we can unwrap these wrappers.
	for {
		sn, ok := n.(*ShortNode)
		if !ok || sn == nil {
			return n
		}
		if len(sn.Key) == 1 && sn.Key[0] == 16 && sn.Val != nil {
			n = sn.Val
			continue
		}
		return n
	}
}

// Some witness construction variants materialize storage continuation directly as
// FullNode while others keep the AccountNode wrapper and attach the same storage
// subtree under AccountNode.Storage. Merge these representations by preserving
// account payload and recursively merging the storage trie.
func mergeAccountWithFullNode(accountNode *AccountNode, fullNode *FullNode, path []byte) (Node, error) {
	if accountNode == nil {
		return nil, fmt.Errorf("mergeAccountWithFullNode: nil account node at path=%s", formatMergePath(path))
	}
	if fullNode == nil {
		return accountNode, nil
	}

	storageNode := normalizeMergeNode(accountNode.Storage)
	if storageNode == nil {
		accountNode.Storage = fullNode
		return accountNode, nil
	}

	mergedStorage, err := mergeNodesRecursive(storageNode, fullNode, mergePathAppend(path, 16))
	if err != nil {
		return nil, err
	}
	accountNode.Storage = mergedStorage
	return accountNode, nil
}

func describeNodeForMerge(n Node) string {
	switch v := n.(type) {
	case nil:
		return "nil"
	case *HashNode:
		return fmt.Sprintf("HashNode(hash=%x)", v.hash)
	case *ShortNode:
		valType := "<nil>"
		if v.Val != nil {
			valType = fmt.Sprintf("%T", v.Val)
		}
		return fmt.Sprintf("ShortNode(key=%x,valType=%s)", v.Key, valType)
	case *FullNode:
		nonNil := 0
		for _, child := range v.Children {
			if child != nil {
				nonNil++
			}
		}
		return fmt.Sprintf("FullNode(nonNilChildren=%d)", nonNil)
	case *AccountNode:
		storageType := "<nil>"
		if v.Storage != nil {
			storageType = fmt.Sprintf("%T", v.Storage)
		}
		return fmt.Sprintf(
			"AccountNode(nonce=%d,balance=%s,root=%x,codeHash=%x,storageType=%s)",
			v.Nonce,
			v.Balance.String(),
			v.Root,
			v.CodeHash,
			storageType,
		)
	case ValueNode:
		return fmt.Sprintf("ValueNode(len=%d,val=%x)", len(v), v)
	default:
		return fmt.Sprintf("%T", n)
	}
}

func describeFullNodeForMerge(node *FullNode) string {
	if node == nil {
		return "FullNode(nil)"
	}
	nonNil := 0
	sample := make([]string, 0, 6)
	for idx, child := range node.Children {
		if child == nil {
			continue
		}
		nonNil++
		if len(sample) < cap(sample) {
			sample = append(sample, fmt.Sprintf("%x:%s", idx, describeNodeForMerge(child)))
		}
	}
	return fmt.Sprintf("FullNode(nonNilChildren=%d,sample=%v)", nonNil, sample)
}

func merge2AccountNodes(node1, node2 *AccountNode) (furtherMergingNeeded bool) {
	storage1 := node1.Storage
	storage2 := node2.Storage
	if storage1 == nil {
		if storage2 != nil {
			node1.Storage = storage2
		}
		return false
	}
	if storage2 == nil {
		return false
	}
	_, isHashNode1 := storage1.(*HashNode) // check if storage1 is a hashnode
	_, isHashNode2 := storage2.(*HashNode) // check if storage2 is a hashnode
	if isHashNode1 && !isHashNode2 {       // node2 has the expanded storage trie, so use that instead of the hashnode
		node1.Storage = storage2
		return false
	}

	if !isHashNode1 && !isHashNode2 { // the 2 storage tries need to be merged
		return true
	}
	return false
}

func merge2Tries(tr1 *Trie, tr2 *Trie) (*Trie, error) {
	merged, err := mergeNodesRecursive(tr1.RootNode, tr2.RootNode, nil)
	if err != nil {
		root1 := common.Hash{}
		root2 := common.Hash{}
		node1 := "<nil>"
		node2 := "<nil>"
		if tr1 != nil {
			node1 = describeNodeForMerge(tr1.RootNode)
			if tr1.RootNode != nil {
				root1 = common.BytesToHash(tr1.Root())
			}
		}
		if tr2 != nil {
			node2 = describeNodeForMerge(tr2.RootNode)
			if tr2.RootNode != nil {
				root2 = common.BytesToHash(tr2.Root())
			}
		}
		return nil, fmt.Errorf(
			"merge2Tries root1=%x root2=%x node1=%s node2=%s: %w",
			root1,
			root2,
			node1,
			node2,
			err,
		)
	}
	tr1.RootNode = merged
	return tr1, nil
}

// mergeNodesRecursive merges node2 into node1 and returns the merged subtree.
// This fully traverses every conflicting expanded branch instead of following
// only a single path, which is required when partial witness tries overlap in
// multiple siblings at the same depth.
func mergeNodesRecursive(node1 Node, node2 Node, path []byte) (Node, error) {
	if node1 == nil {
		return node2, nil
	}
	if node2 == nil {
		return node1, nil
	}

	hashNode1, ok1 := node1.(*HashNode)
	hashNode2, ok2 := node2.(*HashNode)
	switch {
	case ok1 && ok2:
		if !bytes.Equal(hashNode1.hash, hashNode2.hash) {
			if mergeAllowHashnodeMismatch {
				if mergePreferRhsOnHashnodeMismatch {
					return node2, nil
				}
				return node1, nil
			}
			return nil, fmt.Errorf(
				"children hashnodes have different hashes at path=%s hash1(%x)!=hash2(%x) node1=%s node2=%s",
				formatMergePath(path),
				hashNode1.hash,
				hashNode2.hash,
				describeNodeForMerge(node1),
				describeNodeForMerge(node2),
			)
		}
		return node1, nil
	case ok1 && !ok2:
		return node2, nil
	case !ok1 && ok2:
		return node1, nil
	}

	// Merge-equivalent normalization: unwrap terminal short wrappers so
	// AccountNode/value leaves compare consistently across witness variants.
	node1 = normalizeMergeNode(node1)
	node2 = normalizeMergeNode(node2)

	switch n1 := node1.(type) {
	case *FullNode:
		n2, ok := node2.(*FullNode)
		if !ok {
			if shortNode, shortOk := node2.(*ShortNode); shortOk && (mergeAllowShortFullTypeNormalization || mergeAllowShortKeyDivergence) {
				expanded := expandShortNodeForMerge(shortNode)
				if expanded == nil {
					return n1, nil
				}
				return mergeNodesRecursive(n1, expanded, path)
			}
			if accNode, accOk := node2.(*AccountNode); accOk {
				return mergeAccountWithFullNode(accNode, n1, path)
			}
			return nil, fmt.Errorf(
				"children have different types at path=%s: %T != %T child1=%s child2=%s",
				formatMergePath(path),
				node1,
				node2,
				describeNodeForMerge(node1),
				describeNodeForMerge(node2),
			)
		}
		for i := 0; i < len(n1.Children); i++ {
			mergedChild, err := mergeNodesRecursive(
				n1.Children[i],
				n2.Children[i],
				mergePathAppend(path, byte(i)),
			)
			if err != nil {
				return nil, err
			}
			n1.Children[i] = mergedChild
		}
		return n1, nil

	case *ShortNode:
		n2, ok := node2.(*ShortNode)
		if !ok {
			if fullNode, fullOk := node2.(*FullNode); fullOk && (mergeAllowShortFullTypeNormalization || mergeAllowShortKeyDivergence) {
				expanded := expandShortNodeForMerge(n1)
				if expanded == nil {
					return fullNode, nil
				}
				return mergeNodesRecursive(expanded, fullNode, path)
			}
			return nil, fmt.Errorf(
				"children have different types at path=%s: %T != %T child1=%s child2=%s",
				formatMergePath(path),
				node1,
				node2,
				describeNodeForMerge(node1),
				describeNodeForMerge(node2),
			)
		}
		if !bytes.Equal(n1.Key, n2.Key) {
			if canonical, ok := normalizeShortKeyMismatchForMerge(n1.Key, n2.Key); ok && mergeAllowShortTerminatorMismatch {
				n1.Key = canonical
				n2.Key = append([]byte(nil), canonical...)
			} else if mergeAllowShortKeyDivergence {
				expanded1 := expandShortNodeForMerge(n1)
				expanded2 := expandShortNodeForMerge(n2)
				return mergeNodesRecursive(expanded1, expanded2, path)
			} else {
				return nil, fmt.Errorf(
					"mismatch in the short node keys at path=%s node1.Key(%x)!=node2.Key(%x) node1_val=%s node2_val=%s",
					formatMergePath(path),
					n1.Key,
					n2.Key,
					describeNodeForMerge(n1.Val),
					describeNodeForMerge(n2.Val),
				)
			}
		}

		mergedVal, err := mergeNodesRecursive(
			normalizeMergeNode(n1.Val),
			normalizeMergeNode(n2.Val),
			mergePathAppendKey(path, n1.Key),
		)
		if err != nil {
			return nil, err
		}
		n1.Val = mergedVal
		return n1, nil

	case *AccountNode:
		n2, ok := node2.(*AccountNode)
		if !ok {
			if fullNode, fullOk := node2.(*FullNode); fullOk {
				return mergeAccountWithFullNode(n1, fullNode, path)
			}
			return nil, fmt.Errorf(
				"children have different types at path=%s: %T != %T child1=%s child2=%s",
				formatMergePath(path),
				node1,
				node2,
				describeNodeForMerge(node1),
				describeNodeForMerge(node2),
			)
		}
		storage1 := n1.Storage
		storage2 := n2.Storage
		if storage1 == nil {
			n1.Storage = storage2
			return n1, nil
		}
		if storage2 == nil {
			return n1, nil
		}
		_, storageIsHash1 := storage1.(*HashNode)
		_, storageIsHash2 := storage2.(*HashNode)
		switch {
		case storageIsHash1 && !storageIsHash2:
			n1.Storage = storage2
		case !storageIsHash1 && storageIsHash2:
			// Keep expanded storage in node1.
		case !storageIsHash1 && !storageIsHash2:
			mergedStorage, err := mergeNodesRecursive(
				storage1,
				storage2,
				mergePathAppend(path, 16),
			)
			if err != nil {
				return nil, err
			}
			n1.Storage = mergedStorage
		}
		return n1, nil

	case ValueNode:
		n2, ok := node2.(ValueNode)
		if !ok {
			return nil, fmt.Errorf(
				"children have different types at path=%s: %T != %T child1=%s child2=%s",
				formatMergePath(path),
				node1,
				node2,
				describeNodeForMerge(node1),
				describeNodeForMerge(node2),
			)
		}
		if !bytes.Equal(n1, n2) {
			return nil, fmt.Errorf(
				"value nodes differ at path=%s value1(%x)!=value2(%x)",
				formatMergePath(path),
				[]byte(n1),
				[]byte(n2),
			)
		}
		return n1, nil
	}

	if reflect.TypeOf(node1) != reflect.TypeOf(node2) {
		return nil, fmt.Errorf(
			"children have different types at path=%s: %T != %T child1=%s child2=%s",
			formatMergePath(path),
			node1,
			node2,
			describeNodeForMerge(node1),
			describeNodeForMerge(node2),
		)
	}

	return node1, nil
}
func MergeTries(tries []*Trie) (*Trie, error) {
	if len(tries) == 0 {
		return nil, nil
	}

	if len(tries) == 1 {
		return tries[0], nil
	}

	resultingTrie := tries[0]
	for i := 1; i < len(tries); i++ {
		resultingTrie, err := merge2Tries(resultingTrie, tries[i])
		if err != nil {
			return resultingTrie, err
		}
	}
	return resultingTrie, nil
}

// NewTestRLPTrie treats all the data provided to `Update` function as rlp-encoded.
// it is usually used for testing purposes.
func NewTestRLPTrie(root common.Hash) *Trie {
	trie := &Trie{
		valueNodesRLPEncoded: true,
		newHasherFunc:        func() *hasher { return newHasher( /*valueNodesRlpEncoded = */ true) },
	}
	if (root != common.Hash{}) && root != EmptyRoot {
		trie.RootNode = &HashNode{hash: root[:]}
	}
	return trie
}

func (t *Trie) SetStrictHash(strict bool) {
	t.strictHash = strict
}

// Get returns the value for key stored in the trie.
func (t *Trie) Get(key []byte) (value []byte, gotValue bool) {
	if t.RootNode == nil {
		return nil, true
	}

	hex := keybytesToHex(key)
	return t.get(t.RootNode, hex, 0)
}

func (t *Trie) FindPath(key []byte) (value []byte, parents [][]byte, gotValue bool) {
	if t.RootNode == nil {
		return nil, nil, true
	}

	hex := keybytesToHex(key)
	return t.getPath(t.RootNode, nil, hex, 0)
}

func (t *Trie) GetAccount(key []byte) (value *accounts.Account, gotValue bool) {
	if t.RootNode == nil {
		return nil, true
	}

	hex := keybytesToHex(key)

	accNode, gotValue := t.getAccount(t.RootNode, hex, 0)
	if accNode != nil {
		var value accounts.Account
		value.Copy(&accNode.Account)
		return &value, gotValue
	}
	return nil, gotValue
}

func (t *Trie) GetAccountCode(key []byte) (value []byte, gotValue bool) {
	if t.RootNode == nil {
		return nil, false
	}

	hex := keybytesToHex(key)

	accNode, gotValue := t.getAccount(t.RootNode, hex, 0)
	if accNode != nil {
		if bytes.Equal(accNode.Account.CodeHash[:], emptyCodeHash[:]) {
			return nil, gotValue
		}

		if accNode.Code == nil {
			return nil, false
		}

		return accNode.Code, gotValue
	}
	return nil, gotValue
}

func (t *Trie) GetAccountCodeSize(key []byte) (value int, gotValue bool) {
	if t.RootNode == nil {
		return 0, false
	}

	hex := keybytesToHex(key)

	accNode, gotValue := t.getAccount(t.RootNode, hex, 0)
	if accNode != nil {
		if bytes.Equal(accNode.Account.CodeHash[:], emptyCodeHash[:]) {
			return 0, gotValue
		}

		if accNode.CodeSize == codeSizeUncached {
			return 0, false
		}

		return accNode.CodeSize, gotValue
	}
	return 0, gotValue
}

func (t *Trie) getAccount(origNode Node, key []byte, pos int) (value *AccountNode, gotValue bool) {
	switch n := (origNode).(type) {
	case nil:
		return nil, true
	case *ShortNode:
		matchlen := prefixLen(key[pos:], n.Key)
		if matchlen == len(n.Key) {
			if v, ok := n.Val.(*AccountNode); ok {
				return v, true
			} else {
				return t.getAccount(n.Val, key, pos+matchlen)
			}
		} else {
			return nil, true
		}
	case *DuoNode:
		i1, i2 := n.childrenIdx()
		switch key[pos] {
		case i1:
			return t.getAccount(n.child1, key, pos+1)
		case i2:
			return t.getAccount(n.child2, key, pos+1)
		default:
			return nil, true
		}
	case *FullNode:
		child := n.Children[key[pos]]
		return t.getAccount(child, key, pos+1)
	case *HashNode:
		return nil, false

	case *AccountNode:
		return n, true
	default:
		panic(fmt.Sprintf("%T: invalid node: %v", origNode, origNode))
	}
}

func (t *Trie) get(origNode Node, key []byte, pos int) (value []byte, gotValue bool) {
	switch n := (origNode).(type) {
	case nil:
		return nil, true
	case ValueNode:
		return n, true
	case *AccountNode:
		return t.get(n.Storage, key, pos)
	case *ShortNode:
		matchlen := prefixLen(key[pos:], n.Key)
		if matchlen == len(n.Key) || n.Key[matchlen] == 16 {
			value, gotValue = t.get(n.Val, key, pos+matchlen)
		} else {
			value, gotValue = nil, true
		}
		return
	case *DuoNode:
		i1, i2 := n.childrenIdx()
		switch key[pos] {
		case i1:
			value, gotValue = t.get(n.child1, key, pos+1)
		case i2:
			value, gotValue = t.get(n.child2, key, pos+1)
		default:
			value, gotValue = nil, true
		}
		return
	case *FullNode:
		child := n.Children[key[pos]]
		if child == nil {
			return nil, true
		}
		return t.get(child, key, pos+1)
	case *HashNode:
		return n.hash, false

	default:
		panic(fmt.Sprintf("%T: invalid node: %v", origNode, origNode))
	}
}

func (t *Trie) getPath(origNode Node, parents [][]byte, key []byte, pos int) ([]byte, [][]byte, bool) {
	switch n := (origNode).(type) {
	case nil:
		return nil, parents, true
	case ValueNode:
		return n, parents, true
	case *AccountNode:
		return t.getPath(n.Storage, append(parents, n.reference()), key, pos)
	case *ShortNode:
		matchlen := prefixLen(key[pos:], n.Key)
		if matchlen == len(n.Key) || n.Key[matchlen] == 16 {
			return t.getPath(n.Val, append(parents, n.reference()), key, pos+matchlen)
		} else {
			return nil, parents, true
		}

	case *DuoNode:
		i1, i2 := n.childrenIdx()
		switch key[pos] {
		case i1:
			return t.getPath(n.child1, append(parents, n.reference()), key, pos+1)
		case i2:
			return t.getPath(n.child2, append(parents, n.reference()), key, pos+1)
		default:
			return nil, parents, true
		}
	case *FullNode:
		child := n.Children[key[pos]]
		if child == nil {
			return nil, parents, true
		}
		return t.getPath(child, append(parents, n.reference()), key, pos+1)
	case *HashNode:
		return n.hash, parents, false

	default:
		panic(fmt.Sprintf("%T: invalid node: %v", origNode, origNode))
	}
}

// Update associates key with value in the trie. Subsequent calls to
// Get will return value. If value has length zero, any existing value
// is deleted from the trie and calls to Get will return nil.
//
// The value bytes must not be modified by the caller while they are
// stored in the trie.
// DESCRIBED: docs/programmers_guide/guide.md#root
func (t *Trie) Update(key, value []byte) {
	hex := keybytesToHex(key)

	newnode := ValueNode(value)

	if t.RootNode == nil {
		t.RootNode = NewShortNode(hex, newnode)
	} else {
		_, t.RootNode = t.insert(t.RootNode, hex, ValueNode(value))
	}
}

func (t *Trie) UpdateAccount(key []byte, acc *accounts.Account) {
	//make account copy. There are some pointer into big.Int
	value := new(accounts.Account)
	value.Copy(acc)

	hex := keybytesToHex(key)

	var newnode *AccountNode
	if value.Root == EmptyRoot || value.Root == (common.Hash{}) {
		newnode = &AccountNode{*value, nil, true, nil, codeSizeUncached}
	} else {
		newnode = &AccountNode{*value, HashNode{hash: value.Root[:]}, true, nil, codeSizeUncached}
	}

	if t.RootNode == nil {
		t.RootNode = NewShortNode(hex, newnode)
	} else {
		_, t.RootNode = t.insert(t.RootNode, hex, newnode)
	}
}

// UpdateAccountCode attaches the code node to an account at specified key
func (t *Trie) UpdateAccountCode(key []byte, code CodeNode) error {
	if t.RootNode == nil {
		return nil
	}

	hex := keybytesToHex(key)

	accNode, gotValue := t.getAccount(t.RootNode, hex, 0)
	if accNode == nil || !gotValue {
		return fmt.Errorf("account not found with key: %x", key)
	}

	actualCodeHash := crypto.Keccak256(code)
	if !bytes.Equal(accNode.CodeHash[:], actualCodeHash) {
		return fmt.Errorf("inserted code mismatch account hash (acc.CodeHash=%x codeHash=%x)", accNode.CodeHash[:], actualCodeHash)
	}

	accNode.Code = code
	accNode.CodeSize = len(code)

	// t.insert will call the observer methods itself
	_, t.RootNode = t.insert(t.RootNode, hex, accNode)
	return nil
}

// UpdateAccountCodeSize attaches the code size to the account
func (t *Trie) UpdateAccountCodeSize(key []byte, codeSize int) error {
	if t.RootNode == nil {
		return nil
	}

	hex := keybytesToHex(key)

	accNode, gotValue := t.getAccount(t.RootNode, hex, 0)
	if accNode == nil || !gotValue {
		return fmt.Errorf("account not found with key: %x", key)
	}

	accNode.CodeSize = codeSize

	// t.insert will call the observer methods itself
	_, t.RootNode = t.insert(t.RootNode, hex, accNode)
	return nil
}

// LoadRequestForCode Code expresses the need to fetch code from the DB (by its hash) and attach
// to a specific account leaf in the trie.
type LoadRequestForCode struct {
	t        *Trie
	addrHash common.Hash // contract address hash
	codeHash common.Hash
	bytecode bool // include the bytecode too
}

func (lrc *LoadRequestForCode) String() string {
	return fmt.Sprintf("rr_code{addrHash:%x,codeHash:%x,bytecode:%v}", lrc.addrHash, lrc.codeHash, lrc.bytecode)
}

func (t *Trie) NewLoadRequestForCode(addrHash common.Hash, codeHash common.Hash, bytecode bool) *LoadRequestForCode {
	return &LoadRequestForCode{t, addrHash, codeHash, bytecode}
}

func (t *Trie) NeedLoadCode(addrHash common.Hash, codeHash common.Hash, bytecode bool) (bool, *LoadRequestForCode) {
	if bytes.Equal(codeHash[:], emptyCodeHash[:]) {
		return false, nil
	}

	var ok bool
	if bytecode {
		_, ok = t.GetAccountCode(addrHash[:])
	} else {
		_, ok = t.GetAccountCodeSize(addrHash[:])
	}
	if !ok {
		return true, t.NewLoadRequestForCode(addrHash, codeHash, bytecode)
	}

	return false, nil
}

// FindSubTriesToLoad walks over the trie and creates the list of DB prefixes and
// corresponding list of valid bits in the prefix (for the cases when prefix contains an
// odd number of nibbles) that would allow loading the missing information from the database
// It also create list of `hooks`, the paths in the trie (in nibbles) where the loaded
// sub-tries need to be inserted.
func (t *Trie) FindSubTriesToLoad(rl RetainDecider) (prefixes [][]byte, fixedbits []int, hooks [][]byte) {
	return findSubTriesToLoad(t.RootNode, nil, nil, rl, nil, 0, nil, nil, nil)
}

var bytes8 [8]byte
var bytes16 [16]byte

func findSubTriesToLoad(nd Node, nibblePath []byte, hook []byte, rl RetainDecider, dbPrefix []byte, bits int, prefixes [][]byte, fixedbits []int, hooks [][]byte) (newPrefixes [][]byte, newFixedBits []int, newHooks [][]byte) {
	switch n := nd.(type) {
	case *ShortNode:
		nKey := n.Key
		if nKey[len(nKey)-1] == 16 {
			nKey = nKey[:len(nKey)-1]
		}
		nibblePath = append(nibblePath, nKey...)
		hook = append(hook, nKey...)
		if !rl.Retain(nibblePath) {
			return prefixes, fixedbits, hooks
		}
		for _, b := range nKey {
			if bits%8 == 0 {
				dbPrefix = append(dbPrefix, b<<4)
			} else {
				dbPrefix[len(dbPrefix)-1] &= 0xf0
				dbPrefix[len(dbPrefix)-1] |= b & 0xf
			}
			bits += 4
		}
		return findSubTriesToLoad(n.Val, nibblePath, hook, rl, dbPrefix, bits, prefixes, fixedbits, hooks)
	case *DuoNode:
		i1, i2 := n.childrenIdx()
		newPrefixes = prefixes
		newFixedBits = fixedbits
		newHooks = hooks
		newNibblePath := append(nibblePath, i1)
		newHook := append(hook, i1)
		if rl.Retain(newNibblePath) {
			var newDbPrefix []byte
			if bits%8 == 0 {
				newDbPrefix = append(dbPrefix, i1<<4)
			} else {
				newDbPrefix = dbPrefix
				newDbPrefix[len(newDbPrefix)-1] &= 0xf0
				newDbPrefix[len(newDbPrefix)-1] |= i1 & 0xf
			}
			newPrefixes, newFixedBits, newHooks = findSubTriesToLoad(n.child1, newNibblePath, newHook, rl, newDbPrefix, bits+4, newPrefixes, newFixedBits, newHooks)
		}
		newNibblePath = append(nibblePath, i2)
		newHook = append(hook, i2)
		if rl.Retain(newNibblePath) {
			var newDbPrefix []byte
			if bits%8 == 0 {
				newDbPrefix = append(dbPrefix, i2<<4)
			} else {
				newDbPrefix = dbPrefix
				newDbPrefix[len(newDbPrefix)-1] &= 0xf0
				newDbPrefix[len(newDbPrefix)-1] |= i2 & 0xf
			}
			newPrefixes, newFixedBits, newHooks = findSubTriesToLoad(n.child2, newNibblePath, newHook, rl, newDbPrefix, bits+4, newPrefixes, newFixedBits, newHooks)
		}
		return newPrefixes, newFixedBits, newHooks
	case *FullNode:
		newPrefixes = prefixes
		newFixedBits = fixedbits
		newHooks = hooks
		var newNibblePath []byte
		var newHook []byte
		for i, child := range n.Children {
			if child != nil {
				newNibblePath = append(nibblePath, byte(i))
				newHook = append(hook, byte(i))
				if rl.Retain(newNibblePath) {
					var newDbPrefix []byte
					if bits%8 == 0 {
						newDbPrefix = append(dbPrefix, byte(i)<<4)
					} else {
						newDbPrefix = dbPrefix
						newDbPrefix[len(newDbPrefix)-1] &= 0xf0
						newDbPrefix[len(newDbPrefix)-1] |= byte(i) & 0xf
					}
					newPrefixes, newFixedBits, newHooks = findSubTriesToLoad(child, newNibblePath, newHook, rl, newDbPrefix, bits+4, newPrefixes, newFixedBits, newHooks)
				}
			}
		}
		return newPrefixes, newFixedBits, newHooks
	case *AccountNode:
		if n.Storage == nil {
			return prefixes, fixedbits, hooks
		}
		binary.BigEndian.PutUint64(bytes8[:], n.Incarnation)
		dbPrefix = append(dbPrefix, bytes8[:]...)
		// Add decompressed incarnation to the nibblePath
		for i, b := range bytes8[:] {
			bytes16[i*2] = b / 16
			bytes16[i*2+1] = b % 16
		}
		nibblePath = append(nibblePath, bytes16[:]...)
		newPrefixes = prefixes
		newFixedBits = fixedbits
		newHooks = hooks
		if rl.Retain(nibblePath) {
			newPrefixes, newFixedBits, newHooks = findSubTriesToLoad(n.Storage, nibblePath, hook, rl, dbPrefix, bits+64, prefixes, fixedbits, hooks)
		}
		return newPrefixes, newFixedBits, newHooks
	case *HashNode:
		newPrefixes = append(prefixes, common.Copy(dbPrefix))
		newFixedBits = append(fixedbits, bits)
		newHooks = append(hooks, common.Copy(hook))
		return newPrefixes, newFixedBits, newHooks
	}
	return prefixes, fixedbits, hooks
}

// can pass incarnation=0 if start from root, method internally will
// put incarnation from accountNode when pass it by traverse
func (t *Trie) insert(origNode Node, key []byte, value Node) (updated bool, newNode Node) {
	return t.insertRecursive(origNode, key, 0, value)
}

func (t *Trie) insertRecursive(origNode Node, key []byte, pos int, value Node) (updated bool, newNode Node) {
	if len(key) == pos {
		origN, origNok := origNode.(ValueNode)
		vn, vnok := value.(ValueNode)
		if origNok && vnok {
			updated = !bytes.Equal(origN, vn)
			if updated {
				newNode = value
			} else {
				newNode = origN
			}
			return
		}
		origAccN, origNok := origNode.(*AccountNode)
		vAccN, vnok := value.(*AccountNode)
		if origNok && vnok {
			updated = !origAccN.Equals(&vAccN.Account)
			if updated {
				if !bytes.Equal(origAccN.CodeHash[:], vAccN.CodeHash[:]) {
					origAccN.Code = nil
				} else if vAccN.Code != nil {
					origAccN.Code = vAccN.Code
				}
				origAccN.Account.Copy(&vAccN.Account)
				origAccN.CodeSize = vAccN.CodeSize
				origAccN.RootCorrect = false
			}
			newNode = origAccN
			return
		}

		// replacing nodes except accounts
		if !origNok {
			return true, value
		}
	}

	var nn Node
	switch n := origNode.(type) {
	case nil:
		return true, NewShortNode(common.Copy(key[pos:]), value)
	case *AccountNode:
		updated, nn = t.insertRecursive(n.Storage, key, pos, value)
		if updated {
			n.Storage = nn
			n.RootCorrect = false
		}
		return updated, n
	case *ShortNode:
		matchlen := prefixLen(key[pos:], n.Key)
		// If the whole key matches, keep this short node as is
		// and only update the value.
		if matchlen == len(n.Key) || n.Key[matchlen] == 16 {
			updated, nn = t.insertRecursive(n.Val, key, pos+matchlen, value)
			if updated {
				n.Val = nn
				n.ref.len = 0
			}
			newNode = n
		} else {
			// Otherwise branch out at the index where they differ.
			var c1 Node
			if len(n.Key) == matchlen+1 {
				c1 = n.Val
			} else {
				c1 = NewShortNode(common.Copy(n.Key[matchlen+1:]), n.Val)
			}
			var c2 Node
			if len(key) == pos+matchlen+1 {
				c2 = value
			} else {
				c2 = NewShortNode(common.Copy(key[pos+matchlen+1:]), value)
			}
			branch := &DuoNode{}
			if n.Key[matchlen] < key[pos+matchlen] {
				branch.child1 = c1
				branch.child2 = c2
			} else {
				branch.child1 = c2
				branch.child2 = c1
			}
			branch.mask = (1 << (n.Key[matchlen])) | (1 << (key[pos+matchlen]))

			// Replace this shortNode with the branch if it occurs at index 0.
			if matchlen == 0 {
				newNode = branch // current node leaves the generation, but new node branch joins it
			} else {
				// Otherwise, replace it with a short node leading up to the branch.
				n.Key = common.Copy(key[pos : pos+matchlen])
				n.Val = branch
				n.ref.len = 0
				newNode = n
			}
			updated = true
		}
		return

	case *DuoNode:
		i1, i2 := n.childrenIdx()
		switch key[pos] {
		case i1:
			updated, nn = t.insertRecursive(n.child1, key, pos+1, value)
			if updated {
				n.child1 = nn
				n.ref.len = 0
			}
			newNode = n
		case i2:
			updated, nn = t.insertRecursive(n.child2, key, pos+1, value)
			if updated {
				n.child2 = nn
				n.ref.len = 0
			}
			newNode = n
		default:
			var child Node
			if len(key) == pos+1 {
				child = value
			} else {
				child = NewShortNode(common.Copy(key[pos+1:]), value)
			}
			newnode := &FullNode{}
			newnode.Children[i1] = n.child1
			newnode.Children[i2] = n.child2
			newnode.Children[key[pos]] = child
			updated = true
			// current node leaves the generation but newnode joins it
			newNode = newnode
		}
		return

	case *FullNode:
		child := n.Children[key[pos]]
		if child == nil {
			if len(key) == pos+1 {
				n.Children[key[pos]] = value
			} else {
				n.Children[key[pos]] = NewShortNode(common.Copy(key[pos+1:]), value)
			}
			updated = true
			n.ref.len = 0
		} else {
			updated, nn = t.insertRecursive(child, key, pos+1, value)
			if updated {
				n.Children[key[pos]] = nn
				n.ref.len = 0
			}
		}
		newNode = n
		return
	default:
		panic(fmt.Sprintf("%T: invalid node: %v. Searched by: key=%x, pos=%d", n, n, key, pos))
	}
}

// non-recursive version of get and returns: node and parent node
func (t *Trie) getNode(hex []byte, doTouch bool) (Node, Node, bool, uint64) {
	var nd = t.RootNode
	var parent Node
	pos := 0
	var account bool
	var incarnation uint64
	for pos < len(hex) || account {
		switch n := nd.(type) {
		case nil:
			return nil, nil, false, incarnation
		case *ShortNode:
			matchlen := prefixLen(hex[pos:], n.Key)
			if matchlen == len(n.Key) || n.Key[matchlen] == 16 {
				parent = n
				nd = n.Val
				pos += matchlen
				if _, ok := nd.(*AccountNode); ok {
					account = true
				}
			} else {
				return nil, nil, false, incarnation
			}
		case *DuoNode:
			i1, i2 := n.childrenIdx()
			switch hex[pos] {
			case i1:
				parent = n
				nd = n.child1
				pos++
			case i2:
				parent = n
				nd = n.child2
				pos++
			default:
				return nil, nil, false, incarnation
			}
		case *FullNode:
			child := n.Children[hex[pos]]
			if child == nil {
				return nil, nil, false, incarnation
			}
			parent = n
			nd = child
			pos++
		case *AccountNode:
			parent = n
			nd = n.Storage
			incarnation = n.Incarnation
			account = false
		case ValueNode:
			return nd, parent, true, incarnation
		case HashNode:
			return nd, parent, true, incarnation
		default:
			panic(fmt.Sprintf("Unknown node: %T", n))
		}
	}
	return nd, parent, true, incarnation
}

func (t *Trie) HookSubTries(subTries SubTries, hooks [][]byte) error {
	for i, hookNibbles := range hooks {
		root := subTries.roots[i]
		hash := subTries.Hashes[i]
		if root == nil {
			return fmt.Errorf("root==nil for hook %x", hookNibbles)
		}
		if err := t.hook(hookNibbles, root, hash[:]); err != nil {
			return fmt.Errorf("hook %x: %w", hookNibbles, err)
		}
	}
	return nil
}

func (t *Trie) hook(hex []byte, n Node, hash []byte) error {
	nd, parent, ok, incarnation := t.getNode(hex, true)
	if !ok {
		return nil
	}
	if _, ok := nd.(ValueNode); ok {
		return nil
	}
	if hn, ok := nd.(HashNode); ok {
		if !bytes.Equal(hn.hash, hash) {
			return fmt.Errorf("wrong hash when hooking, expected %s, sub-tree hash %x", hn, hash)
		}
	} else if nd != nil {
		return fmt.Errorf("expected hash node at %x, got %T", hex, nd)
	}

	t.touchAll(n, hex, false, incarnation)
	switch p := parent.(type) {
	case nil:
		t.RootNode = n
	case *ShortNode:
		p.Val = n
	case *DuoNode:
		i1, i2 := p.childrenIdx()
		switch hex[len(hex)-1] {
		case i1:
			p.child1 = n
		case i2:
			p.child2 = n
		}
	case *FullNode:
		idx := hex[len(hex)-1]
		p.Children[idx] = n
	case *AccountNode:
		p.Storage = n
	}
	return nil
}

func (t *Trie) touchAll(n Node, hex []byte, del bool, incarnation uint64) {
	switch n := n.(type) {
	case *ShortNode:
		if _, ok := n.Val.(ValueNode); !ok {
			// Don't need to compute prefix for a leaf
			h := n.Key
			// Remove terminator
			if h[len(h)-1] == 16 {
				h = h[:len(h)-1]
			}
			hexVal := concat(hex, h...)
			t.touchAll(n.Val, hexVal, del, incarnation)
		}
	case *DuoNode:
		i1, i2 := n.childrenIdx()
		hex1 := make([]byte, len(hex)+1)
		copy(hex1, hex)
		hex1[len(hex)] = i1
		hex2 := make([]byte, len(hex)+1)
		copy(hex2, hex)
		hex2[len(hex)] = i2
		t.touchAll(n.child1, hex1, del, incarnation)
		t.touchAll(n.child2, hex2, del, incarnation)
	case *FullNode:
		for i, child := range n.Children {
			if child != nil {
				t.touchAll(child, concat(hex, byte(i)), del, incarnation)
			}
		}
	case *AccountNode:
		if n.Storage != nil {
			t.touchAll(n.Storage, hex, del, n.Incarnation)
		}
	}
}

// Delete removes any existing value for key from the trie.
// DESCRIBED: docs/programmers_guide/guide.md#root
func (t *Trie) Delete(key []byte) {
	hex := keybytesToHex(key)
	_, t.RootNode = t.delete(t.RootNode, hex, false)
}

func (t *Trie) convertToShortNode(child Node, pos uint) Node {
	if pos != 16 {
		// If the remaining entry is a short node, it replaces
		// n and its key gets the missing nibble tacked to the
		// front. This avoids creating an invalid
		// shortNode{..., shortNode{...}}.  Since the entry
		// might not be loaded yet, resolve it just for this
		// check.
		if short, ok := child.(*ShortNode); ok {
			k := make([]byte, len(short.Key)+1)
			k[0] = byte(pos)
			copy(k[1:], short.Key)
			return NewShortNode(k, short.Val)
		}
	}
	// Otherwise, n is replaced by a one-nibble short node
	// containing the child.
	return NewShortNode([]byte{byte(pos)}, child)
}

func (t *Trie) delete(origNode Node, key []byte, preserveAccountNode bool) (updated bool, newNode Node) {
	return t.deleteRecursive(origNode, key, 0, preserveAccountNode, 0)
}

// delete returns the new root of the trie with key deleted.
// It reduces the trie to minimal form by simplifying
// nodes on the way up after deleting recursively.
//
// can pass incarnation=0 if start from root, method internally will
// put incarnation from accountNode when pass it by traverse
func (t *Trie) deleteRecursive(origNode Node, key []byte, keyStart int, preserveAccountNode bool, incarnation uint64) (updated bool, newNode Node) {
	var nn Node
	switch n := origNode.(type) {
	case *ShortNode:
		matchlen := prefixLen(key[keyStart:], n.Key)
		if matchlen == min(len(n.Key), len(key[keyStart:])) || n.Key[matchlen] == 16 || key[keyStart+matchlen] == 16 {
			fullMatch := matchlen == len(key)-keyStart
			removeNodeEntirely := fullMatch
			if preserveAccountNode {
				removeNodeEntirely = len(key) == keyStart || matchlen == len(key[keyStart:])-1
			}

			if removeNodeEntirely {
				updated = true
				touchKey := key[:keyStart+matchlen]
				if touchKey[len(touchKey)-1] == 16 {
					touchKey = touchKey[:len(touchKey)-1]
				}
				t.touchAll(n.Val, touchKey, true, incarnation)
				newNode = nil
			} else {
				// The key is longer than n.Key. Remove the remaining suffix
				// from the subtrie. Child can never be nil here since the
				// subtrie must contain at least two other values with keys
				// longer than n.Key.
				updated, nn = t.deleteRecursive(n.Val, key, keyStart+matchlen, preserveAccountNode, incarnation)
				if !updated {
					newNode = n
				} else {
					if nn == nil {
						newNode = nil
					} else {
						if shortChild, ok := nn.(*ShortNode); ok {
							// Deleting from the subtrie reduced it to another
							// short node. Merge the nodes to avoid creating a
							// shortNode{..., shortNode{...}}. Use concat (which
							// always creates a new slice) instead of append to
							// avoid modifying n.Key since it might be shared with
							// other nodes.
							newNode = NewShortNode(concat(n.Key, shortChild.Key...), shortChild.Val)
						} else {
							n.Val = nn
							newNode = n
							n.ref.len = 0
						}
					}
				}
			}
		} else {
			updated = false
			newNode = n // don't replace n on mismatch
		}
		return

	case *DuoNode:
		i1, i2 := n.childrenIdx()
		switch key[keyStart] {
		case i1:
			updated, nn = t.deleteRecursive(n.child1, key, keyStart+1, preserveAccountNode, incarnation)
			if !updated {
				newNode = n
			} else {
				if nn == nil {
					newNode = t.convertToShortNode(n.child2, uint(i2))
				} else {
					n.child1 = nn
					n.ref.len = 0
					newNode = n
				}
			}
		case i2:
			updated, nn = t.deleteRecursive(n.child2, key, keyStart+1, preserveAccountNode, incarnation)
			if !updated {
				newNode = n
			} else {
				if nn == nil {
					newNode = t.convertToShortNode(n.child1, uint(i1))
				} else {
					n.child2 = nn
					n.ref.len = 0
					newNode = n
				}
			}
		default:
			updated = false
			newNode = n
		}
		return

	case *FullNode:
		child := n.Children[key[keyStart]]
		updated, nn = t.deleteRecursive(child, key, keyStart+1, preserveAccountNode, incarnation)
		if !updated {
			newNode = n
		} else {
			n.Children[key[keyStart]] = nn
			// Check how many non-nil entries are left after deleting and
			// reduce the full node to a short node if only one entry is
			// left. Since n must've contained at least two children
			// before deletion (otherwise it would not be a full node) n
			// can never be reduced to nil.
			//
			// When the loop is done, pos contains the index of the single
			// value that is left in n or -2 if n contains at least two
			// values.
			var pos1, pos2 int
			count := 0
			for i, cld := range n.Children {
				if cld != nil {
					if count == 0 {
						pos1 = i
					}
					if count == 1 {
						pos2 = i
					}
					count++
					if count > 2 {
						break
					}
				}
			}
			if count == 1 {
				newNode = t.convertToShortNode(n.Children[pos1], uint(pos1))
			} else if count == 2 {
				duo := &DuoNode{}
				if pos1 == int(key[keyStart]) {
					duo.child1 = nn
				} else {
					duo.child1 = n.Children[pos1]
				}
				if pos2 == int(key[keyStart]) {
					duo.child2 = nn
				} else {
					duo.child2 = n.Children[pos2]
				}
				duo.mask = (1 << uint(pos1)) | (uint32(1) << uint(pos2))
				newNode = duo
			} else if count > 2 {
				// n still contains at least three values and cannot be reduced.
				n.ref.len = 0
				newNode = n
			}
		}
		return

	case ValueNode:
		updated = true
		newNode = nil
		return

	case *AccountNode:
		if keyStart >= len(key) || key[keyStart] == 16 {
			// Key terminates here
			h := key[:keyStart]
			if h[len(h)-1] == 16 {
				h = h[:len(h)-1]
			}
			if n.Storage != nil {
				// Mark all the storage nodes as deleted
				t.touchAll(n.Storage, h, true, n.Incarnation)
			}
			if preserveAccountNode {
				n.Storage = nil
				n.Code = nil
				n.Root = EmptyRoot
				n.RootCorrect = true
				return true, n
			}

			return true, nil
		}
		updated, nn = t.deleteRecursive(n.Storage, key, keyStart, preserveAccountNode, n.Incarnation)
		if updated {
			n.Storage = nn
			n.RootCorrect = false
		}
		newNode = n
		return

	case nil:
		updated = false
		newNode = nil
		return

	default:
		panic(fmt.Sprintf("%T: invalid node: %v (%v)", n, n, key[:keyStart]))
	}
}

// DeleteSubtree removes any existing value for key from the trie.
// The only difference between Delete and DeleteSubtree is that Delete would delete accountNode too,
// wherewas DeleteSubtree will keep the accountNode, but will make the storage sub-trie empty
func (t *Trie) DeleteSubtree(keyPrefix []byte) {
	hexPrefix := keybytesToHex(keyPrefix)

	_, t.RootNode = t.delete(t.RootNode, hexPrefix, true)

}

func concat(s1 []byte, s2 ...byte) []byte {
	r := make([]byte, len(s1)+len(s2))
	copy(r, s1)
	copy(r[len(s1):], s2)
	return r
}

// Root returns the root hash of the trie.
// Deprecated: use Hash instead.
func (t *Trie) Root() []byte { return t.Hash().Bytes() }

// Hash returns the root hash of the trie. It does not write to the
// database and can be used even if the trie doesn't have one.
// DESCRIBED: docs/programmers_guide/guide.md#root
func (t *Trie) Hash() common.Hash {
	if t == nil || t.RootNode == nil {
		return EmptyRoot
	}

	h := t.getHasher()
	defer returnHasherToPool(h)

	var result common.Hash
	_, _ = h.hash(t.RootNode, true, result[:])

	return result
}

func (t *Trie) Reset() {
	resetRefs(t.RootNode)
}

func (t *Trie) getHasher() *hasher {
	return t.newHasherFunc()
}

// DeepHash returns internal hash of a node reachable by the specified key prefix.
// Note that if the prefix points into the middle of a key for a leaf node or of an extension
// node, it will return the hash of a modified leaf node or extension node, where the
// key prefix is removed from the key.
// First returned value is `true` if the node with the specified prefix is found.
func (t *Trie) DeepHash(keyPrefix []byte) (bool, common.Hash) {
	hexPrefix := keybytesToHex(keyPrefix)
	accNode, gotValue := t.getAccount(t.RootNode, hexPrefix, 0)
	if !gotValue {
		return false, common.Hash{}
	}
	if accNode.RootCorrect {
		return true, accNode.Root
	}
	if accNode.Storage == nil {
		accNode.Root = EmptyRoot
		accNode.RootCorrect = true
	} else {
		h := t.getHasher()
		defer returnHasherToPool(h)
		h.hash(accNode.Storage, true, accNode.Root[:])
	}
	return true, accNode.Root
}

func (t *Trie) EvictNode(hex []byte) {
	isCode := IsPointingToCode(hex)
	if isCode {
		hex = AddrHashFromCodeKey(hex)
	}

	nd, parent, ok, incarnation := t.getNode(hex, false)
	if !ok {
		return
	}
	if accNode, ok := parent.(*AccountNode); isCode && ok {
		// add special treatment to code nodes
		accNode.Code = nil
		return
	}

	switch nd.(type) {
	case ValueNode, *HashNode:
		return
	default:
		// can work with other nodes type
	}

	var hn common.Hash
	if nd == nil {
		fmt.Printf("nd == nil, hex %x, parent node: %T\n", hex, parent)
		return
	}
	copy(hn[:], nd.reference())
	hnode := &HashNode{hash: hn[:]}

	t.notifyUnloadRecursive(hex, incarnation, nd)

	switch p := parent.(type) {
	case nil:
		t.RootNode = hnode
	case *ShortNode:
		p.Val = hnode
	case *DuoNode:
		i1, i2 := p.childrenIdx()
		switch hex[len(hex)-1] {
		case i1:
			p.child1 = hnode
		case i2:
			p.child2 = hnode
		}
	case *FullNode:
		idx := hex[len(hex)-1]
		p.Children[idx] = hnode
	case *AccountNode:
		p.Storage = hnode
	}
}

func (t *Trie) notifyUnloadRecursive(hex []byte, incarnation uint64, nd Node) {
	switch n := nd.(type) {
	case *ShortNode:
		hex = append(hex, n.Key...)
		if hex[len(hex)-1] == 16 {
			hex = hex[:len(hex)-1]
		}
		t.notifyUnloadRecursive(hex, incarnation, n.Val)
	case *AccountNode:
		if n.Storage == nil {
			return
		}
		if _, ok := n.Storage.(*HashNode); ok {
			return
		}
		t.notifyUnloadRecursive(hex, n.Incarnation, n.Storage)
	case *FullNode:
		for i := range n.Children {
			if n.Children[i] == nil {
				continue
			}
			if _, ok := n.Children[i].(*HashNode); ok {
				continue
			}
			t.notifyUnloadRecursive(append(hex, uint8(i)), incarnation, n.Children[i])
		}
	case *DuoNode:
		i1, i2 := n.childrenIdx()
		if n.child1 != nil {
			t.notifyUnloadRecursive(append(hex, i1), incarnation, n.child1)
		}
		if n.child2 != nil {
			t.notifyUnloadRecursive(append(hex, i2), incarnation, n.child2)
		}
	default:
		// nothing to do
	}
}

func (t *Trie) TrieSize() int {
	return calcSubtreeSize(t.RootNode)
}

func (t *Trie) NumberOfAccounts() int {
	return calcSubtreeNodes(t.RootNode)
}
