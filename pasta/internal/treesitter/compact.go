package treesitter

import (
	"encoding/binary"
	"errors"
	"fmt"
	"sync"
)

// Compact is a parse tree encoded in a few bytes per node, against
// about 200 for the Go node graph. Tree.Compact encodes a tree, and
// Compact.Tree rebuilds it much faster than parsing the source again.
//
// The encoding names kinds and fields by string, not by grammar symbol
// ID, so it doesn't depend on the parser that produced it. After a
// version byte and the node count, it holds the tree's kind names and
// field names, each a count followed by length-prefixed strings. Then
// each node, in preorder, is five varints: its kind index; its field
// index shifted left 5 bits and ORed with its flags; its start minus
// the previous node's start; its length; and its depth minus the
// previous node's depth.
type Compact []byte

const compactVersion = 1

const flagBits = 5

// Compact encodes t.
func (t *Tree) Compact() Compact {
	kinds := map[string]uint64{}
	fields := map[string]uint64{"": 0}
	var kindNames, fieldNames []string
	fieldNames = append(fieldNames, "")
	body := make([]byte, 0, 6*t.nodes)
	type frame struct {
		n     *node
		depth int64
	}
	stack := []frame{{t.root, 0}}
	var prevStart, prevDepth int64
	for len(stack) > 0 {
		f := stack[len(stack)-1]
		stack = stack[:len(stack)-1]
		n := f.n
		k, ok := kinds[n.kind]
		if !ok {
			k = uint64(len(kindNames))
			kinds[n.kind] = k
			kindNames = append(kindNames, n.kind)
		}
		fi, ok := fields[n.fieldName]
		if !ok {
			fi = uint64(len(fieldNames))
			fields[n.fieldName] = fi
			fieldNames = append(fieldNames, n.fieldName)
		}
		body = binary.AppendUvarint(body, k)
		body = binary.AppendUvarint(body, fi<<flagBits|uint64(n.flags()))
		body = binary.AppendVarint(body, int64(n.start)-prevStart)
		body = binary.AppendUvarint(body, uint64(n.end-n.start))
		body = binary.AppendVarint(body, f.depth-prevDepth)
		prevStart, prevDepth = int64(n.start), f.depth
		for i := len(n.children) - 1; i >= 0; i-- {
			stack = append(stack, frame{n.children[i], f.depth + 1})
		}
	}
	out := make([]byte, 0, len(body)+16*(len(kindNames)+len(fieldNames)))
	out = append(out, compactVersion)
	out = binary.AppendUvarint(out, uint64(t.nodes))
	for _, names := range [][]string{kindNames, fieldNames} {
		out = binary.AppendUvarint(out, uint64(len(names)))
		for _, s := range names {
			out = binary.AppendUvarint(out, uint64(len(s)))
			out = append(out, s...)
		}
	}
	return append(out, body...)
}

var errCompact = errors.New("malformed compact tree")

// Tree rebuilds the tree that c encodes. src, fileID, and lang must be
// those of the tree that was encoded.
func (c Compact) Tree(lang *Language, src []byte, fileID string) (*Tree, error) {
	r := compactReader{b: c}
	if v := r.byte(); v != compactVersion {
		return nil, fmt.Errorf("%w: version %d", errCompact, v)
	}
	n := r.uvarint()
	if r.err == nil && (n == 0 || n > uint64(len(c))) {
		r.err = errCompact
	}
	kinds := r.names()
	fields := r.names()
	if r.err != nil {
		return nil, r.err
	}
	nodes := make([]node, n)
	depths := make([]uint32, n)
	var start, depth int64
	for i := range nodes {
		k := r.uvarint()
		ff := r.uvarint()
		start += r.varint()
		length := r.uvarint()
		depth += r.varint()
		fi := ff >> flagBits
		if r.err != nil || k >= uint64(len(kinds)) || fi >= uint64(len(fields)) ||
			start < 0 || uint64(start)+length > uint64(len(src)) || depth < 0 || (i > 0 && depth == 0) {
			return nil, fmt.Errorf("%w: node %d", errCompact, i)
		}
		nodes[i] = node{
			kind:      kinds[k],
			start:     uint32(start),
			end:       uint32(uint64(start) + length),
			fieldName: fields[fi],
		}
		nodes[i].setFlags(byte(ff & (1<<flagBits - 1)))
		depths[i] = uint32(depth)
	}
	if len(r.b) != 0 || depths[0] != 0 {
		return nil, errCompact
	}
	return &Tree{root: link(nodes, depths), nodes: int(n), src: src, fileID: fileID, lang: lang}, nil
}

// compactReader reads varints from b and records the first error.
type compactReader struct {
	b   []byte
	err error
}

func (r *compactReader) byte() byte {
	if len(r.b) == 0 {
		r.err = errCompact
		return 0
	}
	v := r.b[0]
	r.b = r.b[1:]
	return v
}

func (r *compactReader) uvarint() uint64 {
	v, k := binary.Uvarint(r.b)
	if k <= 0 {
		r.err = errCompact
		r.b = nil
		return 0
	}
	r.b = r.b[k:]
	return v
}

func (r *compactReader) varint() int64 {
	v, k := binary.Varint(r.b)
	if k <= 0 {
		r.err = errCompact
		r.b = nil
		return 0
	}
	r.b = r.b[k:]
	return v
}

func (r *compactReader) names() []string {
	count := r.uvarint()
	if r.err != nil || count > uint64(len(r.b)) {
		r.err = errCompact
		return nil
	}
	names := make([]string, count)
	for i := range names {
		l := r.uvarint()
		if r.err != nil || l > uint64(len(r.b)) {
			r.err = errCompact
			return nil
		}
		names[i] = intern(r.b[:l])
		r.b = r.b[l:]
	}
	return names
}

// internedNames holds every kind and field name that Compact.Tree has
// decoded. Grammars have a bounded set of them, so rebuilt trees share
// one copy of each name instead of allocating it per tree.
var internedNames = struct {
	sync.RWMutex
	m map[string]string
}{m: map[string]string{}}

func intern(b []byte) string {
	internedNames.RLock()
	s, ok := internedNames.m[string(b)]
	internedNames.RUnlock()
	if ok {
		return s
	}
	internedNames.Lock()
	defer internedNames.Unlock()
	if s, ok := internedNames.m[string(b)]; ok {
		return s
	}
	s = string(b)
	internedNames.m[s] = s
	return s
}
