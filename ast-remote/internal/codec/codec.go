// Package codec encodes source files as compact tree-sitter-derived payloads
// and rehydrates the original bytes on decode.
//
// A full AST dump is usually *larger* than the source: every intermediate node
// adds type/field metadata while leaf texts still contain every token. The
// representation that can actually compete with gzip is a **leaf stream**:
// walk the tree-sitter tree in order, intern leaf texts and the trivia gaps
// between them into a string table, and drop the interior nodes. That is still
// "AST-first" (the leaf order and token boundaries come from the parse), but
// it only stores what rehydration needs.
//
// EncodeFile therefore emits the smaller of (leaf-stream+gzip) and gzip(raw).
package codec

import (
	"bytes"
	"compress/gzip"
	"encoding/binary"
	"errors"
	"fmt"
	"io"

	sitter "github.com/smacker/go-tree-sitter"

	"github.com/imjasonh/playground/ast-remote/internal/langs"
)

const (
	magic   = "AST1"
	version = 1

	flagLossless = 1 << 0
	modeLeaves   = 1 // leaf stream + trivia (default, compact)
	modeFullTree = 2 // full flattened tree (usually larger; for experiments)
)

// Encoding names stored in the object store metadata.
const (
	EncodingRaw     = "raw"
	EncodingASTGzip = "ast-gzip" // AST1 leaf-stream (or full tree) + gzip
)

// Result is the outcome of encoding one blob.
type Result struct {
	Encoding      string // EncodingASTGzip or EncodingRaw
	Payload       []byte
	Lang          string
	RawSize       int
	PayloadSize   int
	GzipRawSize   int // gzip(source) for comparison
	LeafASTSize   int // gzip(leaf-stream) before adaptive choice
	FullASTSize   int // gzip(full-tree), 0 if not computed
	StringCount   int
	NodeCount     int // leaves for leaf-mode; all nodes for full-tree
	Mode          string
	SkippedReason string
}

// EncodeOptions controls experimental variants.
type EncodeOptions struct {
	// PreferFullTree stores the full flattened tree instead of the leaf stream.
	// Almost always larger; useful for benchmarks.
	PreferFullTree bool
	// AlsoMeasureFullTree computes FullASTSize even when storing leaves.
	AlsoMeasureFullTree bool
	// NoAdaptive disables "pick min(ast, gzip)" and always stores the AST form
	// when parsing succeeds.
	NoAdaptive bool
}

// EncodeFile losslessly encodes source for path using default options.
func EncodeFile(path string, source []byte) (*Result, error) {
	return EncodeFileOpts(path, source, EncodeOptions{})
}

// EncodeFileOpts is EncodeFile with explicit options.
func EncodeFileOpts(path string, source []byte, opts EncodeOptions) (*Result, error) {
	gzipRaw, err := gzipBytes(source)
	if err != nil {
		return nil, err
	}
	base := &Result{
		RawSize:     len(source),
		GzipRawSize: len(gzipRaw),
	}

	lang := langs.FromPath(path)
	if lang == nil {
		base.Encoding = EncodingRaw
		base.Payload = gzipRaw
		base.PayloadSize = len(gzipRaw)
		base.SkippedReason = "unsupported extension"
		return base, nil
	}

	leafPayload, leafStrs, leafCount, err := encodeLeaves(lang, source)
	if err != nil {
		base.Encoding = EncodingRaw
		base.Payload = gzipRaw
		base.PayloadSize = len(gzipRaw)
		base.Lang = lang.Name
		base.SkippedReason = err.Error()
		return base, nil
	}
	leafGZ, err := gzipBytes(leafPayload)
	if err != nil {
		return nil, err
	}
	base.LeafASTSize = len(leafGZ)
	base.Lang = lang.Name

	var fullGZ []byte
	var fullStrs, fullNodes int
	if opts.PreferFullTree || opts.AlsoMeasureFullTree {
		fullPayload, fs, fn, err := encodeFullTree(lang, source)
		if err != nil {
			return nil, err
		}
		fullGZ, err = gzipBytes(fullPayload)
		if err != nil {
			return nil, err
		}
		base.FullASTSize = len(fullGZ)
		fullStrs, fullNodes = fs, fn
	}

	useFull := opts.PreferFullTree
	var chosen []byte
	var mode string
	var strs, nodes int
	if useFull {
		chosen, mode, strs, nodes = fullGZ, "full-tree", fullStrs, fullNodes
	} else {
		chosen, mode, strs, nodes = leafGZ, "leaves", leafStrs, leafCount
	}

	if !opts.NoAdaptive && len(gzipRaw) <= len(chosen) {
		base.Encoding = EncodingRaw
		base.Payload = gzipRaw
		base.PayloadSize = len(gzipRaw)
		base.Mode = mode
		base.StringCount = strs
		base.NodeCount = nodes
		base.SkippedReason = fmt.Sprintf("gzip smaller than %s AST (%d ≤ %d)", mode, len(gzipRaw), len(chosen))
		return base, nil
	}

	base.Encoding = EncodingASTGzip
	base.Payload = chosen
	base.PayloadSize = len(chosen)
	base.Mode = mode
	base.StringCount = strs
	base.NodeCount = nodes
	return base, nil
}

// Decode rehydrates original source bytes from an encoded payload.
func Decode(encoding string, payload []byte) ([]byte, error) {
	switch encoding {
	case EncodingRaw, "":
		return gunzipBytes(payload)
	case EncodingASTGzip:
		raw, err := gunzipBytes(payload)
		if err != nil {
			return nil, err
		}
		return decodeAST(raw)
	default:
		return nil, fmt.Errorf("unknown encoding %q", encoding)
	}
}

func encodeLeaves(lang *langs.Language, source []byte) ([]byte, int, int, error) {
	root, err := parseRoot(lang, source)
	if err != nil {
		return nil, 0, 0, err
	}
	st := newStringTable()
	langID := st.Intern(lang.Name)

	var leaves []*sitter.Node
	var walk func(n *sitter.Node)
	walk = func(n *sitter.Node) {
		if n.ChildCount() == 0 {
			leaves = append(leaves, n)
			return
		}
		for i := 0; i < int(n.ChildCount()); i++ {
			if ch := n.Child(i); ch != nil {
				walk(ch)
			}
		}
	}
	walk(root)

	leafIDs := make([]uint32, len(leaves))
	gaps := make([]uint32, 0, len(leaves)+1)
	var prevEnd uint32
	for i, ln := range leaves {
		start, end := ln.StartByte(), ln.EndByte()
		gaps = append(gaps, st.InternBytes(source[prevEnd:start]))
		leafIDs[i] = st.InternBytes(source[start:end])
		prevEnd = end
	}
	gaps = append(gaps, st.InternBytes(source[prevEnd:]))

	var buf bytes.Buffer
	buf.WriteString(magic)
	buf.WriteByte(version)
	buf.WriteByte(flagLossless)
	buf.WriteByte(modeLeaves)
	_ = binary.Write(&buf, binary.BigEndian, langID)
	writeStringTable(&buf, st)
	_ = binary.Write(&buf, binary.BigEndian, uint32(len(leafIDs)))
	for _, id := range leafIDs {
		_ = binary.Write(&buf, binary.BigEndian, id)
	}
	_ = binary.Write(&buf, binary.BigEndian, uint32(len(gaps)))
	for _, g := range gaps {
		_ = binary.Write(&buf, binary.BigEndian, g)
	}
	return buf.Bytes(), st.Len(), len(leafIDs), nil
}

func encodeFullTree(lang *langs.Language, source []byte) ([]byte, int, int, error) {
	root, err := parseRoot(lang, source)
	if err != nil {
		return nil, 0, 0, err
	}
	st := newStringTable()
	langID := st.Intern(lang.Name)

	type flatNode struct {
		typeID   uint32
		fieldID  uint32
		isLeaf   bool
		content  uint32
		nChild   uint32
		children []uint32
	}
	nodes := make([]flatNode, 0, 256)
	var walk func(n *sitter.Node, fieldName string) uint32
	walk = func(n *sitter.Node, fieldName string) uint32 {
		idx := uint32(len(nodes))
		nodes = append(nodes, flatNode{})
		fn := flatNode{
			typeID:  st.Intern(n.Type()),
			fieldID: st.Intern(fieldName),
		}
		childCount := int(n.ChildCount())
		if childCount == 0 {
			fn.isLeaf = true
			fn.content = st.InternBytes(source[n.StartByte():n.EndByte()])
		} else {
			fn.children = make([]uint32, 0, childCount)
			for i := 0; i < childCount; i++ {
				ch := n.Child(i)
				if ch == nil {
					continue
				}
				fn.children = append(fn.children, walk(ch, n.FieldNameForChild(i)))
			}
			fn.nChild = uint32(len(fn.children))
		}
		nodes[idx] = fn
		return idx
	}
	_ = walk(root, "")

	var sitterLeaves []*sitter.Node
	var walkLeaves func(n *sitter.Node)
	walkLeaves = func(n *sitter.Node) {
		if n.ChildCount() == 0 {
			sitterLeaves = append(sitterLeaves, n)
			return
		}
		for i := 0; i < int(n.ChildCount()); i++ {
			if ch := n.Child(i); ch != nil {
				walkLeaves(ch)
			}
		}
	}
	walkLeaves(root)

	gaps := make([]uint32, 0, len(sitterLeaves)+1)
	var prevEnd uint32
	for _, ln := range sitterLeaves {
		start, end := ln.StartByte(), ln.EndByte()
		gaps = append(gaps, st.InternBytes(source[prevEnd:start]))
		prevEnd = end
	}
	gaps = append(gaps, st.InternBytes(source[prevEnd:]))

	var buf bytes.Buffer
	buf.WriteString(magic)
	buf.WriteByte(version)
	buf.WriteByte(flagLossless)
	buf.WriteByte(modeFullTree)
	_ = binary.Write(&buf, binary.BigEndian, langID)
	writeStringTable(&buf, st)
	_ = binary.Write(&buf, binary.BigEndian, uint32(len(nodes)))
	for _, n := range nodes {
		_ = binary.Write(&buf, binary.BigEndian, n.typeID)
		_ = binary.Write(&buf, binary.BigEndian, n.fieldID)
		if n.isLeaf {
			buf.WriteByte(1)
			_ = binary.Write(&buf, binary.BigEndian, n.content)
		} else {
			buf.WriteByte(0)
			_ = binary.Write(&buf, binary.BigEndian, n.nChild)
			for _, c := range n.children {
				_ = binary.Write(&buf, binary.BigEndian, c)
			}
		}
	}
	_ = binary.Write(&buf, binary.BigEndian, uint32(len(gaps)))
	for _, g := range gaps {
		_ = binary.Write(&buf, binary.BigEndian, g)
	}
	return buf.Bytes(), st.Len(), len(nodes), nil
}

func parseRoot(lang *langs.Language, source []byte) (*sitter.Node, error) {
	parser := sitter.NewParser()
	parser.SetLanguage(lang.Sitter())
	tree := parser.Parse(nil, source)
	if tree == nil {
		return nil, errors.New("parse returned nil tree")
	}
	root := tree.RootNode()
	if root == nil {
		return nil, errors.New("nil root")
	}
	if root.HasError() {
		return nil, errors.New("parse tree has errors")
	}
	return root, nil
}

func writeStringTable(buf *bytes.Buffer, st *stringTable) {
	_ = binary.Write(buf, binary.BigEndian, uint32(st.Len()))
	for _, s := range st.All() {
		_ = binary.Write(buf, binary.BigEndian, uint32(len(s)))
		buf.Write(s)
	}
}

func decodeAST(payload []byte) ([]byte, error) {
	r := bytes.NewReader(payload)
	mag := make([]byte, 4)
	if _, err := io.ReadFull(r, mag); err != nil {
		return nil, err
	}
	if string(mag) != magic {
		return nil, fmt.Errorf("bad magic %q", mag)
	}
	ver, err := r.ReadByte()
	if err != nil {
		return nil, err
	}
	if ver != version {
		return nil, fmt.Errorf("unsupported version %d", ver)
	}
	flags, err := r.ReadByte()
	if err != nil {
		return nil, err
	}
	if flags&flagLossless == 0 {
		return nil, errors.New("non-lossless payloads are not supported")
	}
	mode, err := r.ReadByte()
	if err != nil {
		return nil, err
	}
	var langID uint32
	if err := binary.Read(r, binary.BigEndian, &langID); err != nil {
		return nil, err
	}
	strings, err := readStringTable(r)
	if err != nil {
		return nil, err
	}
	get := func(id uint32) ([]byte, error) {
		if int(id) >= len(strings) {
			return nil, fmt.Errorf("string id %d out of range", id)
		}
		return strings[id], nil
	}
	if _, err := get(langID); err != nil {
		return nil, err
	}

	switch mode {
	case modeLeaves:
		return decodeLeaves(r, get)
	case modeFullTree:
		return decodeFullTree(r, get)
	default:
		return nil, fmt.Errorf("unknown AST mode %d", mode)
	}
}

func readStringTable(r *bytes.Reader) ([][]byte, error) {
	var strCount uint32
	if err := binary.Read(r, binary.BigEndian, &strCount); err != nil {
		return nil, err
	}
	strings := make([][]byte, strCount)
	for i := uint32(0); i < strCount; i++ {
		var n uint32
		if err := binary.Read(r, binary.BigEndian, &n); err != nil {
			return nil, err
		}
		b := make([]byte, n)
		if _, err := io.ReadFull(r, b); err != nil {
			return nil, err
		}
		strings[i] = b
	}
	return strings, nil
}

func decodeLeaves(r *bytes.Reader, get func(uint32) ([]byte, error)) ([]byte, error) {
	var leafCount uint32
	if err := binary.Read(r, binary.BigEndian, &leafCount); err != nil {
		return nil, err
	}
	leafIDs := make([]uint32, leafCount)
	for i := uint32(0); i < leafCount; i++ {
		if err := binary.Read(r, binary.BigEndian, &leafIDs[i]); err != nil {
			return nil, err
		}
	}
	var gapCount uint32
	if err := binary.Read(r, binary.BigEndian, &gapCount); err != nil {
		return nil, err
	}
	if gapCount != leafCount+1 {
		return nil, fmt.Errorf("gap/leaf mismatch: %d gaps, %d leaves", gapCount, leafCount)
	}
	gaps := make([]uint32, gapCount)
	for i := uint32(0); i < gapCount; i++ {
		if err := binary.Read(r, binary.BigEndian, &gaps[i]); err != nil {
			return nil, err
		}
	}
	var out bytes.Buffer
	for i, id := range leafIDs {
		g, err := get(gaps[i])
		if err != nil {
			return nil, err
		}
		out.Write(g)
		c, err := get(id)
		if err != nil {
			return nil, err
		}
		out.Write(c)
	}
	g, err := get(gaps[leafCount])
	if err != nil {
		return nil, err
	}
	out.Write(g)
	return out.Bytes(), nil
}

func decodeFullTree(r *bytes.Reader, get func(uint32) ([]byte, error)) ([]byte, error) {
	type flatNode struct {
		isLeaf   bool
		content  uint32
		children []uint32
	}
	var nodeCount uint32
	if err := binary.Read(r, binary.BigEndian, &nodeCount); err != nil {
		return nil, err
	}
	nodes := make([]flatNode, nodeCount)
	for i := uint32(0); i < nodeCount; i++ {
		var typeID, fieldID uint32
		if err := binary.Read(r, binary.BigEndian, &typeID); err != nil {
			return nil, err
		}
		if err := binary.Read(r, binary.BigEndian, &fieldID); err != nil {
			return nil, err
		}
		_, _ = typeID, fieldID
		kind, err := r.ReadByte()
		if err != nil {
			return nil, err
		}
		if kind == 1 {
			var content uint32
			if err := binary.Read(r, binary.BigEndian, &content); err != nil {
				return nil, err
			}
			nodes[i] = flatNode{isLeaf: true, content: content}
		} else {
			var nChild uint32
			if err := binary.Read(r, binary.BigEndian, &nChild); err != nil {
				return nil, err
			}
			ch := make([]uint32, nChild)
			for j := uint32(0); j < nChild; j++ {
				if err := binary.Read(r, binary.BigEndian, &ch[j]); err != nil {
					return nil, err
				}
			}
			nodes[i] = flatNode{children: ch}
		}
	}
	var gapCount uint32
	if err := binary.Read(r, binary.BigEndian, &gapCount); err != nil {
		return nil, err
	}
	gaps := make([]uint32, gapCount)
	for i := uint32(0); i < gapCount; i++ {
		if err := binary.Read(r, binary.BigEndian, &gaps[i]); err != nil {
			return nil, err
		}
	}
	var leafContents []uint32
	var walk func(idx uint32)
	walk = func(idx uint32) {
		n := nodes[idx]
		if n.isLeaf {
			leafContents = append(leafContents, n.content)
			return
		}
		for _, c := range n.children {
			walk(c)
		}
	}
	if nodeCount == 0 {
		return nil, errors.New("empty node table")
	}
	walk(0)
	if uint32(len(leafContents)+1) != gapCount {
		return nil, fmt.Errorf("gap/leaf mismatch: %d gaps, %d leaves", gapCount, len(leafContents))
	}
	var out bytes.Buffer
	for i, contentID := range leafContents {
		g, err := get(gaps[i])
		if err != nil {
			return nil, err
		}
		out.Write(g)
		c, err := get(contentID)
		if err != nil {
			return nil, err
		}
		out.Write(c)
	}
	g, err := get(gaps[len(leafContents)])
	if err != nil {
		return nil, err
	}
	out.Write(g)
	return out.Bytes(), nil
}

type stringTable struct {
	index map[string]uint32
	all   [][]byte
}

func newStringTable() *stringTable {
	st := &stringTable{index: make(map[string]uint32)}
	st.Intern("")
	return st
}

func (st *stringTable) Intern(s string) uint32 {
	if id, ok := st.index[s]; ok {
		return id
	}
	id := uint32(len(st.all))
	st.all = append(st.all, []byte(s))
	st.index[s] = id
	return id
}

func (st *stringTable) InternBytes(b []byte) uint32 {
	return st.Intern(string(b))
}

func (st *stringTable) Len() int      { return len(st.all) }
func (st *stringTable) All() [][]byte { return st.all }

func gzipBytes(b []byte) ([]byte, error) {
	var buf bytes.Buffer
	w := gzip.NewWriter(&buf)
	if _, err := w.Write(b); err != nil {
		return nil, err
	}
	if err := w.Close(); err != nil {
		return nil, err
	}
	return buf.Bytes(), nil
}

func gunzipBytes(b []byte) ([]byte, error) {
	r, err := gzip.NewReader(bytes.NewReader(b))
	if err != nil {
		return nil, err
	}
	defer r.Close()
	return io.ReadAll(r)
}
