// Package codec encodes source files as compact tree-sitter-derived payloads
// and rehydrates the original bytes on decode.
//
// Iteration history (sizes vs gzip(raw) on gitdb/):
//
//	AST1 leaf stream + string table + gzip     ~158%
//	AST2 interleaved atoms (V3) + gzip         ~123%
//	AST2 in-place atom substitution + gzip     ~100%
//	AST2 subst (compact frame) + raw flate     ~98.5%
//	raw + fixed language zlib dictionary       ~95–97%
//
// EncodeFile adaptively stores the smallest of those candidates (plus optional
// full-tree for experiments) so the remote never loses to plain gzip on size.
package codec

import (
	"bytes"
	"compress/flate"
	"compress/gzip"
	"encoding/binary"
	"errors"
	"fmt"
	"io"

	sitter "github.com/smacker/go-tree-sitter"

	"github.com/imjasonh/playground/ast-remote/internal/langs"
)

const (
	magicAST1 = "AST1"
	magicAST2 = "AST2"
	version1  = 1
	version2  = 1

	flagLossless = 1 << 0
	modeLeaves   = 1 // AST1 leaf stream + trivia
	modeFullTree = 2 // AST1 full flattened tree

	// AST2 body kinds
	ast2Subst = 12 // in-place multi-byte atom substitution
)

// Encoding names stored in the object store metadata.
const (
	EncodingRaw     = "raw"      // gzip(source)
	EncodingRawDict = "raw-dict" // flate(source, langDict)
	EncodingASTGzip = "ast-gzip" // AST2 subst (or AST1) + flate/gzip
	EncodingASTDict = "ast-dict" // AST2 subst + flate(langDict)

	magicFlate = "FLA1" // prefix for raw-flate-wrapped AST payloads
)

// Result is the outcome of encoding one blob.
type Result struct {
	Encoding      string
	Payload       []byte
	Lang          string
	RawSize       int
	PayloadSize   int
	GzipRawSize   int // gzip(source) baseline (BestCompression)
	LeafASTSize   int // AST2 subst+gzip (primary AST candidate)
	FullASTSize   int // gzip(full-tree), 0 if not computed
	RawDictSize   int // flate(raw, langDict), 0 if no dict
	ASTDictSize   int // flate(subst, langDict), 0 if no dict
	StringCount   int // AST1 string table size; 0 for AST2
	NodeCount     int // leaf count
	Mode          string
	SkippedReason string
}

// EncodeOptions controls experimental variants.
type EncodeOptions struct {
	// PreferFullTree stores the AST1 full flattened tree (usually larger).
	PreferFullTree bool
	// AlsoMeasureFullTree computes FullASTSize even when not storing it.
	AlsoMeasureFullTree bool
	// NoAdaptive disables picking the min candidate and always stores AST
	// (subst+gzip, or full-tree when PreferFullTree).
	NoAdaptive bool
	// PreferLeaves forces the legacy AST1 leaf-stream packing (for comparison).
	PreferLeaves bool
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
	base.Lang = lang.Name

	if opts.PreferFullTree || opts.PreferLeaves {
		return encodeLegacy(lang, source, gzipRaw, base, opts)
	}

	substPayload, leafCount, err := encodeSubst(lang, source)
	if err != nil {
		base.Encoding = EncodingRaw
		base.Payload = gzipRaw
		base.PayloadSize = len(gzipRaw)
		base.SkippedReason = err.Error()
		return base, nil
	}
	substFlate, err := wrapFlate(substPayload)
	if err != nil {
		return nil, err
	}
	base.LeafASTSize = len(substFlate)
	base.NodeCount = leafCount
	base.Mode = "subst"

	dict := dictForLang(lang.Name)
	var rawDict, astDict []byte
	if len(dict) > 0 {
		rawBody, err := flateDictBytes(source, dict)
		if err != nil {
			return nil, err
		}
		astBody, err := flateDictBytes(substPayload, dict)
		if err != nil {
			return nil, err
		}
		rawDict = wrapDictPayload(lang.Name, rawBody)
		astDict = wrapDictPayload(lang.Name, astBody)
		base.RawDictSize = len(rawDict)
		base.ASTDictSize = len(astDict)
	}

	if opts.AlsoMeasureFullTree {
		fullPayload, _, fn, err := encodeFullTree(lang, source)
		if err != nil {
			return nil, err
		}
		fullGZ, err := gzipBytes(fullPayload)
		if err != nil {
			return nil, err
		}
		base.FullASTSize = len(fullGZ)
		_ = fn
	}

	type cand struct {
		enc  string
		mode string
		pay  []byte
	}
	cands := []cand{
		{EncodingASTGzip, "subst", substFlate},
	}
	if len(rawDict) > 0 {
		cands = append(cands, cand{EncodingRawDict, "raw-dict", rawDict})
	}
	if len(astDict) > 0 {
		cands = append(cands, cand{EncodingASTDict, "ast-dict", astDict})
	}

	if opts.NoAdaptive {
		chosen := cands[0]
		base.Encoding = chosen.enc
		base.Payload = chosen.pay
		base.PayloadSize = len(chosen.pay)
		base.Mode = chosen.mode
		return base, nil
	}

	best := cand{EncodingRaw, "raw", gzipRaw}
	for _, c := range cands {
		if len(c.pay) < len(best.pay) {
			best = c
		}
	}
	base.Encoding = best.enc
	base.Payload = best.pay
	base.PayloadSize = len(best.pay)
	base.Mode = best.mode
	if best.enc == EncodingRaw {
		base.SkippedReason = fmt.Sprintf("gzip smaller than AST candidates (%d)", len(gzipRaw))
	}
	return base, nil
}

func encodeLegacy(lang *langs.Language, source, gzipRaw []byte, base *Result, opts EncodeOptions) (*Result, error) {
	if opts.PreferFullTree {
		fullPayload, strs, nodes, err := encodeFullTree(lang, source)
		if err != nil {
			base.Encoding = EncodingRaw
			base.Payload = gzipRaw
			base.PayloadSize = len(gzipRaw)
			base.SkippedReason = err.Error()
			return base, nil
		}
		fullGZ, err := gzipBytes(fullPayload)
		if err != nil {
			return nil, err
		}
		base.FullASTSize = len(fullGZ)
		base.LeafASTSize = len(fullGZ)
		base.StringCount = strs
		base.NodeCount = nodes
		base.Mode = "full-tree"
		if !opts.NoAdaptive && len(gzipRaw) <= len(fullGZ) {
			base.Encoding = EncodingRaw
			base.Payload = gzipRaw
			base.PayloadSize = len(gzipRaw)
			base.SkippedReason = fmt.Sprintf("gzip smaller than full-tree (%d ≤ %d)", len(gzipRaw), len(fullGZ))
			return base, nil
		}
		base.Encoding = EncodingASTGzip
		base.Payload = fullGZ
		base.PayloadSize = len(fullGZ)
		return base, nil
	}

	// PreferLeaves: AST1 leaf stream
	leafPayload, strs, nodes, err := encodeLeaves(lang, source)
	if err != nil {
		base.Encoding = EncodingRaw
		base.Payload = gzipRaw
		base.PayloadSize = len(gzipRaw)
		base.SkippedReason = err.Error()
		return base, nil
	}
	leafGZ, err := gzipBytes(leafPayload)
	if err != nil {
		return nil, err
	}
	base.LeafASTSize = len(leafGZ)
	base.StringCount = strs
	base.NodeCount = nodes
	base.Mode = "leaves"
	if opts.AlsoMeasureFullTree {
		fullPayload, _, _, err := encodeFullTree(lang, source)
		if err == nil {
			if fullGZ, err := gzipBytes(fullPayload); err == nil {
				base.FullASTSize = len(fullGZ)
			}
		}
	}
	if !opts.NoAdaptive && len(gzipRaw) <= len(leafGZ) {
		base.Encoding = EncodingRaw
		base.Payload = gzipRaw
		base.PayloadSize = len(gzipRaw)
		base.SkippedReason = fmt.Sprintf("gzip smaller than leaves (%d ≤ %d)", len(gzipRaw), len(leafGZ))
		return base, nil
	}
	base.Encoding = EncodingASTGzip
	base.Payload = leafGZ
	base.PayloadSize = len(leafGZ)
	return base, nil
}

// Decode rehydrates original source bytes from an encoded payload.
func Decode(encoding string, payload []byte) ([]byte, error) {
	switch encoding {
	case EncodingRaw, "":
		return gunzipBytes(payload)
	case EncodingRawDict:
		return decodeRawDict(payload)
	case EncodingASTGzip:
		raw, err := unwrapCompressed(payload)
		if err != nil {
			return nil, err
		}
		return decodeAST(raw)
	case EncodingASTDict:
		raw, err := inflateDictPayload(payload)
		if err != nil {
			return nil, err
		}
		return decodeAST(raw)
	default:
		return nil, fmt.Errorf("unknown encoding %q", encoding)
	}
}

// encodeSubst builds an AST2 in-place atom-substitution payload.
// Multi-byte keywords/operators/idents (len>=3) become 0x01 + atomID; other
// bytes stay as-is (0x01 in source is escaped as 0x01 0x01). The result is
// near-source bytes with shorter repeated tokens — typically slightly under
// gzip(raw) once wrapped in raw flate.
func encodeSubst(lang *langs.Language, source []byte) ([]byte, int, error) {
	root, err := parseRoot(lang, source)
	if err != nil {
		return nil, 0, err
	}
	leaves := collectLeafNodes(root)
	atoms := atomsForLang(lang.Name)

	var body bytes.Buffer
	pos := 0
	for _, n := range leaves {
		writeEscaped(&body, source[pos:n.StartByte()])
		text := string(source[n.StartByte():n.EndByte()])
		if id, ok := atoms[text]; ok && len(text) >= 3 {
			body.WriteByte(atomEscape)
			body.WriteByte(id)
		} else {
			writeEscaped(&body, []byte(text))
		}
		pos = int(n.EndByte())
	}
	writeEscaped(&body, source[pos:])

	// Compact header: AST2 | ver | kind | u8(langLen) | lang | body
	// (drops srcLen; length is implicit after atom expansion)
	if len(lang.Name) > 255 {
		return nil, 0, fmt.Errorf("language name too long: %q", lang.Name)
	}
	var buf bytes.Buffer
	buf.WriteString(magicAST2)
	buf.WriteByte(version2)
	buf.WriteByte(ast2Subst)
	buf.WriteByte(byte(len(lang.Name)))
	buf.WriteString(lang.Name)
	buf.Write(body.Bytes())
	return buf.Bytes(), len(leaves), nil
}

func writeEscaped(b *bytes.Buffer, data []byte) {
	for _, c := range data {
		if c == atomEscape {
			b.WriteByte(atomEscape)
			b.WriteByte(atomEscape)
		} else {
			b.WriteByte(c)
		}
	}
}

func collectLeafNodes(root *sitter.Node) []*sitter.Node {
	var leaves []*sitter.Node
	var walk func(*sitter.Node)
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
	return leaves
}

func encodeLeaves(lang *langs.Language, source []byte) ([]byte, int, int, error) {
	root, err := parseRoot(lang, source)
	if err != nil {
		return nil, 0, 0, err
	}
	st := newStringTable()
	langID := st.Intern(lang.Name)

	leaves := collectLeafNodes(root)
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
	buf.WriteString(magicAST1)
	buf.WriteByte(version1)
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

	sitterLeaves := collectLeafNodes(root)
	gaps := make([]uint32, 0, len(sitterLeaves)+1)
	var prevEnd uint32
	for _, ln := range sitterLeaves {
		start, end := ln.StartByte(), ln.EndByte()
		gaps = append(gaps, st.InternBytes(source[prevEnd:start]))
		prevEnd = end
	}
	gaps = append(gaps, st.InternBytes(source[prevEnd:]))

	var buf bytes.Buffer
	buf.WriteString(magicAST1)
	buf.WriteByte(version1)
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

func writeUvarint(buf *bytes.Buffer, x uint64) {
	var tmp [binary.MaxVarintLen64]byte
	n := binary.PutUvarint(tmp[:], x)
	buf.Write(tmp[:n])
}

func decodeAST(payload []byte) ([]byte, error) {
	if len(payload) < 4 {
		return nil, errors.New("payload too short")
	}
	switch string(payload[:4]) {
	case magicAST2:
		return decodeAST2(payload)
	case magicAST1:
		return decodeAST1(payload)
	default:
		return nil, fmt.Errorf("bad magic %q", payload[:4])
	}
}

func decodeAST2(payload []byte) ([]byte, error) {
	r := bytes.NewReader(payload)
	mag := make([]byte, 4)
	if _, err := io.ReadFull(r, mag); err != nil {
		return nil, err
	}
	ver, err := r.ReadByte()
	if err != nil {
		return nil, err
	}
	if ver != version2 {
		return nil, fmt.Errorf("unsupported AST2 version %d", ver)
	}
	kind, err := r.ReadByte()
	if err != nil {
		return nil, err
	}
	if kind != ast2Subst {
		return nil, fmt.Errorf("unknown AST2 kind %d", kind)
	}
	langLen, err := r.ReadByte()
	if err != nil {
		return nil, err
	}
	langBuf := make([]byte, langLen)
	if _, err := io.ReadFull(r, langBuf); err != nil {
		return nil, err
	}
	langName := string(langBuf)
	body, err := io.ReadAll(r)
	if err != nil {
		return nil, err
	}
	byID := atomByID(langName)
	var out bytes.Buffer
	out.Grow(len(body) + len(body)/4)
	for i := 0; i < len(body); i++ {
		if body[i] != atomEscape {
			out.WriteByte(body[i])
			continue
		}
		i++
		if i >= len(body) {
			return nil, errors.New("truncated escape")
		}
		if body[i] == atomEscape {
			out.WriteByte(atomEscape)
			continue
		}
		s, ok := byID[body[i]]
		if !ok {
			return nil, fmt.Errorf("unknown atom id %d for %s", body[i], langName)
		}
		out.WriteString(s)
	}
	return out.Bytes(), nil
}

func decodeAST1(payload []byte) ([]byte, error) {
	r := bytes.NewReader(payload)
	mag := make([]byte, 4)
	if _, err := io.ReadFull(r, mag); err != nil {
		return nil, err
	}
	ver, err := r.ReadByte()
	if err != nil {
		return nil, err
	}
	if ver != version1 {
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

// raw-dict / ast-dict wire format: "DICT" + uvarint(langLen) + lang + flate bytes.
// The language selects the fixed dictionary on both sides.
const magicDict = "DICT"

func flateDictBytes(data, dict []byte) ([]byte, error) {
	var body bytes.Buffer
	w, err := flate.NewWriterDict(&body, flate.BestCompression, dict)
	if err != nil {
		return nil, err
	}
	if _, err := w.Write(data); err != nil {
		return nil, err
	}
	if err := w.Close(); err != nil {
		return nil, err
	}
	return body.Bytes(), nil
}

func wrapDictPayload(lang string, flateBody []byte) []byte {
	var buf bytes.Buffer
	buf.WriteString(magicDict)
	writeUvarint(&buf, uint64(len(lang)))
	buf.WriteString(lang)
	buf.Write(flateBody)
	return buf.Bytes()
}

func decodeRawDict(payload []byte) ([]byte, error) {
	lang, body, err := splitDictPayload(payload)
	if err != nil {
		return nil, err
	}
	dict := dictForLang(lang)
	if len(dict) == 0 {
		return nil, fmt.Errorf("no dictionary for language %q", lang)
	}
	r := flate.NewReaderDict(bytes.NewReader(body), dict)
	defer r.Close()
	return io.ReadAll(r)
}

func inflateDictPayload(payload []byte) ([]byte, error) {
	lang, body, err := splitDictPayload(payload)
	if err != nil {
		return nil, err
	}
	dict := dictForLang(lang)
	if len(dict) == 0 {
		return nil, fmt.Errorf("no dictionary for language %q", lang)
	}
	r := flate.NewReaderDict(bytes.NewReader(body), dict)
	defer r.Close()
	return io.ReadAll(r)
}

func splitDictPayload(payload []byte) (lang string, body []byte, err error) {
	if len(payload) < 4 || string(payload[:4]) != magicDict {
		return "", nil, fmt.Errorf("bad dict magic")
	}
	r := bytes.NewReader(payload[4:])
	n, err := binary.ReadUvarint(r)
	if err != nil {
		return "", nil, err
	}
	lb := make([]byte, n)
	if _, err := io.ReadFull(r, lb); err != nil {
		return "", nil, err
	}
	rest, err := io.ReadAll(r)
	return string(lb), rest, err
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
	w, err := gzip.NewWriterLevel(&buf, gzip.BestCompression)
	if err != nil {
		return nil, err
	}
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

func wrapFlate(data []byte) ([]byte, error) {
	var body bytes.Buffer
	w, err := flate.NewWriter(&body, flate.BestCompression)
	if err != nil {
		return nil, err
	}
	if _, err := w.Write(data); err != nil {
		return nil, err
	}
	if err := w.Close(); err != nil {
		return nil, err
	}
	out := make([]byte, 0, 4+body.Len())
	out = append(out, magicFlate...)
	out = append(out, body.Bytes()...)
	return out, nil
}

func unwrapCompressed(payload []byte) ([]byte, error) {
	if len(payload) >= 4 && string(payload[:4]) == magicFlate {
		r := flate.NewReader(bytes.NewReader(payload[4:]))
		defer r.Close()
		return io.ReadAll(r)
	}
	// Legacy AST1/AST2 payloads were gzip-wrapped.
	return gunzipBytes(payload)
}
