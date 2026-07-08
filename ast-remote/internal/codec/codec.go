// Package codec encodes source files with a tree-sitter-derived protocol and
// rehydrates the original bytes on decode.
//
// The protocol walks the parse tree's leaves and substitutes known multi-byte
// tokens (keywords, operators, common idents) with 2-byte atoms, preserving
// layout so deflate still sees source-like structure. EncodeFile then stores
// the smallest of:
//
//   - protocol payload + raw flate
//   - raw source + fixed language zlib dictionary
//   - protocol payload + language dictionary
//   - gzip(source)
//
// On typical Go trees this lands at ~96–98% of plain gzip; adaptive choice
// never stores worse than gzip.
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
	// Wire magic for an uncompressed protocol payload (before flate wrapping).
	magicProto = "ASTR"
	protoVer   = 1

	// Compressed wrappers.
	magicFlate = "FLA1" // raw flate of a protocol payload
	magicDict  = "DICT" // flate with a fixed language dictionary
)

// Encoding names stored in the object store metadata.
const (
	EncodingRaw     = "raw"      // gzip(source)
	EncodingRawDict = "raw-dict" // flate(source, langDict)
	EncodingAST     = "ast"      // protocol + raw flate
	EncodingASTDict = "ast-dict" // protocol + flate(langDict)
)

// Result is the outcome of encoding one blob.
type Result struct {
	Encoding      string
	Payload       []byte
	Lang          string
	RawSize       int
	PayloadSize   int
	GzipRawSize   int // gzip(source) baseline (BestCompression)
	ASTSize       int // protocol + flate
	RawDictSize   int // flate(raw, langDict), 0 if no dict
	ASTDictSize   int // flate(protocol, langDict), 0 if no dict
	NodeCount     int // leaf count
	Mode          string
	SkippedReason string
}

// EncodeOptions controls encode behavior.
type EncodeOptions struct {
	// NoAdaptive disables picking the min candidate and always stores the
	// protocol+flate form when parsing succeeds.
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
	base.Lang = lang.Name

	proto, leafCount, err := encodeProtocol(lang, source)
	if err != nil {
		base.Encoding = EncodingRaw
		base.Payload = gzipRaw
		base.PayloadSize = len(gzipRaw)
		base.SkippedReason = err.Error()
		return base, nil
	}
	astFlate, err := wrapFlate(proto)
	if err != nil {
		return nil, err
	}
	base.ASTSize = len(astFlate)
	base.NodeCount = leafCount
	base.Mode = "subst"

	dict := dictForLang(lang.Name)
	var rawDict, astDict []byte
	if len(dict) > 0 {
		rawBody, err := flateDictBytes(source, dict)
		if err != nil {
			return nil, err
		}
		astBody, err := flateDictBytes(proto, dict)
		if err != nil {
			return nil, err
		}
		rawDict = wrapDictPayload(lang.Name, rawBody)
		astDict = wrapDictPayload(lang.Name, astBody)
		base.RawDictSize = len(rawDict)
		base.ASTDictSize = len(astDict)
	}

	type cand struct {
		enc  string
		mode string
		pay  []byte
	}
	cands := []cand{{EncodingAST, "subst", astFlate}}
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
		base.SkippedReason = fmt.Sprintf("gzip smaller than protocol candidates (%d)", len(gzipRaw))
	}
	return base, nil
}

// Decode rehydrates original source bytes from an encoded payload.
func Decode(encoding string, payload []byte) ([]byte, error) {
	switch encoding {
	case EncodingRaw, "":
		return gunzipBytes(payload)
	case EncodingRawDict:
		return decodeDictRaw(payload)
	case EncodingAST:
		raw, err := unwrapFlate(payload)
		if err != nil {
			return nil, err
		}
		return decodeProtocol(raw)
	case EncodingASTDict:
		raw, err := inflateDictPayload(payload)
		if err != nil {
			return nil, err
		}
		return decodeProtocol(raw)
	default:
		return nil, fmt.Errorf("unknown encoding %q", encoding)
	}
}

// encodeProtocol builds the uncompressed protocol payload: in-place atom
// substitution of multi-byte tokens (len>=3), with 0x01 escaped as 0x01 0x01.
func encodeProtocol(lang *langs.Language, source []byte) ([]byte, int, error) {
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

	if len(lang.Name) > 255 {
		return nil, 0, fmt.Errorf("language name too long: %q", lang.Name)
	}
	var buf bytes.Buffer
	buf.WriteString(magicProto)
	buf.WriteByte(protoVer)
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

func writeUvarint(buf *bytes.Buffer, x uint64) {
	var tmp [binary.MaxVarintLen64]byte
	n := binary.PutUvarint(tmp[:], x)
	buf.Write(tmp[:n])
}

func decodeProtocol(payload []byte) ([]byte, error) {
	if len(payload) < 6 {
		return nil, errors.New("payload too short")
	}
	if string(payload[:4]) != magicProto {
		return nil, fmt.Errorf("bad magic %q", payload[:4])
	}
	r := bytes.NewReader(payload)
	mag := make([]byte, 4)
	if _, err := io.ReadFull(r, mag); err != nil {
		return nil, err
	}
	ver, err := r.ReadByte()
	if err != nil {
		return nil, err
	}
	if ver != protoVer {
		return nil, fmt.Errorf("unsupported protocol version %d", ver)
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

func decodeDictRaw(payload []byte) ([]byte, error) {
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

func unwrapFlate(payload []byte) ([]byte, error) {
	if len(payload) < 4 || string(payload[:4]) != magicFlate {
		return nil, fmt.Errorf("bad flate magic")
	}
	r := flate.NewReader(bytes.NewReader(payload[4:]))
	defer r.Close()
	return io.ReadAll(r)
}
