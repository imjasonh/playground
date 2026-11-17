//go:build cgo && !purego

package tswasm

/*
#cgo CFLAGS: -I${SRCDIR}/csrc -I${SRCDIR}/csrc/vendor/tree-sitter/lib/include -I${SRCDIR}/csrc/vendor/tree-sitter/lib/src
#include "lib.c"
#include "host_extra.c"
*/
import "C"

import (
	"context"
	"fmt"
	"runtime/debug"
	"strings"
	"sync"
	"sync/atomic"
	"time"
	"unsafe"

	tsswift "github.com/alex-pinkus/tree-sitter-swift/bindings/go"
	tshcl "github.com/tree-sitter-grammars/tree-sitter-hcl/bindings/go"
	tstoml "github.com/tree-sitter-grammars/tree-sitter-toml/bindings/go"
	tsyaml "github.com/tree-sitter-grammars/tree-sitter-yaml/bindings/go"
	tsbash "github.com/tree-sitter/tree-sitter-bash/bindings/go"
	tsc "github.com/tree-sitter/tree-sitter-c/bindings/go"
	tscpp "github.com/tree-sitter/tree-sitter-cpp/bindings/go"
	tscss "github.com/tree-sitter/tree-sitter-css/bindings/go"
	tsgo "github.com/tree-sitter/tree-sitter-go/bindings/go"
	tshtml "github.com/tree-sitter/tree-sitter-html/bindings/go"
	tsjava "github.com/tree-sitter/tree-sitter-java/bindings/go"
	tsjavascript "github.com/tree-sitter/tree-sitter-javascript/bindings/go"
	tsjson "github.com/tree-sitter/tree-sitter-json/bindings/go"
	tsphp "github.com/tree-sitter/tree-sitter-php/bindings/go"
	tspython "github.com/tree-sitter/tree-sitter-python/bindings/go"
	tsruby "github.com/tree-sitter/tree-sitter-ruby/bindings/go"
	tsrust "github.com/tree-sitter/tree-sitter-rust/bindings/go"
	tstypescript "github.com/tree-sitter/tree-sitter-typescript/bindings/go"
)

// Each grammar module must stay at the version build.sh compiles into
// the wasm module, so both backends build the same trees;
// scripts/pin-grammars.sh sets them. sql and dockerfile publish no
// usable Go module, so they parse with wasm.
func init() {
	native = &cgoBackend{langs: map[string]*C.TSLanguage{
		"go":         language(tsgo.Language()),
		"python":     language(tspython.Language()),
		"rust":       language(tsrust.Language()),
		"javascript": language(tsjavascript.Language()),
		"typescript": language(tstypescript.LanguageTypescript()),
		"tsx":        language(tstypescript.LanguageTSX()),
		"yaml":       language(tsyaml.Language()),
		"bash":       language(tsbash.Language()),
		"json":       language(tsjson.Language()),
		"c":          language(tsc.Language()),
		"cpp":        language(tscpp.Language()),
		"css":        language(tscss.Language()),
		"html":       language(tshtml.Language()),
		"java":       language(tsjava.Language()),
		"php":        language(tsphp.LanguagePHP()),
		"ruby":       language(tsruby.Language()),
		"swift":      language(tsswift.Language()),
		"toml":       language(tstoml.Language()),
		"hcl":        language(tshcl.Language()),
	}}
}

func language(p unsafe.Pointer) *C.TSLanguage { return (*C.TSLanguage)(p) }

// cgoBackend parses with tree-sitter and the grammars compiled into the
// binary.
type cgoBackend struct {
	langs map[string]*C.TSLanguage
	names sync.Map // grammar → [2]map[uint32]string{kinds, fields}
}

func (b *cgoBackend) has(grammar string) bool { return b.langs[grammar] != nil }

// id names the grammar module versions, so trees cached by a binary
// with other grammars aren't reused.
func (b *cgoBackend) id() string {
	var sb strings.Builder
	sb.WriteString("cgo\n")
	if bi, ok := debug.ReadBuildInfo(); ok {
		for _, m := range bi.Deps {
			if strings.Contains(m.Path, "/tree-sitter-") {
				fmt.Fprintf(&sb, "%s %s\n", m.Path, m.Version)
			}
		}
	}
	return sb.String()
}

func (b *cgoBackend) nameMaps(grammar string, l *C.TSLanguage) (kinds, fields map[uint32]string) {
	if v, ok := b.names.Load(grammar); ok {
		m := v.([2]map[uint32]string)
		return m[0], m[1]
	}
	count := uint32(C.ts_language_symbol_count(l))
	kinds = make(map[uint32]string, count)
	for id := range count {
		kinds[id] = C.GoString(C.ts_language_symbol_name(l, C.TSSymbol(id)))
	}
	// Field ids are 1-based; id 0 means "no field".
	nf := uint32(C.ts_language_field_count(l))
	fields = make(map[uint32]string, nf+1)
	fields[0] = ""
	for id := uint32(1); id <= nf; id++ {
		fields[id] = C.GoString(C.ts_language_field_name_for_id(l, C.TSFieldId(id)))
	}
	b.names.Store(grammar, [2]map[uint32]string{kinds, fields})
	return kinds, fields
}

var emptySrc = []byte{0}

func (b *cgoBackend) parseDump(ctx context.Context, grammar string, src []byte, opts ParseOptions) (treeDump, error) {
	l := b.langs[grammar]
	if l == nil {
		return treeDump{}, fmt.Errorf("unknown grammar %q", grammar)
	}
	p := C.ts_parser_new()
	defer C.ts_parser_delete(p)
	if !C.ts_parser_set_language(p, l) {
		return treeDump{}, fmt.Errorf("grammar %q: incompatible language ABI", grammar)
	}

	var cancel *C.int32_t
	var flag int32
	if ctx.Done() != nil {
		cancel = (*C.int32_t)(unsafe.Pointer(&flag))
		stop := context.AfterFunc(ctx, func() { atomic.StoreInt32(&flag, 1) })
		defer stop()
	}
	var micros C.uint64_t
	if opts.Timeout > 0 {
		micros = C.uint64_t(max(opts.Timeout/time.Microsecond, 1))
	}
	s := src
	if len(s) == 0 {
		s = emptySrc
	}
	tree := C.pasta_parse(p, (*C.char)(unsafe.Pointer(&s[0])), C.uint32_t(len(src)), micros, cancel)
	if err := ctx.Err(); err != nil {
		if tree != nil {
			C.ts_tree_delete(tree)
		}
		return treeDump{}, err
	}
	if tree == nil {
		if opts.Timeout > 0 {
			return treeDump{}, fmt.Errorf("%w: null tree", ErrTimeout)
		}
		return treeDump{}, fmt.Errorf("parse returned null tree")
	}
	defer C.ts_tree_delete(tree)

	kinds, fields := b.nameMaps(grammar, l)
	n := uint32(C.ts_dump_tree(tree, nil, 0))
	if n == 0 {
		return treeDump{kinds: kinds, fields: fields}, nil
	}
	raw := make([]byte, int(n)*recSize)
	if got := uint32(C.ts_dump_tree(tree, (*C.NodeRec)(unsafe.Pointer(&raw[0])), C.uint32_t(n))); got != n {
		return treeDump{}, fmt.Errorf("dump count changed: %d vs %d", n, got)
	}
	return treeDump{raw: raw, n: n, kinds: kinds, fields: fields}, nil
}
