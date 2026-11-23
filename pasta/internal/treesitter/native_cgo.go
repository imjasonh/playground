//go:build cgo && !purego

package treesitter

/*
#cgo CFLAGS: -I${SRCDIR}/csrc -I${SRCDIR}/csrc/vendor/tree-sitter/lib/include -I${SRCDIR}/csrc/vendor/tree-sitter/lib/src
#include "lib.c"
#include "host_extra.c"
*/
import "C"

import (
	"context"
	"fmt"
	"sync/atomic"
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

// sql, dockerfile, and lean have no usable Go module, so they parse with wasm.
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

type cgoBackend struct {
	langs map[string]*C.TSLanguage
}

func (b *cgoBackend) has(grammar string) bool { return b.langs[grammar] != nil }

func names(grammar string, l *C.TSLanguage) grammarNames {
	return namesFor(grammar,
		uint32(C.ts_language_symbol_count(l)),
		uint32(C.ts_language_field_count(l)),
		func(id uint32) string { return C.GoString(C.ts_language_symbol_name(l, C.TSSymbol(id))) },
		func(id uint32) string { return C.GoString(C.ts_language_field_name_for_id(l, C.TSFieldId(id))) })
}

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
	csrc := (*C.char)(unsafe.Pointer(unsafe.SliceData(src)))
	tree := C.pasta_parse(p, csrc, C.uint32_t(len(src)), C.uint64_t(opts.timeoutMicros()), cancel)
	if err := ctx.Err(); err != nil {
		if tree != nil {
			C.ts_tree_delete(tree)
		}
		return treeDump{}, err
	}
	if tree == nil {
		return treeDump{}, opts.nullTreeErr()
	}
	defer C.ts_tree_delete(tree)

	d := treeDump{grammarNames: names(grammar, l)}
	d.n = uint32(C.ts_dump_tree(tree, nil, 0))
	if d.n == 0 {
		return d, nil
	}
	d.raw = make([]byte, int(d.n)*recSize)
	if got := uint32(C.ts_dump_tree(tree, (*C.NodeRec)(unsafe.Pointer(&d.raw[0])), C.uint32_t(d.n))); got != d.n {
		return treeDump{}, fmt.Errorf("dump count changed: %d vs %d", d.n, got)
	}
	return d, nil
}
