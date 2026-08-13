package lang

import "github.com/imjasonh/playground/pasta/internal/tswasm"

// Grammars maps grammar names (referenced from language CUE) to a
// constructor for the WASM tree-sitter language handle. Adding a new
// alias for a grammar already compiled into ts-core.wasm is a CUE
// change. Adding a brand-new grammar means rebuilding the WASM module
// (internal/tswasm/build.sh) and registering it here.
//
// Only grammars embedded in internal/tswasm/ts-core.wasm.br are
// available; see that package's build.sh for the pin list.
var Grammars = map[string]func() *tswasm.Language{
	"go":         lang("go"),
	"python":     lang("python"),
	"rust":       lang("rust"),
	"javascript": lang("javascript"),
	"typescript": lang("typescript"),
	"tsx":        lang("tsx"),
	"yaml":       lang("yaml"),
	"bash":       lang("bash"),
	"json":       lang("json"),
	"c":          lang("c"),
	"cpp":        lang("cpp"),
	"css":        lang("css"),
	"dockerfile": lang("dockerfile"),
	"html":       lang("html"),
	"java":       lang("java"),
	"php":        lang("php"),
	"ruby":       lang("ruby"),
	"sql":        lang("sql"),
	"swift":      lang("swift"),
}

func lang(grammar string) func() *tswasm.Language {
	return func() *tswasm.Language {
		return &tswasm.Language{Grammar: grammar}
	}
}

// grammarNames returns the registered names for error messages.
func grammarNames() []string {
	out := make([]string, 0, len(Grammars))
	for k := range Grammars {
		out = append(out, k)
	}
	return out
}
