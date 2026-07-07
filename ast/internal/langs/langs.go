// Package langs is a registry that maps human language names and file
// extensions to the tree-sitter grammars bundled with go-tree-sitter.
//
// Every grammar is compiled into the binary via cgo (there are no runtime
// downloads or external parser processes), so a single `ast` binary can parse
// every language listed here.
package langs

import (
	"embed"
	"fmt"
	"path"
	"path/filepath"
	"sort"
	"strings"

	sitter "github.com/smacker/go-tree-sitter"
	"github.com/smacker/go-tree-sitter/bash"
	"github.com/smacker/go-tree-sitter/c"
	"github.com/smacker/go-tree-sitter/cpp"
	"github.com/smacker/go-tree-sitter/csharp"
	"github.com/smacker/go-tree-sitter/css"
	"github.com/smacker/go-tree-sitter/cue"
	"github.com/smacker/go-tree-sitter/dockerfile"
	"github.com/smacker/go-tree-sitter/elixir"
	"github.com/smacker/go-tree-sitter/elm"
	"github.com/smacker/go-tree-sitter/golang"
	"github.com/smacker/go-tree-sitter/groovy"
	"github.com/smacker/go-tree-sitter/hcl"
	"github.com/smacker/go-tree-sitter/html"
	"github.com/smacker/go-tree-sitter/java"
	"github.com/smacker/go-tree-sitter/javascript"
	"github.com/smacker/go-tree-sitter/kotlin"
	"github.com/smacker/go-tree-sitter/lua"
	"github.com/smacker/go-tree-sitter/ocaml"
	"github.com/smacker/go-tree-sitter/php"
	"github.com/smacker/go-tree-sitter/protobuf"
	"github.com/smacker/go-tree-sitter/python"
	"github.com/smacker/go-tree-sitter/ruby"
	"github.com/smacker/go-tree-sitter/rust"
	"github.com/smacker/go-tree-sitter/scala"
	"github.com/smacker/go-tree-sitter/sql"
	"github.com/smacker/go-tree-sitter/svelte"
	"github.com/smacker/go-tree-sitter/swift"
	"github.com/smacker/go-tree-sitter/toml"
	"github.com/smacker/go-tree-sitter/typescript/tsx"
	"github.com/smacker/go-tree-sitter/typescript/typescript"
	"github.com/smacker/go-tree-sitter/yaml"
)

// Language pairs a canonical name with a lazily-loaded tree-sitter grammar and
// the file extensions that map to it.
type Language struct {
	Name       string
	Extensions []string
	getLang    func() *sitter.Language

	aliases []string
}

// Sitter returns the compiled tree-sitter grammar for the language.
func (l *Language) Sitter() *sitter.Language { return l.getLang() }

// Aliases returns the alternate names that also resolve to this language.
func (l *Language) Aliases() []string {
	return append([]string(nil), l.aliases...)
}

// queryFS holds the curated tree-sitter query files (tags/highlights/locals)
// that power the normalized `--kind` selectors and scope-aware rename. The
// bundled grammars ship only parsers, not queries, so these are maintained
// in-tree under queries/<lang>/<kind>.scm.
//
//go:embed queries
var queryFS embed.FS

// queryAlias maps a language to another whose query files it reuses (the tsx
// grammar shares TypeScript's node types for the constructs we query).
var queryAlias = map[string]string{"tsx": "typescript"}

// QueryKinds are the supported curated query files.
const (
	QueryTags       = "tags"
	QueryHighlights = "highlights"
	QueryLocals     = "locals"
)

// LoadQuery returns the embedded query source of the given kind
// ("tags"/"highlights"/"locals") for this language, or false if none is
// curated for it.
func (l *Language) LoadQuery(kind string) (string, bool) {
	name := l.Name
	if a, ok := queryAlias[name]; ok {
		name = a
	}
	b, err := queryFS.ReadFile(path.Join("queries", name, kind+".scm"))
	if err != nil {
		return "", false
	}
	return string(b), true
}

// HasQueries reports whether curated queries (needed for --kind and rename)
// exist for this language.
func (l *Language) HasQueries() bool {
	_, ok := l.LoadQuery(QueryLocals)
	return ok
}

// registry is the full set of supported languages. Extensions and aliases must
// be unique across the whole registry; init() enforces that.
var registry = []*Language{
	{Name: "bash", getLang: bash.GetLanguage, Extensions: []string{".sh", ".bash"}, aliases: []string{"shell", "sh"}},
	{Name: "c", getLang: c.GetLanguage, Extensions: []string{".c", ".h"}},
	{Name: "cpp", getLang: cpp.GetLanguage, Extensions: []string{".cc", ".cpp", ".cxx", ".hpp", ".hh", ".hxx"}, aliases: []string{"c++"}},
	{Name: "csharp", getLang: csharp.GetLanguage, Extensions: []string{".cs"}, aliases: []string{"c#", "cs"}},
	{Name: "css", getLang: css.GetLanguage, Extensions: []string{".css"}},
	{Name: "cue", getLang: cue.GetLanguage, Extensions: []string{".cue"}},
	{Name: "dockerfile", getLang: dockerfile.GetLanguage, Extensions: []string{".dockerfile"}, aliases: []string{"docker"}},
	{Name: "elixir", getLang: elixir.GetLanguage, Extensions: []string{".ex", ".exs"}},
	{Name: "elm", getLang: elm.GetLanguage, Extensions: []string{".elm"}},
	{Name: "go", getLang: golang.GetLanguage, Extensions: []string{".go"}, aliases: []string{"golang"}},
	{Name: "groovy", getLang: groovy.GetLanguage, Extensions: []string{".groovy", ".gradle"}},
	{Name: "hcl", getLang: hcl.GetLanguage, Extensions: []string{".hcl", ".tf", ".tfvars"}, aliases: []string{"terraform"}},
	{Name: "html", getLang: html.GetLanguage, Extensions: []string{".html", ".htm"}},
	{Name: "java", getLang: java.GetLanguage, Extensions: []string{".java"}},
	{Name: "javascript", getLang: javascript.GetLanguage, Extensions: []string{".js", ".mjs", ".cjs", ".jsx"}, aliases: []string{"js", "node"}},
	{Name: "kotlin", getLang: kotlin.GetLanguage, Extensions: []string{".kt", ".kts"}},
	{Name: "lua", getLang: lua.GetLanguage, Extensions: []string{".lua"}},
	{Name: "ocaml", getLang: ocaml.GetLanguage, Extensions: []string{".ml", ".mli"}},
	{Name: "php", getLang: php.GetLanguage, Extensions: []string{".php"}},
	{Name: "protobuf", getLang: protobuf.GetLanguage, Extensions: []string{".proto"}, aliases: []string{"proto"}},
	{Name: "python", getLang: python.GetLanguage, Extensions: []string{".py", ".pyi"}, aliases: []string{"py"}},
	{Name: "ruby", getLang: ruby.GetLanguage, Extensions: []string{".rb"}, aliases: []string{"rb"}},
	{Name: "rust", getLang: rust.GetLanguage, Extensions: []string{".rs"}, aliases: []string{"rs"}},
	{Name: "scala", getLang: scala.GetLanguage, Extensions: []string{".scala", ".sc"}},
	{Name: "sql", getLang: sql.GetLanguage, Extensions: []string{".sql"}},
	{Name: "svelte", getLang: svelte.GetLanguage, Extensions: []string{".svelte"}},
	{Name: "swift", getLang: swift.GetLanguage, Extensions: []string{".swift"}},
	{Name: "toml", getLang: toml.GetLanguage, Extensions: []string{".toml"}},
	{Name: "tsx", getLang: tsx.GetLanguage, Extensions: []string{".tsx"}},
	{Name: "typescript", getLang: typescript.GetLanguage, Extensions: []string{".ts", ".mts", ".cts"}, aliases: []string{"ts"}},
	{Name: "yaml", getLang: yaml.GetLanguage, Extensions: []string{".yaml", ".yml"}},
}

var (
	byName = map[string]*Language{}
	byExt  = map[string]*Language{}
)

func init() {
	for _, l := range registry {
		register(l.Name, l)
		for _, a := range l.aliases {
			register(a, l)
		}
		for _, ext := range l.Extensions {
			ext = strings.ToLower(ext)
			if existing, ok := byExt[ext]; ok {
				panic(fmt.Sprintf("langs: extension %q registered for both %q and %q", ext, existing.Name, l.Name))
			}
			byExt[ext] = l
		}
	}
}

func register(name string, l *Language) {
	name = strings.ToLower(name)
	if existing, ok := byName[name]; ok {
		panic(fmt.Sprintf("langs: name %q registered for both %q and %q", name, existing.Name, l.Name))
	}
	byName[name] = l
}

// ByName resolves a language by its canonical name or an alias
// (case-insensitive).
func ByName(name string) (*Language, bool) {
	l, ok := byName[strings.ToLower(strings.TrimSpace(name))]
	return l, ok
}

// ByExtension resolves a language from a file extension, which may be given
// with or without a leading dot (e.g. "go" or ".go").
func ByExtension(ext string) (*Language, bool) {
	ext = strings.ToLower(strings.TrimSpace(ext))
	if ext != "" && !strings.HasPrefix(ext, ".") {
		ext = "." + ext
	}
	l, ok := byExt[ext]
	return l, ok
}

// ByFilename resolves a language from a file path using its extension.
func ByFilename(path string) (*Language, bool) {
	return ByExtension(filepath.Ext(path))
}

// All returns every registered language sorted by canonical name.
func All() []*Language {
	out := make([]*Language, len(registry))
	copy(out, registry)
	sort.Slice(out, func(i, j int) bool { return out[i].Name < out[j].Name })
	return out
}

// Names returns every canonical language name, sorted.
func Names() []string {
	out := make([]string, 0, len(registry))
	for _, l := range registry {
		out = append(out, l.Name)
	}
	sort.Strings(out)
	return out
}
