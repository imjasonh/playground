package langs

import (
	"context"
	"testing"

	sitter "github.com/smacker/go-tree-sitter"
)

func TestByName(t *testing.T) {
	cases := map[string]string{
		"go":         "go",
		"golang":     "go", // alias
		"GO":         "go", // case-insensitive
		"  python  ": "python",
		"py":         "python",
		"js":         "javascript",
		"ts":         "typescript",
		"c++":        "cpp",
		"c#":         "csharp",
		"terraform":  "hcl",
	}
	for input, want := range cases {
		l, ok := ByName(input)
		if !ok {
			t.Errorf("ByName(%q) not found", input)
			continue
		}
		if l.Name != want {
			t.Errorf("ByName(%q) = %q, want %q", input, l.Name, want)
		}
	}
	if _, ok := ByName("nope"); ok {
		t.Error("ByName(nope) should not be found")
	}
}

func TestByExtension(t *testing.T) {
	cases := map[string]string{
		".go":   "go",
		"go":    "go", // without dot
		".rs":   "rust",
		".tsx":  "tsx",
		".ts":   "typescript",
		".JS":   "javascript", // case-insensitive
		".yaml": "yaml",
		".yml":  "yaml",
	}
	for input, want := range cases {
		l, ok := ByExtension(input)
		if !ok {
			t.Errorf("ByExtension(%q) not found", input)
			continue
		}
		if l.Name != want {
			t.Errorf("ByExtension(%q) = %q, want %q", input, l.Name, want)
		}
	}
	if _, ok := ByExtension(".unknownext"); ok {
		t.Error("ByExtension(.unknownext) should not be found")
	}
}

func TestByFilename(t *testing.T) {
	l, ok := ByFilename("/a/b/main.go")
	if !ok || l.Name != "go" {
		t.Errorf("ByFilename(main.go) = %v, %v", l, ok)
	}
	if _, ok := ByFilename("Makefile"); ok {
		t.Error("ByFilename(Makefile) should not resolve")
	}
}

// TestAllGrammarsLoadAndParse ensures every registered grammar can be loaded
// via cgo and used to parse a trivial input without crashing. This is the
// cross-language smoke test that guards the registry.
func TestAllGrammarsLoadAndParse(t *testing.T) {
	for _, l := range All() {
		l := l
		t.Run(l.Name, func(t *testing.T) {
			lang := l.Sitter()
			if lang == nil {
				t.Fatalf("%s: Sitter() returned nil", l.Name)
			}
			parser := sitter.NewParser()
			parser.SetLanguage(lang)
			tree, err := parser.ParseCtx(context.Background(), nil, []byte("x"))
			if err != nil {
				t.Fatalf("%s: parse failed: %v", l.Name, err)
			}
			defer tree.Close()
			if tree.RootNode() == nil {
				t.Fatalf("%s: nil root node", l.Name)
			}
			if len(l.Extensions) == 0 {
				t.Errorf("%s: has no extensions", l.Name)
			}
		})
	}
}

func TestCuratedQueriesCompile(t *testing.T) {
	wantCurated := []string{"go", "python", "javascript", "typescript", "tsx", "rust"}
	for _, name := range wantCurated {
		l, ok := ByName(name)
		if !ok {
			t.Fatalf("language %q not found", name)
		}
		if !l.HasQueries() {
			t.Errorf("%s: expected curated queries", name)
			continue
		}
		for _, kind := range []string{QueryTags, QueryHighlights, QueryLocals} {
			src, ok := l.LoadQuery(kind)
			if !ok {
				t.Errorf("%s: missing %s query", name, kind)
				continue
			}
			q, err := sitter.NewQuery([]byte(src), l.Sitter())
			if err != nil {
				t.Errorf("%s/%s does not compile: %v", name, kind, err)
				continue
			}
			q.Close()
		}
	}
}

func TestLoadQueryMissing(t *testing.T) {
	l, _ := ByName("bash")
	if _, ok := l.LoadQuery(QueryLocals); ok {
		t.Error("bash should not have a locals query")
	}
	if l.HasQueries() {
		t.Error("bash should report no curated queries")
	}
}

func TestTsxAliasesTypescriptQueries(t *testing.T) {
	tsx, _ := ByName("tsx")
	ts, _ := ByName("typescript")
	for _, kind := range []string{QueryTags, QueryHighlights, QueryLocals} {
		a, _ := tsx.LoadQuery(kind)
		b, _ := ts.LoadQuery(kind)
		if a == "" || a != b {
			t.Errorf("tsx %s query should alias typescript's", kind)
		}
	}
}

func TestAliases(t *testing.T) {
	l, ok := ByName("go")
	if !ok {
		t.Fatal("go not found")
	}
	got := l.Aliases()
	if len(got) != 1 || got[0] != "golang" {
		t.Errorf("go aliases = %v, want [golang]", got)
	}
	// Aliases() must return a copy, not the backing slice.
	got[0] = "mutated"
	if again := l.Aliases(); again[0] != "golang" {
		t.Errorf("Aliases() leaked its backing slice: %v", again)
	}
}

func TestNamesAndAllConsistent(t *testing.T) {
	if len(Names()) != len(All()) {
		t.Fatalf("Names()=%d All()=%d", len(Names()), len(All()))
	}
	if len(All()) < 20 {
		t.Errorf("expected many languages, got %d", len(All()))
	}
	// All() must be sorted by name.
	prev := ""
	for _, l := range All() {
		if l.Name < prev {
			t.Errorf("All() not sorted: %q before %q", prev, l.Name)
		}
		prev = l.Name
	}
}
