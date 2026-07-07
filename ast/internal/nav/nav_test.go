package nav

import (
	"context"
	"reflect"
	"sort"
	"strings"
	"testing"

	"github.com/imjasonh/playground/ast/internal/engine"
	"github.com/imjasonh/playground/ast/internal/langs"
)

func lang(t *testing.T, name string) *langs.Language {
	t.Helper()
	l, ok := langs.ByName(name)
	if !ok {
		t.Fatalf("unknown language %q", name)
	}
	return l
}

func TestSelectKinds(t *testing.T) {
	cases := []struct {
		name  string
		lang  string
		src   string
		kinds []string
		want  []string
	}{
		{
			name:  "go functions",
			lang:  "go",
			src:   "package main\nfunc Foo() {}\nfunc Bar() {}\n",
			kinds: []string{"function"},
			want:  []string{"Foo", "Bar"},
		},
		{
			name:  "go calls",
			lang:  "go",
			src:   "package main\nfunc main() { foo(); x.Bar() }\n",
			kinds: []string{"call"},
			want:  []string{"foo", "Bar"},
		},
		{
			name:  "python functions and classes",
			lang:  "python",
			src:   "class C:\n    def m(self):\n        pass\ndef f():\n    pass\n",
			kinds: []string{"function", "class"},
			want:  []string{"C", "m", "f"},
		},
		{
			name:  "javascript strings and comments",
			lang:  "javascript",
			src:   "// hi\nconst s = \"x\";\n",
			kinds: []string{"comment", "string"},
			want:  []string{"// hi", "\"x\""},
		},
		{
			name:  "rust parameters",
			lang:  "rust",
			src:   "fn add(a: i32, b: i32) -> i32 { a + b }\n",
			kinds: []string{"parameter"},
			want:  []string{"a", "b"},
		},
		{
			name:  "typescript interface",
			lang:  "typescript",
			src:   "interface Shape { area(): number; }\n",
			kinds: []string{"interface"},
			want:  []string{"Shape"},
		},
	}
	for _, tc := range cases {
		t.Run(tc.name, func(t *testing.T) {
			hits, err := SelectKinds(context.Background(), []byte(tc.src), lang(t, tc.lang), tc.kinds)
			if err != nil {
				t.Fatal(err)
			}
			var got []string
			for _, h := range hits {
				got = append(got, h.Capture.Text)
			}
			sort.Strings(got)
			want := append([]string(nil), tc.want...)
			sort.Strings(want)
			if !reflect.DeepEqual(got, want) {
				t.Errorf("kinds %v = %q, want %q", tc.kinds, got, want)
			}
		})
	}
}

func TestSelectKindsUnknownKind(t *testing.T) {
	_, err := SelectKinds(context.Background(), []byte("package main"), lang(t, "go"), []string{"bogus"})
	if err == nil || !strings.Contains(err.Error(), "unknown kind") {
		t.Fatalf("expected unknown-kind error, got %v", err)
	}
}

func TestSelectKindsUnavailableLanguage(t *testing.T) {
	// bash has no curated queries.
	_, err := SelectKinds(context.Background(), []byte("echo hi"), lang(t, "bash"), []string{"function"})
	if err == nil || !strings.Contains(err.Error(), "not available") {
		t.Fatalf("expected not-available error, got %v", err)
	}
}

// applyRename applies a RenameResult to src and returns the rewritten source.
func applyRename(t *testing.T, src string, res *RenameResult, to string) string {
	t.Helper()
	edits := make([]engine.Edit, 0, len(res.Occurrences))
	for _, o := range res.Occurrences {
		edits = append(edits, engine.Edit{Start: o.StartByte, End: o.EndByte, Text: to})
	}
	out, err := engine.Apply([]byte(src), edits)
	if err != nil {
		t.Fatal(err)
	}
	return string(out)
}

func TestRenameAtScopeAware(t *testing.T) {
	src := "package main\n\nfunc f() {\n\tx := 1\n\tprintln(x)\n}\n\nfunc g() {\n\tx := 2\n\tprintln(x)\n}\n"
	// Target f's x at line 4, col 2 (1-based) -> row 3, col 1 (0-based).
	res, err := RenameAt(context.Background(), []byte(src), lang(t, "go"), Pos{Row: 3, Column: 1})
	if err != nil {
		t.Fatal(err)
	}
	if len(res.Occurrences) != 2 {
		t.Fatalf("expected 2 occurrences (f's x def+use), got %d", len(res.Occurrences))
	}
	got := applyRename(t, src, res, "n")
	if !strings.Contains(got, "n := 1") || !strings.Contains(got, "println(n)") {
		t.Errorf("f's x not renamed:\n%s", got)
	}
	if !strings.Contains(got, "x := 2") {
		t.Errorf("g's x should be untouched:\n%s", got)
	}
}

func TestRenamePythonExcludesAttribute(t *testing.T) {
	src := "def outer(name):\n    return name\n\ndef other(name):\n    return name.upper()\n"
	// outer's name param at line 1 col 11 (1-based) -> row 0 col 10.
	res, err := RenameAt(context.Background(), []byte(src), lang(t, "python"), Pos{Row: 0, Column: 10})
	if err != nil {
		t.Fatal(err)
	}
	got := applyRename(t, src, res, "label")
	if !strings.Contains(got, "def outer(label):") || !strings.Contains(got, "return label\n") {
		t.Errorf("outer's name not renamed:\n%s", got)
	}
	// other()'s name and the .upper attribute must be untouched.
	if !strings.Contains(got, "def other(name):") || !strings.Contains(got, "name.upper()") {
		t.Errorf("other()/attribute wrongly touched:\n%s", got)
	}
}

func TestRenameRustRecursion(t *testing.T) {
	src := "fn add(a: i32) -> i32 { add(a) }\n"
	// fn name at row 0 col 3 (0-based) -> "add".
	res, err := RenameAt(context.Background(), []byte(src), lang(t, "rust"), Pos{Row: 0, Column: 3})
	if err != nil {
		t.Fatal(err)
	}
	got := applyRename(t, src, res, "plus")
	if got != "fn plus(a: i32) -> i32 { plus(a) }\n" {
		t.Errorf("recursion rename wrong:\n%s", got)
	}
}

func TestRenameAtFreeSymbolErrors(t *testing.T) {
	src := "package main\nfunc main() { println(1) }\n"
	// println at line 2 col 15 (1-based) -> row 1 col 14; it's a builtin, not local.
	_, err := RenameAt(context.Background(), []byte(src), lang(t, "go"), Pos{Row: 1, Column: 14})
	if err == nil || !strings.Contains(err.Error(), "does not resolve to a local binding") {
		t.Fatalf("expected free-symbol error, got %v", err)
	}
}

func TestRenameName(t *testing.T) {
	src := "package main\n\nfunc f() {\n\tx := 1\n\tprintln(x)\n}\n\nfunc g() {\n\tx := 2\n\tprintln(x)\n}\n"
	res, err := RenameName(context.Background(), []byte(src), lang(t, "go"), "x")
	if err != nil {
		t.Fatal(err)
	}
	if len(res.Occurrences) != 4 {
		t.Fatalf("expected 4 occurrences across both scopes, got %d", len(res.Occurrences))
	}
	got := applyRename(t, src, res, "y")
	if strings.Contains(got, "x :=") || strings.Contains(got, "println(x)") {
		t.Errorf("not all x renamed:\n%s", got)
	}
}

func TestRenameUnavailableLanguage(t *testing.T) {
	_, err := RenameName(context.Background(), []byte("echo hi"), lang(t, "bash"), "hi")
	if err == nil || !strings.Contains(err.Error(), "not available") {
		t.Fatalf("expected not-available error, got %v", err)
	}
}

func TestKindsForLanguage(t *testing.T) {
	got := KindsForLanguage(lang(t, "go"))
	for _, want := range []string{"function", "method", "call", "comment", "string", "parameter"} {
		found := false
		for _, k := range got {
			if k == want {
				found = true
			}
		}
		if !found {
			t.Errorf("go kinds missing %q; got %v", want, got)
		}
	}
	// A language without curated queries has no kinds.
	if k := KindsForLanguage(lang(t, "bash")); len(k) != 0 {
		t.Errorf("bash should have no kinds, got %v", k)
	}
}
