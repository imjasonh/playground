package engine

import (
	"context"
	"reflect"
	"strings"
	"testing"

	"github.com/imjasonh/playground/ast/internal/langs"
)

// captureTexts runs a query and returns the text of every capture, in match
// order, restricted to the given capture name.
func captureTexts(t *testing.T, lang, src, query, name string) []string {
	t.Helper()
	l, ok := langs.ByName(lang)
	if !ok {
		t.Fatalf("unknown language %q", lang)
	}
	matches, err := Query(context.Background(), []byte(src), l.Sitter(), query)
	if err != nil {
		t.Fatalf("Query(%s): %v", lang, err)
	}
	var got []string
	for _, m := range matches {
		for _, c := range m.Captures {
			if name == "" || c.Name == name {
				got = append(got, c.Text)
			}
		}
	}
	return got
}

func TestQueryCrossLanguage(t *testing.T) {
	cases := []struct {
		name  string
		lang  string
		src   string
		query string
		want  []string
	}{
		{
			name:  "go functions",
			lang:  "go",
			src:   "package main\nfunc Foo() {}\nfunc Bar() {}\n",
			query: "(function_declaration name: (identifier) @n)",
			want:  []string{"Foo", "Bar"},
		},
		{
			name:  "python functions",
			lang:  "python",
			src:   "def foo():\n    return 1\ndef bar():\n    return 2\n",
			query: "(function_definition name: (identifier) @n)",
			want:  []string{"foo", "bar"},
		},
		{
			name:  "javascript functions",
			lang:  "javascript",
			src:   "function foo(){} function bar(){}",
			query: "(function_declaration name: (identifier) @n)",
			want:  []string{"foo", "bar"},
		},
		{
			name:  "typescript functions",
			lang:  "typescript",
			src:   "function foo(): void {} function bar(): void {}",
			query: "(function_declaration name: (identifier) @n)",
			want:  []string{"foo", "bar"},
		},
		{
			name:  "tsx functions",
			lang:  "tsx",
			src:   "function foo(){} function bar(){}",
			query: "(function_declaration name: (identifier) @n)",
			want:  []string{"foo", "bar"},
		},
		{
			name:  "rust functions",
			lang:  "rust",
			src:   "fn foo() {}\nfn bar() {}\n",
			query: "(function_item name: (identifier) @n)",
			want:  []string{"foo", "bar"},
		},
		{
			name:  "java methods",
			lang:  "java",
			src:   "class C { void foo(){} int bar(){return 1;} }",
			query: "(method_declaration name: (identifier) @n)",
			want:  []string{"foo", "bar"},
		},
		{
			name:  "c functions",
			lang:  "c",
			src:   "int foo(){return 0;}\nvoid bar(){}\n",
			query: "(function_definition declarator: (function_declarator declarator: (identifier) @n))",
			want:  []string{"foo", "bar"},
		},
		{
			name:  "cpp functions",
			lang:  "cpp",
			src:   "int foo(){return 0;}\nvoid bar(){}\n",
			query: "(function_definition declarator: (function_declarator declarator: (identifier) @n))",
			want:  []string{"foo", "bar"},
		},
		{
			name:  "ruby methods",
			lang:  "ruby",
			src:   "def foo\nend\ndef bar\nend\n",
			query: "(method name: (identifier) @n)",
			want:  []string{"foo", "bar"},
		},
		{
			name:  "csharp methods",
			lang:  "csharp",
			src:   "class C { void Foo(){} int Bar(){return 1;} }",
			query: "(method_declaration name: (identifier) @n)",
			want:  []string{"Foo", "Bar"},
		},
		{
			name:  "php functions",
			lang:  "php",
			src:   "<?php function foo(){} function bar(){} ?>",
			query: "(function_definition name: (name) @n)",
			want:  []string{"foo", "bar"},
		},
		{
			name:  "bash functions",
			lang:  "bash",
			src:   "foo() { echo hi; }\nbar() { echo bye; }\n",
			query: "(function_definition name: (word) @n)",
			want:  []string{"foo", "bar"},
		},
		{
			name:  "lua functions",
			lang:  "lua",
			src:   "function foo() end\nfunction bar() end\n",
			query: "(function_name (identifier) @n)",
			want:  []string{"foo", "bar"},
		},
		{
			name:  "scala defs",
			lang:  "scala",
			src:   "object O { def foo() = 1; def bar() = 2 }",
			query: "(function_definition name: (identifier) @n)",
			want:  []string{"foo", "bar"},
		},
		{
			name:  "kotlin functions",
			lang:  "kotlin",
			src:   "fun foo() {} fun bar() {}",
			query: "(function_declaration (simple_identifier) @n)",
			want:  []string{"foo", "bar"},
		},
		{
			name:  "swift functions",
			lang:  "swift",
			src:   "func foo() {} func bar() {}",
			query: "(function_declaration name: (simple_identifier) @n)",
			want:  []string{"foo", "bar"},
		},
		{
			name:  "yaml keys",
			lang:  "yaml",
			src:   "foo: 1\nbar: 2\n",
			query: "(block_mapping_pair key: (flow_node) @n)",
			want:  []string{"foo", "bar"},
		},
		{
			name:  "toml keys",
			lang:  "toml",
			src:   "foo = 1\nbar = 2\n",
			query: "(pair (bare_key) @n)",
			want:  []string{"foo", "bar"},
		},
		{
			name:  "css class selectors",
			lang:  "css",
			src:   ".foo { color: red; } .bar { color: blue; }",
			query: "(class_selector (class_name) @n)",
			want:  []string{"foo", "bar"},
		},
		{
			name:  "sql table refs",
			lang:  "sql",
			src:   "SELECT * FROM foo; SELECT * FROM bar;",
			query: "(object_reference name: (identifier) @n)",
			want:  []string{"foo", "bar"},
		},
		{
			name:  "hcl blocks",
			lang:  "hcl",
			src:   "resource \"x\" {}\nvariable \"y\" {}\n",
			query: "(block (identifier) @n)",
			want:  []string{"resource", "variable"},
		},
		{
			name:  "html tags",
			lang:  "html",
			src:   "<div></div><span></span>",
			query: "(start_tag (tag_name) @n)",
			want:  []string{"div", "span"},
		},
	}

	for _, tc := range cases {
		t.Run(tc.name, func(t *testing.T) {
			got := captureTexts(t, tc.lang, tc.src, tc.query, "n")
			if !reflect.DeepEqual(got, tc.want) {
				t.Errorf("captures = %q, want %q", got, tc.want)
			}
		})
	}
}

func TestQueryPredicateEq(t *testing.T) {
	src := "package main\nfunc foo(){}\nfunc bar(){}\nfunc foo2(){ foo() }\n"
	got := captureTexts(t, "go",
		src,
		`((identifier) @id (#eq? @id "foo"))`, "id")
	want := []string{"foo", "foo"} // declaration name + call
	if !reflect.DeepEqual(got, want) {
		t.Errorf("got %q, want %q", got, want)
	}
}

func TestQueryPredicateMatch(t *testing.T) {
	src := "package main\nfunc fooBar(){}\nfunc bazQux(){}\nfunc fooBaz(){}\n"
	got := captureTexts(t, "go",
		src,
		`((function_declaration name: (identifier) @id) (#match? @id "^foo"))`, "id")
	want := []string{"fooBar", "fooBaz"}
	if !reflect.DeepEqual(got, want) {
		t.Errorf("got %q, want %q", got, want)
	}
}

func TestQueryErrors(t *testing.T) {
	goLang, _ := langs.ByName("go")
	t.Run("invalid query", func(t *testing.T) {
		if _, err := Query(context.Background(), []byte("package main"), goLang.Sitter(), "(nonsense"); err == nil {
			t.Fatal("expected error for malformed query")
		}
	})
	t.Run("no captures", func(t *testing.T) {
		_, err := Query(context.Background(), []byte("package main"), goLang.Sitter(), "(function_declaration)")
		if err == nil || !strings.Contains(err.Error(), "no captures") {
			t.Fatalf("expected no-captures error, got %v", err)
		}
	})
}

func TestApply(t *testing.T) {
	src := []byte("hello world")
	cases := []struct {
		name  string
		edits []Edit
		want  string
	}{
		{"empty", nil, "hello world"},
		{"replace", []Edit{{0, 5, "goodbye"}}, "goodbye world"},
		{"delete", []Edit{{5, 11, ""}}, "hello"},
		{"insert", []Edit{{5, 5, ","}}, "hello, world"},
		{
			name:  "multiple unordered",
			edits: []Edit{{6, 11, "there"}, {0, 5, "hi"}},
			want:  "hi there",
		},
		{
			name:  "insertion at replacement boundary",
			edits: []Edit{{0, 0, ">>"}, {0, 5, "HELLO"}},
			want:  ">>HELLO world",
		},
	}
	for _, tc := range cases {
		t.Run(tc.name, func(t *testing.T) {
			got, err := Apply(src, tc.edits)
			if err != nil {
				t.Fatalf("Apply: %v", err)
			}
			if string(got) != tc.want {
				t.Errorf("got %q, want %q", got, tc.want)
			}
			// Apply must not mutate the input.
			if string(src) != "hello world" {
				t.Errorf("input mutated to %q", src)
			}
		})
	}
}

func TestApplyErrors(t *testing.T) {
	src := []byte("hello world")
	cases := map[string][]Edit{
		"overlap":     {{0, 6, "x"}, {3, 8, "y"}},
		"start > end": {{5, 2, "x"}},
		"past end":    {{0, 100, "x"}},
	}
	for name, edits := range cases {
		t.Run(name, func(t *testing.T) {
			if _, err := Apply(src, edits); err == nil {
				t.Fatalf("expected error for %s", name)
			}
		})
	}
}

func TestMatchCapture(t *testing.T) {
	m := Match{Captures: []Capture{{Name: "a", Text: "x"}, {Name: "b", Text: "y"}}}
	if c, ok := m.Capture("@b"); !ok || c.Text != "y" {
		t.Errorf("Capture(@b) = %+v, %v", c, ok)
	}
	if _, ok := m.Capture("missing"); ok {
		t.Error("expected missing capture to report not found")
	}
}
