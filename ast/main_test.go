package main

import (
	"bytes"
	"os"
	"path/filepath"
	"strings"
	"testing"
)

// runCLI invokes run() with args and returns combined stdout, stderr, and error.
func runCLI(t *testing.T, args ...string) (string, string, error) {
	t.Helper()
	var stdout, stderr bytes.Buffer
	err := run(args, &stdout, &stderr)
	return stdout.String(), stderr.String(), err
}

// writeTemp writes content to a temp file named base and returns its path.
func writeTemp(t *testing.T, base, content string) string {
	t.Helper()
	path := filepath.Join(t.TempDir(), base)
	if err := os.WriteFile(path, []byte(content), 0o644); err != nil {
		t.Fatal(err)
	}
	return path
}

func TestLanguagesCommand(t *testing.T) {
	out, _, err := runCLI(t, "languages")
	if err != nil {
		t.Fatal(err)
	}
	for _, want := range []string{"LANGUAGE", "go", "python", "rust", "languages supported"} {
		if !strings.Contains(out, want) {
			t.Errorf("languages output missing %q:\n%s", want, out)
		}
	}
}

func TestLanguagesJSON(t *testing.T) {
	out, _, err := runCLI(t, "languages", "--json")
	if err != nil {
		t.Fatal(err)
	}
	if !strings.Contains(out, `"name": "go"`) || !strings.Contains(out, `".go"`) {
		t.Errorf("languages --json missing expected content:\n%s", out)
	}
}

func TestTreeCommand(t *testing.T) {
	f := writeTemp(t, "x.go", "package main\nfunc Foo() {}\n")
	out, _, err := runCLI(t, "tree", f)
	if err != nil {
		t.Fatal(err)
	}
	for _, want := range []string{"source_file", "function_declaration", "name: identifier", `"Foo"`} {
		if !strings.Contains(out, want) {
			t.Errorf("tree output missing %q:\n%s", want, out)
		}
	}
}

func TestTreeSexp(t *testing.T) {
	f := writeTemp(t, "x.go", "package main")
	out, _, err := runCLI(t, "tree", "--sexp", f)
	if err != nil {
		t.Fatal(err)
	}
	if !strings.HasPrefix(strings.TrimSpace(out), "(source_file") {
		t.Errorf("expected s-expression, got:\n%s", out)
	}
}

func TestQueryCommandText(t *testing.T) {
	f := writeTemp(t, "x.go", "package main\nfunc Foo() {}\nfunc Bar() {}\n")
	out, _, err := runCLI(t, "query", "-q", "(function_declaration name: (identifier) @name)", f)
	if err != nil {
		t.Fatal(err)
	}
	if !strings.Contains(out, "@name") || !strings.Contains(out, "Foo") || !strings.Contains(out, "Bar") {
		t.Errorf("query output wrong:\n%s", out)
	}
	if !strings.Contains(out, "2 node(s) matched") {
		t.Errorf("missing summary:\n%s", out)
	}
}

func TestQueryCommandJSON(t *testing.T) {
	f := writeTemp(t, "x.py", "def foo():\n    pass\n")
	out, _, err := runCLI(t, "query", "--json", "-q", "(function_definition name: (identifier) @name)", f)
	if err != nil {
		t.Fatal(err)
	}
	for _, want := range []string{`"file"`, `"captures"`, `"name": "name"`, `"text": "foo"`} {
		if !strings.Contains(out, want) {
			t.Errorf("json missing %q:\n%s", want, out)
		}
	}
}

func TestQueryCaptureFilter(t *testing.T) {
	f := writeTemp(t, "x.go", "package main\nfunc Foo(a int) {}\n")
	q := "(function_declaration name: (identifier) @name parameters: (parameter_list) @params)"
	out, _, err := runCLI(t, "query", "-c", "name", "-q", q, f)
	if err != nil {
		t.Fatal(err)
	}
	if strings.Contains(out, "@params") {
		t.Errorf("capture filter should exclude @params:\n%s", out)
	}
	if !strings.Contains(out, "@name") {
		t.Errorf("capture filter dropped @name:\n%s", out)
	}
}

func TestRewriteReplaceStdout(t *testing.T) {
	f := writeTemp(t, "x.go", "package main\nfunc Foo() {}\n")
	out, _, err := runCLI(t, "rewrite",
		"-q", `((identifier) @id (#eq? @id "Foo"))`,
		"--replace", "@id=Bar", f)
	if err != nil {
		t.Fatal(err)
	}
	if !strings.Contains(out, "func Bar()") || strings.Contains(out, "Foo") {
		t.Errorf("replace to stdout wrong:\n%s", out)
	}
	// Original file must be untouched without -w.
	if b, _ := os.ReadFile(f); !strings.Contains(string(b), "Foo") {
		t.Errorf("file changed without -w: %s", b)
	}
}

func TestRewriteWrite(t *testing.T) {
	f := writeTemp(t, "x.go", "package main\nfunc Foo() {}\n")
	_, stderr, err := runCLI(t, "rewrite",
		"-q", `((identifier) @id (#eq? @id "Foo"))`,
		"--replace", "@id=Bar", "-w", f)
	if err != nil {
		t.Fatal(err)
	}
	b, _ := os.ReadFile(f)
	if !strings.Contains(string(b), "func Bar()") {
		t.Errorf("file not rewritten: %s", b)
	}
	if !strings.Contains(stderr, "rewrote") {
		t.Errorf("expected rewrite summary on stderr, got %q", stderr)
	}
}

func TestRewriteDelete(t *testing.T) {
	src := "package main\n\nimport \"fmt\"\n\nfunc main() { fmt.Println(1) }\n"
	f := writeTemp(t, "x.go", src)
	out, _, err := runCLI(t, "rewrite",
		"-q", "(import_declaration) @imp",
		"--delete", "@imp", f)
	if err != nil {
		t.Fatal(err)
	}
	if strings.Contains(out, "import") {
		t.Errorf("import not deleted:\n%s", out)
	}
}

func TestRewriteInsertBeforeAfter(t *testing.T) {
	f := writeTemp(t, "x.go", "package main\nfunc Foo() {}\n")
	out, _, err := runCLI(t, "rewrite",
		"-q", "(function_declaration) @fn",
		"--insert-before", "@fn=//before\n",
		"--insert-after", "@fn=\n//after", f)
	if err != nil {
		t.Fatal(err)
	}
	if !strings.Contains(out, "//before\nfunc Foo() {}\n//after") {
		t.Errorf("insert-before/after wrong:\n%s", out)
	}
}

func TestRewriteInterpolation(t *testing.T) {
	f := writeTemp(t, "x.go", "package main\nfunc Foo() {}\n")
	out, _, err := runCLI(t, "rewrite",
		"-q", "(function_declaration name: (identifier) @name) @fn",
		"--insert-before", "@fn=// {{name}} does things\n", f)
	if err != nil {
		t.Fatal(err)
	}
	if !strings.Contains(out, "// Foo does things") {
		t.Errorf("interpolation wrong:\n%s", out)
	}
}

func TestRewriteInterpolationUnknownCapture(t *testing.T) {
	f := writeTemp(t, "x.go", "package main\nfunc Foo() {}\n")
	_, _, err := runCLI(t, "rewrite",
		"-q", "(function_declaration name: (identifier) @name) @fn",
		"--replace", "@name={{nope}}", f)
	if err == nil || !strings.Contains(err.Error(), "unknown capture") {
		t.Fatalf("expected unknown-capture error, got %v", err)
	}
}

func TestRewriteDiff(t *testing.T) {
	f := writeTemp(t, "x.go", "package main\n\nfunc Foo() {}\n")
	out, _, err := runCLI(t, "rewrite",
		"-q", `((identifier) @id (#eq? @id "Foo"))`,
		"--replace", "@id=Bar", "--diff", f)
	if err != nil {
		t.Fatal(err)
	}
	if !strings.Contains(out, "-func Foo() {}") || !strings.Contains(out, "+func Bar() {}") {
		t.Errorf("diff output wrong:\n%s", out)
	}
	if !strings.Contains(out, "@@") {
		t.Errorf("diff missing hunk header:\n%s", out)
	}
}

// TestRewriteCrossLanguage renames foo -> renamed across a variety of
// languages, exercising the whole pipeline (parse, query, edit, apply).
func TestRewriteCrossLanguage(t *testing.T) {
	cases := []struct {
		lang  string
		file  string
		src   string
		query string
		want  string
	}{
		{"go", "x.go", "package main\nfunc foo() {}\n", `((identifier) @id (#eq? @id "foo"))`, "func renamed()"},
		{"python", "x.py", "def foo():\n    pass\n", `((identifier) @id (#eq? @id "foo"))`, "def renamed()"},
		{"javascript", "x.js", "function foo(){}", `((identifier) @id (#eq? @id "foo"))`, "function renamed()"},
		{"rust", "x.rs", "fn foo() {}\n", `((identifier) @id (#eq? @id "foo"))`, "fn renamed()"},
		{"ruby", "x.rb", "def foo\nend\n", `((identifier) @id (#eq? @id "foo"))`, "def renamed"},
		{"c", "x.c", "int foo(){return 0;}\n", `((identifier) @id (#eq? @id "foo"))`, "int renamed()"},
	}
	for _, tc := range cases {
		t.Run(tc.lang, func(t *testing.T) {
			f := writeTemp(t, tc.file, tc.src)
			out, _, err := runCLI(t, "rewrite", "-q", tc.query, "--replace", "@id=renamed", f)
			if err != nil {
				t.Fatal(err)
			}
			if !strings.Contains(out, tc.want) {
				t.Errorf("%s rewrite = %q, want substring %q", tc.lang, out, tc.want)
			}
			if strings.Contains(out, "foo") {
				t.Errorf("%s still contains foo:\n%s", tc.lang, out)
			}
		})
	}
}

func TestForcedLanguageOverride(t *testing.T) {
	// A file with a misleading extension parsed as Python via -l.
	f := writeTemp(t, "script.txt", "def foo():\n    pass\n")
	out, _, err := runCLI(t, "query", "-l", "python",
		"-q", "(function_definition name: (identifier) @n)", f)
	if err != nil {
		t.Fatal(err)
	}
	if !strings.Contains(out, "foo") {
		t.Errorf("forced language failed:\n%s", out)
	}
}

func TestErrors(t *testing.T) {
	goFile := writeTemp(t, "x.go", "package main\n")
	cases := []struct {
		name string
		args []string
		want string
	}{
		{"no subcommand", nil, "subcommand is required"},
		{"unknown subcommand", []string{"bogus"}, "unknown subcommand"},
		{"query missing -q", []string{"query", goFile}, "requires -q"},
		{"query no files", []string{"query", "-q", "(x)@a"}, "at least one file"},
		{"unknown language", []string{"query", "-l", "klingon", "-q", "(x)@a", goFile}, "unknown language"},
		{"cannot infer language", []string{"query", "-q", "(x)@a", writeTemp(t, "mystery.zzz", "x")}, "cannot infer language"},
		{"rewrite no ops", []string{"rewrite", "-q", "(identifier)@a", goFile}, "at least one operation"},
		{"rewrite bad op", []string{"rewrite", "-q", "(identifier)@a", "--replace", "@a", goFile}, "@capture=TEXT"},
	}
	for _, tc := range cases {
		t.Run(tc.name, func(t *testing.T) {
			_, _, err := runCLI(t, tc.args...)
			if err == nil {
				t.Fatalf("expected error containing %q, got nil", tc.want)
			}
			if !strings.Contains(err.Error(), tc.want) {
				t.Errorf("error = %q, want substring %q", err, tc.want)
			}
		})
	}
}
