package main

import (
	"os"
	"path/filepath"
	"reflect"
	"strings"
	"testing"
)

func TestStagedSources(t *testing.T) {
	repo, _ := newHookRepo(t)
	write := func(rel, content string) {
		t.Helper()
		writeFile(t, filepath.Join(repo, rel), content, 0o644)
	}
	write("gone.go", "package gone\n")
	runGit(t, repo, "add", "gone.go")
	runGit(t, repo, "commit", "--quiet", "-m", "base")

	write("a.go", "package a // staged\n")
	write("sub/c.go", "package c\n")
	write("big.go", "package big\n"+strings.Repeat("//\n", 100))
	write("vendor/v.go", "package v\n")
	write("x/testdata/t.go", "package t\n")
	write("a.go.golden", "package a\n")
	write("notes.txt", "notes\n")
	if err := os.Symlink("a.go", filepath.Join(repo, "link.go")); err != nil {
		t.Skipf("symlink not supported: %v", err)
	}
	runGit(t, repo, "add", ".")
	runGit(t, repo, "rm", "--quiet", "gone.go")
	write("a.go", "package a // unstaged\n")
	write("untracked.go", "package u\n")

	specs, oversized, err := stagedSources(parseSkipDirs("", nil), 100)
	if err != nil {
		t.Fatal(err)
	}
	got := map[string]string{}
	for _, s := range specs {
		got[s.Path] = string(s.Src)
	}
	want := map[string]string{
		"a.go":                       "package a // staged\n",
		filepath.Join("sub", "c.go"): "package c\n",
	}
	if !reflect.DeepEqual(got, want) {
		t.Errorf("staged sources:\n got %q\nwant %q", got, want)
	}
	if !reflect.DeepEqual(oversized, []string{"big.go"}) {
		t.Errorf("oversized = %q, want [big.go]", oversized)
	}

	t.Chdir(filepath.Join(repo, "sub"))
	specs, _, err = stagedSources(parseSkipDirs("", nil), 0)
	if err != nil {
		t.Fatal(err)
	}
	if len(specs) != 1 || specs[0].Path != "c.go" {
		t.Errorf("staged sources from sub/: %v, want only c.go", specs)
	}
}

func TestRunFix_staged(t *testing.T) {
	rules := analyzerRules(t, "js_debugger")
	repo, _ := newHookRepo(t)
	js := filepath.Join(repo, "a.js")
	run := func(flags ...string) (string, int) {
		t.Helper()
		var code int
		out := captureStderr(t, func() {
			code = runFix(append([]string{"-nocache", "-rules", rules, "-fail-on=warning"}, flags...))
		})
		return out, code
	}

	writeFile(t, js, "debugger;\n", 0o644)
	runGit(t, repo, "add", "a.js")
	writeFile(t, js, "const ok = 1;\n", 0o644)
	if out, code := run("-staged"); code != 1 || !strings.Contains(out, "a.js:1: warning: debugger statement") {
		t.Errorf("debugger staged, fixed in the working tree: exit %d, want 1 with the finding:\n%s", code, out)
	}

	runGit(t, repo, "add", "a.js")
	writeFile(t, js, "debugger;\n", 0o644)
	if out, code := run("-staged"); code != 0 || strings.Contains(out, "debugger statement") {
		t.Errorf("clean copy staged, debugger in the working tree: exit %d, want 0 with no finding:\n%s", code, out)
	}
	if out, code := run(); code != 1 {
		t.Errorf("without -staged: exit %d, want 1 from the working-tree copy:\n%s", code, out)
	}

	if out, code := run("-staged", "-fix"); code != 2 {
		t.Errorf("-staged -fix: exit %d, want 2:\n%s", code, out)
	}
	if out, code := run("-staged", "a.js"); code != 2 {
		t.Errorf("-staged with a source argument: exit %d, want 2:\n%s", code, out)
	}
}
