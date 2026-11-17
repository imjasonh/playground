package codefacts

import (
	"os"
	"path/filepath"
	"reflect"
	"sort"
	"testing"
)

// writeTree writes files (relative path -> contents) under a fresh temp dir and
// returns the dir.
func writeTree(t *testing.T, files map[string]string) string {
	t.Helper()
	dir := t.TempDir()
	for rel, body := range files {
		full := filepath.Join(dir, rel)
		if err := os.MkdirAll(filepath.Dir(full), 0o755); err != nil {
			t.Fatal(err)
		}
		if err := os.WriteFile(full, []byte(body), 0o644); err != nil {
			t.Fatal(err)
		}
	}
	return dir
}

func buildT(t *testing.T, dir string, opts BuildOptions) *Index {
	t.Helper()
	idx, err := Build(t.Context(), []string{dir}, opts)
	if err != nil {
		t.Fatalf("Build: %v", err)
	}
	return idx
}

const goFixture = `package app

import (
	"fmt"
	"strings"
)

type Closer interface {
	Close() error
}

type Thing struct{}

// Close always returns nil but can't lose its signature: it satisfies Closer.
func (t *Thing) Close() error { return nil }

func mkThing(name string, verbose bool) *Thing {
	if true {
		_ = name
	}
	if false {
		panic("never")
	}
	return &Thing{}
}

func helperUnused(a int) int { return a }

func withIgnored(_ignored int, real int) int { return 7 }

func dupA(x int) int {
	y := x + 1
	z := y * 2
	return z + 1
}

func dupB(x int) int {
	y := x + 1
	z := y * 2
	return z + 1
}

func caller() {
	mkThing("fixed", true)
	mkThing("fixed", false)
	mkThing("fixed", true)
	s := fmt.Sprint("hi")
	_ = s
	if s == "x" == true {
		_ = s
	}
}
`

func TestInterfaceMethodNotFlagged(t *testing.T) {
	dir := writeTree(t, map[string]string{"app/app.go": goFixture})
	idx := buildT(t, dir, DefaultBuildOptions())

	// Close satisfies the in-file Closer interface: it must not appear in
	// constant_returns, unused_symbols, or dead_code.
	for _, r := range ConstantReturns(idx) {
		if r["function"] == "Close" {
			t.Error("Close (interface method) wrongly in constant_returns")
		}
	}
	for _, u := range UnusedSymbols(idx, true) {
		if u.Name == "Close" {
			t.Error("Close (interface method) wrongly in unused_symbols")
		}
	}
	for _, d := range DeadCode(idx) {
		if d.Name == "Close" {
			t.Error("Close (interface method) wrongly in dead_code")
		}
	}
}

func TestReceiverQualifier(t *testing.T) {
	dir := writeTree(t, map[string]string{"app/app.go": goFixture})
	idx := buildT(t, dir, DefaultBuildOptions())
	var got string
	for _, d := range idx.defs["Close"] {
		got = d.Qualified()
	}
	if got != "Thing.Close" {
		t.Errorf("receiver qualifier = %q, want Thing.Close", got)
	}
}

func TestUnusedSymbolHighConfidence(t *testing.T) {
	dir := writeTree(t, map[string]string{"app/app.go": goFixture})
	idx := buildT(t, dir, DefaultBuildOptions())
	us := UnusedSymbols(idx, true)
	var found *Unused
	for i := range us {
		if us[i].Name == "helperUnused" {
			found = &us[i]
		}
	}
	if found == nil {
		t.Fatal("helperUnused not flagged unused")
	}
	if found.Confidence != "high" {
		t.Errorf("helperUnused confidence = %q, want high", found.Confidence)
	}
}

func TestUnderscoreParamSkipped(t *testing.T) {
	dir := writeTree(t, map[string]string{"app/app.go": goFixture})
	idx := buildT(t, dir, DefaultBuildOptions())
	for _, p := range UnusedParameters(idx) {
		if p.Param == "_ignored" {
			t.Error("underscore-prefixed param wrongly flagged unused")
		}
	}
}

func TestConstantArguments(t *testing.T) {
	dir := writeTree(t, map[string]string{"app/app.go": goFixture})
	idx := buildT(t, dir, DefaultBuildOptions())
	cands := ConstantArguments(idx, 2)
	var hit *Candidate
	for i := range cands {
		if cands[i].Name == "mkThing" && cands[i].Param == "name" {
			hit = &cands[i]
		}
	}
	if hit == nil {
		t.Fatal("mkThing name=\"fixed\" constant arg not found")
	}
	if hit.ValueKind != "literal" || hit.Value != `"fixed"` {
		t.Errorf("got value=%q kind=%q, want \"fixed\" literal", hit.Value, hit.ValueKind)
	}
}

func TestConstantConditions(t *testing.T) {
	dir := writeTree(t, map[string]string{"app/app.go": goFixture})
	idx := buildT(t, dir, DefaultBuildOptions())
	got := ConstantConditions(idx)
	if len(got) != 2 {
		t.Fatalf("constant_conditions = %d, want 2 (if true / if false)", len(got))
	}
}

func TestRedundantStrictNoteOnlyForJS(t *testing.T) {
	dir := writeTree(t, map[string]string{
		"app/app.go": goFixture,
		"web/a.js":   "function f(x){ if (x === true) { return 1; } return 0; }\n",
	})
	idx := buildT(t, dir, DefaultBuildOptions())
	var jsLow, goHigh bool
	for _, r := range RedundantConditions(idx) {
		if r["lang"] == "javascript" && r["operator"] == "===" {
			if r["confidence"] == "low" {
				jsLow = true
			}
		}
		if r["lang"] == "go" {
			if r["confidence"] == "high" {
				goHigh = true
			}
		}
	}
	if !jsLow {
		t.Error("JS strict === true should be low confidence")
	}
	if !goHigh {
		t.Error("Go == true should be high confidence")
	}
}

func TestDuplicateBodies(t *testing.T) {
	dir := writeTree(t, map[string]string{"app/app.go": goFixture})
	idx := buildT(t, dir, DefaultBuildOptions())
	found := false
	for _, g := range DuplicateBodies(idx, 10) {
		names := map[string]bool{}
		for _, m := range g["members"].([]map[string]any) {
			names[m["name"].(string)] = true
		}
		if names["dupA"] && names["dupB"] {
			found = true
		}
	}
	if !found {
		t.Error("dupA/dupB identical bodies not grouped")
	}
}

func TestScopeExcludeAndTests(t *testing.T) {
	files := map[string]string{
		"app/app.go":      goFixture,
		"app/app_test.go": "package app\n\nfunc TestX(t *testing.T) { helperUnused(1) }\n",
		"vend/skip.go":    "package vend\n\nfunc Orphan() int { return 1 }\n",
	}
	dir := writeTree(t, files)

	// Including the test, helperUnused is referenced, so not unused.
	idxAll := buildT(t, dir, DefaultBuildOptions())
	for _, u := range UnusedSymbols(idxAll, true) {
		if u.Name == "helperUnused" {
			t.Error("helperUnused should not be unused when its test is indexed")
		}
	}
	// Excluding tests, it becomes unused (test-only production code).
	noTests := DefaultBuildOptions()
	noTests.IncludeTests = false
	idxNoTests := buildT(t, dir, noTests)
	sawHelper := false
	for _, u := range UnusedSymbols(idxNoTests, true) {
		if u.Name == "helperUnused" {
			sawHelper = true
		}
	}
	if !sawHelper {
		t.Error("helperUnused should be unused once tests are excluded")
	}

	// Exclude drops a whole subtree.
	excl := DefaultBuildOptions()
	excl.Exclude = []string{"vend/**"}
	idxExcl := buildT(t, dir, excl)
	if len(idxExcl.defs["Orphan"]) != 0 {
		t.Error("vend/** should have been excluded")
	}
}

func TestUnusedImport(t *testing.T) {
	dir := writeTree(t, map[string]string{
		"app/imp.go": "package app\n\nimport (\n\t\"fmt\"\n\t\"strings\"\n)\n\nfunc use() { fmt.Println(\"x\") }\n",
	})
	idx := buildT(t, dir, DefaultBuildOptions())
	got := UnusedImports(idx)
	if len(got) != 1 || got[0]["name"] != "strings" {
		t.Errorf("unused_imports = %v, want one entry for strings", got)
	}
}

func TestGoImportName(t *testing.T) {
	cases := []struct {
		path string
		name string
		ok   bool
	}{
		{"context", "context", true},
		{"math/rand/v2", "rand", true},
		{"go.yaml.in/yaml/v3", "yaml", true},
		{"gopkg.in/yaml.v3", "yaml", true},
		{"github.com/go-git/go-git/v5", "git", true},
		{"github.com/sethvargo/go-envconfig", "envconfig", true},
		{"github.com/nats-io/nats.go", "nats", true},
		{"github.com/imjasonh/playground/palette-swap", "", false}, // package name diverges
	}
	for _, c := range cases {
		got, ok := goImportName(c.path)
		if ok != c.ok || (ok && got != c.name) {
			t.Errorf("goImportName(%q) = (%q,%v), want (%q,%v)", c.path, got, ok, c.name, c.ok)
		}
	}
}

func TestTypeOnlyImportNotUnused(t *testing.T) {
	// context is used only in a type position (context.Context), which parses as
	// package_identifier, not identifier. It must not be flagged unused.
	dir := writeTree(t, map[string]string{
		"app/imp.go": "package app\n\nimport (\n\t\"context\"\n)\n\nfunc use(ctx context.Context) {}\n",
	})
	idx := buildT(t, dir, DefaultBuildOptions())
	for _, r := range UnusedImports(idx) {
		if r["name"] == "context" {
			t.Error("context used as a type was wrongly flagged unused")
		}
	}
}

func TestBuildMergesFilesInWalkOrder(t *testing.T) {
	files := map[string]string{
		"app/main.go":   "package app\n\nfunc main() { a() }\n",
		"app/a.go":      "package app\n\nfunc a() { b() }\n",
		"app/b.go":      "package app\n\nfunc b() {}\n",
		"app/orphan.go": "package app\n\nfunc orphan() { leaf() }\n",
		"app/z.go":      "package app\n\nfunc leaf() {}\n",
	}
	for i := range 20 {
		files[filepath.Join("pad", string(rune('a'+i))+".go")] = "package pad\n\nfunc main() { pad() }\n\nfunc pad() {}\n"
	}
	dir := writeTree(t, files)
	idx := buildT(t, dir, DefaultBuildOptions())

	if got, want := len(idx.defsByID), idx.nextID; got != want {
		t.Fatalf("defsByID has %d entries, nextID = %d", got, want)
	}
	for id, d := range idx.defsByID {
		if d.ID != id {
			t.Errorf("defsByID[%d] holds def %d (%s)", id, d.ID, d.Name)
		}
	}
	// IDs follow walk order: app/ sorts before pad/, and a.go before b.go.
	if a, b := idx.defs["a"][0].ID, idx.defs["b"][0].ID; a >= b {
		t.Errorf("a has ID %d, b has ID %d; want walk order", a, b)
	}

	// Reachability crosses files only when caller IDs survive the merge.
	dead := map[string]bool{}
	for _, d := range DeadCode(idx) {
		dead[d.Name] = true
	}
	for _, name := range []string{"a", "b", "pad"} {
		if dead[name] {
			t.Errorf("%s is reachable from main but reported dead", name)
		}
	}
	for _, name := range []string{"orphan", "leaf"} {
		if !dead[name] {
			t.Errorf("%s is unreachable but not reported dead", name)
		}
	}
	if got := len(idx.calls["pad"]); got != 20 {
		t.Errorf("%d calls to pad, want 20", got)
	}
}

func TestMergeChunksMatchesMergeFiles(t *testing.T) {
	files := map[string]string{
		"app/app.go":    goFixture,
		"app/main.go":   "package app\n\nfunc main() { a(1); mkThing() }\n",
		"app/a.go":      "package app\n\nfunc a(n int) { b(n) }\n",
		"app/b.go":      "package app\n\nfunc b(n int) {\n\tif false {\n\t\tleaf()\n\t}\n}\n",
		"app/orphan.go": "package app\n\nfunc orphan() { leaf() } // pasta:ignore unused\n",
		"app/z.go":      "package app\n\nfunc leaf() {}\n",
		"lib/lib.js":    "function helper(x) { return x }\nhelper(1)\nhelper(1)\n",
	}
	dir := writeTree(t, files)
	var cands []candidate
	for rel := range files {
		p := filepath.Join(dir, rel)
		cands = appendCandidate(cands, p, dir, nil, DefaultBuildOptions())
	}
	sort.Slice(cands, func(i, j int) bool { return cands[i].rel < cands[j].rel })

	build := func(chunk int) *Index {
		idx := newIndex()
		for i := 0; i < len(cands); i += chunk {
			c := newIndex()
			for _, cand := range cands[i:min(i+chunk, len(cands))] {
				c.merge(indexFile(t.Context(), cand, DefaultBuildOptions()))
			}
			idx.merge(c)
		}
		return idx
	}
	want := build(1)
	for _, chunk := range []int{2, 3, len(cands)} {
		got := build(chunk)
		if w, g := Report(want), Report(got); !reflect.DeepEqual(w, g) {
			t.Errorf("chunk %d: Report = %v, want %v", chunk, g, w)
		}
		if w, g := DeadCode(want), DeadCode(got); !reflect.DeepEqual(w, g) {
			t.Errorf("chunk %d: DeadCode = %v, want %v", chunk, g, w)
		}
	}
}

func TestBuildCountsFileOnceUnderRootThatAcceptsIt(t *testing.T) {
	// Under dir the file is in tests/, so it's a test; under tests/app it isn't.
	dir := writeTree(t, map[string]string{"tests/app/app.go": goFixture})
	opts := DefaultBuildOptions()
	opts.IncludeTests = false
	idx, err := Build(t.Context(), []string{dir, filepath.Join(dir, "tests", "app")}, opts)
	if err != nil {
		t.Fatal(err)
	}
	if idx.files != 1 || len(idx.defs["mkThing"]) != 1 {
		t.Errorf("files = %d, mkThing defs = %d; want 1 and 1", idx.files, len(idx.defs["mkThing"]))
	}
}

func TestBuildCountsFileOnceAcrossRoots(t *testing.T) {
	dir := writeTree(t, map[string]string{"app/app.go": goFixture})
	idx, err := Build(t.Context(), []string{dir, filepath.Join(dir, "app")}, DefaultBuildOptions())
	if err != nil {
		t.Fatal(err)
	}
	if idx.files != 1 || len(idx.defs["mkThing"]) != 1 {
		t.Errorf("files = %d, mkThing defs = %d; want 1 and 1", idx.files, len(idx.defs["mkThing"]))
	}
}

func TestFindNodes(t *testing.T) {
	dir := writeTree(t, map[string]string{"app/app.go": goFixture})
	res, err := FindNodes(t.Context(), []string{dir}, "go", "if_statement", "", 50)
	if err != nil {
		t.Fatal(err)
	}
	if res["count"].(int) < 2 {
		t.Errorf("find_nodes if_statement count = %v, want >= 2", res["count"])
	}
}
