package factstore_test

import (
	"testing"

	"github.com/imjasonh/playground/pasta/internal/factstore"
	"github.com/imjasonh/playground/pasta/internal/lang"
	"github.com/imjasonh/playground/pasta/internal/tsutil"
)

// file is a parsed source file.
type file struct {
	root tsutil.Node
}

func parse(t *testing.T, language, fileID, src string) file {
	t.Helper()
	l, ok := lang.All[language]
	if !ok {
		t.Fatalf("no language %q", language)
	}
	tree, root, err := tsutil.Parse(t.Context(), l.GetLanguage(), []byte(src), fileID)
	if err != nil {
		t.Fatal(err)
	}
	t.Cleanup(tree.Release)
	return file{root: root}
}

// ident returns the nth (from 0) identifier-like node with the given text.
func (f file) ident(t *testing.T, text string, nth int) tsutil.Node {
	t.Helper()
	var found []tsutil.Node
	tsutil.Walk(f.root, func(n tsutil.Node) bool {
		switch n.Type() {
		case "identifier", "field_identifier", "property_identifier":
			if n.Text() == text {
				found = append(found, n)
			}
		}
		return true
	})
	if nth >= len(found) {
		t.Fatalf("found %d identifiers %q, want more than %d", len(found), text, nth)
	}
	return found[nth]
}

func TestLocalDefinitionShadowsRemoteFact(t *testing.T) {
	s := factstore.New()
	app := parse(t, "go", "app/helper.go", "package app\n\nfunc writeFile(name string) error { return nil }\n")
	client := parse(t, "go", "client/config_test.go",
		"package client\n\nfunc writeFile(t T, name string) {}\n\nfunc TestX(t T) { writeFile(t, \"x\") }\n")
	s.Define(app.ident(t, "writeFile", 0))
	s.Define(client.ident(t, "writeFile", 0))
	s.Emit("returns_error", app.ident(t, "writeFile", 0), nil)

	if s.Has(client.ident(t, "writeFile", 1), "returns_error") {
		t.Error("a call binds to the error-returning writeFile in another package, not the one in its own file")
	}

	caller := parse(t, "go", "app/save.go", "package app\n\nfunc save() { writeFile(\"x\") }\n")
	if !s.Has(caller.ident(t, "writeFile", 0), "returns_error") {
		t.Error("a call in package app doesn't bind to app's error-returning writeFile")
	}
}

func TestFactOnAnyDefinitionWhenNoneIsLocal(t *testing.T) {
	s := factstore.New()
	api := parse(t, "go", "api/api.go", "package api\n\nfunc mayFail() error { return nil }\n")
	s.Define(api.ident(t, "mayFail", 0))
	s.Emit("returns_error", api.ident(t, "mayFail", 0), nil)

	caller := parse(t, "go", "cmd/main.go", "package main\n\nfunc main() { mayFail() }\n")
	if !s.Has(caller.ident(t, "mayFail", 0), "returns_error") {
		t.Error("a call with no nearer definition doesn't see the fact on the only definition")
	}
}

func TestDefinitionsInOtherLanguagesDontShadow(t *testing.T) {
	s := factstore.New()
	goDef := parse(t, "go", "api/api.go", "package api\n\nfunc writeFile() error { return nil }\n")
	pyDef := parse(t, "python", "cmd/tool.py", "def writeFile():\n    pass\n")
	s.Define(goDef.ident(t, "writeFile", 0))
	s.Define(pyDef.ident(t, "writeFile", 0))
	s.Emit("returns_error", goDef.ident(t, "writeFile", 0), nil)

	caller := parse(t, "go", "cmd/main.go", "package main\n\nfunc main() { writeFile() }\n")
	if !s.Has(caller.ident(t, "writeFile", 0), "returns_error") {
		t.Error("a Python definition in the caller's directory shadows the Go definition")
	}
}

func TestTestFilesPreferTestDefinitions(t *testing.T) {
	s := factstore.New()
	// Two definitions in one directory are equally near, so whether the
	// caller is a test file decides.
	testHelper := parse(t, "go", "pkg/helpers_test.go", "package pkg\n\nfunc load() error { return nil }\n")
	prod := parse(t, "go", "pkg/load.go", "package pkg\n\nfunc load() {}\n")
	s.Define(testHelper.ident(t, "load", 0))
	s.Define(prod.ident(t, "load", 0))
	s.Emit("returns_error", testHelper.ident(t, "load", 0), nil)

	testCaller := parse(t, "go", "pkg/pkg_test.go", "package pkg\n\nfunc TestLoad() { load() }\n")
	if !s.Has(testCaller.ident(t, "load", 0), "returns_error") {
		t.Error("a test file doesn't bind to the test helper")
	}
	prodCaller := parse(t, "go", "pkg/use.go", "package pkg\n\nfunc use() { load() }\n")
	if s.Has(prodCaller.ident(t, "load", 0), "returns_error") {
		t.Error("a non-test file binds to the test helper instead of the non-test definition")
	}
}

func TestFactsOnVariablesMatchByName(t *testing.T) {
	s := factstore.New()
	// A function named data elsewhere doesn't stop a fact on a variable
	// named data from matching other uses of the name.
	fn := parse(t, "python", "lib/data.py", "def data():\n    pass\n")
	src := parse(t, "python", "app/view.py", "data = request.args\nprint(data)\n")
	s.Define(fn.ident(t, "data", 0))
	s.Emit("tainted", src.ident(t, "data", 0), nil)

	if !s.Has(src.ident(t, "data", 1), "tainted") {
		t.Error("a fact on a variable doesn't match a later use of its name")
	}
}

func TestGetIsDeterministic(t *testing.T) {
	// Two definitions in sibling directories are equally near to the
	// caller; the file ID breaks the tie whatever the emission order.
	for _, order := range [][]string{{"a/x.go", "b/x.go"}, {"b/x.go", "a/x.go"}} {
		s := factstore.New()
		files := map[string]file{}
		for _, id := range order {
			f := parse(t, "go", id, "package x\n\nfunc mayFail() error { return nil }\n")
			files[id] = f
			s.Define(f.ident(t, "mayFail", 0))
			s.Emit("returns_error", f.ident(t, "mayFail", 0), map[string]any{"file": id})
		}
		caller := parse(t, "go", "c/main.go", "package main\n\nfunc main() { mayFail() }\n")
		f, ok := s.Get(caller.ident(t, "mayFail", 0), "returns_error")
		if !ok || f.Payload["file"] != "a/x.go" {
			t.Errorf("with emission order %v, Get = %v, %v; want the fact from a/x.go", order, f.Payload, ok)
		}
	}
}
