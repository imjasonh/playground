package analysis

import (
	"os"
	"path/filepath"
	"reflect"
	"strings"
	"testing"
)

func writeModule(t *testing.T, files map[string]string) string {
	t.Helper()
	dir := t.TempDir()
	for name, body := range files {
		p := filepath.Join(dir, name)
		if err := os.MkdirAll(filepath.Dir(p), 0o750); err != nil {
			t.Fatal(err)
		}
		if err := os.WriteFile(p, []byte(body), 0o600); err != nil {
			t.Fatal(err)
		}
	}
	return dir
}

// fw is a framework package for the test modules.
const fw = `package fw

type Object struct{}

type Resource[T any] interface{ *T }

func Get[T any, P Resource[T]]() *T     { return nil }
func Own[T any, P Resource[T]](p P) P   { return p }
func Other[T any]()                     {}
`

func TestFind(t *testing.T) {
	dir := writeModule(t, map[string]string{
		"go.mod":   "module example.com/prog\n\ngo 1.26.0\n",
		"fw/fw.go": fw,
		"types/types.go": `package types

import "example.com/prog/fw"

type Widget struct {
	fw.Object ` + "`kube:\"group=example.dev\"`" + `
	Spec      struct{} ` + "`json:\"spec\"`" + `
	Status    struct{} ` + "`json:\"status,omitzero\"`" + `
	Notes     string   ` + "`json:\"-\"`" + `
	cache     string   ` + "`json:\"cache\"`" + `
}

type ConfigMap struct {
	fw.Object ` + "`kube:\"apiVersion=v1,kind=ConfigMap\"`" + `
	Data map[string]string
}

type Gizmo struct {
	fw.Object ` + "`kube:\"group=example.dev,plural=gizmoes\"`" + `
}

type Unused struct {
	fw.Object ` + "`kube:\"group=example.dev\"`" + `
}
`,
		"helpers/helpers.go": `package helpers

import "example.com/prog/fw"

func fetch[T any, P fw.Resource[T]]() *T { return fw.Get[T, P]() }

// Twice reaches fw.Get through another generic function.
func Twice[T any, P fw.Resource[T]]() { fetch[T, P](); fetch[T, P]() }
`,
		"main.go": `package main

import (
	"example.com/prog/fw"
	"example.com/prog/helpers"
	"example.com/prog/types"
)

type box[T any] struct{}

func (box[T]) get() { fw.Get[T, *T]() }

func main() {
	fw.Get[types.Widget]()
	fw.Own(&types.ConfigMap{})
	helpers.Twice[types.Gizmo]()
	fw.Other[int]()
	box[types.Unused]{}.get()
}
`,
	})
	uses, unresolved, err := Find(t.Context(), Config{
		Dir: dir, Env: append(os.Environ(), "CGO_ENABLED=0", "GOFLAGS=-mod=mod"), Pattern: "example.com/prog",
		Package: "example.com/prog/fw", Funcs: []string{"Get", "Own"}, Marker: "Object",
	})
	if err != nil {
		t.Fatal(err)
	}
	var got []string
	for _, u := range uses {
		got = append(got, u.Func+" "+u.Type+" "+u.Name+" "+u.Tag)
	}
	want := []string{
		"Get example.com/prog/types.Gizmo Gizmo kube:\"group=example.dev,plural=gizmoes\"",
		"Get example.com/prog/types.Widget Widget kube:\"group=example.dev\"",
		"Own example.com/prog/types.ConfigMap ConfigMap kube:\"apiVersion=v1,kind=ConfigMap\"",
	}
	if !reflect.DeepEqual(got, want) {
		t.Errorf("uses =\n%s\nwant\n%s", strings.Join(got, "\n"), strings.Join(want, "\n"))
	}
	if got := lines(unresolved); !reflect.DeepEqual(got, []string{"Get main.go:11"}) {
		t.Errorf("unresolved = %q", got)
	}
	if !strings.HasSuffix(uses[1].Pos, "main.go:14:5") {
		t.Errorf("position = %s", uses[1].Pos)
	}
	if got := uses[1].Fields; !reflect.DeepEqual(got, []string{"spec", "status"}) {
		t.Errorf("Widget's fields = %q, want spec and status", got)
	}
	if got := uses[2].Fields; got != nil {
		t.Errorf("ConfigMap's fields = %q, want none, because its field has no json tag", got)
	}
}

// lines describes unresolved uses by function, file, and line.
func lines(unresolved []Use) []string {
	var out []string
	for _, u := range unresolved {
		pos := filepath.Base(u.Pos)
		out = append(out, u.Func+" "+pos[:strings.LastIndex(pos, ":")])
	}
	return out
}

func TestFindUnresolved(t *testing.T) {
	dir := writeModule(t, map[string]string{
		"go.mod":   "module example.com/prog\n\ngo 1.26.0\n",
		"fw/fw.go": fw,
		"main.go": `package main

import "example.com/prog/fw"

type Widget struct {
	fw.Object ` + "`kube:\"group=example.dev\"`" + `
}

type Item[T any] struct {
	fw.Object ` + "`kube:\"group=example.dev\"`" + `
	Spec      T
}

func own[T any, P fw.Resource[T]](p P) { fw.Own[T, P](p) }

func noop[T any]() {}

type owner[T any, P fw.Resource[T]] struct{}

func (owner[T, P]) direct(p P) { fw.Own[T, P](p) }

func (owner[T, P]) helper(p P) { own[T, P](p) }

func (owner[T, P]) neither() { noop[T](); fw.Other[T]() }

func item[T any]() { own(&Item[T]{}) }

func main() {
	own(&Widget{})
	o := owner[Widget, *Widget]{}
	o.direct(&Widget{})
	o.helper(&Widget{})
	o.neither()
	item[int]()
}
`,
	})
	uses, unresolved, err := Find(t.Context(), Config{
		Dir: dir, Env: append(os.Environ(), "CGO_ENABLED=0", "GOFLAGS=-mod=mod"), Pattern: "example.com/prog",
		Package: "example.com/prog/fw", Funcs: []string{"Get", "Own"}, Marker: "Object",
	})
	if err != nil {
		t.Fatal(err)
	}
	if len(uses) != 1 || uses[0].Func != "Own" || uses[0].Type != "example.com/prog.Widget" {
		t.Errorf("uses = %q", uses)
	}
	want := []string{"Own main.go:20", "Own main.go:22", "Own main.go:26"}
	if got := lines(unresolved); !reflect.DeepEqual(got, want) {
		t.Errorf("unresolved = %q, want %q", got, want)
	}
	for _, u := range unresolved {
		if u.Type != "" || u.Name != "" || u.Tag != "" {
			t.Errorf("unresolved use %+v has a type", u)
		}
	}
}

func TestFindInExamples(t *testing.T) {
	for _, tc := range []struct {
		pkg  string
		want []string
	}{
		{"github.com/imjasonh/playground/kube/examples/replicator", []string{"List k8s.Namespace", "Fetch k8s.Secret", "Own k8s.Secret"}},
		{"github.com/imjasonh/playground/kube/examples/reloader", []string{"Get main.SecretMeta", "Get k8s.ConfigMap", "Apply main.Deployment"}},
	} {
		uses, unresolved, err := Find(t.Context(), Config{
			Dir: ".", Env: append(os.Environ(), "CGO_ENABLED=0", "GOOS=linux", "GOARCH=amd64"), Pattern: tc.pkg,
			Package: "github.com/imjasonh/playground/kube", Funcs: []string{"Get", "List", "Fetch", "Own", "Apply", "Delete"}, Marker: "Object",
		})
		if err != nil {
			t.Fatal(err)
		}
		var got []string
		for _, u := range uses {
			name := u.Type[strings.LastIndex(u.Type, "/")+1:]
			got = append(got, u.Func+" "+strings.Replace(name, tc.pkg[strings.LastIndex(tc.pkg, "/")+1:]+".", "main.", 1))
		}
		if !reflect.DeepEqual(got, tc.want) || len(unresolved) != 0 {
			t.Errorf("%s: uses = %q, unresolved = %q, want %q", tc.pkg, got, lines(unresolved), tc.want)
		}
	}
}
