package analysis

import (
	"os"
	"path/filepath"
	"reflect"
	"strconv"
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

// TestFindTags checks that Find reads the files that Tags pick, and not
// those that tags in GOFLAGS pick.
func TestFindTags(t *testing.T) {
	dir := writeModule(t, map[string]string{
		"go.mod":   "module example.com/prog\n\ngo 1.26.0\n",
		"fw/fw.go": fw,
		"main.go": `package main

import "example.com/prog/fw"

type On struct {
	fw.Object ` + "`kube:\"group=example.dev\"`" + `
}

type Off struct {
	fw.Object ` + "`kube:\"group=example.dev\"`" + `
}

func main() { get() }
`,
		"on.go": `//go:build foo

package main

import "example.com/prog/fw"

func get() { fw.Get[On]() }
`,
		"off.go": `//go:build !foo

package main

import "example.com/prog/fw"

func get() { fw.Get[Off]() }
`,
	})
	for _, tc := range []struct {
		tags    []string
		goflags string
		want    string
	}{
		{nil, "", "example.com/prog.Off"},
		{[]string{"foo"}, "", "example.com/prog.On"},
		{nil, "-tags=foo", "example.com/prog.Off"},
	} {
		uses, _, err := Find(t.Context(), Config{
			Dir: dir, Env: append(os.Environ(), "CGO_ENABLED=0", "GOFLAGS=-mod=mod "+tc.goflags), Tags: tc.tags, Pattern: "example.com/prog",
			Package: "example.com/prog/fw", Funcs: []string{"Get"}, Marker: "Object",
		})
		if err != nil {
			t.Fatal(err)
		}
		if len(uses) != 1 || uses[0].Type != tc.want {
			t.Errorf("Find with tags %q and GOFLAGS %q = %v, want a Get of %s", tc.tags, tc.goflags, uses, tc.want)
		}
	}
}

func TestFindCalls(t *testing.T) {
	dir := writeModule(t, map[string]string{
		"go.mod": "module example.com/prog\n\ngo 1.26.0\n",
		"fw/fw.go": `package fw

type Object struct{}

type Recorder struct{}

func Eventf(format string, args ...any)          {}
func (Recorder) Eventf(format string, args ...any) {}
func Unused()                                     {}
`,
		"helpers/helpers.go": `package helpers

import "example.com/prog/fw"

// Record is fw.Eventf, passed as a value.
var Record = fw.Eventf
`,
		"main.go": `package main

import (
	"example.com/prog/fw"
	"example.com/prog/helpers"
)

func main() {
	fw.Eventf("a")
	fw.Recorder{}.Eventf("b")
	helpers.Record("c")
}
`,
	})
	uses, warnings, err := Find(t.Context(), Config{
		Dir: dir, Env: append(os.Environ(), "CGO_ENABLED=0", "GOFLAGS=-mod=mod"), Pattern: "example.com/prog",
		Package: "example.com/prog/fw", Calls: []string{"Eventf", "Unused", "Missing"}, Marker: "Object",
	})
	if err != nil {
		t.Fatal(err)
	}
	var got []string
	for _, u := range uses {
		got = append(got, u.String())
	}
	if len(got) != 2 || !strings.HasPrefix(got[0], "Eventf at ") || !strings.HasSuffix(got[0], filepath.Join("helpers", "helpers.go")+":6:17") || !strings.HasSuffix(got[1], "main.go:9:5") || len(warnings) != 0 {
		t.Errorf("uses = %q, warnings = %q, want the function's two uses and not the method's", got, warnings)
	}
}

func TestFindConstants(t *testing.T) {
	dir := writeModule(t, map[string]string{
		"go.mod": "module example.com/prog\n\ngo 1.26.0\n",
		"fw/fw.go": `package fw

func Token(n int, audience string) string { return audience }
func Value(n int, audience string) string { return audience }
func Only(n int, audience string) string  { return audience }
`,
		"helpers/helpers.go": `package helpers

import "example.com/prog/fw"

const Audience = "named"

func Named() { fw.Token(1, Audience) }
`,
		"main.go": `package main

import (
	"os"

	"example.com/prog/fw"
	"example.com/prog/helpers"
)

func main() {
	fw.Token(1, "literal")
	fw.Token(2, "lit"+"eral")
	(fw.Token)(3, "paren")
	helpers.Named()
	fw.Token(4, os.Args[0])
	f := fw.Value
	f(5, "through a variable")
	fw.Only(6, "only")
	fw.Only(7, "")
}
`,
	})
	uses, unresolved, err := Find(t.Context(), Config{
		Dir: dir, Env: append(os.Environ(), "CGO_ENABLED=0", "GOFLAGS=-mod=mod"), Pattern: "example.com/prog",
		Package: "example.com/prog/fw", Calls: []string{"Token", "Value", "Only"},
		Consts: map[string]int{"Token": 1, "Value": 1, "Only": 1},
	})
	if err != nil {
		t.Fatal(err)
	}
	var got []string
	for _, u := range uses {
		u.Pos = filepath.Base(u.Pos)
		got = append(got, u.String())
	}
	want := []string{
		`Only("only") at main.go:18:5`,
		`Only("") at main.go:19:5`,
		`Token("named") at helpers.go:7:19`,
		`Token("literal") at main.go:11:5`,
		`Token("literal") at main.go:12:5`,
		`Token("paren") at main.go:13:6`,
		"Token at main.go:15:5",
		"Value at main.go:16:10",
	}
	if !reflect.DeepEqual(got, want) || len(unresolved) != 0 {
		t.Errorf("uses =\n%s\nwant\n%s\nunresolved = %q", strings.Join(got, "\n"), strings.Join(want, "\n"), lines(unresolved))
	}
}

// TestFindObjects finds the calls that pass their type argument and
// constants as the namespace and name. A call through a generic function or a
// function value, or with a namespace that isn't a constant, names no object.
func TestFindObjects(t *testing.T) {
	dir := writeModule(t, map[string]string{
		"go.mod": "module example.com/prog\n\ngo 1.26.0\n",
		"fw/fw.go": `package fw

type Object struct{}

type Resource[T any] interface{ *T }

func Fetch[T any, P Resource[T]](namespace, name string) *T { return nil }
`,
		"types/types.go": `package types

import "example.com/prog/fw"

type ConfigMap struct{ fw.Object }

type Secret struct{ fw.Object }
`,
		"helpers/helpers.go": `package helpers

import "example.com/prog/fw"

const Namespace = "ns"

// Fetch passes constants, but not a type, to fw.Fetch.
func Fetch[T any, P fw.Resource[T]]() { fw.Fetch[T, P](Namespace, "helper") }
`,
		"main.go": `package main

import (
	"os"

	"example.com/prog/fw"
	"example.com/prog/helpers"
	"example.com/prog/types"
)

func main() {
	fw.Fetch[types.ConfigMap]("ns", "name")
	fw.Fetch[types.ConfigMap]("ns", "name")
	fw.Fetch[types.ConfigMap](helpers.Namespace, "other")
	(fw.Fetch[types.ConfigMap, *types.ConfigMap])("ns", "paren")
	fw.Fetch[types.ConfigMap](os.Args[0], "name")
	f := fw.Fetch[types.ConfigMap]
	f("ns", "value")
	helpers.Fetch[types.Secret]()
}
`,
	})
	uses, unresolved, err := Find(t.Context(), Config{
		Dir: dir, Env: append(os.Environ(), "CGO_ENABLED=0", "GOFLAGS=-mod=mod"), Pattern: "example.com/prog",
		Package: "example.com/prog/fw", Funcs: []string{"Fetch"}, Objects: map[string]int{"Fetch": 0}, Marker: "Object",
	})
	if err != nil {
		t.Fatal(err)
	}
	var got []string
	for _, u := range uses {
		u.Pos = filepath.Base(u.Pos)
		got = append(got, u.String())
	}
	want := []string{
		"Fetch[example.com/prog/types.ConfigMap] at main.go:16:5",
		`Fetch[example.com/prog/types.ConfigMap]("ns", "name") at main.go:12:5`,
		`Fetch[example.com/prog/types.ConfigMap]("ns", "other") at main.go:14:5`,
		`Fetch[example.com/prog/types.ConfigMap]("ns", "paren") at main.go:15:6`,
		"Fetch[example.com/prog/types.Secret] at main.go:19:10",
	}
	if !reflect.DeepEqual(got, want) || len(unresolved) != 0 {
		t.Errorf("uses =\n%s\nwant\n%s\nunresolved = %q", strings.Join(got, "\n"), strings.Join(want, "\n"), lines(unresolved))
	}
}

func TestFindInExamples(t *testing.T) {
	for _, tc := range []struct {
		pkg  string
		want []string
	}{
		{"github.com/imjasonh/playground/kube/examples/replicator", []string{"List k8s.Namespace", "Fetch k8s.Secret", "Own k8s.Secret"}},
		{"github.com/imjasonh/playground/kube/examples/reloader", []string{"Get main.SecretMeta", "Get k8s.ConfigMap", "Apply main.Deployment"}},
		{"github.com/imjasonh/playground/kube/examples/probe", []string{"Get main.Probe", `RequestToken "probe"`, "ReviewToken"}},
	} {
		uses, unresolved, err := Find(t.Context(), Config{
			Dir: ".", Env: append(os.Environ(), "CGO_ENABLED=0", "GOOS=linux", "GOARCH=amd64"), Pattern: tc.pkg,
			Package: "github.com/imjasonh/playground/kube", Funcs: []string{"Get", "List", "Fetch", "Own", "Apply", "Delete"},
			Calls: []string{"Eventf", "RequestToken", "ReviewToken"}, Consts: map[string]int{"RequestToken": 1}, Marker: "Object",
		})
		if err != nil {
			t.Fatal(err)
		}
		var got []string
		for _, u := range uses {
			if u.Constant {
				got = append(got, u.Func+" "+strconv.Quote(u.Value))
				continue
			}
			name := u.Type[strings.LastIndex(u.Type, "/")+1:]
			got = append(got, strings.TrimSpace(u.Func+" "+strings.Replace(name, tc.pkg[strings.LastIndex(tc.pkg, "/")+1:]+".", "main.", 1)))
		}
		if !reflect.DeepEqual(got, tc.want) || len(unresolved) != 0 {
			t.Errorf("%s: uses = %q, unresolved = %q, want %q", tc.pkg, got, lines(unresolved), tc.want)
		}
	}
}
