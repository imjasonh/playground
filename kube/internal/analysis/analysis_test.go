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

func TestFind(t *testing.T) {
	dir := writeModule(t, map[string]string{
		"go.mod": "module example.com/prog\n\ngo 1.26.0\n",
		"fw/fw.go": `package fw

type Object struct{}

type Resource[T any] interface{ *T }

func Get[T any, P Resource[T]]() *T     { return nil }
func Own[T any, P Resource[T]](p P) P   { return p }
func Other[T any]()                     {}

func Review() {}

func Unreferenced() {}

type Client struct{}

func (Client) Request() {}
`,
		"types/types.go": `package types

import "example.com/prog/fw"

type Widget struct {
	fw.Object ` + "`kube:\"group=example.dev\"`" + `
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

// Review refers to fw.Review twice, and calls a method with the name of
// one of Funcs.
func Review() func() {
	fw.Client{}.Request()
	fw.Review()
	return fw.Review
}
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
	uses, warnings, err := Find(t.Context(), Config{
		Dir: dir, Env: append(os.Environ(), "CGO_ENABLED=0", "GOFLAGS=-mod=mod"), Pattern: "example.com/prog",
		Package: "example.com/prog/fw", Funcs: []string{"Get", "Own", "Review", "Request", "Unreferenced"}, Marker: "Object",
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
		"Review   ",
	}
	if !reflect.DeepEqual(got, want) {
		t.Errorf("uses =\n%s\nwant\n%s", strings.Join(got, "\n"), strings.Join(want, "\n"))
	}
	if len(warnings) != 1 || !strings.Contains(warnings[0], "main.go:11") || !strings.Contains(warnings[0], "fw.Get") {
		t.Errorf("warnings = %q", warnings)
	}
	if !strings.HasSuffix(uses[1].Pos, "main.go:14:5") {
		t.Errorf("position = %s", uses[1].Pos)
	}
	if len(uses) == 4 && !strings.HasSuffix(uses[3].Pos, "helpers.go:14:5") {
		t.Errorf("position of the first reference to fw.Review = %s", uses[3].Pos)
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
	uses, warnings, err := Find(t.Context(), Config{
		Dir: dir, Env: append(os.Environ(), "CGO_ENABLED=0", "GOFLAGS=-mod=mod"), Pattern: "example.com/prog",
		Package: "example.com/prog/fw", Funcs: []string{"Token", "Value", "Only"},
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
		"Token at main.go:15:5",
		`Token("literal") at main.go:11:5`,
		`Token("named") at helpers.go:7:19`,
		`Token("paren") at main.go:13:6`,
		"Value at main.go:16:10",
		`Only("") at main.go:19:5`,
		`Only("only") at main.go:18:5`,
	}
	if !reflect.DeepEqual(got, want) || len(warnings) != 0 {
		t.Errorf("uses =\n%s\nwant\n%s\nwarnings = %q", strings.Join(got, "\n"), strings.Join(want, "\n"), warnings)
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
		uses, warnings, err := Find(t.Context(), Config{
			Dir: ".", Env: append(os.Environ(), "CGO_ENABLED=0", "GOOS=linux", "GOARCH=amd64"), Pattern: tc.pkg,
			Package: "github.com/imjasonh/playground/kube", Funcs: []string{"Get", "List", "Fetch", "Own", "Apply", "Delete", "RequestToken", "ReviewToken"},
			Consts: map[string]int{"RequestToken": 1}, Marker: "Object",
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
		if !reflect.DeepEqual(got, tc.want) || len(warnings) != 0 {
			t.Errorf("%s: uses = %q, warnings = %q, want %q", tc.pkg, got, warnings, tc.want)
		}
	}
}
