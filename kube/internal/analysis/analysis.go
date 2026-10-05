// Package analysis finds the types that a program passes to a package's
// generic functions, by type-checking the program's source with export data
// from the go command.
package analysis

import (
	"bytes"
	"context"
	"encoding/json"
	"fmt"
	"go/ast"
	"go/importer"
	"go/parser"
	"go/token"
	"go/types"
	"io"
	"maps"
	"os"
	"os/exec"
	"path/filepath"
	"reflect"
	"slices"
	"strings"
)

// Config says what to look for.
type Config struct {
	// Dir is where to run the go command: inside the program's module.
	Dir string
	// Env is the go command's environment. GOOS, GOARCH, and CGO_ENABLED
	// decide which files are part of the program.
	Env []string
	// Pattern names the program's main package.
	Pattern string
	// Package is the import path of the package that declares Funcs.
	Package string
	// Funcs are the names of generic functions whose first type argument
	// to report.
	Funcs []string
	// Marker is a struct type in Package. Find reports the tag of the field
	// through which a type argument embeds it.
	Marker string
}

// A Use is a call of one of Funcs with a type argument.
type Use struct {
	// Func is the function's name, such as "Get".
	Func string
	// Type is the type argument, such as "example.com/app.Widget", and Name
	// is its name without the package, such as "Widget".
	Type, Name string
	// Tag is the struct tag of the field that embeds Marker.
	Tag string
	// Fields are the names in the json tags of the type's exported fields,
	// other than the field that embeds Marker.
	Fields []string
	// Pos is where the call is.
	Pos string
}

type listedPackage struct {
	ImportPath string
	Dir        string
	GoFiles    []string
	Export     string
	Standard   bool
	ImportMap  map[string]string
	Imports    []string
	Error      *struct{ Err string }
}

// Find type-checks the packages of the program that import Package,
// directly or through each other, and returns each call of one of Funcs
// whose type argument embeds Marker. A call inside a generic function
// counts once for each type that the function is instantiated with
// anywhere in those packages. Find also returns the calls of Funcs whose
// type arguments it can't tell, with only Func and Pos set. Pos is where
// the program passes a type argument that Find can't tell, which can be a
// call of a generic function that passes it on to one of Funcs.
func Find(ctx context.Context, cfg Config) (uses, unresolved []Use, err error) {
	cmd := exec.CommandContext(ctx, "go", "list", "-deps", "-export", "-json=ImportPath,Dir,GoFiles,Export,Standard,ImportMap,Imports,Error", "--", cfg.Pattern) // #nosec G204 -- the go command with a package pattern.
	cmd.Dir, cmd.Env = cfg.Dir, cfg.Env
	var stderr bytes.Buffer
	cmd.Stderr = &stderr
	out, err := cmd.Output()
	if err != nil {
		return nil, nil, fmt.Errorf("analysis: go list %s: %w\n%s", cfg.Pattern, err, stderr.String())
	}
	var pkgs []*listedPackage
	exports := map[string]string{}
	dec := json.NewDecoder(bytes.NewReader(out))
	for dec.More() {
		p := &listedPackage{}
		if err := dec.Decode(p); err != nil {
			return nil, nil, fmt.Errorf("analysis: decoding go list output: %w", err)
		}
		if p.Error != nil {
			return nil, nil, fmt.Errorf("analysis: %s: %s", p.ImportPath, p.Error.Err)
		}
		pkgs = append(pkgs, p)
		exports[p.ImportPath] = p.Export
	}

	// The packages to check are those through which the program reaches
	// Package.
	reaches := map[string]bool{cfg.Package: true}
	for changed := true; changed; {
		changed = false
		for _, p := range pkgs {
			if reaches[p.ImportPath] || p.Standard {
				continue
			}
			for _, imp := range p.Imports {
				if reaches[imp] {
					reaches[p.ImportPath], changed = true, true
					break
				}
			}
		}
	}
	a := &analyzer{
		cfg:      cfg,
		exports:  exports,
		edges:    map[node][]node{},
		concrete: map[node]map[string]typeArg{},
	}
	for _, p := range pkgs {
		if reaches[p.ImportPath] && p.ImportPath != cfg.Package {
			if err := a.check(p); err != nil {
				return nil, nil, err
			}
		}
	}
	uses, unresolved = a.uses()
	return uses, unresolved, nil
}

// A node is a type parameter of a generic function: the function's full
// name and the parameter's index.
type node struct {
	fn    string
	index int
}

// A typeArg is a type that a type parameter is instantiated with, and
// where. A nil t is a type argument that Find can't tell.
type typeArg struct {
	t   types.Type
	pos string
}

// key tells type arguments apart: by type, or, for one that Find can't
// tell, by where it is. No type string starts with "?".
func (t typeArg) key() string {
	if t.t == nil {
		return "?" + t.pos
	}
	return types.TypeString(t.t, nil)
}

type analyzer struct {
	cfg     Config
	exports map[string]string
	// edges lead from a type parameter of a generic function to the type
	// parameters of the functions it passes it to.
	edges map[node][]node
	// concrete holds the types that each type parameter is instantiated
	// with, by key.
	concrete map[node]map[string]typeArg
}

func (a *analyzer) check(p *listedPackage) error {
	fset := token.NewFileSet()
	var files []*ast.File
	for _, name := range p.GoFiles {
		f, err := parser.ParseFile(fset, filepath.Join(p.Dir, name), nil, parser.SkipObjectResolution)
		if err != nil {
			return fmt.Errorf("analysis: %w", err)
		}
		files = append(files, f)
	}
	conf := types.Config{
		Importer: importer.ForCompiler(fset, "gc", func(path string) (io.ReadCloser, error) {
			if mapped, ok := p.ImportMap[path]; ok {
				path = mapped
			}
			if a.exports[path] == "" {
				return nil, fmt.Errorf("no export data for %s", path)
			}
			return os.Open(a.exports[path])
		}),
	}
	info := &types.Info{
		Instances: map[*ast.Ident]types.Instance{},
		Uses:      map[*ast.Ident]types.Object{},
		Defs:      map[*ast.Ident]types.Object{},
	}
	if _, err := conf.Check(p.ImportPath, fset, files, info); err != nil {
		return fmt.Errorf("analysis: type-checking %s: %w", p.ImportPath, err)
	}
	// Each generic function declaration, to find whose type parameter a
	// type argument is.
	var decls []*ast.FuncDecl
	for _, f := range files {
		for _, d := range f.Decls {
			if fd, ok := d.(*ast.FuncDecl); ok {
				decls = append(decls, fd)
			}
		}
	}
	enclosing := func(pos token.Pos) *types.Func {
		for _, d := range decls {
			if d.Pos() <= pos && pos < d.End() {
				fn, _ := info.Defs[d.Name].(*types.Func)
				return fn
			}
		}
		return nil
	}
	ids := slices.SortedFunc(maps.Keys(info.Instances), func(x, y *ast.Ident) int { return int(x.Pos() - y.Pos()) })
	for _, id := range ids {
		inst := info.Instances[id]
		fn, ok := info.Uses[id].(*types.Func)
		if !ok || fn.Pkg() == nil {
			continue
		}
		target := fn.Pkg().Path() == a.cfg.Package && slices.Contains(a.cfg.Funcs, fn.Name())
		if fn.Pkg().Path() == a.cfg.Package && !target {
			continue
		}
		pos := fset.Position(id.Pos()).String()
		for j := range inst.TypeArgs.Len() {
			if target && j > 0 {
				break
			}
			to := node{fn.FullName(), j}
			arg := inst.TypeArgs.At(j)
			if tp, ok := arg.(*types.TypeParam); ok {
				if g := enclosing(id.Pos()); g != nil && ownsTypeParam(g, tp) {
					from := node{g.FullName(), tp.Index()}
					a.edges[from] = append(a.edges[from], to)
					continue
				}
			}
			if hasTypeParam(arg) {
				// A type parameter that the enclosing function doesn't
				// declare belongs to a method's generic receiver type,
				// whose instantiations Find doesn't follow. Find also
				// doesn't substitute types into one such as Item[T].
				arg = nil
			}
			a.add(to, typeArg{arg, pos})
		}
	}
	return nil
}

func ownsTypeParam(fn *types.Func, tp *types.TypeParam) bool {
	tps := fn.Signature().TypeParams()
	for i := range tps.Len() {
		if tps.At(i) == tp {
			return true
		}
	}
	return false
}

// hasTypeParam reports whether t mentions a type parameter.
func hasTypeParam(t types.Type) bool {
	switch t := types.Unalias(t).(type) {
	case *types.TypeParam:
		return true
	case *types.Pointer:
		return hasTypeParam(t.Elem())
	case *types.Slice:
		return hasTypeParam(t.Elem())
	case *types.Array:
		return hasTypeParam(t.Elem())
	case *types.Map:
		return hasTypeParam(t.Key()) || hasTypeParam(t.Elem())
	case *types.Chan:
		return hasTypeParam(t.Elem())
	case *types.Named:
		args := t.TypeArgs()
		for i := range args.Len() {
			if hasTypeParam(args.At(i)) {
				return true
			}
		}
	}
	return false
}

func (a *analyzer) add(n node, t typeArg) bool {
	key := t.key()
	if _, ok := a.concrete[n][key]; ok {
		return false
	}
	if a.concrete[n] == nil {
		a.concrete[n] = map[string]typeArg{}
	}
	a.concrete[n][key] = t
	return true
}

// uses follows the edges from each instantiated type parameter, then
// reports the types that reach Funcs, and the type arguments that Find
// can't tell that reach them.
func (a *analyzer) uses() (uses, unresolved []Use) {
	queue := slices.Collect(maps.Keys(a.concrete))
	for len(queue) > 0 {
		n := queue[0]
		queue = queue[1:]
		for _, to := range a.edges[n] {
			changed := false
			for _, t := range a.concrete[n] {
				changed = a.add(to, t) || changed
			}
			if changed {
				queue = append(queue, to)
			}
		}
	}
	for _, f := range a.cfg.Funcs {
		args := a.concrete[node{a.cfg.Package + "." + f, 0}]
		for _, key := range slices.Sorted(maps.Keys(args)) {
			t := args[key]
			if t.t == nil {
				unresolved = append(unresolved, Use{Func: f, Pos: t.pos})
				continue
			}
			if u, ok := a.use(f, t); ok {
				uses = append(uses, u)
			}
		}
	}
	return uses, unresolved
}

// use describes a call of f with type argument t, if t embeds Marker.
func (a *analyzer) use(f string, t typeArg) (Use, bool) {
	named, ok := types.Unalias(t.t).(*types.Named)
	if !ok {
		return Use{}, false
	}
	st, ok := named.Underlying().(*types.Struct)
	if !ok {
		return Use{}, false
	}
	for i := range st.NumFields() {
		field := st.Field(i)
		if !field.Embedded() {
			continue
		}
		ft, ok := types.Unalias(field.Type()).(*types.Named)
		if ok && ft.Obj().Pkg() != nil && ft.Obj().Pkg().Path() == a.cfg.Package && ft.Obj().Name() == a.cfg.Marker {
			return Use{Func: f, Type: types.TypeString(named, nil), Name: named.Obj().Name(), Tag: st.Tag(i), Fields: jsonFields(st, i), Pos: t.pos}, true
		}
	}
	return Use{}, false
}

// jsonFields returns the names in the json tags of st's exported fields,
// other than field skip.
func jsonFields(st *types.Struct, skip int) []string {
	var out []string
	for i := range st.NumFields() {
		name, _, _ := strings.Cut(reflect.StructTag(st.Tag(i)).Get("json"), ",")
		if i == skip || !st.Field(i).Exported() || name == "" || name == "-" {
			continue
		}
		out = append(out, name)
	}
	return out
}

// String formats a use for messages.
func (u Use) String() string {
	return fmt.Sprintf("%s[%s] at %s", u.Func, strings.TrimPrefix(u.Type, "*"), u.Pos)
}
