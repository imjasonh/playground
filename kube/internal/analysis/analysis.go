// Package analysis finds which of a package's functions a program calls, and
// the types that it passes to the generic ones, by type-checking the
// program's source with export data from the go command.
package analysis

import (
	"bytes"
	"context"
	"encoding/json"
	"fmt"
	"go/ast"
	"go/constant"
	"go/importer"
	"go/parser"
	"go/token"
	"go/types"
	"io"
	"maps"
	"os"
	"os/exec"
	"path/filepath"
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
	// Funcs are the names of the functions to report. For a generic
	// function, Find reports each first type argument.
	Funcs []string
	// Consts maps some of Funcs that aren't generic to the index of a
	// string parameter. Find reports each constant that the program passes
	// there, and the first other reference to the function, such as a call
	// that passes a variable.
	Consts map[string]int
	// Marker is a struct type in Package. Find reports the tag of the field
	// through which a type argument embeds it.
	Marker string
}

// A Use is a call of one of Funcs, with a type argument if it's generic.
type Use struct {
	// Func is the function's name, such as "Get".
	Func string
	// Type is the type argument, such as "example.com/app.Widget", and Name
	// is its name without the package, such as "Widget". Both are empty for
	// a function that isn't generic.
	Type, Name string
	// Tag is the struct tag of the field that embeds Marker.
	Tag string
	// Constant is set for a call that passes a constant as the argument
	// that Consts names, and Value is the constant.
	Constant bool
	Value    string
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
// anywhere in those packages. For each of Funcs that isn't generic, Find
// returns the first reference to it, if those packages have one, and the
// first call with each constant that Consts asks for. Find also returns
// warnings about calls whose type arguments it can't tell.
func Find(ctx context.Context, cfg Config) ([]Use, []string, error) {
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
		calls:    map[string]string{},
		consts:   map[string]map[string]string{},
	}
	for _, p := range pkgs {
		if reaches[p.ImportPath] && p.ImportPath != cfg.Package {
			if err := a.check(p); err != nil {
				return nil, nil, err
			}
		}
	}
	return a.uses(), a.warnings, nil
}

// A node is a type parameter of a generic function: the function's full
// name and the parameter's index.
type node struct {
	fn    string
	index int
}

type typeArg struct {
	t   types.Type
	pos string
}

type analyzer struct {
	cfg     Config
	exports map[string]string
	// edges lead from a type parameter of a generic function to the type
	// parameters of the functions it passes it to.
	edges map[node][]node
	// concrete holds the types that each type parameter is instantiated
	// with, by type string.
	concrete map[node]map[string]typeArg
	// calls holds where the program first refers to each of Funcs that
	// isn't generic, other than in the calls that consts holds. consts
	// holds where the program first passes each constant to one of Consts,
	// by function and constant.
	calls    map[string]string
	consts   map[string]map[string]string
	warnings []string
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
		Types:     map[ast.Expr]types.TypeAndValue{},
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
				g := enclosing(id.Pos())
				if g == nil || !ownsTypeParam(g, tp) {
					if target {
						a.warnings = append(a.warnings, fmt.Sprintf("%s: can't tell which types %s.%s is called with", pos, fn.Pkg().Name(), fn.Name()))
					}
					continue
				}
				from := node{g.FullName(), tp.Index()}
				a.edges[from] = append(a.edges[from], to)
				continue
			}
			if hasTypeParam(arg) {
				if target {
					a.warnings = append(a.warnings, fmt.Sprintf("%s: can't tell which types %s.%s is called with", pos, fn.Pkg().Name(), fn.Name()))
				}
				continue
			}
			a.add(to, typeArg{arg, pos})
		}
	}
	// constArg holds the constant argument that Consts asks for, by the
	// called function's identifier, for calls that pass one.
	constArg := map[*ast.Ident]string{}
	for _, f := range files {
		ast.Inspect(f, func(n ast.Node) bool {
			call, ok := n.(*ast.CallExpr)
			if !ok {
				return true
			}
			var id *ast.Ident
			switch fun := ast.Unparen(call.Fun).(type) {
			case *ast.Ident:
				id = fun
			case *ast.SelectorExpr:
				id = fun.Sel
			}
			fn, ok := info.Uses[id].(*types.Func)
			if !ok || fn.Pkg() == nil || fn.Pkg().Path() != a.cfg.Package {
				return true
			}
			if i, ok := a.cfg.Consts[fn.Name()]; ok && i < len(call.Args) {
				if v := info.Types[call.Args[i]].Value; v != nil && v.Kind() == constant.String {
					constArg[id] = constant.StringVal(v)
				}
			}
			return true
		})
	}
	first := map[string]token.Pos{}
	firstConst := map[string]map[string]token.Pos{}
	for id, obj := range info.Uses {
		fn, ok := obj.(*types.Func)
		if !ok || fn.Pkg() == nil || fn.Pkg().Path() != a.cfg.Package || !slices.Contains(a.cfg.Funcs, fn.Name()) {
			continue
		}
		if sig := fn.Origin().Signature(); sig.Recv() != nil || sig.TypeParams().Len() > 0 {
			continue
		}
		if v, ok := constArg[id]; ok {
			if firstConst[fn.Name()] == nil {
				firstConst[fn.Name()] = map[string]token.Pos{}
			}
			if p, ok := firstConst[fn.Name()][v]; !ok || id.Pos() < p {
				firstConst[fn.Name()][v] = id.Pos()
			}
			continue
		}
		if p, ok := first[fn.Name()]; !ok || id.Pos() < p {
			first[fn.Name()] = id.Pos()
		}
	}
	for name, p := range first {
		if _, ok := a.calls[name]; !ok {
			a.calls[name] = fset.Position(p).String()
		}
	}
	for name, values := range firstConst {
		if a.consts[name] == nil {
			a.consts[name] = map[string]string{}
		}
		for v, p := range values {
			if _, ok := a.consts[name][v]; !ok {
				a.consts[name][v] = fset.Position(p).String()
			}
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
	key := types.TypeString(t.t, nil)
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
// reports the types that reach Funcs.
func (a *analyzer) uses() []Use {
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
	var out []Use
	for _, f := range a.cfg.Funcs {
		if pos, ok := a.calls[f]; ok {
			out = append(out, Use{Func: f, Pos: pos})
		}
		for _, v := range slices.Sorted(maps.Keys(a.consts[f])) {
			out = append(out, Use{Func: f, Constant: true, Value: v, Pos: a.consts[f][v]})
		}
		args := a.concrete[node{a.cfg.Package + "." + f, 0}]
		for _, key := range slices.Sorted(maps.Keys(args)) {
			if u, ok := a.use(f, args[key]); ok {
				out = append(out, u)
			}
		}
	}
	return out
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
			return Use{Func: f, Type: types.TypeString(named, nil), Name: named.Obj().Name(), Tag: st.Tag(i), Pos: t.pos}, true
		}
	}
	return Use{}, false
}

// String formats a use for messages.
func (u Use) String() string {
	if u.Constant {
		return fmt.Sprintf("%s(%q) at %s", u.Func, u.Value, u.Pos)
	}
	if u.Type == "" {
		return fmt.Sprintf("%s at %s", u.Func, u.Pos)
	}
	return fmt.Sprintf("%s[%s] at %s", u.Func, strings.TrimPrefix(u.Type, "*"), u.Pos)
}
