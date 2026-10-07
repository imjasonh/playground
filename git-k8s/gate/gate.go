// Package gate compiles and evaluates the when expressions of merge
// policies, which are CEL. Only the core program imports it, so the checks
// don't link CEL.
package gate

import (
	"errors"
	"fmt"
	"path"
	"reflect"
	"strings"
	"sync"

	"cel.dev/cel-go/cel"
	"cel.dev/cel-go/common"
	celast "cel.dev/cel-go/common/ast"
	"cel.dev/cel-go/common/operators"
	"cel.dev/cel-go/ext"

	gitk8s "github.com/imjasonh/playground/git-k8s"
)

// costLimit bounds the work of one evaluation, so that an expression that
// loops over the checks many times can't stall the merge controller.
const costLimit = 100_000

var env = sync.OnceValues(func() (*cel.Env, error) {
	t := reflect.TypeFor[gitk8s.GateCheck]()
	// cel-go names a Go type by the last element of its package path, not
	// by the package's name.
	name := path.Base(t.PkgPath()) + "." + t.Name()
	return cel.NewEnv(
		ext.NativeTypes(t, ext.ParseStructTag("json")),
		cel.Variable("checks", cel.MapType(cel.StringType, cel.ObjectType(name))),
	)
})

// Gate is a compiled when expression.
type Gate struct {
	prg cel.Program
}

// Parse compiles the when expression of a merge policy that lists checks.
// It checks field names and types, and that the expression names only
// listed checks, as in checks.gofmt or checks["go-vet"], because it sees
// no others. The expression must be a bool.
func Parse(src string, checks []gitk8s.CheckPolicy) (*Gate, error) {
	e, err := env()
	if err != nil {
		return nil, err
	}
	ast, iss := e.Compile(src)
	if err := iss.Err(); err != nil {
		err = brief(err)
		// CEL reads checks.go-vet as a subtraction, and its errors don't say
		// so.
		for _, c := range checks {
			if strings.Contains(c.Name, "-") && strings.Contains(src, "checks."+c.Name) {
				return nil, fmt.Errorf("%w; write checks[%q] for a check whose name has a hyphen", err, c.Name)
			}
		}
		return nil, err
	}
	if err := unlisted(ast, checks); err != nil {
		return nil, err
	}
	if t := ast.OutputType(); !t.IsExactType(cel.BoolType) && !t.IsExactType(cel.DynType) {
		return nil, fmt.Errorf("the expression is a %s, not a bool", t)
	}
	prg, err := e.Program(ast, cel.CostLimit(costLimit))
	if err != nil {
		return nil, err
	}
	return &Gate{prg: prg}, nil
}

// Eval evaluates the gate for the checks that a merge policy lists.
func (g *Gate) Eval(checks map[string]gitk8s.GateCheck) (bool, error) {
	out, _, err := g.prg.Eval(map[string]any{"checks": checks})
	if err != nil {
		return false, err
	}
	b, ok := out.Value().(bool)
	if !ok {
		return false, fmt.Errorf("the expression is a %s, not a bool", out.Type())
	}
	return b, nil
}

// unlisted reports each constant key that the expression looks up in
// checks, as in checks.gofmt, checks["go-vet"], has(checks.gofmt), or
// "gofmt" in checks, that isn't a listed check. Such a lookup fails or is
// false on every branch.
func unlisted(a *cel.Ast, checks []gitk8s.CheckPolicy) error {
	listed := map[string]bool{}
	for _, c := range checks {
		listed[c.Name] = true
	}
	native := a.NativeRep()
	iss := cel.NewIssuesWithSourceInfo(common.NewErrors(a.Source()), native.SourceInfo())
	celast.PreOrderVisit(native.Expr(), celast.NewExprVisitor(func(e celast.Expr) {
		if name, ok := checkKey(e); ok && !listed[name] {
			iss.ReportErrorAtID(e.ID(), "the merge policy doesn't list a check named '%s'", name)
		}
	}))
	if err := iss.Err(); err != nil {
		return brief(err)
	}
	return nil
}

// checkKey returns the key that e looks up in checks, if e is a lookup with
// a constant key.
func checkKey(e celast.Expr) (string, bool) {
	isChecks := func(e celast.Expr) bool { return e.Kind() == celast.IdentKind && e.AsIdent() == "checks" }
	switch e.Kind() {
	case celast.SelectKind:
		s := e.AsSelect()
		return s.FieldName(), isChecks(s.Operand())
	case celast.CallKind:
		c := e.AsCall()
		if len(c.Args()) != 2 {
			return "", false
		}
		var m, key celast.Expr
		switch c.FunctionName() {
		case operators.Index:
			m, key = c.Args()[0], c.Args()[1]
		case operators.In:
			key, m = c.Args()[0], c.Args()[1]
		default:
			return "", false
		}
		if !isChecks(m) || key.Kind() != celast.LiteralKind {
			return "", false
		}
		name, ok := key.AsLiteral().Value().(string)
		return name, ok
	}
	return "", false
}

// brief keeps the first line of each of CEL's compile errors, leaving out
// the lines that draw the expression and point at the error, which don't
// read well in a condition's message.
func brief(err error) error {
	var lines []string
	for line := range strings.SplitSeq(err.Error(), "\n") {
		if msg, ok := strings.CutPrefix(line, "ERROR: <input>:"); ok {
			lines = append(lines, msg)
		}
	}
	if len(lines) == 0 {
		return err
	}
	return errors.New(strings.Join(lines, "; "))
}
