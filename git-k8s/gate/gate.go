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

// Parse compiles a when expression. It checks field names and types, and
// the expression must be a bool.
func Parse(src string) (*Gate, error) {
	e, err := env()
	if err != nil {
		return nil, err
	}
	ast, iss := e.Compile(src)
	if err := iss.Err(); err != nil {
		return nil, brief(err)
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
