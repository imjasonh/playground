package gitk8s

import (
	"errors"
	"fmt"
	"strconv"
	"strings"
)

// GateCheck is what a merge gate sees of one check.
type GateCheck struct {
	Passed  bool
	State   string
	Outputs map[string]string
}

// GateChecks returns what a merge gate sees of the checks that policy lists,
// for a branch at head whose parent is at parentHead. A check without a
// fresh result has state Pending.
func GateChecks(policy *MergePolicy, results map[string]CheckResult, head, parentHead string) map[string]GateCheck {
	out := map[string]GateCheck{}
	if policy == nil {
		return out
	}
	for _, c := range policy.Checks {
		r, ok := results[c.Name]
		if !ok || !r.Fresh(head, parentHead) {
			out[c.Name] = GateCheck{State: Pending}
			continue
		}
		out[c.Name] = GateCheck{Passed: r.State == Passed, State: r.State, Outputs: r.Outputs}
	}
	return out
}

// Gate is a parsed MergePolicy.When expression.
//
// The language is a subset of CEL. It has the checks variable, string
// literals in single or double quotes, true and false, field selection
// (checks.gofmt.passed), indexing with a string (checks["my-check"]), the
// has() macro, ==, !=, !, &&, ||, and parentheses. As in CEL, && and || give
// a result when one side decides it even if the other side is an error, so
// checks.risk.outputs.level == "low" || checks.approval.passed is true for an
// approved branch whose risk check hasn't reported a level yet.
type Gate struct {
	root node
}

// ParseGate parses a merge gate expression.
func ParseGate(src string) (*Gate, error) {
	p := &parser{src: src}
	if err := p.lex(); err != nil {
		return nil, err
	}
	n, err := p.expr()
	if err != nil {
		return nil, err
	}
	if p.pos < len(p.toks) {
		return nil, fmt.Errorf("unexpected %q at offset %d", p.toks[p.pos].text, p.toks[p.pos].off)
	}
	return &Gate{root: n}, nil
}

// Eval evaluates the gate. It returns an error if the expression reads a
// field that doesn't exist or mixes types, unless && or || decides the
// result without that part.
func (g *Gate) Eval(checks map[string]GateCheck) (bool, error) {
	vars := map[string]any{}
	for name, c := range checks {
		outputs := map[string]any{}
		for k, v := range c.Outputs {
			outputs[k] = v
		}
		vars[name] = map[string]any{"passed": c.Passed, "state": c.State, "outputs": outputs}
	}
	v, err := g.root.eval(map[string]any{"checks": vars})
	if err != nil {
		return false, err
	}
	b, ok := v.(bool)
	if !ok {
		return false, fmt.Errorf("expression is a %s, not a bool", typeName(v))
	}
	return b, nil
}

type tokKind int

const (
	tIdent tokKind = iota
	tString
	tOp
)

type token struct {
	kind tokKind
	text string
	off  int
}

type parser struct {
	src  string
	toks []token
	pos  int
}

func (p *parser) lex() error {
	s := p.src
	for i := 0; i < len(s); {
		c := s[i]
		switch {
		case c == ' ' || c == '\t' || c == '\n' || c == '\r':
			i++
		case c == '_' || c >= 'a' && c <= 'z' || c >= 'A' && c <= 'Z':
			j := i + 1
			for j < len(s) && (s[j] == '_' || s[j] >= 'a' && s[j] <= 'z' || s[j] >= 'A' && s[j] <= 'Z' || s[j] >= '0' && s[j] <= '9') {
				j++
			}
			p.toks = append(p.toks, token{tIdent, s[i:j], i})
			i = j
		case c == '"' || c == '\'':
			j := i + 1
			for j < len(s) && s[j] != c {
				if s[j] == '\\' {
					j++
				}
				j++
			}
			if j >= len(s) {
				return fmt.Errorf("unterminated string at offset %d", i)
			}
			lit := s[i : j+1]
			if c == '\'' {
				lit = `"` + strings.ReplaceAll(strings.ReplaceAll(lit[1:len(lit)-1], `"`, `\"`), `\'`, `'`) + `"`
			}
			text, err := strconv.Unquote(lit)
			if err != nil {
				return fmt.Errorf("bad string at offset %d: %w", i, err)
			}
			p.toks = append(p.toks, token{tString, text, i})
			i = j + 1
		default:
			two := ""
			if i+1 < len(s) {
				two = s[i : i+2]
			}
			switch {
			case two == "&&" || two == "||" || two == "==" || two == "!=":
				p.toks = append(p.toks, token{tOp, two, i})
				i += 2
			case strings.IndexByte("!().[]", c) >= 0:
				p.toks = append(p.toks, token{tOp, string(c), i})
				i++
			default:
				return fmt.Errorf("unexpected %q at offset %d", c, i)
			}
		}
	}
	return nil
}

func (p *parser) peek(text string) bool {
	return p.pos < len(p.toks) && p.toks[p.pos].kind == tOp && p.toks[p.pos].text == text
}

func (p *parser) expect(text string) error {
	if !p.peek(text) {
		return p.unexpected("expected " + strconv.Quote(text))
	}
	p.pos++
	return nil
}

func (p *parser) unexpected(want string) error {
	if p.pos >= len(p.toks) {
		return fmt.Errorf("%s at end of expression", want)
	}
	t := p.toks[p.pos]
	return fmt.Errorf("%s, got %q at offset %d", want, t.text, t.off)
}

func (p *parser) expr() (node, error) {
	left, err := p.and()
	if err != nil {
		return nil, err
	}
	for p.peek("||") {
		p.pos++
		right, err := p.and()
		if err != nil {
			return nil, err
		}
		left = orNode{left, right}
	}
	return left, nil
}

func (p *parser) and() (node, error) {
	left, err := p.unary()
	if err != nil {
		return nil, err
	}
	for p.peek("&&") {
		p.pos++
		right, err := p.unary()
		if err != nil {
			return nil, err
		}
		left = andNode{left, right}
	}
	return left, nil
}

func (p *parser) unary() (node, error) {
	if p.peek("!") {
		p.pos++
		n, err := p.unary()
		if err != nil {
			return nil, err
		}
		return notNode{n}, nil
	}
	left, err := p.term()
	if err != nil {
		return nil, err
	}
	for _, op := range []string{"==", "!="} {
		if p.peek(op) {
			p.pos++
			right, err := p.term()
			if err != nil {
				return nil, err
			}
			return cmpNode{op == "==", left, right}, nil
		}
	}
	return left, nil
}

func (p *parser) term() (node, error) {
	if p.pos >= len(p.toks) {
		return nil, p.unexpected("expected a value")
	}
	t := p.toks[p.pos]
	switch {
	case t.kind == tOp && t.text == "(":
		p.pos++
		n, err := p.expr()
		if err != nil {
			return nil, err
		}
		return n, p.expect(")")
	case t.kind == tString:
		p.pos++
		return litNode{t.text}, nil
	case t.kind == tIdent && (t.text == "true" || t.text == "false"):
		p.pos++
		return litNode{t.text == "true"}, nil
	case t.kind == tIdent && t.text == "has":
		p.pos++
		if err := p.expect("("); err != nil {
			return nil, err
		}
		sel, err := p.path()
		if err != nil {
			return nil, err
		}
		if len(sel.fields) == 0 {
			return nil, errors.New("has() needs a field selection, such as has(checks.risk.outputs.level)")
		}
		return hasNode{sel}, p.expect(")")
	case t.kind == tIdent:
		return p.path()
	}
	return nil, p.unexpected("expected a value")
}

func (p *parser) path() (pathNode, error) {
	t := p.toks[p.pos]
	if t.kind != tIdent {
		return pathNode{}, p.unexpected("expected a variable")
	}
	if t.text != "checks" {
		return pathNode{}, fmt.Errorf("unknown variable %q at offset %d; the only variable is checks", t.text, t.off)
	}
	p.pos++
	n := pathNode{root: t.text}
	for {
		switch {
		case p.peek("."):
			p.pos++
			if p.pos >= len(p.toks) || p.toks[p.pos].kind != tIdent {
				return pathNode{}, p.unexpected("expected a field name")
			}
			n.fields = append(n.fields, p.toks[p.pos].text)
			p.pos++
		case p.peek("["):
			p.pos++
			if p.pos >= len(p.toks) || p.toks[p.pos].kind != tString {
				return pathNode{}, p.unexpected("expected a string index")
			}
			n.fields = append(n.fields, p.toks[p.pos].text)
			p.pos++
			if err := p.expect("]"); err != nil {
				return pathNode{}, err
			}
		default:
			return n, nil
		}
	}
}

type node interface {
	eval(vars map[string]any) (any, error)
}

type litNode struct{ v any }

func (n litNode) eval(map[string]any) (any, error) { return n.v, nil }

type pathNode struct {
	root   string
	fields []string
}

func (n pathNode) eval(vars map[string]any) (any, error) {
	v := vars[n.root]
	for _, f := range n.fields {
		m, ok := v.(map[string]any)
		if !ok {
			return nil, fmt.Errorf("can't select %q from a %s", f, typeName(v))
		}
		if v, ok = m[f]; !ok {
			return nil, fmt.Errorf("no such key: %s", f)
		}
	}
	return v, nil
}

type hasNode struct{ sel pathNode }

func (n hasNode) eval(vars map[string]any) (any, error) {
	parent := pathNode{root: n.sel.root, fields: n.sel.fields[:len(n.sel.fields)-1]}
	v, err := parent.eval(vars)
	if err != nil {
		return nil, err
	}
	m, ok := v.(map[string]any)
	if !ok {
		return nil, fmt.Errorf("has() can't select from a %s", typeName(v))
	}
	_, ok = m[n.sel.fields[len(n.sel.fields)-1]]
	return ok, nil
}

type notNode struct{ n node }

func (n notNode) eval(vars map[string]any) (any, error) {
	v, err := n.n.eval(vars)
	if err != nil {
		return nil, err
	}
	b, ok := v.(bool)
	if !ok {
		return nil, fmt.Errorf("! needs a bool, not a %s", typeName(v))
	}
	return !b, nil
}

type cmpNode struct {
	eq          bool
	left, right node
}

func (n cmpNode) eval(vars map[string]any) (any, error) {
	l, err := n.left.eval(vars)
	if err != nil {
		return nil, err
	}
	r, err := n.right.eval(vars)
	if err != nil {
		return nil, err
	}
	switch l.(type) {
	case bool, string:
	default:
		return nil, fmt.Errorf("can't compare a %s", typeName(l))
	}
	if typeName(l) != typeName(r) {
		return nil, fmt.Errorf("can't compare a %s with a %s", typeName(l), typeName(r))
	}
	return (l == r) == n.eq, nil
}

type andNode struct{ left, right node }

func (n andNode) eval(vars map[string]any) (any, error) {
	return logic(vars, n.left, n.right, false)
}

type orNode struct{ left, right node }

func (n orNode) eval(vars map[string]any) (any, error) {
	return logic(vars, n.left, n.right, true)
}

// logic evaluates && (decider false) or || (decider true). Either side that
// evaluates to the decider decides the result, even if the other side is an
// error.
func logic(vars map[string]any, left, right node, decider bool) (any, error) {
	var errs []error
	for _, side := range []node{left, right} {
		v, err := side.eval(vars)
		if err != nil {
			errs = append(errs, err)
			continue
		}
		b, ok := v.(bool)
		if !ok {
			errs = append(errs, fmt.Errorf("&& and || need bools, not a %s", typeName(v)))
			continue
		}
		if b == decider {
			return decider, nil
		}
	}
	if len(errs) > 0 {
		return nil, errs[0]
	}
	return !decider, nil
}

func typeName(v any) string {
	switch v.(type) {
	case bool:
		return "bool"
	case string:
		return "string"
	case map[string]any:
		return "map"
	default:
		return "null"
	}
}
