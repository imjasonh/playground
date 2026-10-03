package gate

import (
	"fmt"
	"strings"
	"testing"

	gitk8s "github.com/imjasonh/playground/git-k8s"
)

func TestGate(t *testing.T) {
	checks := map[string]gitk8s.GateCheck{
		"base":     {Passed: true, State: gitk8s.Passed},
		"gofmt":    {Passed: true, State: gitk8s.Passed},
		"risk":     {Passed: true, State: gitk8s.Passed, Outputs: map[string]string{"level": "high", "lines": "120"}},
		"approval": {State: gitk8s.Failed},
		"my-check": {State: gitk8s.Pending},
	}
	for _, c := range []struct {
		expr string
		want bool
	}{
		{"checks.base.passed", true},
		{"checks.base.passed && checks.gofmt.passed", true},
		{`checks.risk.outputs.level == "low" || checks.approval.passed`, false},
		{`checks.risk.outputs.level != 'low'`, true},
		{`checks["my-check"].state == "Pending"`, true},
		{"!checks.approval.passed", true},
		{"has(checks.risk.outputs.level)", true},
		{"has(checks.gofmt.outputs.level)", false},
		// A side that decides the result wins over an error on the other.
		{"checks.base.passed || checks.gofmt.outputs.level == 'low'", true},
		{"checks.gofmt.outputs.level == 'low' || checks.base.passed", true},
		{"checks.approval.passed && checks.gofmt.outputs.level == 'low'", false},
		// The rest of CEL works too.
		{"int(checks.risk.outputs.lines) < 500", true},
		{`checks.risk.outputs.level in ["low", "medium"]`, false},
		{"checks.exists(c, checks[c].state == 'Pending')", true},
		{"checks.all(c, c in ['approval', 'my-check'] || checks[c].passed)", true},
		{"size(checks) == 5", true},
	} {
		g, err := Parse(c.expr)
		if err != nil {
			t.Errorf("Parse(%q): %v", c.expr, err)
			continue
		}
		got, err := g.Eval(checks)
		if err != nil {
			t.Errorf("Eval(%q): %v", c.expr, err)
			continue
		}
		if got != c.want {
			t.Errorf("Eval(%q) = %v, want %v", c.expr, got, c.want)
		}
	}
}

func TestGateErrors(t *testing.T) {
	for _, c := range []struct{ expr, parseErr, evalErr string }{
		{expr: "checks.base.passed &&", parseErr: "Syntax error"},
		{expr: "checks.gofmt.pased", parseErr: "undefined field 'pased'"},
		{expr: "nope.passed", parseErr: "undeclared reference to 'nope'"},
		{expr: "checks.base.passed == 'true'", parseErr: "no matching overload"},
		{expr: "checks.base", parseErr: "not a bool"},
		{expr: "checks.nope.passed", evalErr: "no such key: nope"},
		{expr: "checks.gofmt.outputs.level == 'low'", evalErr: "no such key: level"},
	} {
		g, err := Parse(c.expr)
		if c.parseErr != "" {
			if err == nil || !strings.Contains(err.Error(), c.parseErr) {
				t.Errorf("Parse(%q) error = %v, want %q", c.expr, err, c.parseErr)
			}
			if err != nil && strings.Contains(err.Error(), "\n") {
				t.Errorf("Parse(%q) error has more than one line: %q", c.expr, err)
			}
			continue
		}
		if err != nil {
			t.Errorf("Parse(%q): %v", c.expr, err)
			continue
		}
		checks := map[string]gitk8s.GateCheck{"base": {Passed: true, State: gitk8s.Passed}, "gofmt": {State: gitk8s.Pending}}
		if _, err := g.Eval(checks); err == nil || !strings.Contains(err.Error(), c.evalErr) {
			t.Errorf("Eval(%q) error = %v, want %q", c.expr, err, c.evalErr)
		}
	}
}

func TestGateCostLimit(t *testing.T) {
	checks := map[string]gitk8s.GateCheck{}
	for i := range 20 {
		checks[fmt.Sprintf("c%d", i)] = gitk8s.GateCheck{Passed: true}
	}
	g, err := Parse("checks.all(a, checks.all(b, checks.all(c, checks.all(d, checks[d].passed))))")
	if err != nil {
		t.Fatal(err)
	}
	if _, err := g.Eval(checks); err == nil || !strings.Contains(err.Error(), "cost limit exceeded") {
		t.Errorf("Eval error = %v, want the cost limit", err)
	}
}
