package gitk8s

import (
	"strings"
	"testing"
)

func TestGate(t *testing.T) {
	checks := map[string]GateCheck{
		"base":     {Passed: true, State: Passed},
		"gofmt":    {Passed: true, State: Passed},
		"risk":     {Passed: true, State: Passed, Outputs: map[string]string{"level": "high"}},
		"approval": {State: Failed},
		"my-check": {State: Pending},
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
		{"(checks.base.passed || checks.approval.passed) && !(checks.approval.passed)", true},
		{"has(checks.risk.outputs.level)", true},
		{"has(checks.gofmt.outputs.level)", false},
		// A side that decides the result wins over an error on the other.
		{"checks.base.passed || checks.gofmt.outputs.level == 'low'", true},
		{"checks.gofmt.outputs.level == 'low' || checks.base.passed", true},
		{"checks.approval.passed && checks.gofmt.outputs.level == 'low'", false},
		{"true", true},
	} {
		g, err := ParseGate(c.expr)
		if err != nil {
			t.Errorf("ParseGate(%q): %v", c.expr, err)
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
		{expr: "checks.base.passed &&", parseErr: "at end of expression"},
		{expr: "checks.base.passed & true", parseErr: `unexpected '&'`},
		{expr: "size(checks)", parseErr: "unknown variable"},
		{expr: "'unterminated", parseErr: "unterminated string"},
		{expr: "(checks.base.passed", parseErr: `expected ")"`},
		{expr: "checks.base.passed checks", parseErr: "unexpected"},
		{expr: "checks.nope.passed", evalErr: "no such key: nope"},
		{expr: "checks.gofmt.outputs.level == 'low'", evalErr: "no such key: level"},
		{expr: "checks.base.passed == 'true'", evalErr: "can't compare a bool with a string"},
		{expr: "checks.base", evalErr: "not a bool"},
		{expr: "checks.base.state && true", evalErr: "need bools"},
	} {
		g, err := ParseGate(c.expr)
		if c.parseErr != "" {
			if err == nil || !strings.Contains(err.Error(), c.parseErr) {
				t.Errorf("ParseGate(%q) error = %v, want %q", c.expr, err, c.parseErr)
			}
			continue
		}
		if err != nil {
			t.Errorf("ParseGate(%q): %v", c.expr, err)
			continue
		}
		checks := map[string]GateCheck{"base": {Passed: true, State: Passed}, "gofmt": {State: Pending}}
		if _, err := g.Eval(checks); err == nil || !strings.Contains(err.Error(), c.evalErr) {
			t.Errorf("Eval(%q) error = %v, want %q", c.expr, err, c.evalErr)
		}
	}
}

func TestGateChecks(t *testing.T) {
	policy := &MergePolicy{Checks: []CheckPolicy{{Name: "base"}, {Name: "gofmt"}, {Name: "risk"}}}
	results := map[string]CheckResult{
		"base":  {Commit: "h1", ParentCommit: "p0", State: Passed},
		"gofmt": {Commit: "h1", State: Passed},
		"risk":  {Commit: "h0", State: Passed},
		"other": {Commit: "h1", State: Passed},
	}
	got := GateChecks(policy, results, "h1", "p1")
	if len(got) != 3 {
		t.Fatalf("GateChecks returned %d checks, want the 3 that the policy lists", len(got))
	}
	if got["base"].State != Pending || got["risk"].State != Pending {
		t.Errorf("stale results must be Pending: %+v", got)
	}
	if !got["gofmt"].Passed {
		t.Errorf("gofmt = %+v, want passed", got["gofmt"])
	}
}
