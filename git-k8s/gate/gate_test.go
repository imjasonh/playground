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
		var listed []gitk8s.CheckPolicy
		for name := range checks {
			listed = append(listed, gitk8s.CheckPolicy{Name: name})
		}
		g, err := Parse(c.expr, listed)
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
		{expr: "checks.nope.passed", parseErr: "the merge policy doesn't list a check named 'nope'"},
		{expr: "checks.gofmt.outputs.level == 'low'", evalErr: "no such key: level"},
	} {
		g, err := Parse(c.expr, []gitk8s.CheckPolicy{{Name: "base"}, {Name: "gofmt"}})
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

// A when expression can name only the checks that its merge policy lists,
// because it sees no others.
func TestGateNamesOnlyListedChecks(t *testing.T) {
	listed := []gitk8s.CheckPolicy{{Name: "base"}, {Name: "go-vet"}}
	for _, c := range []struct{ expr, err string }{
		{"checks.base.passed && checks.gofmy.passed", "1:29: the merge policy doesn't list a check named 'gofmy'"},
		{"checks.gofmy.passed || checks.nope.passed", "1:7: the merge policy doesn't list a check named 'gofmy'; 1:30: the merge policy doesn't list a check named 'nope'"},
		{`checks["gofmy"].passed`, "doesn't list a check named 'gofmy'"},
		{"has(checks.gofmy)", "doesn't list a check named 'gofmy'"},
		{`"gofmy" in checks`, "doesn't list a check named 'gofmy'"},
		{"checks.exists(c, checks.gofmy.passed)", "doesn't list a check named 'gofmy'"},
		{"checks.go-vet.passed", `undeclared reference to 'vet' (in container ''); write checks["go-vet"] for a check whose name has a hyphen`},
	} {
		if _, err := Parse(c.expr, listed); err == nil || !strings.Contains(err.Error(), c.err) {
			t.Errorf("Parse(%q) error = %v, want %q", c.expr, err, c.err)
		}
	}
	for _, expr := range []string{
		`checks["go-vet"].passed && checks.base.passed`,
		`has(checks.base) && "go-vet" in checks`,
		"checks.all(c, checks[c].passed)",
	} {
		if _, err := Parse(expr, listed); err != nil {
			t.Errorf("Parse(%q): %v", expr, err)
		}
	}
}

func TestGateCostLimit(t *testing.T) {
	checks := map[string]gitk8s.GateCheck{}
	for i := range 20 {
		checks[fmt.Sprintf("c%d", i)] = gitk8s.GateCheck{Passed: true}
	}
	g, err := Parse("checks.all(a, checks.all(b, checks.all(c, checks.all(d, checks[d].passed))))", nil)
	if err != nil {
		t.Fatal(err)
	}
	if _, err := g.Eval(checks); err == nil || !strings.Contains(err.Error(), "cost limit exceeded") {
		t.Errorf("Eval error = %v, want the cost limit", err)
	}
}
