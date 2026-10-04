package gitk8s

import (
	"reflect"
	"regexp"
	"strings"
	"testing"
)

var labelValueRE = regexp.MustCompile(`^[a-z0-9]([-a-z0-9]*[a-z0-9])?$`)

func TestBranchObjectName(t *testing.T) {
	names := []string{
		BranchObjectName("app", "main"),
		BranchObjectName("app", "c/add"),
		BranchObjectName("app", "c-add"),
		BranchObjectName("app", "C/Add"),
		BranchObjectName("app", strings.Repeat("x", 300)),
		BranchObjectName("app", "///"),
		BranchObjectName("my.repo", "feature/ünïcode"),
	}
	seen := map[string]bool{}
	for _, n := range names {
		if len(n) > 63 || !labelValueRE.MatchString(n) {
			t.Errorf("%q isn't a valid object name and label value", n)
		}
		if seen[n] {
			t.Errorf("%q appears twice", n)
		}
		seen[n] = true
	}
	if !strings.HasPrefix(names[1], "app-c-add-") {
		t.Errorf("name for c/add = %q, want prefix app-c-add-", names[1])
	}
	if names[1] != BranchObjectName("app", "c/add") {
		t.Error("BranchObjectName isn't deterministic")
	}
}

func TestFresh(t *testing.T) {
	r := &CheckResult{Commit: "h1", State: Passed}
	if !r.Fresh("h1", "p1") || !r.Fresh("h1", "p2") || r.Fresh("h2", "p1") {
		t.Error("a result without a parent commit must depend only on the head")
	}
	r.ParentCommit = "p1"
	if !r.Fresh("h1", "p1") || r.Fresh("h1", "p2") {
		t.Error("a result with a parent commit must depend on both heads")
	}
	var missing *CheckResult
	if missing.Fresh("h1", "p1") || missing.Final() {
		t.Error("a missing result is never fresh or final")
	}
}

func TestEqual(t *testing.T) {
	r := &CheckResult{Commit: "h1", State: Passed, Message: "ok", Outputs: map[string]string{"level": "low"}}
	same := &CheckResult{Commit: "h1", State: Passed, Message: "ok", Outputs: map[string]string{"level": "low"}}
	if !r.Equal(same) {
		t.Error("results with the same fields aren't equal")
	}
	for _, o := range []*CheckResult{
		nil,
		{Commit: "h2", State: Passed, Message: "ok", Outputs: map[string]string{"level": "low"}},
		{Commit: "h1", ParentCommit: "p1", State: Passed, Message: "ok", Outputs: map[string]string{"level": "low"}},
		{Commit: "h1", State: Failed, Message: "ok", Outputs: map[string]string{"level": "low"}},
		{Commit: "h1", State: Passed, Message: "fine", Outputs: map[string]string{"level": "low"}},
		{Commit: "h1", State: Passed, Message: "ok", Outputs: map[string]string{"level": "high"}},
		{Commit: "h1", State: Passed, Message: "ok"},
	} {
		if r.Equal(o) || o.Equal(r) {
			t.Errorf("%+v equals %+v", r, o)
		}
	}
	var missing *CheckResult
	if !missing.Equal(nil) {
		t.Error("nil results aren't equal")
	}
	empty := &CheckResult{Commit: "h1", State: Passed, Outputs: map[string]string{}}
	if !empty.Equal(&CheckResult{Commit: "h1", State: Passed}) {
		t.Error("empty outputs don't equal no outputs, but they look the same after a status write")
	}
}

func TestChecksMapIsAtomic(t *testing.T) {
	f, _ := reflect.TypeFor[GitBranchStatus]().FieldByName("Checks")
	if got := f.Tag.Get("kube"); got != "mapType=atomic" {
		t.Errorf("status.checks has kube tag %q; it must be an atomic map, so that the results controller owns every entry and can remove any of them", got)
	}
}

func TestMergePolicyDefaults(t *testing.T) {
	var p *MergePolicy
	if p.MaxCommits() != 5 || p.Check("gofmt") != nil {
		t.Error("a nil policy has the default limit and no checks")
	}
	zero := int32(0)
	p = &MergePolicy{Checks: []CheckPolicy{{Name: "gofmt", MayPush: true}}, MaxAutomatedCommits: &zero}
	if p.MaxCommits() != 0 {
		t.Errorf("MaxCommits = %d, want an explicit 0", p.MaxCommits())
	}
	if c := p.Check("gofmt"); c == nil || !c.MayPush {
		t.Errorf("Check(gofmt) = %+v", c)
	}
}
