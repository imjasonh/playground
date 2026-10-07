package gitk8s

import "testing"

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

func TestLandingGateChecks(t *testing.T) {
	policy := &MergePolicy{Checks: []CheckPolicy{{Name: "base"}, {Name: "gofmt"}, {Name: "risk"}, {Name: "approval"}, {Name: "review"}}}
	results := map[string]CheckResult{
		"base":     {Commit: "h1", ParentCommit: "p1", State: Passed},
		"gofmt":    {Commit: "h1", State: Passed},
		"risk":     {Commit: "h1", MergeBase: "p1", State: Passed, Outputs: map[string]string{"level": "low"}},
		"approval": {Commit: "h1", MergeBase: "p0", State: Passed},
		"review":   {Commit: "h0", MergeBase: "p1", State: Passed},
	}
	got := LandingGateChecks(policy, results, "h1", "p1")
	if !got["base"].Passed || !got["gofmt"].Passed || !got["risk"].Passed || got["risk"].Outputs["level"] != "low" {
		t.Errorf("results for the head without a merge base, or with the parent's head as their merge base, must count: %+v", got)
	}
	if got["approval"].State != Pending || got["approval"].Passed {
		t.Errorf("approval = %+v, want Pending because its result is for the change on top of another merge base", got["approval"])
	}
	if got["review"].State != Pending {
		t.Errorf("review = %+v, want Pending because its result is stale", got["review"])
	}
	if !GateChecks(policy, results, "h1", "p1")["approval"].Passed {
		t.Error("a result for the change on top of another merge base must still count outside a landing")
	}
}

func TestRewrittenGateChecks(t *testing.T) {
	policy := &MergePolicy{Checks: []CheckPolicy{{Name: "base"}, {Name: "gofmt"}, {Name: "dco"}, {Name: "risk"}, {Name: "approval"}}}
	results := map[string]CheckResult{
		"base":     {Commit: "h1", ParentCommit: "p1", State: Passed, FilesOnly: true},
		"gofmt":    {Commit: "h1", State: Passed, FilesOnly: true},
		"dco":      {Commit: "h1", State: Passed},
		"risk":     {Commit: "h0", State: Passed, FilesOnly: true},
		"approval": {Commit: "h1", MergeBase: "p0", State: Passed, FilesOnly: true},
	}
	got := RewrittenGateChecks(policy, results, "h1", "p1")
	if !got["base"].Passed || !got["gofmt"].Passed {
		t.Errorf("filesOnly results for the head must count for a commit with the same files on the same parent: %+v", got)
	}
	if got["dco"].State != Pending || got["dco"].Passed {
		t.Errorf("dco = %+v, want Pending because its result doesn't have filesOnly", got["dco"])
	}
	if got["risk"].State != Pending {
		t.Errorf("risk = %+v, want Pending because its result is stale", got["risk"])
	}
	if got["approval"].State != Pending {
		t.Errorf("approval = %+v, want Pending because its result is for the change on top of another merge base", got["approval"])
	}
	if !GateChecks(policy, results, "h1", "p1")["dco"].Passed {
		t.Error("filesOnly must not change what the gate sees of the head itself")
	}
}
