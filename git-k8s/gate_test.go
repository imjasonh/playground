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

func TestRewrittenGateChecks(t *testing.T) {
	policy := &MergePolicy{Checks: []CheckPolicy{{Name: "base"}, {Name: "gofmt"}, {Name: "dco"}, {Name: "risk"}}}
	results := map[string]CheckResult{
		"base":  {Commit: "h1", ParentCommit: "p1", State: Passed, FilesOnly: true},
		"gofmt": {Commit: "h1", State: Passed, FilesOnly: true},
		"dco":   {Commit: "h1", State: Passed},
		"risk":  {Commit: "h0", State: Passed, FilesOnly: true},
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
	if !GateChecks(policy, results, "h1", "p1")["dco"].Passed {
		t.Error("filesOnly must not change what the gate sees of the head itself")
	}
}
