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
