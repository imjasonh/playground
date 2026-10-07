package gitk8s

// GateCheck is what a merge gate sees of one check. The JSON names are the
// field names in gate expressions.
type GateCheck struct {
	Passed  bool              `json:"passed"`
	State   string            `json:"state"`
	Outputs map[string]string `json:"outputs"`
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

// LandingGateChecks returns what a merge gate sees of the checks that policy
// lists, for a branch at head that lands on its parent at parentHead. What
// lands is head's change on top of parentHead, so a fresh result with a
// merge base counts only when the merge base is parentHead.
func LandingGateChecks(policy *MergePolicy, results map[string]CheckResult, head, parentHead string) map[string]GateCheck {
	out := GateChecks(policy, results, head, parentHead)
	for name, c := range out {
		if base := results[name].MergeBase; c.State != Pending && base != "" && base != parentHead {
			out[name] = GateCheck{State: Pending}
		}
	}
	return out
}

// RewrittenGateChecks returns what a merge gate sees of the checks that
// policy lists, for a commit that a squash or rebase landing makes from a
// branch at head whose parent is at parentHead. The commit has head's files
// and builds on parentHead, so a result for head that counts for landing head
// counts for it when the result has FilesOnly.
func RewrittenGateChecks(policy *MergePolicy, results map[string]CheckResult, head, parentHead string) map[string]GateCheck {
	out := LandingGateChecks(policy, results, head, parentHead)
	for name := range out {
		if !results[name].FilesOnly {
			out[name] = GateCheck{State: Pending}
		}
	}
	return out
}
