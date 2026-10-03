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
