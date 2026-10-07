package gitk8s

import (
	"strings"
	"testing"
)

func TestValidate(t *testing.T) {
	outputs := func(n, nameLen, valueLen int) map[string]string {
		m := map[string]string{}
		for i := range n {
			name := strings.Repeat("n", nameLen-1) + string(rune('a'+i))
			m[name] = strings.Repeat("v", valueLen)
		}
		return m
	}
	for _, tc := range []struct {
		name string
		edit func(*CheckResult)
		err  string
	}{
		{"passed", func(*CheckResult) {}, ""},
		{"running", func(r *CheckResult) { r.State = Running }, ""},
		{"failed", func(r *CheckResult) { r.State = Failed }, ""},
		{"fixed", func(r *CheckResult) { r.State = Fixed }, ""},
		{"error", func(r *CheckResult) { r.State = Error }, ""},
		{"pending", func(r *CheckResult) { r.State = Pending }, `state "Pending" isn't`},
		{"no state", func(r *CheckResult) { r.State = "" }, `state "" isn't`},
		{"no commit", func(r *CheckResult) { r.Commit = "" }, "no commit"},
		{"no scope", func(r *CheckResult) { r.Scope = "" }, "no scope"},
		{"a scope that the core program doesn't know", func(r *CheckResult) { r.Scope = "parent" }, `scope "parent" isn't Head, Parent, or Change`},
		{"head with a parent commit", func(r *CheckResult) { r.ParentCommit = "p1" }, "scope Head has neither parentCommit nor mergeBase"},
		{"head with a merge base", func(r *CheckResult) { r.MergeBase = "b1" }, "scope Head has neither parentCommit nor mergeBase"},
		{"parent", func(r *CheckResult) { r.Scope, r.ParentCommit = ScopeParent, "p1" }, ""},
		{"parent without a parent commit", func(r *CheckResult) { r.Scope = ScopeParent }, "scope Parent has parentCommit and not mergeBase"},
		{"parent with a merge base", func(r *CheckResult) { r.Scope, r.ParentCommit, r.MergeBase = ScopeParent, "p1", "b1" }, "scope Parent has parentCommit and not mergeBase"},
		{"change", func(r *CheckResult) { r.Scope, r.MergeBase = ScopeChange, "b1" }, ""},
		{"change without a merge base", func(r *CheckResult) { r.Scope = ScopeChange }, "scope Change has mergeBase and not parentCommit"},
		{"change with a parent commit", func(r *CheckResult) { r.Scope, r.ParentCommit, r.MergeBase = ScopeChange, "p1", "b1" }, "scope Change has mergeBase and not parentCommit"},
		{"the longest message", func(r *CheckResult) { r.Message = strings.Repeat("x", MaxMessageLength) }, ""},
		{"a longer message", func(r *CheckResult) { r.Message = strings.Repeat("x", MaxMessageLength+1) }, "message is longer than 1024 bytes"},
		{"the most outputs", func(r *CheckResult) { r.Outputs = outputs(MaxOutputs, 2, 1) }, ""},
		{"more outputs", func(r *CheckResult) { r.Outputs = outputs(MaxOutputs+1, 2, 1) }, "more than 16 outputs"},
		{"the longest output name", func(r *CheckResult) { r.Outputs = outputs(1, MaxOutputNameLength, 1) }, ""},
		{"a longer output name", func(r *CheckResult) { r.Outputs = outputs(1, MaxOutputNameLength+1, 1) }, "output name isn't 1 to 63 bytes"},
		{"an empty output name", func(r *CheckResult) { r.Outputs = map[string]string{"": "v"} }, "output name isn't 1 to 63 bytes"},
		{"the longest output value", func(r *CheckResult) { r.Outputs = outputs(1, 1, MaxOutputValueLength) }, ""},
		{"a longer output value", func(r *CheckResult) {
			r.Outputs = map[string]string{"files": strings.Repeat("v", MaxOutputValueLength+1)}
		}, "output files is longer than 1024 bytes"},
	} {
		t.Run(tc.name, func(t *testing.T) {
			r := &CheckResult{Commit: "h1", Scope: ScopeHead, State: Passed}
			tc.edit(r)
			err := r.Validate()
			if tc.err == "" && err != nil || tc.err != "" && (err == nil || !strings.Contains(err.Error(), tc.err)) {
				t.Errorf("Validate = %v, want %q", err, tc.err)
			}
		})
	}
}
