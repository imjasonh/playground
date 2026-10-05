package checks_test

import (
	"fmt"
	"slices"
	"testing"

	gitk8s "github.com/imjasonh/playground/git-k8s"
	"github.com/imjasonh/playground/git-k8s/checks"
	"github.com/imjasonh/playground/kube"
)

func TestRecordsAnEventForAPushedFix(t *testing.T) {
	zero := int32(0)
	for name, test := range map[string]struct {
		policy gitk8s.CheckPolicy
		limit  *int32
		pushes bool
	}{
		"pushes":       {policy: gitk8s.CheckPolicy{Name: "touch", MayPush: true}, pushes: true},
		"may not push": {policy: gitk8s.CheckPolicy{Name: "touch"}},
		"at the limit": {policy: gitk8s.CheckPolicy{Name: "touch", MayPush: true}, limit: &zero},
	} {
		t.Run(name, func(t *testing.T) {
			f := newFixture(t, test.policy)
			f.branch.Spec.Merge.MaxAutomatedCommits = test.limit
			runs := 0
			ctx, rec := kube.Fake(t.Context(), f.branch, f.repo, f.secret)
			if err := checks.NewReconciler[Branch](touch(&runs), f.cfg).Reconcile(ctx, f.branch); err != nil {
				t.Fatal(err)
			}
			var want []kube.Event
			if test.pushes {
				fix := f.branch.Status.Checks.Result.Outputs["fix"]
				want = []kube.Event{{Type: kube.Normal, Reason: "PushedFix", Note: fmt.Sprintf("pushed %s to c/x: not touched", gitk8s.Short(fix))}}
			}
			if got := rec.Events(); !slices.Equal(got, want) {
				t.Errorf("events = %+v, want %+v", got, want)
			}
		})
	}
}
