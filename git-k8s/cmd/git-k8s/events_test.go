package main

import (
	"fmt"
	"slices"
	"testing"

	gitk8s "github.com/imjasonh/playground/git-k8s"
	"github.com/imjasonh/playground/kube"
)

func TestRecordsLandingEvents(t *testing.T) {
	for name, test := range map[string]struct {
		edit    func(*gitk8s.GitBranch)
		reasons []string
	}{
		"lands and deletes": {func(*gitk8s.GitBranch) {}, []string{reasonLanded, "DeletedBranch"}},
		"keeps the branch": {func(b *gitk8s.GitBranch) {
			p := *policy
			p.DeleteMergedBranches = false
			b.Spec.Merge = &p
		}, []string{reasonLanded}},
		"waits for checks": {func(b *gitk8s.GitBranch) { delete(b.Status.Checks, "gofmt") }, nil},
		"already merged":   {func(b *gitk8s.GitBranch) { b.Spec.ParentHead = b.Spec.Head }, nil},
	} {
		t.Run(name, func(t *testing.T) {
			f := newFixture(t)
			b := f.branches()
			test.edit(b)
			notes := map[string]string{
				reasonLanded:    fmt.Sprintf("fast-forwarded main from %s to c/x at %s", gitk8s.Short(b.Spec.ParentHead), gitk8s.Short(b.Spec.Head)),
				"DeletedBranch": fmt.Sprintf("deleted c/x at %s after it landed on main", gitk8s.Short(b.Spec.Head)),
			}
			var want []kube.Event
			for _, reason := range test.reasons {
				want = append(want, kube.Event{Type: kube.Normal, Reason: reason, Note: notes[reason]})
			}
			rec, err := f.merge(b)
			if err != nil {
				t.Fatal(err)
			}
			if events := rec.Events(); !slices.Equal(events, want) {
				t.Errorf("events = %+v, want %+v", events, want)
			}
		})
	}
}
