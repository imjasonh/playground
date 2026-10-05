package main

import (
	"fmt"
	"slices"
	"testing"

	gitk8s "github.com/imjasonh/playground/git-k8s"
	"github.com/imjasonh/playground/git-k8s/internal/git"
	"github.com/imjasonh/playground/kube"
)

func TestRecordsLandingEvents(t *testing.T) {
	for name, test := range map[string]struct {
		edit    func(*gitk8s.GitBranch)
		reasons []string
	}{
		"lands and deletes": {func(*gitk8s.GitBranch) {}, []string{reasonLanded, "DeletedBranch"}},
		"lands without a queue": {func(b *gitk8s.GitBranch) {
			p := *policy
			p.Checks = []gitk8s.CheckPolicy{{Name: "base"}, {Name: "gofmt", MayPush: true}}
			b.Spec.Merge = &p
		}, []string{reasonLanded, "DeletedBranch"}},
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

func TestRecordsRewritingLandingEvents(t *testing.T) {
	verbs := map[string]string{gitk8s.Squash: "squashed", gitk8s.Rebase: "rebased"}
	for _, landing := range []string{gitk8s.Squash, gitk8s.Rebase} {
		for _, keep := range []bool{false, true} {
			t.Run(fmt.Sprintf("%s keeping the branch %v", landing, keep), func(t *testing.T) {
				f, b, w := branches(t)
				moveParent(t, b, w, "m.txt", "m\n")
				mergeParent(b, w)
				refresh(t, f, b)
				p := *b.Spec.Merge
				p.Landing = landing
				p.DeleteMergedBranches = !keep
				b.Spec.Merge = &p
				main, head := b.Spec.ParentHead, b.Spec.Head
				b.Status.Queued = &gitk8s.Queued{Head: head, Position: 1}
				ctx, rec := kube.Fake(t.Context(), b, f.world(f.repo, parentOf(b, b.Spec.Branch))...)
				m := &merger{mirror: f.mirror, ident: git.Identity{Name: "git-k8s", Email: "git-k8s@example.com"}}
				if err := m.Reconcile(ctx, b); err != nil {
					t.Fatal(err)
				}
				f.fetch()
				landed := f.srv.Heads(t, "app")["main"]
				if landed == main || landed == head {
					t.Fatalf("main = %s, want a new commit on %s", landed, gitk8s.Short(main))
				}
				want := []kube.Event{{Type: kube.Normal, Reason: reasonLanded, Note: fmt.Sprintf("%s c/x at %s onto main, which moved from %s to %s",
					verbs[landing], gitk8s.Short(head), gitk8s.Short(main), gitk8s.Short(landed))}}
				if !keep {
					want = append(want, kube.Event{Type: kube.Normal, Reason: "DeletedBranch", Note: fmt.Sprintf("deleted c/x at %s after it landed on main", gitk8s.Short(head))})
				}
				if events := rec.Events(); !slices.Equal(events, want) {
					t.Errorf("events = %+v, want %+v", events, want)
				}
			})
		}
	}
}
