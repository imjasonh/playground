package main

import (
	"fmt"
	"maps"
	"os"
	"slices"
	"strings"
	"testing"
	"time"

	gitk8s "github.com/imjasonh/playground/git-k8s"
	"github.com/imjasonh/playground/git-k8s/internal/git"
	"github.com/imjasonh/playground/git-k8s/internal/gittest"
	"github.com/imjasonh/playground/git-k8s/internal/mirror"
	"github.com/imjasonh/playground/kube"
)

// proposal returns the GitBranch of a branch of repository that proposes
// changes to parent, with q as its place in parent's queue.
func proposal(repository, branch, parent string, q *gitk8s.Queued) *gitk8s.GitBranch {
	b := &gitk8s.GitBranch{Object: kube.Meta(gitk8s.BranchObjectName(repository, branch), map[string]string{gitk8s.RepositoryLabel: repository})}
	b.Namespace = "default"
	b.Spec = gitk8s.GitBranchSpec{Repository: repository, Branch: branch, Parent: parent, Merge: policy}
	b.Status.Queued = q
	return b
}

// parentOf returns the GitBranch of b's parent, with queue as its merge
// queue.
func parentOf(b *gitk8s.GitBranch, queue ...string) *gitk8s.GitBranch {
	p := &gitk8s.GitBranch{Object: kube.Meta(gitk8s.BranchObjectName(b.Spec.Repository, b.Spec.Parent), map[string]string{gitk8s.RepositoryLabel: b.Spec.Repository})}
	p.Namespace = b.Namespace
	p.Spec = gitk8s.GitBranchSpec{Repository: b.Spec.Repository, Branch: b.Spec.Parent, Head: b.Spec.ParentHead}
	p.Status.Queue = queue
	return p
}

// repository returns the GitRepository app with rules, at an address where
// nothing listens.
func repository(rules ...gitk8s.BranchRule) *gitk8s.GitRepository {
	repo := &gitk8s.GitRepository{Object: kube.Meta("app", nil), Spec: gitk8s.GitRepositorySpec{URL: "http://127.0.0.1:1/app.git", Branches: rules}}
	repo.Namespace = "default"
	return repo
}

// noCopies returns a mirror without copies, for reconciles that only
// order a queue.
func noCopies(t *testing.T) *mirror.Mirror {
	return &mirror.Mirror{Git: &git.Git{}, Dir: t.TempDir()}
}

// queueOf reconciles parent among the GitBranches in world, and returns its
// merge queue.
func queueOf(t *testing.T, parent *gitk8s.GitBranch, world ...any) []string {
	t.Helper()
	ctx, _ := kube.Fake(t.Context(), parent, append([]any{repository(rules()...)}, world...)...)
	if err := (&merger{mirror: noCopies(t)}).Reconcile(ctx, parent); err != nil {
		t.Fatal(err)
	}
	return parent.Status.Queue
}

func TestQueueOrder(t *testing.T) {
	t0 := time.Date(2026, 1, 1, 0, 0, 0, 0, time.UTC)
	at := func(d time.Duration) *gitk8s.Queued { return &gitk8s.Queued{Since: t0.Add(d), Head: "abc"} }
	b := proposal("app", "c/b", "main", at(time.Minute))
	main := parentOf(b, "c/b", "c/gone", "c/left")
	world := []any{
		b,
		proposal("app", "c/d", "main", at(0)),
		proposal("app", "c/c", "main", at(time.Second)),
		proposal("app", "c/a", "main", at(time.Second)),
		proposal("app", "c/left", "main", nil),
		proposal("app", "c/waiting", "main", nil),
		proposal("other", "c/e", "main", at(0)),
	}
	t.Log("c/b keeps the front. c/gone's GitBranch is gone and c/left left the queue. Branches that joined since follow in the order that they joined, then by name.")
	if got, want := queueOf(t, main, world...), []string{"c/b", "c/d", "c/a", "c/c"}; !slices.Equal(got, want) {
		t.Fatalf("queue = %q, want %q", got, want)
	}

	t.Log("c/b leaves. The others keep their places ahead of a branch that joins after them, whatever its time.")
	b.Status.Queued = nil
	world = append(world, proposal("app", "c/early", "main", at(-time.Hour)))
	if got, want := queueOf(t, main, world...), []string{"c/d", "c/a", "c/c", "c/early"}; !slices.Equal(got, want) {
		t.Errorf("queue = %q, want %q", got, want)
	}
}

func TestOnlyParentsHaveQueues(t *testing.T) {
	release := proposal("app", "release", "", nil)
	release.Spec.Merge = nil
	if got := queueOf(t, release, proposal("app", "c/x", "release", &gitk8s.Queued{Head: "abc"})); got != nil {
		t.Errorf("queue = %q, but no rule names release as a parent", got)
	}

	p := *policy
	p.Checks = []gitk8s.CheckPolicy{{Name: "base"}, {Name: "gofmt", MayPush: true}}
	x := proposal("app", "c/x", "main", &gitk8s.Queued{Head: "abc"})
	x.Spec.Merge = &p
	main := parentOf(x, "c/x")
	repo := repository(gitk8s.BranchRule{Match: "main", Merge: &p}, gitk8s.BranchRule{Match: "c/**", Parent: "main"})
	ctx, _ := kube.Fake(t.Context(), main, repo, x)
	if err := (&merger{mirror: noCopies(t)}).Reconcile(ctx, main); err != nil {
		t.Fatal(err)
	}
	if main.Status.Queue != nil {
		t.Errorf("queue = %q, but main's merge policy doesn't let the base check push", main.Status.Queue)
	}
}

// behind pushes main, then c/one and c/two from it, then moves main ahead,
// all in the external repository of a new fixture, and syncs the mirror.
// It returns the fixture, the branches' GitBranches with fresh, passing
// results, and the fixture's working repository: both branches merge main
// cleanly, so the base check passes them but reports that they're behind.
func behind(t *testing.T) (f *fixture, one, two *gitk8s.GitBranch, w *gittest.Work) {
	f = newFixture(t)
	w = f.work
	start := w.Commit("main")
	w.Write("y.txt", "y\n")
	main := w.Commit("main moves")
	w.Push("main")
	var bs []*gitk8s.GitBranch
	for _, branch := range []string{"c/one", "c/two"} {
		w.Branch(branch, start)
		w.Write(strings.TrimPrefix(branch, "c/")+".txt", branch+"\n")
		head := w.Commit("add " + branch)
		w.Push(branch)
		b := proposal("app", branch, "main", nil)
		b.Spec.Head, b.Spec.ParentHead = head, main
		b.Status.Checks = map[string]gitk8s.CheckResult{
			"base":  {Commit: head, ParentCommit: main, State: gitk8s.Passed, Outputs: map[string]string{"behind": "true"}},
			"gofmt": {Commit: head, State: gitk8s.Passed},
		}
		bs = append(bs, b)
	}
	f.fetch()
	return f, bs[0], bs[1], w
}

func TestQueuedBranchesLandInTurn(t *testing.T) {
	f, one, two, w := behind(t)
	main := parentOf(one)
	start := main.Spec.Head
	reconcile := func(b *gitk8s.GitBranch) string {
		t.Helper()
		return f.mergeIn(main, b)
	}

	t.Log("Both branches become ready together and join main's queue.")
	for _, b := range []*gitk8s.GitBranch{one, two} {
		if msg := reconcile(b); b.Status.State != reasonQueued || msg != "joining main's queue" {
			t.Fatalf("%s: state %q, %q", b.Spec.Branch, b.Status.State, msg)
		}
	}
	if got, want := queueOf(t, main, one, two), []string{"c/one", "c/two"}; !slices.Equal(got, want) {
		t.Fatalf("queue = %q, want %q", got, want)
	}
	since := two.Status.Queued.Since

	t.Log("c/one, at the front, waits for the base check to merge main in. c/two waits for its turn.")
	if msg := reconcile(one); one.Status.Queued.Position != 1 || msg != "first in main's queue; waiting for the base check to merge main in" {
		t.Errorf("c/one: queued %+v, %q", one.Status.Queued, msg)
	}
	if msg := reconcile(two); two.Status.Queued.Position != 2 || msg != "2 of 2 in main's queue" {
		t.Errorf("c/two: queued %+v, %q", two.Status.Queued, msg)
	}
	if got := f.mirrorHeads()["main"]; got != start {
		t.Fatalf("main moved to %s", got)
	}

	t.Log("The base check merges main into c/one. gofmt's result is for what c/one changed on top of the old merge base, so c/one keeps the front without landing.")
	old := w.Git("merge-base", one.Spec.Head, start)
	w.Branch("c/one", one.Spec.Head)
	w.Git("merge", "--quiet", "--no-ff", "-m", "Merge main into c/one\n\n"+git.FixerTrailer+": base", start)
	merged := w.Git("rev-parse", "HEAD")
	f.pushToMirror("c/one")
	one.Generation++
	one.Spec.Head = merged
	one.Status.Checks = map[string]gitk8s.CheckResult{
		"base":  {Commit: merged, ParentCommit: start, State: gitk8s.Passed},
		"gofmt": {Commit: merged, MergeBase: old, State: gitk8s.Passed},
	}
	if msg := reconcile(one); one.Status.State != reasonWaitingForChecks || one.Status.Queued == nil || msg != "checks: base Passed, gofmt Pending" {
		t.Fatalf("c/one: state %q, queued %+v, %q", one.Status.State, one.Status.Queued, msg)
	}
	if got := f.mirrorHeads()["main"]; got != start {
		t.Fatalf("main moved to %s", got)
	}

	t.Log("gofmt's result moves to main's head as the merge base, and c/one lands.")
	one.Status.Checks["gofmt"] = gitk8s.CheckResult{Commit: merged, MergeBase: start, State: gitk8s.Passed}
	if msg := reconcile(one); one.Status.State != reasonLanded || one.Status.Queued != nil {
		t.Fatalf("c/one: state %q, queued %+v, %q", one.Status.State, one.Status.Queued, msg)
	}
	if got := f.mirrorHeads()["main"]; got != merged {
		t.Fatalf("main = %s, want %s", got, merged)
	}

	t.Log("Until the repository controller lists c/one again, it stays landed.")
	if msg := reconcile(one); one.Status.State != reasonLanded || one.Status.Queued != nil {
		t.Errorf("c/one after landing: state %q, queued %+v, %q", one.Status.State, one.Status.Queued, msg)
	}

	t.Log("c/two moves to the front, and waits for the base check to merge main's new head in.")
	if got, want := queueOf(t, main, one, two), []string{"c/two"}; !slices.Equal(got, want) {
		t.Fatalf("queue = %q, want %q", got, want)
	}
	two.Generation++
	two.Spec.ParentHead = merged
	two.Status.Checks["base"] = gitk8s.CheckResult{Commit: two.Spec.Head, ParentCommit: merged, State: gitk8s.Passed, Outputs: map[string]string{"behind": "true"}}
	if msg := reconcile(two); two.Status.Queued.Position != 1 || !two.Status.Queued.Since.Equal(since) ||
		msg != "first in main's queue; waiting for the base check to merge main in" {
		t.Errorf("c/two: queued %+v, %q", two.Status.Queued, msg)
	}
}

func TestUpToDateBranchesWaitTheirTurn(t *testing.T) {
	f, one, two, w := behind(t)
	main := parentOf(one)
	start := main.Spec.Head
	reconcile := func(b *gitk8s.GitBranch) string {
		t.Helper()
		return f.mergeIn(main, b)
	}
	w.Branch("c/two", start)
	w.Write("two.txt", "c/two\n")
	two.Spec.Head = w.Commit("add c/two")
	w.Push("c/two")
	f.fetch()
	two.Status.Checks = map[string]gitk8s.CheckResult{
		"base":  {Commit: two.Spec.Head, ParentCommit: start, State: gitk8s.Passed},
		"gofmt": {Commit: two.Spec.Head, State: gitk8s.Passed},
	}

	t.Log("c/one is behind main, and c/two contains main's head. Both join main's queue, and c/two doesn't land before the queue lists it.")
	for _, b := range []*gitk8s.GitBranch{one, two} {
		if msg := reconcile(b); b.Status.State != reasonQueued || msg != "joining main's queue" {
			t.Fatalf("%s: state %q, %q", b.Spec.Branch, b.Status.State, msg)
		}
	}
	if got := f.mirrorHeads()["main"]; got != start {
		t.Fatalf("main moved to %s", got)
	}
	if got, want := queueOf(t, main, one, two), []string{"c/one", "c/two"}; !slices.Equal(got, want) {
		t.Fatalf("queue = %q, want %q", got, want)
	}

	t.Log("c/two waits behind c/one, which waits for the base check to merge main in.")
	if msg := reconcile(two); msg != "2 of 2 in main's queue" || two.Status.Queued == nil || two.Status.Queued.Position != 2 {
		t.Errorf("c/two: queued %+v, %q", two.Status.Queued, msg)
	}
	if msg := reconcile(one); msg != "first in main's queue; waiting for the base check to merge main in" {
		t.Errorf("c/one: %q", msg)
	}
	if got := f.mirrorHeads()["main"]; got != start {
		t.Fatalf("main moved to %s", got)
	}

	t.Log("c/one's gofmt check fails, so c/one leaves the queue, and c/two lands.")
	one.Status.Checks["gofmt"] = gitk8s.CheckResult{Commit: one.Spec.Head, State: gitk8s.Failed}
	if msg := reconcile(one); one.Status.State != reasonWaitingForChecks || one.Status.Queued != nil {
		t.Fatalf("c/one: state %q, queued %+v, %q", one.Status.State, one.Status.Queued, msg)
	}
	if got := f.mirrorHeads()["main"]; got != start {
		t.Fatalf("main moved to %s", got)
	}
	if got, want := queueOf(t, main, one, two), []string{"c/two"}; !slices.Equal(got, want) {
		t.Fatalf("queue = %q, want %q", got, want)
	}
	if msg := reconcile(two); two.Status.State != reasonLanded {
		t.Fatalf("c/two: state %q, %q", two.Status.State, msg)
	}
	if got := f.mirrorHeads()["main"]; got != two.Spec.Head {
		t.Errorf("main = %s, want %s", got, two.Spec.Head)
	}
}

func TestRejoinsAtTheBack(t *testing.T) {
	for _, branch := range []string{"c/one", "c/two"} {
		t.Run(branch, func(t *testing.T) {
			f, one, two, w := behind(t)
			main := parentOf(one, "c/one", "c/two")
			start := main.Spec.Head
			since := time.Date(2026, 1, 1, 0, 0, 0, 0, time.UTC)
			one.Status.Queued = &gitk8s.Queued{Since: since, Head: one.Spec.Head, Position: 1}
			two.Status.Queued = &gitk8s.Queued{Since: since, Head: two.Spec.Head, Position: 2}
			pushed, other := one, two
			if branch == "c/two" {
				pushed, other = two, one
			}
			reconcile := func(b *gitk8s.GitBranch) string {
				t.Helper()
				return f.mergeIn(main, b)
			}

			t.Logf("Someone pushes to %s in main's queue, and the checks pass on the new head before main's queue drops %[1]s.", branch)
			w.Branch(branch, pushed.Spec.Head)
			w.Write("more.txt", "more\n")
			head := w.Commit("more work")
			w.Push(branch)
			f.fetch()
			pushed.Generation++
			pushed.Spec.Head = head
			pushed.Status.Checks = map[string]gitk8s.CheckResult{
				"base":  {Commit: head, ParentCommit: start, State: gitk8s.Passed, Outputs: map[string]string{"behind": "true"}},
				"gofmt": {Commit: head, State: gitk8s.Passed},
			}
			if msg := reconcile(pushed); pushed.Status.Queued != nil || msg != "rejoining main's queue at the back" {
				t.Fatalf("%s: queued %+v, %q", branch, pushed.Status.Queued, msg)
			}
			t.Logf("%s waits until main's queue drops it.", branch)
			if msg := reconcile(pushed); pushed.Status.Queued != nil || msg != "rejoining main's queue at the back" {
				t.Fatalf("%s: queued %+v, %q", branch, pushed.Status.Queued, msg)
			}

			t.Logf("main's queue drops %s, which then joins at the back.", branch)
			if got, want := queueOf(t, main, one, two), []string{other.Spec.Branch}; !slices.Equal(got, want) {
				t.Fatalf("queue = %q, want %q", got, want)
			}
			if msg := reconcile(pushed); pushed.Status.Queued == nil || msg != "joining main's queue" {
				t.Fatalf("%s: queued %+v, %q", branch, pushed.Status.Queued, msg)
			}
			if got, want := queueOf(t, main, one, two), []string{other.Spec.Branch, branch}; !slices.Equal(got, want) {
				t.Fatalf("queue = %q, want %q", got, want)
			}
			if msg := reconcile(pushed); msg != "2 of 2 in main's queue" {
				t.Errorf("%s: %q", branch, msg)
			}
			if msg := reconcile(other); msg != "first in main's queue; waiting for the base check to merge main in" {
				t.Errorf("%s: %q", other.Spec.Branch, msg)
			}
			if got := f.mirrorHeads()["main"]; got != start {
				t.Errorf("main moved to %s", got)
			}
		})
	}
}

func TestKeepsItsPlaceWhileItsCacheLags(t *testing.T) {
	f, one, two, _ := behind(t)
	main := parentOf(one, "c/one", "c/two")
	start := main.Spec.Head
	since := time.Date(2026, 1, 1, 0, 0, 0, 0, time.UTC)
	t.Log("c/one and c/two join main's queue, and main lists them before their own caches have the writes in which they joined.")
	for _, tc := range []struct {
		b    *gitk8s.GitBranch
		pos  int32
		want string
	}{
		{one, 1, "first in main's queue; waiting for the base check to merge main in"},
		{two, 2, "2 of 2 in main's queue"},
	} {
		// live is the branch as the API server has it.
		live := *tc.b
		live.Status.Queued = &gitk8s.Queued{Since: since, Head: tc.b.Spec.Head}
		msg := f.mergeIn(main, tc.b, &live)
		if q := tc.b.Status.Queued; q == nil || !q.Since.Equal(since) || q.Position != tc.pos || msg != tc.want {
			t.Errorf("%s: queued %+v, %q; want its place at %d, %q", tc.b.Spec.Branch, q, msg, tc.pos, tc.want)
		}
	}
	if got := f.mirrorHeads()["main"]; got != start {
		t.Errorf("main moved to %s", got)
	}
}

func TestLeavingTheQueue(t *testing.T) {
	since := time.Date(2026, 1, 1, 0, 0, 0, 0, time.UTC)
	for _, tc := range []struct {
		name string
		edit func(*fixture, *gitk8s.GitBranch)
		// state is the branch's state afterward, Queued if it keeps its place.
		state string
	}{{
		name: "a check pushes a fix",
		edit: func(f *fixture, b *gitk8s.GitBranch) {
			f.work.Write("x.txt", "fixed\n")
			b.Spec.Head = f.work.Commit("Fix x\n\n" + git.FixerTrailer + ": gofmt")
			f.pushToMirror("c/x")
		},
		state: reasonQueued,
	}, {
		name: "a check is still running",
		edit: func(_ *fixture, b *gitk8s.GitBranch) {
			b.Status.Checks["gofmt"] = gitk8s.CheckResult{Commit: b.Spec.Head, State: gitk8s.Running}
		},
		state: reasonQueued,
	}, {
		name: "a person pushes",
		edit: func(f *fixture, b *gitk8s.GitBranch) {
			f.work.Write("more.txt", "more\n")
			b.Spec.Head = f.work.Commit("more work")
			f.work.Push("c/x")
			f.fetch()
		},
		state: reasonWaitingForChecks,
	}, {
		name: "someone force-pushes",
		edit: func(f *fixture, b *gitk8s.GitBranch) {
			f.work.Branch("c/x", b.Spec.ParentHead)
			f.work.Write("other.txt", "other\n")
			b.Spec.Head = f.work.Commit("start over")
			f.work.Push("c/x")
			f.fetch()
		},
		state: reasonWaitingForChecks,
	}, {
		name: "the branch diverges",
		edit: func(f *fixture, b *gitk8s.GitBranch) {
			head := b.Spec.Head
			f.work.Write("x.txt", "fixed\n")
			b.Spec.Head = f.work.Commit("Fix x\n\n" + git.FixerTrailer + ": gofmt")
			f.pushToMirror("c/x")
			f.work.Branch("person", head)
			f.work.Write("person.txt", "person\n")
			f.work.Commit("a person's change")
			f.work.Push("c/x")
			f.fetch()
		},
		state: reasonDiverged,
	}, {
		name: "a check fails",
		edit: func(_ *fixture, b *gitk8s.GitBranch) {
			b.Status.Checks["gofmt"] = gitk8s.CheckResult{Commit: b.Spec.Head, State: gitk8s.Failed}
		},
		state: reasonWaitingForChecks,
	}, {
		name: "the gate is invalid",
		edit: func(_ *fixture, b *gitk8s.GitBranch) {
			p := *policy
			p.When = "checks.missing.passed"
			b.Spec.Merge = &p
		},
		state: reasonInvalidGate,
	}, {
		name:  "the parent is gone",
		edit:  func(_ *fixture, b *gitk8s.GitBranch) { b.Spec.ParentHead = "" },
		state: reasonParentMissing,
	}} {
		t.Run(tc.name, func(t *testing.T) {
			f, b, _ := branches(t)
			b.Status.Queued = &gitk8s.Queued{Since: since, Head: b.Spec.Head, Position: 1}
			main := b.Spec.ParentHead
			tc.edit(f, b)
			if _, err := f.merge(b); err != nil {
				t.Fatal(err)
			}
			if b.Status.State != tc.state {
				t.Errorf("state = %q, want %s", b.Status.State, tc.state)
			}
			switch q := b.Status.Queued; {
			case tc.state != reasonQueued && q != nil:
				t.Errorf("queued = %+v, want the branch out of the queue", q)
			case tc.state == reasonQueued && (q == nil || !q.Since.Equal(since) || q.Head != b.Spec.Head || q.Position != 1):
				t.Errorf("queued = %+v, want its place at the front, at head %s", q, gitk8s.Short(b.Spec.Head))
			}
			if got := f.mirrorHeads()["main"]; got != main {
				t.Errorf("main moved to %s", got)
			}
		})
	}
}

// TestKeepingThePlaceThroughAnError checks that a branch keeps its place in
// its parent's queue when its reconcile fails, since kube writes the status
// of a failed reconcile too, and that it lands once the error passes.
func TestKeepingThePlaceThroughAnError(t *testing.T) {
	since := time.Date(2026, 1, 1, 0, 0, 0, 0, time.UTC)
	f, b, _ := branches(t)
	b.Status.Queued = &gitk8s.Queued{Since: since, Head: b.Spec.Head, Position: 1}
	main := b.Spec.ParentHead
	results := b.Status.Checks
	// The mirror keeps its copy open, so the next read of the copy fails
	// once its directory is gone.
	moved := f.copyDir() + ".moved"
	if err := os.Rename(f.copyDir(), moved); err != nil {
		t.Fatal(err)
	}
	if _, err := f.merge(b); err == nil {
		t.Fatal("merge succeeded without the mirror's copy")
	}
	if q := b.Status.Queued; q == nil || !q.Since.Equal(since) || q.Head != b.Spec.Head || q.Position != 1 {
		t.Fatalf("queued = %+v, want its place at the front, at head %s", q, gitk8s.Short(b.Spec.Head))
	}

	if err := os.Rename(moved, f.copyDir()); err != nil {
		t.Fatal(err)
	}
	// The merge controller leaves the checks' results out of its status
	// write, so the next reconcile still reads them.
	b.Status.Checks = results
	if _, err := f.merge(b); err != nil {
		t.Fatal(err)
	}
	if b.Status.State != reasonLanded {
		t.Errorf("state = %q, want %s", b.Status.State, reasonLanded)
	}
	if got := f.mirrorHeads()["main"]; got == main {
		t.Errorf("main is still at %s", gitk8s.Short(main))
	}
}

func TestLeavingTheFront(t *testing.T) {
	since := time.Date(2026, 1, 1, 0, 0, 0, 0, time.UTC)
	for _, tc := range []struct {
		name string
		// when is the gate of a merge policy that lists base, gofmt, and
		// approval. approval doesn't finish.
		when  string
		base  string
		gofmt string
		// queue is main's queue.
		queue []string
		// stays reports whether c/x keeps its place.
		stays bool
	}{{
		name:  "every check must pass",
		base:  gitk8s.Passed,
		gofmt: gitk8s.Failed,
		queue: []string{"c/x"},
	}, {
		name:  "behind the front",
		base:  gitk8s.Passed,
		gofmt: gitk8s.Failed,
		queue: []string{"c/a", "c/x"},
		stays: true,
	}, {
		name:  "the gate can still pass",
		when:  `checks.base.passed && (checks.gofmt.passed || checks.approval.passed)`,
		base:  gitk8s.Passed,
		gofmt: gitk8s.Failed,
		queue: []string{"c/x"},
		stays: true,
	}, {
		name:  "the gate can't pass",
		when:  `checks.base.passed && checks.gofmt.passed`,
		base:  gitk8s.Passed,
		gofmt: gitk8s.Failed,
		queue: []string{"c/x"},
	}, {
		name:  "the gate reads an output that isn't set yet",
		when:  `checks.base.passed && (checks.gofmt.passed || checks.approval.outputs.approver == "alice")`,
		base:  gitk8s.Passed,
		gofmt: gitk8s.Failed,
		queue: []string{"c/x"},
		stays: true,
	}, {
		name:  "the base check fails",
		when:  `checks.approval.passed`,
		base:  gitk8s.Failed,
		gofmt: gitk8s.Failed,
		queue: []string{"c/x"},
	}, {
		name:  "the gate passes, but the base check fails",
		when:  `checks.gofmt.passed`,
		base:  gitk8s.Failed,
		gofmt: gitk8s.Passed,
		queue: []string{"c/x"},
	}} {
		t.Run(tc.name, func(t *testing.T) {
			f, b, _ := branches(t)
			p := *policy
			p.Checks = append(p.Checks[:2:2], gitk8s.CheckPolicy{Name: "approval"})
			p.When = tc.when
			b.Spec.Merge = &p
			b.Status.Checks["base"] = gitk8s.CheckResult{Commit: b.Spec.Head, ParentCommit: b.Spec.ParentHead, State: tc.base}
			b.Status.Checks["gofmt"] = gitk8s.CheckResult{Commit: b.Spec.Head, State: tc.gofmt}
			pos := int32(slices.Index(tc.queue, "c/x") + 1)
			b.Status.Queued = &gitk8s.Queued{Since: since, Head: b.Spec.Head, Position: pos}
			main := b.Spec.ParentHead
			msg := f.mergeIn(parentOf(b, tc.queue...), b)
			switch q := b.Status.Queued; {
			case tc.stays && (b.Status.State != reasonQueued || q == nil || !q.Since.Equal(since) || q.Position != pos):
				t.Errorf("state = %q, queued %+v, %q; want its place at %d", b.Status.State, q, msg, pos)
			case !tc.stays && (b.Status.State != reasonWaitingForChecks || q != nil):
				t.Errorf("state = %q, queued %+v, %q; want %s, out of the queue", b.Status.State, q, msg, reasonWaitingForChecks)
			}
			if got := f.mirrorHeads()["main"]; got != main {
				t.Errorf("main moved to %s", got)
			}
		})
	}
}

// A rebase landing at the front of the queue can find that the branch needs
// a person to rebase it. The branch leaves the queue, so the next branch
// moves to the front, and it joins again only after its spec changes.
func TestNeedsRebaseLeavesTheQueue(t *testing.T) {
	since := time.Date(2026, 1, 1, 0, 0, 0, 0, time.UTC)
	f, one, two, w := behind(t)
	main := parentOf(one, "c/one", "c/two")
	start := main.Spec.Head
	reconcile := func(b *gitk8s.GitBranch) string {
		t.Helper()
		return f.mergeIn(main, b)
	}
	// list moves c/one to head, as the repository controller does, with
	// passing results for head.
	list := func(head string) {
		one.Generation++
		one.Spec.Head = head
		one.Status.Checks = map[string]gitk8s.CheckResult{
			"base":  {Commit: head, ParentCommit: start, State: gitk8s.Passed, FilesOnly: true},
			"gofmt": {Commit: head, State: gitk8s.Passed, FilesOnly: true},
		}
	}
	p := *policy
	p.Landing = gitk8s.Rebase
	one.Spec.Merge = &p
	two.Status.Queued = &gitk8s.Queued{Since: since, Head: two.Spec.Head, Position: 2}

	t.Log("The base check merges main into c/one at the front, and the checks pass, but the merge changes a file, which a rebase leaves out.")
	w.Branch("c/one", one.Spec.Head)
	w.Git("merge", "--quiet", "--no-ff", "--no-commit", start)
	w.Write("merge.txt", "merge\n")
	list(w.Commit("Merge main into c/one\n\n" + git.FixerTrailer + ": base"))
	f.pushToMirror("c/one")
	one.Status.Queued = &gitk8s.Queued{Since: since, Head: one.Spec.Head, Position: 1}
	msg := reconcile(one)
	if one.Status.State != reasonNeedsRebase || one.Status.Queued != nil {
		t.Fatalf("c/one: state %q, queued %+v, %q; want %s, out of the queue", one.Status.State, one.Status.Queued, msg, reasonNeedsRebase)
	}
	heads := f.mirrorHeads()
	if heads["main"] != start {
		t.Fatalf("main moved to %s", heads["main"])
	}

	t.Log("Until its spec changes, c/one stays out of main's queue, and the merge controller doesn't land it again.")
	if again := reconcile(one); one.Status.State != reasonNeedsRebase || one.Status.Queued != nil || again != msg {
		t.Errorf("c/one: state %q, queued %+v, %q; want it unchanged", one.Status.State, one.Status.Queued, again)
	}
	if got, want := queueOf(t, main, one, two), []string{"c/two"}; !slices.Equal(got, want) {
		t.Fatalf("queue = %q, want %q", got, want)
	}
	if again := reconcile(one); one.Status.State != reasonNeedsRebase || one.Status.Queued != nil || again != msg {
		t.Errorf("c/one after main's queue dropped it: state %q, queued %+v, %q; want it unchanged", one.Status.State, one.Status.Queued, again)
	}
	if after := f.mirrorHeads(); !maps.Equal(after, heads) {
		t.Errorf("heads = %v, want %v", after, heads)
	}

	t.Log("c/two moves to the front.")
	if msg := reconcile(two); two.Status.Queued == nil || two.Status.Queued.Position != 1 ||
		msg != "first in main's queue; waiting for the base check to merge main in" {
		t.Errorf("c/two: queued %+v, %q", two.Status.Queued, msg)
	}

	t.Log("Someone pushes to c/one, and it joins main's queue at the back when its gate passes.")
	w.Write("more.txt", "more\n")
	list(w.Commit("more work"))
	w.Push("c/one")
	f.fetch()
	if msg := reconcile(one); one.Status.State != reasonQueued || one.Status.Queued == nil || msg != "joining main's queue" {
		t.Fatalf("c/one: state %q, queued %+v, %q", one.Status.State, one.Status.Queued, msg)
	}
	if got, want := queueOf(t, main, one, two), []string{"c/two", "c/one"}; !slices.Equal(got, want) {
		t.Errorf("queue = %q, want %q", got, want)
	}
}

// A squash landing at the front of the queue pushes the squashed commit to
// the branch when a check's results don't have filesOnly. The branch holds
// the front while the checks run on that commit and push fixes to it, and
// then the commit and the fixes land by fast-forward.
func TestRewrittenBranchHoldsTheFront(t *testing.T) {
	since := time.Date(2026, 1, 1, 0, 0, 0, 0, time.UTC)
	f, one, two, w := behind(t)
	main := parentOf(one, "c/one", "c/two")
	start := main.Spec.Head
	reconcile := func(b *gitk8s.GitBranch) string {
		t.Helper()
		return f.mergeIn(main, b)
	}
	// list moves c/one to head, as the repository controller does.
	list := func(head string) {
		one.Generation++
		one.Spec.Head = head
	}
	// pass gives c/one passing results for its head.
	pass := func() {
		one.Status.Checks = map[string]gitk8s.CheckResult{
			"base":  {Commit: one.Spec.Head, ParentCommit: start, State: gitk8s.Passed, FilesOnly: true},
			"gofmt": {Commit: one.Spec.Head, State: gitk8s.Passed, FilesOnly: true},
		}
		withHistoryCheck(one)
	}
	// front reports whether c/one is at the front of main's queue at head.
	front := func(head string) bool {
		q := one.Status.Queued
		return q != nil && q.Since.Equal(since) && q.Head == head && q.Position == 1
	}
	p := *policy
	p.Landing = gitk8s.Squash
	one.Spec.Merge = &p
	two.Status.Queued = &gitk8s.Queued{Since: since, Head: two.Spec.Head, Position: 2}

	t.Log("The base check merges main into c/one at the front, and the checks pass, but dco has to check the squashed commit.")
	w.Branch("c/one", one.Spec.Head)
	w.Git("merge", "--quiet", "--no-ff", "-m", "Merge main into c/one\n\n"+git.FixerTrailer+": base", start)
	f.pushToMirror("c/one")
	list(w.Git("rev-parse", "HEAD"))
	pass()
	one.Status.Queued = &gitk8s.Queued{Since: since, Head: one.Spec.Head, Position: 1}
	msg := reconcile(one)
	heads := f.mirrorHeads()
	squashed := heads["c/one"]
	want := fmt.Sprintf("squashed c/one onto main at %s as %s and moved c/one there, because the results of dco might depend on the branch's commits",
		gitk8s.Short(start), gitk8s.Short(squashed))
	if one.Status.State != reasonRewritten || msg != want || !front(squashed) {
		t.Fatalf("c/one: state %q, queued %+v, %q; want %s at the front at %s, %q", one.Status.State, one.Status.Queued, msg, reasonRewritten, squashed, want)
	}
	if heads["main"] != start {
		t.Fatalf("main moved to %s", heads["main"])
	}

	t.Log("Until the repository controller lists the squashed commit, c/one holds the front, and the merge controller doesn't land it again.")
	if again := reconcile(one); one.Status.State != reasonRewritten || again != msg || !front(squashed) {
		t.Errorf("c/one: state %q, queued %+v, %q; want it unchanged", one.Status.State, one.Status.Queued, again)
	}
	if after := f.mirrorHeads(); !maps.Equal(after, heads) {
		t.Errorf("heads = %v, want %v", after, heads)
	}
	if got, want := queueOf(t, main, one, two), []string{"c/one", "c/two"}; !slices.Equal(got, want) {
		t.Fatalf("queue = %q, want %q", got, want)
	}
	if msg := reconcile(two); msg != "2 of 2 in main's queue" {
		t.Errorf("c/two: queued %+v, %q", two.Status.Queued, msg)
	}

	t.Log("The repository controller lists the squashed commit, and c/one waits at the front for the checks to run on it.")
	list(squashed)
	if msg := reconcile(one); one.Status.State != reasonQueued || !front(squashed) ||
		msg != "first in main's queue; checks: base Pending, dco Pending, gofmt Pending" {
		t.Errorf("c/one: state %q, queued %+v, %q", one.Status.State, one.Status.Queued, msg)
	}

	t.Log("gofmt pushes a fix, which keeps c/one's place. The checks pass, and the squashed commit and the fix land by fast-forward.")
	w.Branch("c/one", f.fetchFromMirror("c/one"))
	w.Write("one.txt", "c/one, fixed\n")
	fixed := w.Commit("Fix one.txt\n\n" + git.FixerTrailer + ": gofmt")
	f.pushToMirror("c/one")
	list(fixed)
	pass()
	want = fmt.Sprintf("fast-forwarded main from %s to %s", gitk8s.Short(start), gitk8s.Short(fixed))
	if msg := reconcile(one); one.Status.State != reasonLanded || one.Status.Queued != nil || msg != want {
		t.Fatalf("c/one: state %q, queued %+v, %q; want %s, out of the queue, %q", one.Status.State, one.Status.Queued, msg, reasonLanded, want)
	}
	if got := f.mirrorHeads()["main"]; got != fixed {
		t.Errorf("main = %s, want %s", got, fixed)
	}
	if got, want := queueOf(t, main, one, two), []string{"c/two"}; !slices.Equal(got, want) {
		t.Errorf("queue = %q, want %q", got, want)
	}
}

func TestLandsWithoutAQueue(t *testing.T) {
	f, b, _ := branches(t)
	p := *policy
	p.Checks = []gitk8s.CheckPolicy{{Name: "base"}, {Name: "gofmt", MayPush: true}}
	b.Spec.Merge = &p
	ctx, _ := kube.Fake(t.Context(), b, f.world(f.repo)...)
	if err := (&merger{mirror: f.mirror}).Reconcile(ctx, b); err != nil {
		t.Fatal(err)
	}
	if b.Status.State != reasonLanded || b.Status.Queued != nil {
		t.Errorf("state = %q, queued %+v; a base check that can't push merges nothing, so branches land without a queue", b.Status.State, b.Status.Queued)
	}
}
