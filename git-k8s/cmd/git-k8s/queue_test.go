package main

import (
	"slices"
	"strings"
	"testing"
	"time"

	gitk8s "github.com/imjasonh/playground/git-k8s"
	"github.com/imjasonh/playground/git-k8s/internal/git"
	"github.com/imjasonh/playground/git-k8s/internal/gittest"
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

// queueOf reconciles parent among the GitBranches in world, and returns its
// merge queue.
func queueOf(t *testing.T, parent *gitk8s.GitBranch, world ...any) []string {
	t.Helper()
	ctx, _ := kube.Fake(t.Context(), parent, append([]any{repository(rules()...)}, world...)...)
	if err := (&merger{}).Reconcile(ctx, parent); err != nil {
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
	if err := (&merger{}).Reconcile(ctx, main); err != nil {
		t.Fatal(err)
	}
	if main.Status.Queue != nil {
		t.Errorf("queue = %q, but main's merge policy doesn't let the base check push", main.Status.Queue)
	}
}

// behind pushes main, then c/one and c/two from it, then moves main ahead.
// It returns the branches' GitBranches with fresh, passing results: both
// merge main cleanly, so the base check passes them but reports that they're
// behind.
func behind(t *testing.T, srv *gittest.Server) (one, two *gitk8s.GitBranch, w *gittest.Work) {
	w = srv.NewWork(t, "app")
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
	return bs[0], bs[1], w
}

func TestQueuedBranchesLandInTurn(t *testing.T) {
	srv := gittest.NewServer(t, "")
	one, two, w := behind(t, srv)
	main := parentOf(one)
	start := main.Spec.Head
	reconcile := func(b *gitk8s.GitBranch) string {
		t.Helper()
		return mergeIn(t, srv, main, b)
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
	if got := srv.Heads(t, "app")["main"]; got != start {
		t.Fatalf("main moved to %s", got)
	}

	t.Log("The base check merges main into c/one, the checks pass again, and c/one lands.")
	w.Branch("c/one", one.Spec.Head)
	w.Git("merge", "--quiet", "--no-ff", "-m", "Merge main into c/one\n\n"+git.FixerTrailer+": base", start)
	merged := w.Git("rev-parse", "HEAD")
	w.Push("c/one")
	one.Generation++
	one.Spec.Head = merged
	one.Status.Checks = map[string]gitk8s.CheckResult{
		"base":  {Commit: merged, ParentCommit: start, State: gitk8s.Passed},
		"gofmt": {Commit: merged, State: gitk8s.Passed},
	}
	if msg := reconcile(one); one.Status.State != reasonLanded || one.Status.Queued != nil {
		t.Fatalf("c/one: state %q, queued %+v, %q", one.Status.State, one.Status.Queued, msg)
	}
	if got := srv.Heads(t, "app")["main"]; got != merged {
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
	srv := gittest.NewServer(t, "")
	one, two, w := behind(t, srv)
	main := parentOf(one)
	start := main.Spec.Head
	reconcile := func(b *gitk8s.GitBranch) string {
		t.Helper()
		return mergeIn(t, srv, main, b)
	}
	w.Branch("c/two", start)
	w.Write("two.txt", "c/two\n")
	two.Spec.Head = w.Commit("add c/two")
	w.Push("c/two")
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
	if got := srv.Heads(t, "app")["main"]; got != start {
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
	if got := srv.Heads(t, "app")["main"]; got != start {
		t.Fatalf("main moved to %s", got)
	}

	t.Log("c/one's gofmt check fails, so c/one leaves the queue, and c/two lands.")
	one.Status.Checks["gofmt"] = gitk8s.CheckResult{Commit: one.Spec.Head, State: gitk8s.Failed}
	if msg := reconcile(one); one.Status.State != reasonWaitingForChecks || one.Status.Queued != nil {
		t.Fatalf("c/one: state %q, queued %+v, %q", one.Status.State, one.Status.Queued, msg)
	}
	if got := srv.Heads(t, "app")["main"]; got != start {
		t.Fatalf("main moved to %s", got)
	}
	if got, want := queueOf(t, main, one, two), []string{"c/two"}; !slices.Equal(got, want) {
		t.Fatalf("queue = %q, want %q", got, want)
	}
	if msg := reconcile(two); two.Status.State != reasonLanded {
		t.Fatalf("c/two: state %q, %q", two.Status.State, msg)
	}
	if got := srv.Heads(t, "app")["main"]; got != two.Spec.Head {
		t.Errorf("main = %s, want %s", got, two.Spec.Head)
	}
}

func TestRejoinsAtTheBack(t *testing.T) {
	srv := gittest.NewServer(t, "")
	one, two, w := behind(t, srv)
	main := parentOf(one, "c/one", "c/two")
	start := main.Spec.Head
	since := time.Date(2026, 1, 1, 0, 0, 0, 0, time.UTC)
	one.Status.Queued = &gitk8s.Queued{Since: since, Head: one.Spec.Head, Position: 1}
	two.Status.Queued = &gitk8s.Queued{Since: since, Head: two.Spec.Head, Position: 2}
	reconcile := func(b *gitk8s.GitBranch) string {
		t.Helper()
		return mergeIn(t, srv, main, b)
	}

	t.Log("Someone pushes to c/one at the front of main's queue, and the checks pass on the new head before main's queue drops c/one.")
	w.Branch("c/one", one.Spec.Head)
	w.Write("more.txt", "more\n")
	head := w.Commit("more work")
	w.Push("c/one")
	one.Generation++
	one.Spec.Head = head
	one.Status.Checks = map[string]gitk8s.CheckResult{
		"base":  {Commit: head, ParentCommit: start, State: gitk8s.Passed, Outputs: map[string]string{"behind": "true"}},
		"gofmt": {Commit: head, State: gitk8s.Passed},
	}
	if msg := reconcile(one); one.Status.Queued != nil || msg != "rejoining main's queue at the back" {
		t.Fatalf("c/one: queued %+v, %q", one.Status.Queued, msg)
	}

	t.Log("main's queue drops c/one, which then joins at the back.")
	if got, want := queueOf(t, main, one, two), []string{"c/two"}; !slices.Equal(got, want) {
		t.Fatalf("queue = %q, want %q", got, want)
	}
	if msg := reconcile(one); one.Status.Queued == nil || msg != "joining main's queue" {
		t.Fatalf("c/one: queued %+v, %q", one.Status.Queued, msg)
	}
	if got, want := queueOf(t, main, one, two), []string{"c/two", "c/one"}; !slices.Equal(got, want) {
		t.Fatalf("queue = %q, want %q", got, want)
	}
	if msg := reconcile(one); msg != "2 of 2 in main's queue" {
		t.Errorf("c/one: %q", msg)
	}
	if msg := reconcile(two); msg != "first in main's queue; waiting for the base check to merge main in" {
		t.Errorf("c/two: %q", msg)
	}
	if got := srv.Heads(t, "app")["main"]; got != start {
		t.Errorf("main moved to %s", got)
	}
}

func TestKeepsItsPlaceWhileItsCacheLags(t *testing.T) {
	srv := gittest.NewServer(t, "")
	one, two, _ := behind(t, srv)
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
		msg := mergeIn(t, srv, main, tc.b, &live)
		if q := tc.b.Status.Queued; q == nil || !q.Since.Equal(since) || q.Position != tc.pos || msg != tc.want {
			t.Errorf("%s: queued %+v, %q; want its place at %d, %q", tc.b.Spec.Branch, q, msg, tc.pos, tc.want)
		}
	}
	if got := srv.Heads(t, "app")["main"]; got != start {
		t.Errorf("main moved to %s", got)
	}
}

func TestLeavingTheQueue(t *testing.T) {
	since := time.Date(2026, 1, 1, 0, 0, 0, 0, time.UTC)
	for _, tc := range []struct {
		name string
		edit func(*gitk8s.GitBranch, *gittest.Work)
		// state is the branch's state afterward, Queued if it keeps its place.
		state string
	}{{
		name: "a check pushes a fix",
		edit: func(b *gitk8s.GitBranch, w *gittest.Work) {
			w.Write("x.txt", "fixed\n")
			b.Spec.Head = w.Commit("Fix x\n\n" + git.FixerTrailer + ": gofmt")
			w.Push("c/x")
		},
		state: reasonQueued,
	}, {
		name: "a check is still running",
		edit: func(b *gitk8s.GitBranch, _ *gittest.Work) {
			b.Status.Checks["gofmt"] = gitk8s.CheckResult{Commit: b.Spec.Head, State: gitk8s.Running}
		},
		state: reasonQueued,
	}, {
		name: "a person pushes",
		edit: func(b *gitk8s.GitBranch, w *gittest.Work) {
			w.Write("more.txt", "more\n")
			b.Spec.Head = w.Commit("more work")
			w.Push("c/x")
		},
		state: reasonWaitingForChecks,
	}, {
		name: "someone force-pushes",
		edit: func(b *gitk8s.GitBranch, w *gittest.Work) {
			w.Branch("c/x", b.Spec.ParentHead)
			w.Write("other.txt", "other\n")
			b.Spec.Head = w.Commit("start over")
			w.Push("c/x")
		},
		state: reasonWaitingForChecks,
	}, {
		name: "a check fails",
		edit: func(b *gitk8s.GitBranch, _ *gittest.Work) {
			b.Status.Checks["gofmt"] = gitk8s.CheckResult{Commit: b.Spec.Head, State: gitk8s.Failed}
		},
		state: reasonWaitingForChecks,
	}, {
		name: "the gate is invalid",
		edit: func(b *gitk8s.GitBranch, _ *gittest.Work) {
			p := *policy
			p.When = "checks.missing.passed"
			b.Spec.Merge = &p
		},
		state: reasonInvalidGate,
	}, {
		name:  "the parent is gone",
		edit:  func(b *gitk8s.GitBranch, _ *gittest.Work) { b.Spec.ParentHead = "" },
		state: reasonParentMissing,
	}} {
		t.Run(tc.name, func(t *testing.T) {
			srv := gittest.NewServer(t, "")
			b, w := branches(t, srv)
			b.Status.Queued = &gitk8s.Queued{Since: since, Head: b.Spec.Head, Position: 1}
			main := b.Spec.ParentHead
			tc.edit(b, w)
			if err := merge(t, srv, b); err != nil {
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
			if got := srv.Heads(t, "app")["main"]; got != main {
				t.Errorf("main moved to %s", got)
			}
		})
	}
}

func TestLeavingTheFront(t *testing.T) {
	since := time.Date(2026, 1, 1, 0, 0, 0, 0, time.UTC)
	for _, tc := range []struct {
		name string
		// when is the gate of a merge policy that lists base, gofmt, and
		// approval. gofmt fails, and approval doesn't finish.
		when string
		base string
		// queue is main's queue.
		queue []string
		// stays reports whether c/x keeps its place.
		stays bool
	}{{
		name:  "every check must pass",
		base:  gitk8s.Passed,
		queue: []string{"c/x"},
	}, {
		name:  "behind the front",
		base:  gitk8s.Passed,
		queue: []string{"c/a", "c/x"},
		stays: true,
	}, {
		name:  "the gate can still pass",
		when:  `checks.base.passed && (checks.gofmt.passed || checks.approval.passed)`,
		base:  gitk8s.Passed,
		queue: []string{"c/x"},
		stays: true,
	}, {
		name:  "the gate can't pass",
		when:  `checks.base.passed && checks.gofmt.passed`,
		base:  gitk8s.Passed,
		queue: []string{"c/x"},
	}, {
		name:  "the gate reads an output that isn't set yet",
		when:  `checks.base.passed && (checks.gofmt.passed || checks.approval.outputs.by != "")`,
		base:  gitk8s.Passed,
		queue: []string{"c/x"},
		stays: true,
	}, {
		name:  "the base check fails",
		when:  `checks.approval.passed`,
		base:  gitk8s.Failed,
		queue: []string{"c/x"},
	}} {
		t.Run(tc.name, func(t *testing.T) {
			srv := gittest.NewServer(t, "")
			b, _ := branches(t, srv)
			p := *policy
			p.Checks = append(p.Checks[:2:2], gitk8s.CheckPolicy{Name: "approval"})
			p.When = tc.when
			b.Spec.Merge = &p
			b.Status.Checks["base"] = gitk8s.CheckResult{Commit: b.Spec.Head, ParentCommit: b.Spec.ParentHead, State: tc.base}
			b.Status.Checks["gofmt"] = gitk8s.CheckResult{Commit: b.Spec.Head, State: gitk8s.Failed}
			pos := int32(slices.Index(tc.queue, "c/x") + 1)
			b.Status.Queued = &gitk8s.Queued{Since: since, Head: b.Spec.Head, Position: pos}
			main := b.Spec.ParentHead
			msg := mergeIn(t, srv, parentOf(b, tc.queue...), b)
			switch q := b.Status.Queued; {
			case tc.stays && (b.Status.State != reasonQueued || q == nil || !q.Since.Equal(since) || q.Position != pos):
				t.Errorf("state = %q, queued %+v, %q; want its place at %d", b.Status.State, q, msg, pos)
			case !tc.stays && (b.Status.State != reasonWaitingForChecks || q != nil):
				t.Errorf("state = %q, queued %+v, %q; want %s, out of the queue", b.Status.State, q, msg, reasonWaitingForChecks)
			}
			if got := srv.Heads(t, "app")["main"]; got != main {
				t.Errorf("main moved to %s", got)
			}
		})
	}
}

func TestLandsWithoutAQueue(t *testing.T) {
	srv := gittest.NewServer(t, "")
	b, _ := branches(t, srv)
	p := *policy
	p.Checks = []gitk8s.CheckPolicy{{Name: "base"}, {Name: "gofmt", MayPush: true}}
	b.Spec.Merge = &p
	repo, secret := srv.Repository("app", rules()...)
	ctx, _ := kube.Fake(t.Context(), b, repo, secret)
	if err := (&merger{cache: &gitk8s.Cache{Git: &git.Git{}, Dir: t.TempDir()}}).Reconcile(ctx, b); err != nil {
		t.Fatal(err)
	}
	if b.Status.State != reasonLanded || b.Status.Queued != nil {
		t.Errorf("state = %q, queued %+v; a base check that can't push merges nothing, so branches land without a queue", b.Status.State, b.Status.Queued)
	}
}
