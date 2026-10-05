package checks_test

import (
	"context"
	"strings"
	"testing"

	gitk8s "github.com/imjasonh/playground/git-k8s"
	"github.com/imjasonh/playground/git-k8s/checks"
	"github.com/imjasonh/playground/git-k8s/internal/git"
	"github.com/imjasonh/playground/git-k8s/internal/gittest"
	"github.com/imjasonh/playground/kube"
)

type Branch struct {
	kube.Object `kube:"apiVersion=git-k8s.imjasonh.com/v1alpha1,kind=GitBranch,plural=gitbranches,scope=Namespaced"`
	Spec        gitk8s.GitBranchSpec `json:"spec"`
	Status      struct {
		Checks struct {
			Result *gitk8s.CheckResult `json:"touch,omitempty"`
		} `json:"checks,omitzero"`
	} `json:"status,omitzero"`
}

func (b *Branch) Parts() (*kube.ObjectMeta, *gitk8s.GitBranchSpec, **gitk8s.CheckResult) {
	return &b.ObjectMeta, &b.Spec, &b.Status.Checks.Result
}

// touch passes branches that have a TOUCHED file, and otherwise proposes a
// commit that adds one. It reaches the fixture's server in place of the
// mirror.
func (f *fixture) touch(runs *int) checks.Check {
	return checks.Check{Name: "touch", Remote: f.srv.RemoteFor, Run: func(ctx context.Context, in *checks.Input) (checks.Verdict, error) {
		*runs++
		repo, err := in.Repo(ctx)
		if err != nil {
			return checks.Verdict{}, err
		}
		entries, err := repo.LsTree(ctx, in.Spec.Head)
		if err != nil {
			return checks.Verdict{}, err
		}
		for _, e := range entries {
			if e.Path == "TOUCHED" {
				return checks.Pass("touched"), nil
			}
		}
		blob, err := repo.WriteBlob(ctx, []byte("touched\n"))
		if err != nil {
			return checks.Verdict{}, err
		}
		c, err := repo.Commit(ctx, in.Spec.Head)
		if err != nil {
			return checks.Verdict{}, err
		}
		tree, err := repo.ReplaceFiles(ctx, c.Tree, []git.TreeEntry{{Mode: "100644", SHA: blob, Path: "TOUCHED"}})
		if err != nil {
			return checks.Verdict{}, err
		}
		fix, err := repo.CommitTree(ctx, tree, []string{in.Spec.Head}, "Touch\n\n"+git.FixerTrailer+": touch\n", in.Identity, c.Time)
		if err != nil {
			return checks.Verdict{}, err
		}
		v := checks.Fail("not touched")
		v.Fix = fix
		return v, nil
	}}
}

type fixture struct {
	srv    *gittest.Server
	work   *gittest.Work
	repo   *gitk8s.GitRepository
	branch *Branch
	cfg    *checks.Config
}

// newFixture pushes main and a branch c/x that adds a file, and returns a
// GitBranch view for c/x whose policy runs the touch check.
func newFixture(t *testing.T, policy gitk8s.CheckPolicy) *fixture {
	srv := gittest.NewServer(t, "pw")
	w := srv.NewWork(t, "app")
	w.Write("README.md", "hello\n")
	main := w.Commit("main")
	w.Push("main")
	w.Branch("c/x", main)
	w.Write("x.txt", "x\n")
	head := w.Commit("add x")
	w.Push("c/x")

	repo := &gitk8s.GitRepository{
		Object: kube.Meta("app", nil),
		Spec:   gitk8s.GitRepositorySpec{URL: srv.Remote("app").URL},
	}
	repo.Namespace = "default"
	b := &Branch{Object: kube.Meta(gitk8s.BranchObjectName("app", "c/x"), nil)}
	b.Namespace = "default"
	b.Spec = gitk8s.GitBranchSpec{
		Repository: "app", Branch: "c/x", Head: head, Parent: "main", ParentHead: main,
		Merge: &gitk8s.MergePolicy{Checks: []gitk8s.CheckPolicy{policy}},
	}
	cfg := &checks.Config{CacheDir: t.TempDir(), Identity: git.Identity{Name: "git-k8s", Email: "git-k8s@example.com"}}
	return &fixture{srv: srv, work: w, repo: repo, branch: b, cfg: cfg}
}

func (f *fixture) reconcile(t *testing.T, check checks.Check) error {
	t.Helper()
	ctx, _ := kube.Fake(t.Context(), f.branch, f.repo)
	return checks.NewReconciler[Branch](check, f.cfg).Reconcile(ctx, f.branch)
}

func TestRepoNeedsRemote(t *testing.T) {
	f := newFixture(t, gitk8s.CheckPolicy{Name: "touch", MayPush: true})
	runs := 0
	check := f.touch(&runs)
	check.Remote = nil
	err := f.reconcile(t, check)
	if err == nil || !strings.Contains(err.Error(), "set Check.Remote to mirror.Remote") {
		t.Fatalf("err = %v, want one that says to set Check.Remote", err)
	}
	if res := f.branch.Status.Checks.Result; res == nil || res.State != gitk8s.Error {
		t.Errorf("result = %+v, want Error", res)
	}
}

func TestPushesFixThenPasses(t *testing.T) {
	f := newFixture(t, gitk8s.CheckPolicy{Name: "touch", MayPush: true})
	runs := 0
	if err := f.reconcile(t, f.touch(&runs)); err != nil {
		t.Fatal(err)
	}
	res := f.branch.Status.Checks.Result
	if res == nil || res.State != gitk8s.Fixed || res.Commit != f.branch.Spec.Head {
		t.Fatalf("result = %+v, want Fixed for the head", res)
	}
	fix := res.Outputs["fix"]
	if got := f.srv.Heads(t, "app")["c/x"]; got != fix {
		t.Fatalf("c/x = %s, want the fix %s", got, fix)
	}
	if msg := f.work.Git("log", "-1", "--format=%B", f.work.Fetch("c/x")); !strings.Contains(msg, git.FixerTrailer+": touch") {
		t.Errorf("fix commit message = %q, want the fixer trailer", msg)
	}

	// The repository controller lists the new head, and the check passes.
	f.branch.Spec.Head = fix
	if err := f.reconcile(t, f.touch(&runs)); err != nil {
		t.Fatal(err)
	}
	if res := f.branch.Status.Checks.Result; res.State != gitk8s.Passed || res.Commit != fix || res.ParentCommit != "" {
		t.Errorf("result = %+v, want Passed for the fix and no parent commit", res)
	}

	// A final result for the same head doesn't run the check again.
	before := runs
	if err := f.reconcile(t, f.touch(&runs)); err != nil {
		t.Fatal(err)
	}
	if runs != before {
		t.Errorf("the check ran again for a head with a final result")
	}
}

func TestStaleRunsTheCheckAgain(t *testing.T) {
	f := newFixture(t, gitk8s.CheckPolicy{Name: "touch"})
	f.work.Write("TOUCHED", "touched\n")
	f.branch.Spec.Head = f.work.Commit("touch")
	f.work.Push("c/x")
	runs, stale := 0, false
	check := f.touch(&runs)
	check.Stale = func(_ context.Context, meta *kube.ObjectMeta, spec *gitk8s.GitBranchSpec, previous *gitk8s.CheckResult) bool {
		if meta.Name != f.branch.Name || previous.Commit != spec.Head {
			t.Errorf("Stale got %s with a result for %s, want %s with a result for its head", meta.Name, previous.Commit, f.branch.Name)
		}
		return stale
	}
	for i, step := range []struct {
		stale bool
		runs  int
	}{{false, 1}, {false, 1}, {true, 2}} {
		stale = step.stale
		if err := f.reconcile(t, check); err != nil {
			t.Fatal(err)
		}
		if res := f.branch.Status.Checks.Result; runs != step.runs || res.State != gitk8s.Passed {
			t.Errorf("reconcile %d with Stale returning %v: %d runs, result %+v; want %d runs and Passed", i, step.stale, runs, res, step.runs)
		}
	}
}

func TestRecordsFilesOnly(t *testing.T) {
	f := newFixture(t, gitk8s.CheckPolicy{Name: "touch"})
	runs := 0
	check := f.touch(&runs)
	check.FilesOnly = true
	if err := f.reconcile(t, check); err != nil {
		t.Fatal(err)
	}
	if res := f.branch.Status.Checks.Result; res == nil || !res.Final() || !res.FilesOnly {
		t.Fatalf("result = %+v, want a final result with filesOnly", res)
	}

	// A result with filesOnly from before the check stopped setting it
	// must not count for a squashed commit, so the check runs again.
	check.FilesOnly = false
	for range 2 {
		if err := f.reconcile(t, check); err != nil {
			t.Fatal(err)
		}
	}
	if res := f.branch.Status.Checks.Result; res.FilesOnly || runs != 2 {
		t.Fatalf("result = %+v after %d runs, want no filesOnly after 2 runs", res, runs)
	}

	// A result without filesOnly only costs a landing a round of checks, so
	// a check that starts setting FilesOnly doesn't run again for it.
	check.FilesOnly = true
	if err := f.reconcile(t, check); err != nil {
		t.Fatal(err)
	}
	if res := f.branch.Status.Checks.Result; res.FilesOnly || runs != 2 {
		t.Errorf("result = %+v after %d runs, want the same result without filesOnly", res, runs)
	}
}

func TestRemovesResultWhenNotListed(t *testing.T) {
	f := newFixture(t, gitk8s.CheckPolicy{Name: "other"})
	f.branch.Status.Checks.Result = &gitk8s.CheckResult{Commit: "old", State: gitk8s.Passed}
	runs := 0
	if err := f.reconcile(t, f.touch(&runs)); err != nil {
		t.Fatal(err)
	}
	if f.branch.Status.Checks.Result != nil || runs != 0 {
		t.Errorf("result = %+v after %d runs; want no result and no runs", f.branch.Status.Checks.Result, runs)
	}
}

func TestDoesNotPushWithoutPermission(t *testing.T) {
	f := newFixture(t, gitk8s.CheckPolicy{Name: "touch"})
	head := f.branch.Spec.Head
	runs := 0
	if err := f.reconcile(t, f.touch(&runs)); err != nil {
		t.Fatal(err)
	}
	res := f.branch.Status.Checks.Result
	if res.State != gitk8s.Failed || !strings.Contains(res.Message, "doesn't let this check push") {
		t.Errorf("result = %+v, want Failed because of the policy", res)
	}
	if got := f.srv.Heads(t, "app")["c/x"]; got != head {
		t.Errorf("c/x moved to %s without permission", got)
	}
}

func TestStopsAtAutomatedCommitLimit(t *testing.T) {
	f := newFixture(t, gitk8s.CheckPolicy{Name: "touch", MayPush: true})
	zero := int32(0)
	f.branch.Spec.Merge.MaxAutomatedCommits = &zero
	head := f.branch.Spec.Head
	runs := 0
	if err := f.reconcile(t, f.touch(&runs)); err != nil {
		t.Fatal(err)
	}
	if res := f.branch.Status.Checks.Result; res.State != gitk8s.Failed || !strings.Contains(res.Message, "the limit") {
		t.Errorf("result = %+v, want Failed at the limit", res)
	}
	if got := f.srv.Heads(t, "app")["c/x"]; got != head {
		t.Errorf("c/x moved to %s past the limit", got)
	}
}

func TestStaleHeadIsRetried(t *testing.T) {
	f := newFixture(t, gitk8s.CheckPolicy{Name: "touch", MayPush: true})
	// Someone pushes after the repository controller listed the branch.
	f.work.Write("y.txt", "y\n")
	f.work.Commit("add y")
	f.work.Push("c/x")
	runs := 0
	err := f.reconcile(t, f.touch(&runs))
	if err == nil || !strings.Contains(err.Error(), "push rejected") {
		t.Fatalf("err = %v, want a rejected push", err)
	}
	if f.branch.Status.Checks.Result != nil {
		t.Errorf("result = %+v, want none until the check runs on the new head", f.branch.Status.Checks.Result)
	}
}

func TestRunErrorIsReported(t *testing.T) {
	f := newFixture(t, gitk8s.CheckPolicy{Name: "touch"})
	runs := 0
	check := f.touch(&runs)
	check.Remote = func(context.Context, *gitk8s.Repository) (git.Remote, error) {
		r := f.srv.Remote("app")
		r.Auth.Password = "wrong"
		return r, nil
	}
	if err := f.reconcile(t, check); err == nil {
		t.Fatal("reconcile with the wrong password succeeded")
	}
	if res := f.branch.Status.Checks.Result; res == nil || res.State != gitk8s.Error {
		t.Errorf("result = %+v, want Error", res)
	}
}

func TestWaitsForHeads(t *testing.T) {
	f := newFixture(t, gitk8s.CheckPolicy{Name: "touch"})
	f.branch.Spec.ParentHead = ""
	runs := 0
	if err := f.reconcile(t, f.touch(&runs)); err != nil || runs != 0 {
		t.Errorf("reconcile = %v after %d runs, want no runs while the parent is missing", err, runs)
	}
}
