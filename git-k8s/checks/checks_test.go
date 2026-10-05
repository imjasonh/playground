package checks_test

import (
	"context"
	"net/http/httptest"
	"reflect"
	"strings"
	"testing"

	gitk8s "github.com/imjasonh/playground/git-k8s"
	"github.com/imjasonh/playground/git-k8s/checks"
	"github.com/imjasonh/playground/git-k8s/internal/git"
	"github.com/imjasonh/playground/git-k8s/internal/gitserver"
	"github.com/imjasonh/playground/git-k8s/internal/gittest"
	"github.com/imjasonh/playground/git-k8s/signing"
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

// remote reaches the repository at the GitRepository's URL in place of the
// mirror. Every test server here requires the password pw.
func remote(_ context.Context, repo *gitk8s.Repository) (git.Remote, error) {
	return git.Remote{URL: repo.Spec.URL, Auth: &git.Auth{Username: "git-k8s", Password: "pw"}}, nil
}

// touch passes branches that have a TOUCHED file, and otherwise proposes a
// commit that adds one.
func touch(runs *int) checks.Check {
	return checks.Check{Name: "touch", Remote: remote, SigningKey: signing.Key, Run: func(ctx context.Context, in *checks.Input) (checks.Verdict, error) {
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
		fix, err := in.CommitTree(ctx, tree, []string{in.Spec.Head}, "Touch\n\n"+git.FixerTrailer+": touch\n", c.Time)
		if err != nil {
			return checks.Verdict{}, err
		}
		v := checks.Fail("not touched")
		v.Fix = fix
		return v, nil
	}}
}

// replay proposes the branch's head replayed onto the parent's head, and
// then onto that replay, as a check that replays several commits does. It
// has touch's name, so the fixture's policy runs it.
func replay() checks.Check {
	return checks.Check{Name: "touch", Remote: remote, SigningKey: signing.Key, Run: func(ctx context.Context, in *checks.Input) (checks.Verdict, error) {
		repo, err := in.Repo(ctx)
		if err != nil {
			return checks.Verdict{}, err
		}
		c, err := repo.Commit(ctx, in.Spec.Head)
		if err != nil {
			return checks.Verdict{}, err
		}
		tip := in.Spec.ParentHead
		for range 2 {
			if tip, err = in.Replay(ctx, in.Spec.Head, tip, c.Tree); err != nil {
				return checks.Verdict{}, err
			}
		}
		v := checks.Fail("replayed")
		v.Fix = tip
		return v, nil
	}}
}

// forEachCommitter runs test with a check that commits with
// Input.CommitTree, and with one that commits with Input.Replay.
func forEachCommitter(t *testing.T, test func(t *testing.T, check checks.Check)) {
	runs := 0
	t.Run("CommitTree", func(t *testing.T) { test(t, touch(&runs)) })
	t.Run("Replay", func(t *testing.T) { test(t, replay()) })
}

type fixture struct {
	srv    *gittest.Server
	work   *gittest.Work
	repo   *gitk8s.GitRepository
	branch *Branch
	cfg    *checks.Config
	world  []any
}

// newFixture pushes main and a branch c/x that adds a file, and returns a
// GitBranch view for c/x whose policy runs the touch check.
func newFixture(t *testing.T, policy gitk8s.CheckPolicy) *fixture {
	srv := gittest.NewServer(t, "pw")
	return newFixtureOn(t, srv, srv.NewWork(t, "app"), policy)
}

// newFixtureOn is newFixture with a server, and a working repository for
// the repository app on it.
func newFixtureOn(t *testing.T, srv *gittest.Server, w *gittest.Work, policy gitk8s.CheckPolicy) *fixture {
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
	ctx, _ := kube.Fake(t.Context(), f.branch, append([]any{f.repo}, f.world...)...)
	return checks.NewReconciler[Branch](check, f.cfg).Reconcile(ctx, f.branch)
}

func TestRepoNeedsRemote(t *testing.T) {
	f := newFixture(t, gitk8s.CheckPolicy{Name: "touch", MayPush: true})
	runs := 0
	check := touch(&runs)
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
	if err := f.reconcile(t, touch(&runs)); err != nil {
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
	if err := f.reconcile(t, touch(&runs)); err != nil {
		t.Fatal(err)
	}
	if res := f.branch.Status.Checks.Result; res.State != gitk8s.Passed || res.Commit != fix || res.ParentCommit != "" {
		t.Errorf("result = %+v, want Passed for the fix and no parent commit", res)
	}

	// A final result for the same head doesn't run the check again.
	before := runs
	if err := f.reconcile(t, touch(&runs)); err != nil {
		t.Fatal(err)
	}
	if runs != before {
		t.Errorf("the check ran again for a head with a final result")
	}
}

func TestSignsFixes(t *testing.T) {
	f := newFixture(t, gitk8s.CheckPolicy{Name: "touch", MayPush: true})
	signer := gittest.NewSigner(t, f.cfg.Identity.Email)
	f.world = append(f.world, signer.Sign(f.repo))
	runs := 0
	if err := f.reconcile(t, touch(&runs)); err != nil {
		t.Fatal(err)
	}
	fix := f.work.Fetch("c/x")
	if res := f.branch.Status.Checks.Result; res.State != gitk8s.Fixed || res.Outputs["fix"] != fix {
		t.Fatalf("result = %+v, want Fixed with the pushed fix %s", res, fix)
	}
	if err := signer.Verify(f.work.Dir, fix); err != nil {
		t.Error(err)
	}
}

func TestSignsReplays(t *testing.T) {
	f := newFixture(t, gitk8s.CheckPolicy{Name: "touch", MayPush: true})
	signer := gittest.NewSigner(t, f.cfg.Identity.Email)
	f.world = append(f.world, signer.Sign(f.repo))
	reads := 0
	check := replay()
	check.SigningKey = func(ctx context.Context, repo *gitk8s.Repository) (*git.SigningKey, error) {
		reads++
		return signing.Key(ctx, repo)
	}
	if err := f.reconcile(t, check); err != nil {
		t.Fatal(err)
	}
	fix := f.work.Fetch("c/x")
	if res := f.branch.Status.Checks.Result; res.State != gitk8s.Fixed || res.Outputs["fix"] != fix {
		t.Fatalf("result = %+v, want Fixed with the pushed replays %s", res, fix)
	}
	for _, c := range []string{fix, fix + "~1"} {
		if err := signer.Verify(f.work.Dir, c); err != nil {
			t.Error(err)
		}
	}
	if reads != 1 {
		t.Errorf("read the signing key %d times for two replays, want once", reads)
	}
}

func TestCommitsNeedSigningKey(t *testing.T) {
	forEachCommitter(t, func(t *testing.T, check checks.Check) {
		f := newFixture(t, gitk8s.CheckPolicy{Name: "touch", MayPush: true})
		head := f.branch.Spec.Head
		check.SigningKey = nil
		err := f.reconcile(t, check)
		if err == nil || !strings.Contains(err.Error(), "set Check.SigningKey to signing.Key") {
			t.Fatalf("err = %v, want one that says to set Check.SigningKey", err)
		}
		if res := f.branch.Status.Checks.Result; res == nil || res.State != gitk8s.Error {
			t.Errorf("result = %+v, want Error", res)
		}
		if got := f.srv.Heads(t, "app")["c/x"]; got != head {
			t.Errorf("c/x moved to %s", got)
		}
	})
}

func TestMissingSigningKeyIsReported(t *testing.T) {
	forEachCommitter(t, func(t *testing.T, check checks.Check) {
		f := newFixture(t, gitk8s.CheckPolicy{Name: "touch", MayPush: true})
		f.repo.Spec.SigningKeyRef = &gitk8s.SecretRef{Name: "app-signing"}
		head := f.branch.Spec.Head
		if err := f.reconcile(t, check); err == nil {
			t.Fatal("reconcile without the signing key's Secret succeeded")
		}
		if res := f.branch.Status.Checks.Result; res == nil || res.State != gitk8s.Error || !strings.Contains(res.Message, "Secret app-signing doesn't exist") {
			t.Errorf("result = %+v, want Error because the Secret is missing", res)
		}
		if got := f.srv.Heads(t, "app")["c/x"]; got != head {
			t.Errorf("c/x moved to %s without a signature", got)
		}
	})
}

func TestStaleRunsTheCheckAgain(t *testing.T) {
	f := newFixture(t, gitk8s.CheckPolicy{Name: "touch"})
	f.work.Write("TOUCHED", "touched\n")
	f.branch.Spec.Head = f.work.Commit("touch")
	f.work.Push("c/x")
	runs, stale := 0, false
	check := touch(&runs)
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
	check := touch(&runs)
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
	if err := f.reconcile(t, touch(&runs)); err != nil {
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
	if err := f.reconcile(t, touch(&runs)); err != nil {
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

func TestDoesNotReadSigningKeyWithoutPermission(t *testing.T) {
	forEachCommitter(t, func(t *testing.T, check checks.Check) {
		f := newFixture(t, gitk8s.CheckPolicy{Name: "touch"})
		// The key's Secret doesn't exist, so reading the key fails.
		f.repo.Spec.SigningKeyRef = &gitk8s.SecretRef{Name: "app-signing"}
		if err := f.reconcile(t, check); err != nil {
			t.Fatal(err)
		}
		if res := f.branch.Status.Checks.Result; res.State != gitk8s.Failed || !strings.Contains(res.Message, "doesn't let this check push") {
			t.Errorf("result = %+v, want Failed because of the policy", res)
		}
	})
}

func TestStopsAtAutomatedCommitLimit(t *testing.T) {
	f := newFixture(t, gitk8s.CheckPolicy{Name: "touch", MayPush: true})
	zero := int32(0)
	f.branch.Spec.Merge.MaxAutomatedCommits = &zero
	head := f.branch.Spec.Head
	runs := 0
	if err := f.reconcile(t, touch(&runs)); err != nil {
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
	err := f.reconcile(t, touch(&runs))
	if err == nil || !strings.Contains(err.Error(), "push rejected") {
		t.Fatalf("err = %v, want a rejected push", err)
	}
	first := f.branch.Status.Checks.Result
	if first == nil || first.State != gitk8s.Error || first.Commit != f.branch.Spec.Head || !strings.Contains(first.Message, "stale info") {
		t.Fatalf("result = %+v, want Error for the listed head because the branch moved", first)
	}

	// kube retries until the next listing changes the head. Each retry
	// leaves the same result, so kube doesn't write the status again.
	if err := f.reconcile(t, touch(&runs)); err == nil {
		t.Fatal("retrying the stale head succeeded")
	}
	if got := f.branch.Status.Checks.Result; !reflect.DeepEqual(got, first) {
		t.Errorf("result after a retry = %+v, want the same as before, %+v", got, first)
	}
}

func TestRefusedPushIsReported(t *testing.T) {
	signer := gittest.NewSigner(t, "author@example.com")
	hs := httptest.NewServer(&gitserver.Server{Root: t.TempDir(), Username: "git-k8s", Password: "pw", AllowedSigners: signer.AllowedSigners})
	t.Cleanup(hs.Close)
	srv := &gittest.Server{URL: hs.URL, Username: "git-k8s", Password: "pw"}
	w := srv.NewWork(t, "app")
	w.SignWith(signer)
	f := newFixtureOn(t, srv, w, gitk8s.CheckPolicy{Name: "touch", MayPush: true})
	head := f.branch.Spec.Head

	// The server requires signed commits, and the repository names no
	// signing key, so the server refuses the fix.
	runs := 0
	if err := f.reconcile(t, touch(&runs)); err == nil {
		t.Fatal("reconcile succeeded though the server refused the fix")
	}
	if res := f.branch.Status.Checks.Result; res == nil || res.State != gitk8s.Error || !strings.Contains(res.Message, "isn't signed with its committer's key") {
		t.Errorf("result = %+v, want Error with the server's reason", res)
	}
	if got := f.srv.Heads(t, "app")["c/x"]; got != head {
		t.Errorf("c/x moved to %s", got)
	}
}

func TestRunErrorIsReported(t *testing.T) {
	f := newFixture(t, gitk8s.CheckPolicy{Name: "touch"})
	runs := 0
	check := touch(&runs)
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
	if err := f.reconcile(t, touch(&runs)); err != nil || runs != 0 {
		t.Errorf("reconcile = %v after %d runs, want no runs while the parent is missing", err, runs)
	}
}
