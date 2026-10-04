package checks_test

import (
	"context"
	"fmt"
	"strings"
	"testing"

	gitk8s "github.com/imjasonh/playground/git-k8s"
	"github.com/imjasonh/playground/git-k8s/checks"
	"github.com/imjasonh/playground/git-k8s/credentials"
	"github.com/imjasonh/playground/git-k8s/internal/git"
	"github.com/imjasonh/playground/git-k8s/internal/gittest"
	"github.com/imjasonh/playground/kube"
	"github.com/imjasonh/playground/kube/k8s"
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
// commit that adds one.
func touch(runs *int) checks.Check {
	return checks.Check{Name: "touch", Remote: credentials.Remote, Run: func(ctx context.Context, in *checks.Input) (checks.Verdict, error) {
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
	secret *k8s.Secret
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
		Spec:   gitk8s.GitRepositorySpec{URL: srv.Remote("app").URL, SecretRef: &gitk8s.SecretRef{Name: "creds"}},
	}
	repo.Namespace = "default"
	secret := &k8s.Secret{Object: kube.Meta("creds", nil), Data: map[string][]byte{"username": []byte(srv.Username), "password": []byte(srv.Password)}}
	secret.Namespace = "default"
	b := &Branch{Object: kube.Meta(gitk8s.BranchObjectName("app", "c/x"), nil)}
	b.Namespace = "default"
	b.Spec = gitk8s.GitBranchSpec{
		Repository: "app", Branch: "c/x", Head: head, Parent: "main", ParentHead: main,
		Merge: &gitk8s.MergePolicy{Checks: []gitk8s.CheckPolicy{policy}},
	}
	cfg := &checks.Config{CacheDir: t.TempDir(), Identity: git.Identity{Name: "git-k8s", Email: "git-k8s@example.com"}}
	return &fixture{srv: srv, work: w, repo: repo, secret: secret, branch: b, cfg: cfg}
}

func (f *fixture) reconcile(t *testing.T, check checks.Check) error {
	t.Helper()
	ctx, _ := kube.Fake(t.Context(), f.branch, f.repo, f.secret)
	return checks.NewReconciler[Branch](check, f.cfg).Reconcile(ctx, f.branch)
}

func TestRepoNeedsRemote(t *testing.T) {
	f := newFixture(t, gitk8s.CheckPolicy{Name: "touch", MayPush: true})
	runs := 0
	check := touch(&runs)
	check.Remote = nil
	err := f.reconcile(t, check)
	if err == nil || !strings.Contains(err.Error(), "set Check.Remote to credentials.Remote") {
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

// The output fix counts toward the core program's limit, and the framework
// checks the Fixed result before it pushes, so that a fix doesn't land with
// an Error result.
func TestChecksFixedResultBeforePushing(t *testing.T) {
	for _, tc := range []struct {
		name          string
		outputs       int
		mayPush       bool
		state         string
		msg           string
		resultOutputs int
		pushed        bool
	}{
		{"the most outputs", gitk8s.MaxOutputs, true, gitk8s.Error,
			"not pushing the fix because the core program wouldn't accept the Fixed result: the result has more than 16 outputs", 0, false},
		{"room for the fix", gitk8s.MaxOutputs - 1, true, gitk8s.Fixed, "; pushed ", gitk8s.MaxOutputs, true},
		{"no permission to push", gitk8s.MaxOutputs - 1, false, gitk8s.Failed, "doesn't let this check push", gitk8s.MaxOutputs - 1, false},
	} {
		t.Run(tc.name, func(t *testing.T) {
			f := newFixture(t, gitk8s.CheckPolicy{Name: "touch", MayPush: tc.mayPush})
			head := f.branch.Spec.Head
			runs := 0
			check := touch(&runs)
			run := check.Run
			check.Run = func(ctx context.Context, in *checks.Input) (checks.Verdict, error) {
				v, err := run(ctx, in)
				v.Outputs = map[string]string{}
				for i := range tc.outputs {
					v.Outputs[fmt.Sprintf("output-%d", i)] = "v"
				}
				return v, err
			}
			if err := f.reconcile(t, check); err != nil {
				t.Fatal(err)
			}
			res := f.branch.Status.Checks.Result
			if res == nil || res.State != tc.state || !strings.Contains(res.Message, tc.msg) || len(res.Outputs) != tc.resultOutputs {
				t.Errorf("result = %+v, want %s with %d outputs and a message that contains %q", res, tc.state, tc.resultOutputs, tc.msg)
			}
			if pushed := f.srv.Heads(t, "app")["c/x"] != head; pushed != tc.pushed {
				t.Errorf("pushed the fix: %v, want %v", pushed, tc.pushed)
			}
		})
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
	if f.branch.Status.Checks.Result != nil {
		t.Errorf("result = %+v, want none until the check runs on the new head", f.branch.Status.Checks.Result)
	}
}

func TestRunErrorIsReported(t *testing.T) {
	f := newFixture(t, gitk8s.CheckPolicy{Name: "touch"})
	f.secret.Data["password"] = []byte("wrong")
	runs := 0
	if err := f.reconcile(t, touch(&runs)); err == nil {
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
