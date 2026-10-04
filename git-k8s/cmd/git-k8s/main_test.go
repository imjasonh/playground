package main

import (
	"os"
	"regexp"
	"strconv"
	"strings"
	"testing"
	"time"

	gitk8s "github.com/imjasonh/playground/git-k8s"
	"github.com/imjasonh/playground/git-k8s/internal/git"
	"github.com/imjasonh/playground/git-k8s/internal/gittest"
	"github.com/imjasonh/playground/kube"
)

var policy = &gitk8s.MergePolicy{
	Checks:               []gitk8s.CheckPolicy{{Name: "base", MayPush: true}, {Name: "gofmt", MayPush: true}},
	DeleteMergedBranches: true,
}

func rules() []gitk8s.BranchRule {
	return []gitk8s.BranchRule{{Match: "main", Merge: policy}, {Match: "c/**", Parent: "main"}}
}

func TestListsBranches(t *testing.T) {
	srv := gittest.NewServer(t, "pw")
	w := srv.NewWork(t, "app")
	main := w.Commit("main")
	w.Push("main")
	w.Branch("c/add", main)
	add := w.Commit("add")
	w.Push("c/add")
	w.Push("feature/ignored")

	repo, secret := srv.Repository("app", rules()...)
	ctx, rec := kube.Fake(t.Context(), repo, secret)
	if err := (&repositories{git: &git.Git{}}).Reconcile(ctx, repo); err != nil {
		t.Fatal(err)
	}
	owned := kube.Owned[gitk8s.GitBranch](rec)
	if len(owned) != 2 {
		t.Fatalf("owned %d GitBranches, want 2: %+v", len(owned), owned)
	}
	got := map[string]*gitk8s.GitBranch{}
	for _, b := range owned {
		got[b.Spec.Branch] = b
	}
	b := got["c/add"]
	if b == nil || b.Name != gitk8s.BranchObjectName("app", "c/add") || b.Labels[gitk8s.RepositoryLabel] != "app" {
		t.Fatalf("c/add = %+v", b)
	}
	if b.Spec.Head != add || b.Spec.ParentHead != main || b.Spec.Merge != policy {
		t.Errorf("c/add spec = %+v", b.Spec)
	}
	if got["main"] == nil || got["main"].Spec.Parent != "" {
		t.Errorf("main = %+v", got["main"])
	}
	if repo.Status.Branches != 2 || rec.RequeueAfter() != 30*time.Second {
		t.Errorf("status branches = %d, requeue = %v", repo.Status.Branches, rec.RequeueAfter())
	}
	if c := kube.FindCondition(repo.Status.Conditions, "Ready"); c == nil || c.Status != kube.True || c.Message != "tracking 2 of 3 branches" {
		t.Errorf("Ready = %+v", c)
	}
}

func TestReusesARecentListing(t *testing.T) {
	srv := gittest.NewServer(t, "pw")
	w := srv.NewWork(t, "app")
	main := w.Commit("main")
	w.Push("main")
	w.Branch("c/add", main)
	add := w.Commit("add")
	w.Push("c/add")
	repo, secret := srv.Repository("app", rules()...)
	now := time.Unix(1000, 0)
	r := &repositories{git: &git.Git{}, now: func() time.Time { return now }}
	reconcile := func() (head string, requeue time.Duration) {
		t.Helper()
		ctx, rec := kube.Fake(t.Context(), repo, secret)
		if err := r.Reconcile(ctx, repo); err != nil {
			t.Fatal(err)
		}
		for _, b := range kube.Owned[gitk8s.GitBranch](rec) {
			if b.Spec.Branch == "c/add" {
				head = b.Spec.Head
			}
		}
		return head, rec.RequeueAfter()
	}
	if head, _ := reconcile(); head != add {
		t.Fatalf("c/add = %s, want %s", head, add)
	}

	t.Log("A check pushes a fix. Its result runs the reconcile a second later, which reuses the listing and runs again once the listing is 5s old.")
	w.Write("fix.txt", "fix\n")
	fix := w.Commit("fix")
	w.Push("c/add")
	now = now.Add(time.Second)
	if head, requeue := reconcile(); head != add || requeue != 4*time.Second {
		t.Errorf("c/add = %s, requeue = %v; want the listed head %s and a requeue in 4s", head, requeue, add)
	}
	now = now.Add(4 * time.Second)
	if head, requeue := reconcile(); head != fix || requeue != 30*time.Second {
		t.Errorf("c/add = %s, requeue = %v; want the fix %s and the poll interval", head, requeue, fix)
	}
}

func TestReportsAdmissionPolicies(t *testing.T) {
	srv := gittest.NewServer(t, "pw")
	w := srv.NewWork(t, "app")
	w.Commit("main")
	w.Push("main")
	repo, secret := srv.Repository("app", rules()...)
	reconcile := func(world ...any) *kube.Condition {
		t.Helper()
		ctx, _ := kube.Fake(t.Context(), repo, append([]any{secret}, world...)...)
		if err := (&repositories{git: &git.Git{}}).Reconcile(ctx, repo); err != nil {
			t.Fatal(err)
		}
		return kube.FindCondition(repo.Status.Conditions, "PoliciesInstalled")
	}
	if c := reconcile(); c == nil || c.Status != kube.False || !strings.Contains(c.Message, "git-k8s-check-results and git-k8s-branches aren't installed with bindings that deny") {
		t.Errorf("without the policies, PoliciesInstalled = %+v", c)
	}

	var world []any
	var policies []*admissionPolicy
	var bindings []*admissionPolicyBinding
	for _, name := range policyNames {
		p := &admissionPolicy{Object: kube.Meta(name, nil)}
		b := &admissionPolicyBinding{Object: kube.Meta(name, nil)}
		b.Spec.PolicyName, b.Spec.ValidationActions = name, []string{"Warn"}
		policies, bindings = append(policies, p), append(bindings, b)
		world = append(world, p, b)
	}
	if c := reconcile(world...); c.Status != kube.False || c.Reason != "Missing" {
		t.Errorf("with bindings that only warn, PoliciesInstalled = %+v", c)
	}
	for _, b := range bindings {
		b.Spec.ValidationActions = []string{"Deny"}
	}
	if c := reconcile(world...); c.Status != kube.False || c.Reason != "Outdated" || !strings.Contains(c.Message, "git-k8s-check-results and git-k8s-branches don't have git-k8s.imjasonh.com/policy-version=2") {
		t.Errorf("with policies from an earlier release, which have no version, PoliciesInstalled = %+v", c)
	}
	bindings[0].Spec.ValidationActions = []string{"Warn"}
	if c := reconcile(world...); c.Status != kube.False || c.Reason != "Missing" || !strings.Contains(c.Message, ": "+policyNames[0]+" isn't installed") {
		t.Errorf("with one binding that only warns and the other policy from an earlier release, PoliciesInstalled = %+v", c)
	}
	bindings[0].Spec.ValidationActions = []string{"Deny"}
	current, later := strconv.Itoa(policyVersion), strconv.Itoa(policyVersion+1)
	policies[0].Annotations = map[string]string{policyVersionAnnotation: "1"}
	policies[1].Annotations = map[string]string{policyVersionAnnotation: current}
	if c := reconcile(world...); c.Status != kube.False || c.Reason != "Outdated" || !strings.Contains(c.Message, ": git-k8s-check-results doesn't have") {
		t.Errorf("with one policy at an earlier version, PoliciesInstalled = %+v", c)
	}
	policies[0].Annotations[policyVersionAnnotation] = later
	policies[1].Annotations[policyVersionAnnotation] = "v3"
	if c := reconcile(world...); c.Status != kube.False || c.Reason != "Outdated" || !strings.Contains(c.Message, ": git-k8s-branches doesn't have") {
		t.Errorf("with one policy at a later version and the other at a version that isn't a number, PoliciesInstalled = %+v", c)
	}
	policies[1].Annotations[policyVersionAnnotation] = later
	if c := reconcile(world...); c.Status != kube.False || c.Reason != "Newer" || strings.Contains(c.Message, "apply") ||
		!strings.Contains(c.Message, "upgrade the core program: git-k8s-check-results and git-k8s-branches have a git-k8s.imjasonh.com/policy-version later than 2") {
		t.Errorf("with policies from a later release, PoliciesInstalled = %+v", c)
	}
	for _, p := range policies {
		p.Annotations = map[string]string{policyVersionAnnotation: current}
	}
	if c := reconcile(world...); c.Status != kube.True {
		t.Errorf("with the policies installed, PoliciesInstalled = %+v", c)
	}
}

// Each policy in config/policy.yaml has the version that policiesCondition
// expects, or PoliciesInstalled stays False.
func TestPolicyFileVersion(t *testing.T) {
	data, err := os.ReadFile("../../config/policy.yaml")
	if err != nil {
		t.Fatal(err)
	}
	kind := regexp.MustCompile(`(?m)^kind: ValidatingAdmissionPolicy$`)
	name := regexp.MustCompile(`(?m)^  name: (\S+)$`)
	version := regexp.MustCompile(`(?m)^    ` + regexp.QuoteMeta(policyVersionAnnotation) + `: "(.*)"$`)
	versions := map[string]string{}
	for _, doc := range strings.Split(string(data), "\n---\n") {
		if !kind.MatchString(doc) {
			continue
		}
		n, v := name.FindStringSubmatch(doc), version.FindStringSubmatch(doc)
		if n == nil || v == nil {
			t.Fatalf("found a policy without a name or a version:\n%s", doc)
		}
		versions[n[1]] = v[1]
	}
	want := strconv.Itoa(policyVersion)
	for _, n := range policyNames {
		if versions[n] != want {
			t.Errorf("config/policy.yaml has %s at version %q, want %q", n, versions[n], want)
		}
	}
}

func TestListFailureKeepsBranches(t *testing.T) {
	srv := gittest.NewServer(t, "pw")
	repo, secret := srv.Repository("app", rules()...)
	secret.Data["password"] = []byte("wrong")
	ctx, rec := kube.Fake(t.Context(), repo, secret)
	if err := (&repositories{git: &git.Git{}}).Reconcile(ctx, repo); err == nil {
		t.Fatal("reconcile with the wrong password succeeded")
	}
	if c := kube.FindCondition(repo.Status.Conditions, "Ready"); c == nil || c.Reason != "ListFailed" {
		t.Errorf("Ready = %+v", c)
	}
	if len(kube.Owned[gitk8s.GitBranch](rec)) != 0 {
		t.Error("declared GitBranches without listing the remote")
	}
}

func TestInvalidPolicyIsPermanent(t *testing.T) {
	for _, mod := range []func(*gitk8s.GitRepository){
		func(r *gitk8s.GitRepository) { r.Spec.PollInterval = "1ms" },
		func(r *gitk8s.GitRepository) {
			r.Spec.Branches = []gitk8s.BranchRule{{Match: "main", Merge: &gitk8s.MergePolicy{When: "checks.base.passed &&"}}}
		},
	} {
		repo := &gitk8s.GitRepository{Object: kube.Meta("app", nil), Spec: gitk8s.GitRepositorySpec{URL: "http://127.0.0.1:1/app.git"}}
		repo.Namespace = "default"
		mod(repo)
		ctx, _ := kube.Fake(t.Context(), repo)
		if err := (&repositories{git: &git.Git{}}).Reconcile(ctx, repo); !kube.IsPermanent(err) {
			t.Errorf("err = %v, want a permanent error", err)
		}
	}
}

// branches pushes main and c/x, which adds a file on top of main, and
// returns c/x's GitBranch with fresh, passing results for the policy's
// checks.
func branches(t *testing.T, srv *gittest.Server) (*gitk8s.GitBranch, *gittest.Work) {
	w := srv.NewWork(t, "app")
	main := w.Commit("main")
	w.Push("main")
	w.Branch("c/x", main)
	w.Write("x.txt", "x\n")
	head := w.Commit("add x")
	w.Push("c/x")
	b := &gitk8s.GitBranch{Object: kube.Meta(gitk8s.BranchObjectName("app", "c/x"), nil)}
	b.Namespace = "default"
	b.Spec = gitk8s.GitBranchSpec{Repository: "app", Branch: "c/x", Head: head, Parent: "main", ParentHead: main, Merge: policy}
	b.Status.Checks = map[string]gitk8s.CheckResult{
		"base":  {Commit: head, ParentCommit: main, State: gitk8s.Passed},
		"gofmt": {Commit: head, State: gitk8s.Passed},
	}
	return b, w
}

func merge(t *testing.T, srv *gittest.Server, b *gitk8s.GitBranch) error {
	t.Helper()
	repo, secret := srv.Repository("app", rules()...)
	ctx, _ := kube.Fake(t.Context(), b, repo, secret)
	return (&merger{cache: &gitk8s.Cache{Git: &git.Git{}, Dir: t.TempDir()}}).Reconcile(ctx, b)
}

func TestLandsAndDeletesBranch(t *testing.T) {
	srv := gittest.NewServer(t, "pw")
	b, _ := branches(t, srv)
	if err := merge(t, srv, b); err != nil {
		t.Fatal(err)
	}
	heads := srv.Heads(t, "app")
	if heads["main"] != b.Spec.Head {
		t.Errorf("main = %s, want %s", heads["main"], b.Spec.Head)
	}
	if _, ok := heads["c/x"]; ok {
		t.Error("c/x wasn't deleted after it landed")
	}
	c := kube.FindCondition(b.Status.Conditions, "Merged")
	if c == nil || c.Status != kube.True || c.Reason != reasonLanded || b.Status.State != reasonLanded {
		t.Errorf("Merged = %+v, state %q", c, b.Status.State)
	}
	if b.Status.Checks != nil {
		t.Error("the merge controller must leave status.checks out of its status write")
	}
}

func TestWaitsForFreshPassingChecks(t *testing.T) {
	for name, edit := range map[string]func(*gitk8s.GitBranch){
		"pending": func(b *gitk8s.GitBranch) { delete(b.Status.Checks, "gofmt") },
		"failed": func(b *gitk8s.GitBranch) {
			b.Status.Checks["gofmt"] = gitk8s.CheckResult{Commit: b.Spec.Head, State: gitk8s.Failed}
		},
		"stale head": func(b *gitk8s.GitBranch) {
			b.Status.Checks["gofmt"] = gitk8s.CheckResult{Commit: "old", State: gitk8s.Passed}
		},
		"stale parent": func(b *gitk8s.GitBranch) {
			b.Status.Checks["base"] = gitk8s.CheckResult{Commit: b.Spec.Head, ParentCommit: "old", State: gitk8s.Passed}
		},
	} {
		t.Run(name, func(t *testing.T) {
			srv := gittest.NewServer(t, "")
			b, _ := branches(t, srv)
			edit(b)
			main := b.Spec.ParentHead
			if err := merge(t, srv, b); err != nil {
				t.Fatal(err)
			}
			if b.Status.State != reasonWaitingForChecks {
				t.Errorf("state = %q, want %s", b.Status.State, reasonWaitingForChecks)
			}
			if got := srv.Heads(t, "app")["main"]; got != main {
				t.Errorf("main moved to %s", got)
			}
		})
	}
}

func TestGateExpression(t *testing.T) {
	srv := gittest.NewServer(t, "")
	b, _ := branches(t, srv)
	p := *policy
	p.Checks = append(p.Checks[:2:2], gitk8s.CheckPolicy{Name: "risk"}, gitk8s.CheckPolicy{Name: "approval"})
	p.When = `checks.base.passed && checks.gofmt.passed && (checks.risk.outputs.level == "low" || checks.approval.passed)`
	b.Spec.Merge = &p
	b.Status.Checks["risk"] = gitk8s.CheckResult{Commit: b.Spec.Head, ParentCommit: b.Spec.ParentHead, State: gitk8s.Passed, Outputs: map[string]string{"level": "high"}}
	b.Status.Checks["approval"] = gitk8s.CheckResult{Commit: b.Spec.Head, State: gitk8s.Failed}
	results := b.Status.Checks
	if err := merge(t, srv, b); err != nil {
		t.Fatal(err)
	}
	if b.Status.State != reasonWaitingForChecks || !strings.Contains(kube.FindCondition(b.Status.Conditions, "Merged").Message, "risk Passed (high)") {
		t.Fatalf("state = %q, conditions %+v", b.Status.State, b.Status.Conditions)
	}

	results["approval"] = gitk8s.CheckResult{Commit: b.Spec.Head, State: gitk8s.Passed}
	b.Status.Checks = results
	if err := merge(t, srv, b); err != nil {
		t.Fatal(err)
	}
	if b.Status.State != reasonLanded {
		t.Errorf("state after approval = %q, want %s", b.Status.State, reasonLanded)
	}
}

func TestNotFastForward(t *testing.T) {
	srv := gittest.NewServer(t, "")
	b, w := branches(t, srv)
	w.Branch("main", b.Spec.ParentHead)
	w.Write("y.txt", "y\n")
	b.Spec.ParentHead = w.Commit("main moves")
	w.Push("main")
	b.Status.Checks["base"] = gitk8s.CheckResult{Commit: b.Spec.Head, ParentCommit: b.Spec.ParentHead, State: gitk8s.Passed}
	if err := merge(t, srv, b); err != nil {
		t.Fatal(err)
	}
	if b.Status.State != reasonNotFastForward {
		t.Errorf("state = %q, want %s", b.Status.State, reasonNotFastForward)
	}
}

func TestParentMovedAfterListing(t *testing.T) {
	srv := gittest.NewServer(t, "")
	b, w := branches(t, srv)
	w.Branch("main", b.Spec.Head)
	w.Write("z.txt", "z\n")
	w.Commit("main moves past the branch")
	w.Push("main")
	if err := merge(t, srv, b); err == nil || !strings.Contains(err.Error(), "push rejected") {
		t.Errorf("err = %v, want a rejected push", err)
	}
}

// A branch that's already merged, such as one just created from its parent,
// isn't deleted, because the merge controller didn't land it.
func TestAlreadyMergedBranchesStay(t *testing.T) {
	for name, setup := range map[string]func(*gitk8s.GitBranch, *gittest.Work){
		"at the parent's head": func(b *gitk8s.GitBranch, w *gittest.Work) {
			w.Push("main")
			b.Spec.ParentHead = b.Spec.Head
		},
		"behind the parent": func(b *gitk8s.GitBranch, w *gittest.Work) {
			w.Write("y.txt", "y\n")
			b.Spec.ParentHead = w.Commit("main moves past the branch")
			w.Push("main")
			b.Status.Checks["base"] = gitk8s.CheckResult{Commit: b.Spec.Head, ParentCommit: b.Spec.ParentHead, State: gitk8s.Passed}
		},
	} {
		t.Run(name, func(t *testing.T) {
			srv := gittest.NewServer(t, "")
			b, w := branches(t, srv)
			setup(b, w)
			if err := merge(t, srv, b); err != nil {
				t.Fatal(err)
			}
			if b.Status.State != reasonMerged {
				t.Errorf("state = %q, want %s", b.Status.State, reasonMerged)
			}
			if _, ok := srv.Heads(t, "app")["c/x"]; !ok {
				t.Error("deleted a branch that the merge controller didn't land")
			}
		})
	}
}

func TestInvalidGateWithFinalResults(t *testing.T) {
	srv := gittest.NewServer(t, "")
	b, _ := branches(t, srv)
	p := *policy
	p.When = "checks.missing.passed"
	b.Spec.Merge = &p
	if err := merge(t, srv, b); err != nil {
		t.Fatal(err)
	}
	if b.Status.State != reasonInvalidGate {
		t.Errorf("state = %q, want %s", b.Status.State, reasonInvalidGate)
	}
}

func TestNoParentNoState(t *testing.T) {
	b := &gitk8s.GitBranch{Object: kube.Meta("app-main", nil), Spec: gitk8s.GitBranchSpec{Repository: "app", Branch: "main", Head: "abc"}}
	b.Namespace = "default"
	ctx, _ := kube.Fake(t.Context(), b)
	if err := (&merger{}).Reconcile(ctx, b); err != nil || b.Status.State != "" || len(b.Status.Conditions) != 0 {
		t.Errorf("err = %v, status = %+v", err, b.Status)
	}
}
