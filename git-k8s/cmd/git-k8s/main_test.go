package main

import (
	"bytes"
	"encoding/json"
	"errors"
	"fmt"
	"io"
	"maps"
	"net/http"
	"net/http/httptest"
	"os"
	"path/filepath"
	"slices"
	"strconv"
	"strings"
	"testing"
	"time"

	gitk8s "github.com/imjasonh/playground/git-k8s"
	"github.com/imjasonh/playground/git-k8s/config"
	"github.com/imjasonh/playground/git-k8s/internal/git"
	"github.com/imjasonh/playground/git-k8s/internal/gittest"
	"github.com/imjasonh/playground/git-k8s/internal/mirror"
	"github.com/imjasonh/playground/kube"
	"github.com/imjasonh/playground/kube/k8s"
	"go.yaml.in/yaml/v3"
)

var policy = &gitk8s.MergePolicy{
	Checks:               []gitk8s.CheckPolicy{{Name: "base", MayPush: true}, {Name: "gofmt", MayPush: true}},
	DeleteLandedBranches: true,
}

func rules() []gitk8s.BranchRule {
	return []gitk8s.BranchRule{{Match: "main", Merge: policy}, {Match: "c/**", Parent: "main"}}
}

// fixture is the GitRepository default/app, its external repository on a
// git server, and the mirror's copy of it, which a server serves.
type fixture struct {
	t   *testing.T
	srv *gittest.Server
	// work makes commits, and pushes them to the external repository with
	// Push or to the mirror with pushToMirror.
	work   *gittest.Work
	repo   *gitk8s.GitRepository
	secret *k8s.Secret
	mirror *mirror.Mirror
	// mirrorURL is the copy's URL on a server that runs the mirror's
	// handler.
	mirrorURL string
	r         *repositories
	now       time.Time
}

func newFixture(t *testing.T) *fixture {
	t.Helper()
	srv := gittest.NewServer(t, "pw")
	repo, secret := srv.Repository("app", rules()...)
	repo.UID = "uid-1"
	m := &mirror.Mirror{Git: &git.Git{}, Dir: t.TempDir(), Prefixes: []mirror.Prefix{{Namespace: "test", ServiceAccount: "pusher", Prefix: "c/"}}}
	f := &fixture{
		t:      t,
		srv:    srv,
		work:   srv.NewWork(t, "app"),
		repo:   repo,
		secret: secret,
		mirror: m,
		now:    time.Unix(1000, 0),
	}
	f.r = &repositories{mirror: m, now: func() time.Time { return f.now }}

	// The handler gets its own GitRepository, which reconciles don't write.
	served := &gitk8s.GitRepository{Object: kube.Meta("app", nil), Spec: gitk8s.GitRepositorySpec{URL: repo.Spec.URL, Branches: rules()}}
	served.Namespace, served.UID = repo.Namespace, repo.UID
	token := kube.FakeToken{Token: "pusher", User: kube.UserInfo{Username: "system:serviceaccount:test:pusher"}, Audiences: []string{gitk8s.MirrorAudience}}
	hs := httptest.NewServer(http.HandlerFunc(func(w http.ResponseWriter, r *http.Request) {
		ctx, rec := kube.FakeRequest(r.Context(), served, token)
		m.ServeHTTP(w, r.WithContext(ctx))
		if err := rec.Err(); err != nil {
			t.Errorf("the handler did what a kube.Serve handler can't: %v", err)
		}
	}))
	t.Cleanup(hs.Close)
	f.mirrorURL = hs.URL + "/default/app.git"
	return f
}

func (f *fixture) world(extra ...any) []any {
	if f.secret != nil {
		extra = append(extra, f.secret)
	}
	return extra
}

func (f *fixture) tryReconcile(world ...any) (*kube.Recorder, error) {
	ctx, rec := kube.Fake(f.t.Context(), f.repo, f.world(world...)...)
	return rec, f.r.Reconcile(ctx, f.repo)
}

// reconcile runs the repositories controller, which fetches from the
// external repository if the poll interval has passed since it last did.
func (f *fixture) reconcile(world ...any) *kube.Recorder {
	f.t.Helper()
	rec, err := f.tryReconcile(world...)
	if err != nil {
		f.t.Fatal(err)
	}
	return rec
}

// fetch moves the clock past the poll interval and reconciles, so that the
// mirror fetches from the external repository.
func (f *fixture) fetch(world ...any) *kube.Recorder {
	f.t.Helper()
	f.now = f.now.Add(time.Hour)
	return f.reconcile(world...)
}

// merge reconciles b at the front of its parent's merge queue. A b that
// isn't queued joined in an earlier reconcile.
func (f *fixture) merge(b *gitk8s.GitBranch) (*kube.Recorder, error) {
	if b.Status.Queued == nil {
		b.Status.Queued = &gitk8s.Queued{Head: b.Spec.Head, Position: 1}
	}
	ctx, rec := kube.Fake(f.t.Context(), b, f.world(f.repo, parentOf(b, b.Spec.Branch))...)
	return rec, (&merger{mirror: f.mirror}).Reconcile(ctx, b)
}

// mergeIn reconciles b with parent as its parent's GitBranch, and returns
// the Landed condition's message. Reads see the objects in world over b and
// parent. b keeps its check results, which the merge controller leaves out
// of its status write.
func (f *fixture) mergeIn(parent, b *gitk8s.GitBranch, world ...any) string {
	f.t.Helper()
	results := b.Status.Checks
	ctx, _ := kube.Fake(f.t.Context(), b, f.world(append([]any{f.repo, parent}, world...)...)...)
	m := &merger{mirror: f.mirror, ident: git.Identity{Name: "git-k8s", Email: "git-k8s@example.com"}}
	if err := m.Reconcile(ctx, b); err != nil {
		f.t.Fatal(err)
	}
	b.Status.Checks = results
	if c := kube.FindCondition(b.Status.Conditions, "Landed"); c != nil {
		return c.Message
	}
	return ""
}

func (f *fixture) finalize() error {
	ctx, _ := kube.Fake(f.t.Context(), f.repo, f.world()...)
	return f.r.Finalize(ctx, f.repo)
}

func (f *fixture) copyDir() string { return filepath.Join(f.mirror.Dir, "default", "app.git") }

// pushToMirror pushes the working repository's HEAD to branch through the
// mirror's handler, as the controller that starts branches under c/.
func (f *fixture) pushToMirror(branch string) {
	f.t.Helper()
	f.mirrorGit("push", "--quiet", "--force", f.mirrorURL, "HEAD:refs/heads/"+branch)
}

// mirrorGit runs git in the working repository with the token of the
// controller that starts branches under c/, which may fetch too.
func (f *fixture) mirrorGit(args ...string) string {
	f.t.Helper()
	return f.work.Git(append([]string{"-c", "http.extraHeader=Authorization: Bearer pusher"}, args...)...)
}

// fetchFromMirror fetches branch from the mirror's copy into the working
// repository, and returns its head.
func (f *fixture) fetchFromMirror(branch string) string {
	f.t.Helper()
	f.mirrorGit("fetch", "--quiet", f.mirrorURL, "+refs/heads/"+branch+":refs/remotes/mirror/"+branch)
	return f.work.Git("rev-parse", "refs/remotes/mirror/"+branch)
}

func (f *fixture) mirrorHeads() map[string]string {
	f.t.Helper()
	heads, err := (&git.Git{}).LsRemote(f.t.Context(), git.Remote{URL: f.mirrorURL, Auth: &git.Auth{Token: "pusher"}})
	if err != nil {
		f.t.Fatal(err)
	}
	return heads
}

// landInMirror moves main to commit in the mirror's copy, which only the
// merge controller can do: it pushes commit to c/landing, and lands it.
func (f *fixture) landInMirror(commit string) {
	f.t.Helper()
	parent := f.mirrorHeads()["main"]
	f.mirrorGit("push", "--quiet", f.mirrorURL, commit+":refs/heads/c/landing")
	b := &gitk8s.GitBranch{Object: kube.Meta(gitk8s.BranchObjectName("app", "c/landing"), map[string]string{gitk8s.RepositoryLabel: "app"})}
	b.Namespace = "default"
	b.Spec = gitk8s.GitBranchSpec{Repository: "app", Branch: "c/landing", Head: commit, Parent: "main", ParentHead: parent, Merge: policy}
	pass(b)
	if _, err := f.merge(b); err != nil || b.Status.State != gitk8s.MergeStateLanded {
		f.t.Fatalf("landing %s on main: err = %v, state = %q", gitk8s.Short(commit), err, b.Status.State)
	}
}

func (f *fixture) condition(typ string) *kube.Condition {
	return kube.FindCondition(f.repo.Status.Conditions, typ)
}

// branches pushes main and c/x, which adds a file on top of main, to the
// external repository, syncs the mirror, and returns c/x's GitBranch with
// fresh, passing results for the policy's checks.
func (f *fixture) branches() *gitk8s.GitBranch {
	f.t.Helper()
	w := f.work
	main := w.Commit("main")
	w.Push("main")
	w.Branch("c/x", main)
	w.Write("x.txt", "x\n")
	head := w.Commit("add x")
	w.Push("c/x")
	f.fetch()
	b := &gitk8s.GitBranch{Object: kube.Meta(gitk8s.BranchObjectName("app", "c/x"), map[string]string{gitk8s.RepositoryLabel: "app"})}
	b.Namespace = "default"
	b.Spec = gitk8s.GitBranchSpec{Repository: "app", Branch: "c/x", Head: head, Parent: "main", ParentHead: main, Merge: policy}
	pass(b)
	return b
}

// pass gives b fresh, passing results for the policy's checks.
func pass(b *gitk8s.GitBranch) {
	b.Status.Checks = map[string]gitk8s.CheckResult{
		"base":  {Commit: b.Spec.Head, Scope: gitk8s.ScopeParent, ParentCommit: b.Spec.ParentHead, State: gitk8s.Passed},
		"gofmt": {Commit: b.Spec.Head, Scope: gitk8s.ScopeHead, State: gitk8s.Passed},
	}
}

// owned returns the GitBranches that a reconcile declared, by branch.
func owned(rec *kube.Recorder) map[string]*gitk8s.GitBranch {
	got := map[string]*gitk8s.GitBranch{}
	for _, b := range kube.Owned[gitk8s.GitBranch](rec) {
		got[b.Spec.Branch] = b
	}
	return got
}

// ownedPolicies describes the NetworkPolicies that a reconcile declared. A
// reconcile of default/app that returns nil must declare wantPolicy, or
// kube deletes the test Pods' NetworkPolicy.
func ownedPolicies(rec *kube.Recorder) string {
	var s []string
	for _, p := range kube.Owned[NetworkPolicy](rec) {
		s = append(s, p.Name+" selecting "+labels(p.Spec.PodSelector.MatchLabels).String())
	}
	return strings.Join(s, "; ")
}

const wantPolicy = "app-test-pods selecting kube.imjasonh.github.io/controller=check-gotest"

func TestListsBranches(t *testing.T) {
	f := newFixture(t)
	w := f.work
	main := w.Commit("main")
	w.Push("main")
	w.Branch("c/add", main)
	add := w.Commit("add")
	w.Push("c/add")
	w.Push("feature/ignored")

	rec := f.reconcile()
	got := owned(rec)
	if len(got) != 2 {
		t.Fatalf("owned %d GitBranches, want 2: %+v", len(got), got)
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
	if got := ownedPolicies(rec); got != wantPolicy {
		t.Errorf("owned NetworkPolicies: %q, want %q", got, wantPolicy)
	}
	if f.repo.Status.Branches != 2 || rec.RequeueAfter() != 30*time.Second {
		t.Errorf("status branches = %d, requeue = %v", f.repo.Status.Branches, rec.RequeueAfter())
	}
	if c := f.condition("Ready"); c == nil || c.Status != kube.True || c.Message != "tracking 2 of 3 branches" {
		t.Errorf("Ready = %+v", c)
	}
	if c := f.condition("ExternalSynced"); c == nil || c.Status != kube.True || c.Reason != "InSync" {
		t.Errorf("ExternalSynced = %+v", c)
	}
	if heads := f.mirrorHeads(); heads["c/add"] != add || heads["feature/ignored"] != add {
		t.Errorf("the mirror's copy has %v", heads)
	}
}

// The external repository is fetched once each poll interval, and a change
// in the mirror shows up and syncs as soon as a reconcile runs.
func TestPollsExternalRepository(t *testing.T) {
	f := newFixture(t)
	w := f.work
	main := w.Commit("main")
	w.Push("main")
	w.Branch("c/add", main)
	add := w.Commit("add")
	w.Push("c/add")
	reconcile := func() (head string, requeue time.Duration) {
		t.Helper()
		rec := f.reconcile()
		if b := owned(rec)["c/add"]; b != nil {
			head = b.Spec.Head
		}
		return head, rec.RequeueAfter()
	}
	if head, requeue := reconcile(); head != add || requeue != 30*time.Second {
		t.Fatalf("c/add = %s, requeue = %v; want %s and the poll interval", head, requeue, add)
	}

	t.Log("A person pushes to the external repository. The mirror fetches it once the poll interval passes.")
	w.Write("person.txt", "person\n")
	person := w.Commit("person")
	w.Push("c/add")
	f.now = f.now.Add(10 * time.Second)
	if head, requeue := reconcile(); head != add || requeue != 20*time.Second {
		t.Errorf("c/add = %s, requeue = %v; want %s and a requeue at the next poll, in 20s", head, requeue, add)
	}
	f.now = f.now.Add(20 * time.Second)
	if head, requeue := reconcile(); head != person || requeue != 30*time.Second {
		t.Errorf("c/add = %s, requeue = %v; want the person's %s and the poll interval", head, requeue, person)
	}

	t.Log("A check pushes a fix to the mirror. The reconcile that the push triggers tracks the fix and pushes it to the external repository.")
	w.Write("fix.txt", "fix\n")
	fix := w.Commit("fix")
	f.pushToMirror("c/add")
	f.now = f.now.Add(time.Second)
	if head, requeue := reconcile(); head != fix || requeue != 29*time.Second {
		t.Errorf("c/add = %s, requeue = %v; want the fix %s and a requeue at the next poll, in 29s", head, requeue, fix)
	}
	if got := f.srv.Heads(t, "app")["c/add"]; got != fix {
		t.Errorf("the external repository has c/add at %s, want the fix %s", got, fix)
	}
	if c := f.condition("ExternalSynced"); c.Status != kube.True {
		t.Errorf("ExternalSynced = %+v", c)
	}
}

func TestReportsAdmissionPolicies(t *testing.T) {
	f := newFixture(t)
	f.work.Commit("main")
	f.work.Push("main")
	r := f.r
	reconcile := func(world ...any) *kube.Condition {
		t.Helper()
		f.reconcile(world...)
		return f.condition("PoliciesInstalled")
	}
	all := "git-k8s-check-results, git-k8s-branches, git-k8s-check-pods, and git-k8s-approvals"
	if c := reconcile(); c == nil || c.Status != kube.False || c.Reason != "Missing" ||
		c.Message != all+" aren't fully installed, so any service account that can write GitBranch status can write check results and status.diverged, checks that can write GitBranch status can change a branch's state and merge queue, git-k8s service accounts with the approve verb can approve branches, checks and git-k8s-deps can change GitBranch objects, checks that own Pods can write any Pod in the cluster, anyone who can patch a GitBranch can approve it, and the approved-by annotation can name someone who didn't approve; apply config/policy.yaml" {
		t.Errorf("without the policies, PoliciesInstalled = %+v", c)
	}
	r.installPolicies = true
	if c := reconcile(); c.Status != kube.False ||
		!strings.HasSuffix(c.Message, "; run kubectl -n git-k8s rollout restart deployment/git-k8s to install config/policy.yaml again") {
		t.Errorf("without the policies that the program installs, PoliciesInstalled = %+v", c)
	}

	// checksRef returns the paramRef from config/policy.yaml, with action as
	// its parameterNotFoundAction.
	checksRef := func(action string) *paramRef {
		return &paramRef{Name: "git-k8s-checks", Namespace: "git-k8s", ParameterNotFoundAction: action}
	}
	var world []any
	var vaps []*admissionPolicy
	var bindings []*admissionPolicyBinding
	current, later := strconv.Itoa(policyVersion), strconv.Itoa(policyVersion+1)
	for _, p := range policies {
		vap := &admissionPolicy{Object: kube.Meta(p.name, nil)}
		vap.Annotations = map[string]string{policyVersionAnnotation: current}
		b := &admissionPolicyBinding{Object: kube.Meta(p.name, nil)}
		b.Spec.PolicyName, b.Spec.ValidationActions = p.name, []string{"Warn"}
		if p.name == "git-k8s-check-results" || p.name == "git-k8s-branches" {
			vap.Spec.ParamKind = &struct{}{}
			b.Spec.ParamRef = checksRef("Deny")
		}
		vaps, bindings = append(vaps, vap), append(bindings, b)
		world = append(world, vap, b)
	}
	// A restart would add Deny next to Warn in these bindings' validationActions,
	// which the API server rejects, so the fix patches them instead.
	warns := `kubectl patch validatingadmissionpolicybinding %s --type=merge -p '{"spec":{"validationActions":["Deny"]}}'`
	if c := reconcile(world...); c.Status != kube.False || c.Reason != "NotDenying" ||
		!strings.HasSuffix(c.Message, "; run "+fmt.Sprintf(warns, "git-k8s-check-results")+", "+fmt.Sprintf(warns, "git-k8s-branches")+", "+fmt.Sprintf(warns, "git-k8s-check-pods")+", and "+fmt.Sprintf(warns, "git-k8s-approvals")) ||
		strings.Contains(c.Message, "restart") {
		t.Errorf("with bindings that only warn, PoliciesInstalled = %+v", c)
	}
	if c := reconcile(world[1:]...); c.Status != kube.False || c.Reason != "Missing" ||
		!strings.HasSuffix(c.Message, ", and "+fmt.Sprintf(warns, "git-k8s-approvals")+", then run kubectl -n git-k8s rollout restart deployment/git-k8s to install config/policy.yaml again") {
		t.Errorf("without a policy whose binding only warns, PoliciesInstalled = %+v", c)
	}
	for _, b := range bindings {
		b.Spec.ValidationActions = []string{"Deny"}
	}
	for _, vap := range vaps {
		vap.Annotations = nil
	}
	if c := reconcile(world...); c.Status != kube.False || c.Reason != "Outdated" ||
		c.Message != all+" don't have git-k8s.imjasonh.com/policy-version=3; run kubectl -n git-k8s rollout restart deployment/git-k8s to install config/policy.yaml again" {
		t.Errorf("with policies from an earlier release, which have no version, PoliciesInstalled = %+v", c)
	}
	r.installPolicies = false
	if c := reconcile(world...); c.Status != kube.False || c.Reason != "Outdated" ||
		c.Message != all+" don't have git-k8s.imjasonh.com/policy-version=3; apply config/policy.yaml from this release" {
		t.Errorf("with policies from an earlier release that the program doesn't install, PoliciesInstalled = %+v", c)
	}
	bindings[0].Spec.ValidationActions = []string{"Warn"}
	if c := reconcile(world...); c.Status != kube.False || c.Reason != "NotDenying" ||
		c.Message != "the binding git-k8s-check-results doesn't deny every request that its policy rejects, so any service account that can write GitBranch status can write check results and status.diverged, and checks that can write GitBranch status can change a branch's state and merge queue; "+all+" don't have git-k8s.imjasonh.com/policy-version=3; run "+fmt.Sprintf(warns, "git-k8s-check-results")+", then apply config/policy.yaml from this release" {
		t.Errorf("with one binding that only warns and policies from an earlier release, PoliciesInstalled = %+v", c)
	}
	bindings[0].Spec.ValidationActions = []string{"Deny"}
	for _, vap := range vaps {
		vap.Annotations = map[string]string{policyVersionAnnotation: current}
	}
	vaps[0].Annotations[policyVersionAnnotation] = "1"
	if c := reconcile(world...); c.Status != kube.False || c.Reason != "Outdated" ||
		c.Message != "git-k8s-check-results doesn't have git-k8s.imjasonh.com/policy-version=3; apply config/policy.yaml from this release" {
		t.Errorf("with one policy at an earlier version, PoliciesInstalled = %+v", c)
	}
	vaps[0].Annotations[policyVersionAnnotation] = later
	for _, v := range []string{"v3", "99999999999999999999"} {
		vaps[1].Annotations[policyVersionAnnotation] = v
		if c := reconcile(world...); c.Status != kube.False || c.Reason != "Outdated" ||
			c.Message != "git-k8s-branches doesn't have git-k8s.imjasonh.com/policy-version=3; git-k8s-check-results has a git-k8s.imjasonh.com/policy-version later than 3; upgrade the core program, or, if you rolled it back, apply config/policy.yaml from this release" {
			t.Errorf("with one policy at a later version and the other at %q, which doesn't parse as an int, PoliciesInstalled = %+v", v, c)
		}
	}
	vaps[1].Annotations[policyVersionAnnotation] = current
	if c := reconcile(world...); c.Status != kube.False || c.Reason != "Newer" ||
		c.Message != "git-k8s-check-results has a git-k8s.imjasonh.com/policy-version later than 3; upgrade the core program, or, if you rolled it back, apply config/policy.yaml from this release" {
		t.Errorf("with one policy at a later version, PoliciesInstalled = %+v", c)
	}
	for _, vap := range vaps {
		vap.Annotations[policyVersionAnnotation] = later
	}
	if c := reconcile(world...); c.Status != kube.False || c.Reason != "Newer" ||
		c.Message != all+" have a git-k8s.imjasonh.com/policy-version later than 3; upgrade the core program, or, if you rolled it back, apply config/policy.yaml from this release" {
		t.Errorf("with policies from a later release, PoliciesInstalled = %+v", c)
	}
	// Applying the policies from a later release installs the missing one too,
	// so the fix for the later policies replaces the fix for the missing one.
	if c := reconcile(world[2:]...); c.Status != kube.False || c.Reason != "Missing" ||
		c.Message != "git-k8s-check-results isn't fully installed, so any service account that can write GitBranch status can write check results and status.diverged, and checks that can write GitBranch status can change a branch's state and merge queue; git-k8s-branches, git-k8s-check-pods, and git-k8s-approvals have a git-k8s.imjasonh.com/policy-version later than 3; upgrade the core program, or, if you rolled it back, apply config/policy.yaml from this release" {
		t.Errorf("without git-k8s-check-results, and with the other policies from a later release, PoliciesInstalled = %+v", c)
	}
	r.installPolicies = true
	if c := reconcile(world...); c.Status != kube.False || c.Reason != "Newer" ||
		!strings.HasSuffix(c.Message, "; upgrade the core program, or, if you rolled it back, run kubectl -n git-k8s rollout restart deployment/git-k8s to install config/policy.yaml again") {
		t.Errorf("with policies from a later release that the program installs, PoliciesInstalled = %+v", c)
	}
	for _, vap := range vaps {
		vap.Annotations[policyVersionAnnotation] = current
	}
	if c := reconcile(world...); c.Status != kube.True || c.Reason != "Installed" ||
		c.Message != "the admission policies keep git-k8s service accounts from approving branches, let no service account but the core program's write check results, keep checks to their own Pods, and check who approves branches" {
		t.Errorf("with the policies installed, PoliciesInstalled = %+v", c)
	}
	bindings[1].Spec.ValidationActions = []string{"Warn"}
	if c := reconcile(world...); c.Status != kube.False ||
		c.Message != "the binding git-k8s-branches doesn't deny every request that its policy rejects, so git-k8s service accounts with the approve verb can approve branches, and checks and git-k8s-deps can change GitBranch objects; the binding git-k8s-branches warns, so the core program stops the next time it starts; run "+fmt.Sprintf(warns, "git-k8s-branches") {
		t.Errorf("with only git-k8s-branches warning, PoliciesInstalled = %+v", c)
	}
	// Another binding that denies enforces git-k8s-branches, but the next start
	// still adds Deny next to Warn in the binding from config/policy.yaml.
	admin := &admissionPolicyBinding{Object: kube.Meta("admin-branches", nil)}
	admin.Spec.PolicyName, admin.Spec.ValidationActions = "git-k8s-branches", []string{"Deny"}
	admin.Spec.ParamRef = checksRef("Deny")
	if c := reconcile(append([]any{admin}, world...)...); c.Status != kube.False || c.Reason != "BindingWarns" ||
		c.Message != "the binding git-k8s-branches warns, so the core program stops the next time it starts; run "+fmt.Sprintf(warns, "git-k8s-branches") {
		t.Errorf("with git-k8s-branches warning while admin-branches denies, PoliciesInstalled = %+v", c)
	}
	if c := reconcile(append([]any{admin}, world[2:]...)...); c.Status != kube.False || c.Reason != "Missing" ||
		!strings.HasSuffix(c.Message, "; run "+fmt.Sprintf(warns, "git-k8s-branches")+", then run kubectl -n git-k8s rollout restart deployment/git-k8s to install config/policy.yaml again") {
		t.Errorf("without git-k8s-check-results, and with git-k8s-branches warning while admin-branches denies, PoliciesInstalled = %+v", c)
	}
	// The reason for a binding that lets requests through takes precedence over
	// the reason for a warning that another binding hides.
	bindings[0].Spec.MatchResources = &matchResources{ObjectSelector: &labelSelector{MatchLabels: map[string]string{"tier": "web"}}}
	if c := reconcile(append([]any{admin}, world...)...); c.Status != kube.False || c.Reason != "NotDenying" ||
		c.Message != `the binding git-k8s-check-results doesn't deny every request that its policy rejects, so any service account that can write GitBranch status can write check results and status.diverged, and checks that can write GitBranch status can change a branch's state and merge queue; the binding git-k8s-branches warns, so the core program stops the next time it starts; run kubectl patch validatingadmissionpolicybinding git-k8s-check-results --type=merge -p '{"spec":{"matchResources":null}}' and `+fmt.Sprintf(warns, "git-k8s-branches") {
		t.Errorf("with git-k8s-check-results limited, and git-k8s-branches warning while admin-branches denies, PoliciesInstalled = %+v", c)
	}
	bindings[0].Spec.MatchResources = nil
	// A binding limited with matchResources doesn't enforce the policy for every
	// request, so the message gives the consequences instead.
	narrow := &admissionPolicyBinding{Object: kube.Meta("narrow-branches", nil)}
	narrow.Spec.PolicyName, narrow.Spec.ValidationActions = "git-k8s-branches", []string{"Deny"}
	narrow.Spec.ParamRef = checksRef("Deny")
	narrow.Spec.MatchResources = &matchResources{ObjectSelector: &labelSelector{MatchLabels: map[string]string{"tier": "web"}}}
	if c := reconcile(append([]any{narrow}, world...)...); c.Status != kube.False || c.Reason != "NotDenying" ||
		c.Message != "the binding git-k8s-branches doesn't deny every request that its policy rejects, so git-k8s service accounts with the approve verb can approve branches, and checks and git-k8s-deps can change GitBranch objects; the binding git-k8s-branches warns, so the core program stops the next time it starts; run "+fmt.Sprintf(warns, "git-k8s-branches") {
		t.Errorf("with git-k8s-branches warning while narrow-branches is limited, PoliciesInstalled = %+v", c)
	}
	r.installPolicies = false
	if c := reconcile(append([]any{admin}, world...)...); c.Status != kube.True {
		t.Errorf("with git-k8s-branches warning while admin-branches denies, and policies that the program doesn't install, PoliciesInstalled = %+v", c)
	}
	r.installPolicies = true
	bindings[1].Spec.ValidationActions = []string{"Deny"}
	for _, b := range bindings {
		b.Spec.ParamRef = checksRef("Allow")
	}
	// The API server ignores the paramRef of a binding whose policy has no
	// paramKind, so only the bindings of the policies that read parameters let
	// requests through while the parameters are missing.
	params := `kubectl patch validatingadmissionpolicybinding %s --type=merge -p '{"spec":{"paramRef":{"parameterNotFoundAction":"Deny"}}}'`
	if c := reconcile(world...); c.Status != kube.False || c.Reason != "NotDenying" ||
		c.Message != "the bindings git-k8s-check-results and git-k8s-branches don't deny every request that their policies reject, so any service account that can write GitBranch status can write check results and status.diverged, checks that can write GitBranch status can change a branch's state and merge queue, git-k8s service accounts with the approve verb can approve branches, and checks and git-k8s-deps can change GitBranch objects; run "+fmt.Sprintf(params, "git-k8s-check-results")+" and "+fmt.Sprintf(params, "git-k8s-branches") {
		t.Errorf("with bindings that allow requests while their parameters are missing, PoliciesInstalled = %+v", c)
	}
	bindings[0].Spec.ParamRef.ParameterNotFoundAction = "Deny"
	bindings[1].Spec.ParamRef.ParameterNotFoundAction = "Deny"
	if c := reconcile(world...); c.Status != kube.True {
		t.Errorf("with bindings that deny requests while their parameters are missing, PoliciesInstalled = %+v", c)
	}
	// The patch for a binding whose policy reads no parameters leaves its
	// paramRef alone, whether or not another binding enforces the policy.
	bindings[2].Spec.ValidationActions = []string{"Warn"}
	if c := reconcile(world...); c.Status != kube.False || c.Reason != "NotDenying" ||
		c.Message != "the binding git-k8s-check-pods doesn't deny every request that its policy rejects, so checks that own Pods can write any Pod in the cluster; the binding git-k8s-check-pods warns, so the core program stops the next time it starts; run "+fmt.Sprintf(warns, "git-k8s-check-pods") {
		t.Errorf("with git-k8s-check-pods warning, and a paramRef that allows requests, PoliciesInstalled = %+v", c)
	}
	pods := &admissionPolicyBinding{Object: kube.Meta("admin-pods", nil)}
	pods.Spec.PolicyName, pods.Spec.ValidationActions = "git-k8s-check-pods", []string{"Deny"}
	if c := reconcile(append([]any{pods}, world...)...); c.Status != kube.False || c.Reason != "BindingWarns" ||
		c.Message != "the binding git-k8s-check-pods warns, so the core program stops the next time it starts; run "+fmt.Sprintf(warns, "git-k8s-check-pods") {
		t.Errorf("with git-k8s-check-pods warning while admin-pods denies, and a paramRef that allows requests, PoliciesInstalled = %+v", c)
	}
	bindings[2].Spec.ValidationActions = []string{"Deny"}
	// While git-k8s-check-pods is missing, the condition can't tell whether the
	// policy reads parameters, so it doesn't give a patch for the paramRef of
	// the binding that's left. The restart installs the policy again.
	orphaned := slices.DeleteFunc(slices.Clone(world), func(o any) bool {
		p, ok := o.(*admissionPolicy)
		return ok && p.Name == "git-k8s-check-pods"
	})
	if c := reconcile(orphaned...); c.Status != kube.False || c.Reason != "Missing" ||
		c.Message != "git-k8s-check-pods isn't fully installed, so checks that own Pods can write any Pod in the cluster; run kubectl -n git-k8s rollout restart deployment/git-k8s to install config/policy.yaml again" {
		t.Errorf("without git-k8s-check-pods, and with a paramRef that allows requests on its binding, PoliciesInstalled = %+v", c)
	}
	// Without a paramRef, the API server evaluates git-k8s-check-results
	// without parameters, so the policy ignores the entries in the
	// git-k8s-checks ConfigMap but enforces the rest. The patch adds the
	// paramRef again.
	addParams := `kubectl patch validatingadmissionpolicybinding %s --type=merge -p '{"spec":{"paramRef":{"name":"git-k8s-checks","namespace":"git-k8s","parameterNotFoundAction":"Deny"}}}'`
	bindings[0].Spec.ParamRef = nil
	if c := reconcile(world...); c.Status != kube.False || c.Reason != "NotDenying" ||
		c.Message != "the binding git-k8s-check-results has no paramRef, so git-k8s-check-results ignores the entries in the git-k8s-checks ConfigMap; run "+fmt.Sprintf(addParams, "git-k8s-check-results") {
		t.Errorf("with git-k8s-check-results's binding without a paramRef, PoliciesInstalled = %+v", c)
	}
	bindings[1].Spec.ParamRef = nil
	if c := reconcile(world...); c.Status != kube.False || c.Reason != "NotDenying" ||
		c.Message != "the bindings git-k8s-check-results and git-k8s-branches have no paramRef, so git-k8s-check-results and git-k8s-branches ignore the entries in the git-k8s-checks ConfigMap; run "+fmt.Sprintf(addParams, "git-k8s-check-results")+" and "+fmt.Sprintf(addParams, "git-k8s-branches") {
		t.Errorf("with the bindings of both policies that read parameters without a paramRef, PoliciesInstalled = %+v", c)
	}
	// A binding that only warns enforces nothing, with or without a paramRef.
	bindings[0].Spec.ValidationActions = []string{"Warn"}
	if c := reconcile(world...); c.Status != kube.False || c.Reason != "NotDenying" ||
		c.Message != `the binding git-k8s-check-results doesn't deny every request that its policy rejects, and the binding git-k8s-branches has no paramRef, so any service account that can write GitBranch status can write check results and status.diverged, checks that can write GitBranch status can change a branch's state and merge queue, and git-k8s-branches ignores the entries in the git-k8s-checks ConfigMap; the binding git-k8s-check-results warns, so the core program stops the next time it starts; run kubectl patch validatingadmissionpolicybinding git-k8s-check-results --type=merge -p '{"spec":{"validationActions":["Deny"],"paramRef":{"name":"git-k8s-checks","namespace":"git-k8s","parameterNotFoundAction":"Deny"}}}' and `+fmt.Sprintf(addParams, "git-k8s-branches") {
		t.Errorf("with git-k8s-check-results's binding warning and git-k8s-branches's without a paramRef, PoliciesInstalled = %+v", c)
	}
	bindings[0].Spec.ValidationActions = []string{"Deny"}
	bindings[0].Spec.ParamRef = checksRef("Deny")
	// Another binding without a paramRef enforces git-k8s-branches while the
	// binding from config/policy.yaml is missing.
	unbound := slices.DeleteFunc(slices.Clone(world), func(o any) bool {
		b, ok := o.(*admissionPolicyBinding)
		return ok && b.Name == "git-k8s-branches"
	})
	bare := &admissionPolicyBinding{Object: kube.Meta("admin-branches", nil)}
	bare.Spec.PolicyName, bare.Spec.ValidationActions = "git-k8s-branches", []string{"Deny"}
	if c := reconcile(append(unbound, bare)...); c.Status != kube.False || c.Reason != "Missing" ||
		c.Message != "git-k8s-branches isn't fully installed, so git-k8s-branches ignores the entries in the git-k8s-checks ConfigMap; run kubectl -n git-k8s rollout restart deployment/git-k8s to install config/policy.yaml again" {
		t.Errorf("without git-k8s-branches's binding, and with admin-branches without a paramRef, PoliciesInstalled = %+v", c)
	}
	bindings[1].Spec.ParamRef = checksRef("Deny")
	// With a paramRef that doesn't name git-k8s/git-k8s-checks, the API server
	// evaluates git-k8s-check-results with another ConfigMap, so the policy
	// ignores the entries in git-k8s-checks. The patch sets the paramRef from
	// config/policy.yaml again.
	for _, tc := range []struct {
		does  string
		ref   *paramRef
		patch string
	}{
		{"names another ConfigMap", &paramRef{Name: "other-checks", Namespace: "git-k8s", ParameterNotFoundAction: "Deny"}, addParams},
		{"names git-k8s-checks in another namespace", &paramRef{Name: "git-k8s-checks", Namespace: "default", ParameterNotFoundAction: "Deny"}, addParams},
		{"names git-k8s-checks in the GitBranch's namespace", &paramRef{Name: "git-k8s-checks", ParameterNotFoundAction: "Deny"}, addParams},
		{"selects ConfigMaps by label", &paramRef{Namespace: "git-k8s", Selector: &struct{}{}, ParameterNotFoundAction: "Deny"}, `kubectl patch validatingadmissionpolicybinding %s --type=merge -p '{"spec":{"paramRef":{"name":"git-k8s-checks","namespace":"git-k8s","parameterNotFoundAction":"Deny","selector":null}}}'`},
	} {
		bindings[0].Spec.ParamRef = tc.ref
		if c := reconcile(world...); c.Status != kube.False || c.Reason != "NotDenying" ||
			c.Message != "the binding git-k8s-check-results has a paramRef that doesn't name git-k8s/git-k8s-checks, so git-k8s-check-results ignores the entries in the git-k8s-checks ConfigMap; run "+fmt.Sprintf(tc.patch, "git-k8s-check-results") {
			t.Errorf("with git-k8s-check-results's paramRef that %s, PoliciesInstalled = %+v", tc.does, c)
		}
	}
	// While the other ConfigMap is missing, a paramRef that allows requests
	// lets every request through.
	bindings[0].Spec.ParamRef = &paramRef{Name: "other-checks", Namespace: "git-k8s", ParameterNotFoundAction: "Allow"}
	if c := reconcile(world...); c.Status != kube.False || c.Reason != "NotDenying" ||
		c.Message != "the binding git-k8s-check-results doesn't deny every request that its policy rejects, so any service account that can write GitBranch status can write check results and status.diverged, and checks that can write GitBranch status can change a branch's state and merge queue; run "+fmt.Sprintf(addParams, "git-k8s-check-results") {
		t.Errorf("with git-k8s-check-results's paramRef to another ConfigMap that allows requests, PoliciesInstalled = %+v", c)
	}
	bindings[0].Spec.ParamRef.ParameterNotFoundAction = "Deny"
	bindings[1].Spec.ParamRef = &paramRef{Name: "git-k8s-checks", Namespace: "default", ParameterNotFoundAction: "Deny"}
	if c := reconcile(world...); c.Status != kube.False || c.Reason != "NotDenying" ||
		c.Message != "the bindings git-k8s-check-results and git-k8s-branches have paramRefs that don't name git-k8s/git-k8s-checks, so git-k8s-check-results and git-k8s-branches ignore the entries in the git-k8s-checks ConfigMap; run "+fmt.Sprintf(addParams, "git-k8s-check-results")+" and "+fmt.Sprintf(addParams, "git-k8s-branches") {
		t.Errorf("with the bindings of both policies that read parameters with paramRefs to other ConfigMaps, PoliciesInstalled = %+v", c)
	}
	bindings[0].Spec.ParamRef = nil
	if c := reconcile(world...); c.Status != kube.False || c.Reason != "NotDenying" ||
		c.Message != "the binding git-k8s-check-results has no paramRef, and the binding git-k8s-branches has a paramRef that doesn't name git-k8s/git-k8s-checks, so git-k8s-check-results and git-k8s-branches ignore the entries in the git-k8s-checks ConfigMap; run "+fmt.Sprintf(addParams, "git-k8s-check-results")+" and "+fmt.Sprintf(addParams, "git-k8s-branches") {
		t.Errorf("with git-k8s-check-results's binding without a paramRef and git-k8s-branches's with a paramRef to another ConfigMap, PoliciesInstalled = %+v", c)
	}
	bindings[0].Spec.ParamRef, bindings[1].Spec.ParamRef = checksRef("Deny"), checksRef("Deny")

	// The API server stores matchResources like these. It fills in matchPolicy
	// and empty selectors when someone adds matchResources.
	for _, tc := range []struct {
		matchResources string
		limits         bool
	}{
		{`{"matchPolicy":"Equivalent","namespaceSelector":{},"objectSelector":{}}`, false},
		{`{"matchPolicy":"Equivalent","namespaceSelector":{"matchExpressions":[{"key":"kubernetes.io/metadata.name","operator":"NotIn","values":["app"]}]},"objectSelector":{}}`, true},
		{`{"matchPolicy":"Equivalent","namespaceSelector":{},"objectSelector":{"matchLabels":{"tier":"web"}}}`, true},
		{`{"matchPolicy":"Equivalent","namespaceSelector":{},"objectSelector":{},"resourceRules":[{"apiGroups":["apps"],"apiVersions":["*"],"operations":["UPDATE"],"resources":["deployments"]}]}`, true},
		{`{"matchPolicy":"Equivalent","namespaceSelector":{},"objectSelector":{},"excludeResourceRules":[{"apiGroups":["git-k8s.imjasonh.com"],"apiVersions":["*"],"operations":["UPDATE"],"resources":["gitbranches/status"]}]}`, true},
	} {
		bindings[0].Spec.MatchResources = nil
		if err := json.Unmarshal([]byte(tc.matchResources), &bindings[0].Spec.MatchResources); err != nil {
			t.Fatal(err)
		}
		c := reconcile(world...)
		if !tc.limits && c.Status != kube.True {
			t.Errorf("with matchResources %s, PoliciesInstalled = %+v", tc.matchResources, c)
		}
		if tc.limits && (c.Status != kube.False || c.Reason != "NotDenying" ||
			!strings.HasSuffix(c.Message, `; run kubectl patch validatingadmissionpolicybinding git-k8s-check-results --type=merge -p '{"spec":{"matchResources":null}}'`)) {
			t.Errorf("with matchResources %s, PoliciesInstalled = %+v", tc.matchResources, c)
		}
	}
}

// TestPoliciesMatchConfig checks PoliciesInstalled against the policies and
// bindings in config/policy.yaml, which the core program installs.
func TestPoliciesMatchConfig(t *testing.T) {
	var world []any
	var names []string
	reads := map[string]bool{}
	var bindings []*admissionPolicyBinding
	// paramRefIn returns the fields of the paramRef in a binding, or in a
	// merge patch for one.
	paramRefIn := func(b []byte) map[string]string {
		var o struct {
			Spec struct {
				ParamRef map[string]string `json:"paramRef"`
			} `json:"spec"`
		}
		if err := json.Unmarshal(b, &o); err != nil {
			t.Fatal(err)
		}
		return o.Spec.ParamRef
	}
	refs := map[string]map[string]string{}
	dec := yaml.NewDecoder(bytes.NewReader(config.Policy))
	for {
		var doc map[string]any
		err := dec.Decode(&doc)
		if errors.Is(err, io.EOF) {
			break
		}
		if err != nil {
			t.Fatal(err)
		}
		b, err := json.Marshal(doc)
		if err != nil {
			t.Fatal(err)
		}
		switch doc["kind"] {
		case "ValidatingAdmissionPolicy":
			p := &admissionPolicy{}
			if err := json.Unmarshal(b, p); err != nil {
				t.Fatal(err)
			}
			names = append(names, p.Name)
			reads[p.Name] = p.Spec.ParamKind != nil
			world = append(world, p)
		case "ValidatingAdmissionPolicyBinding":
			binding := &admissionPolicyBinding{}
			if err := json.Unmarshal(b, binding); err != nil {
				t.Fatal(err)
			}
			bindings = append(bindings, binding)
			world = append(world, binding)
			refs[binding.Name] = paramRefIn(b)
		}
	}
	var want []string
	for _, p := range policies {
		want = append(want, p.name)
	}
	if !slices.Equal(names, want) {
		t.Errorf("config/policy.yaml holds the policies %v, but PoliciesInstalled reads %v", names, want)
	}
	for _, b := range bindings {
		if (b.Spec.ParamRef != nil) != reads[b.Spec.PolicyName] {
			t.Errorf("binding %s names parameters = %v, but its policy %s reads them = %v", b.Name, b.Spec.ParamRef != nil, b.Spec.PolicyName, reads[b.Spec.PolicyName])
		}
		if ref := b.Spec.ParamRef; ref != nil {
			b.Spec.ParamRef = nil
			patch := denyPatch(b, true)
			b.Spec.ParamRef = ref
			if patch == "" || !maps.Equal(paramRefIn([]byte(patch)), refs[b.Name]) {
				t.Errorf("without a paramRef, binding %s gets the patch %q, but config/policy.yaml sets the paramRef %v", b.Name, patch, refs[b.Name])
			}
		}
	}
	repo := &gitk8s.GitRepository{Object: kube.Meta("app", nil)}
	repo.Namespace = "default"
	ctx, _ := kube.Fake(t.Context(), repo, world...)
	if c := policiesCondition(ctx, true); c.Status != kube.True {
		t.Errorf("with the objects in config/policy.yaml, PoliciesInstalled = %+v", c)
	}
}

func TestFirstFetchFailureKeepsBranches(t *testing.T) {
	for name, tc := range map[string]struct {
		edit   func(*fixture)
		reason string
	}{
		"wrong password": {func(f *fixture) { f.secret.Data["password"] = []byte("wrong") }, "FetchFailed"},
		"no Secret":      {func(f *fixture) { f.secret = nil }, "CredentialsUnavailable"},
	} {
		t.Run(name, func(t *testing.T) {
			f := newFixture(t)
			f.work.Commit("main")
			f.work.Push("main")
			tc.edit(f)
			rec, err := f.tryReconcile()
			if err == nil {
				t.Fatal("reconcile succeeded without fetching from the external repository")
			}
			if c := f.condition("Ready"); c == nil || c.Reason != tc.reason {
				t.Errorf("Ready = %+v, want reason %s", c, tc.reason)
			}
			if len(owned(rec)) != 0 {
				t.Error("declared GitBranches without fetching from the external repository")
			}
		})
	}
}

// Once the mirror has a copy, git-k8s keeps working while the external
// repository fails, and the mirror tries it again after a while.
func TestExternalFailureBacksOff(t *testing.T) {
	f := newFixture(t)
	f.repo.Spec.PollInterval = "5m"
	b := f.branches()

	t.Log("The external repository starts refusing the mirror's credentials.")
	f.secret.Data["password"] = []byte("wrong")
	f.now = f.now.Add(5 * time.Minute)
	rec := f.reconcile()
	if len(owned(rec)) != 2 || rec.RequeueAfter() != 30*time.Second {
		t.Errorf("owned %d GitBranches, requeue = %v; want 2 and a retry in 30s", len(owned(rec)), rec.RequeueAfter())
	}
	if got := ownedPolicies(rec); got != wantPolicy {
		t.Errorf("while the external repository fails, owned NetworkPolicies: %q, want %q", got, wantPolicy)
	}
	if c := f.condition("Ready"); c.Status != kube.True {
		t.Errorf("Ready = %+v", c)
	}
	if c := f.condition("ExternalSynced"); c.Status != kube.False || c.Reason != "SyncFailed" || !strings.Contains(c.Message, "fetching from the external repository") {
		t.Errorf("ExternalSynced = %+v", c)
	}

	t.Log("The credentials work again, and a check pushes a fix. Until the retry, reconciles track the fix without pushing it.")
	f.secret.Data["password"] = []byte("pw")
	f.work.Write("fix.txt", "fix\n")
	fix := f.work.Commit("fix")
	f.pushToMirror("c/x")
	f.now = f.now.Add(time.Second)
	rec = f.reconcile()
	if got := owned(rec)["c/x"]; got == nil || got.Spec.Head != fix || rec.RequeueAfter() != 29*time.Second {
		t.Errorf("c/x = %+v, requeue = %v; want the fix %s and a retry in 29s", got, rec.RequeueAfter(), fix)
	}
	if got := f.srv.Heads(t, "app")["c/x"]; got != b.Spec.Head {
		t.Errorf("pushed to the external repository before the retry: c/x = %s", got)
	}
	if c := f.condition("ExternalSynced"); c.Reason != "SyncFailed" {
		t.Errorf("before the retry, ExternalSynced = %+v", c)
	}

	f.now = f.now.Add(29 * time.Second)
	rec = f.reconcile()
	if got := f.srv.Heads(t, "app")["c/x"]; got != fix || rec.RequeueAfter() != 5*time.Minute {
		t.Errorf("after the retry, the external repository has c/x at %s, requeue = %v; want %s and the poll interval", got, rec.RequeueAfter(), fix)
	}
	if c := f.condition("ExternalSynced"); c.Status != kube.True {
		t.Errorf("after the retry, ExternalSynced = %+v", c)
	}
}

// A lock that a killed git left in the mirror's copy stops the copy from
// taking the external repository's changes, and a condition says why.
func TestReportsStaleLock(t *testing.T) {
	for _, tc := range []struct {
		ref, condition, reason string
		fails                  bool
	}{
		{ref: "refs/heads/c/x", condition: "Ready", reason: "MirrorFailed", fails: true},
		{ref: "refs/git-k8s/downstream/heads/c/x", condition: "ExternalSynced", reason: "SyncFailed"},
	} {
		t.Run(tc.ref, func(t *testing.T) {
			f := newFixture(t)
			f.branches()
			if err := os.WriteFile(filepath.Join(f.copyDir(), filepath.FromSlash(tc.ref)+".lock"), nil, 0o644); err != nil {
				t.Fatal(err)
			}
			f.work.Write("person.txt", "person\n")
			f.work.Commit("a person's change")
			f.work.Push("c/x")
			f.now = f.now.Add(time.Hour)
			if _, err := f.tryReconcile(); (err != nil) != tc.fails {
				t.Errorf("reconcile = %v, want an error: %t", err, tc.fails)
			}
			if c := f.condition(tc.condition); c == nil || c.Status != kube.False || c.Reason != tc.reason || !strings.Contains(c.Message, "x.lock") {
				t.Errorf("%s = %+v, want %s and a message that names the lock", tc.condition, c, tc.reason)
			}
		})
	}
}

// A branch whose heads the mirror can't compare stays as it is on each
// side and doesn't land, and the other branches still sync.
func TestReportsBranchesItCantCompare(t *testing.T) {
	f := newFixture(t)
	b := f.branches()
	w := f.work
	w.Write("fix.txt", "fix\n")
	fix := w.Commit("a check's fix")
	f.pushToMirror("c/x")
	w.Branch("person", b.Spec.Head)
	w.Commit("a person's change")
	w.Push("c/x")
	w.Branch("newer", b.Spec.ParentHead)
	newer := w.Commit("newer main")
	w.Push("main")
	// git merge-base fails on a synced head that isn't a commit.
	w.Git("--git-dir="+f.copyDir(), "update-ref", "refs/git-k8s/synced/heads/c/x", b.Spec.ParentHead+"^{tree}")

	f.fetch()
	if c := f.condition("ExternalSynced"); c.Status != kube.False || c.Reason != "CompareFailed" || !strings.Contains(c.Message, "c/x (") {
		t.Errorf("ExternalSynced = %+v", c)
	}
	if got := f.mirrorHeads()["main"]; got != newer {
		t.Errorf("the mirror has main at %s, want the external repository's %s", got, newer)
	}
	b.Spec.Head = fix
	pass(b)
	if _, err := f.merge(b); err == nil {
		t.Errorf("the merge controller reconciled c/x without an error; state = %q", b.Status.State)
	}
	if err := f.finalize(); err == nil || !strings.Contains(err.Error(), "couldn't be compared with the mirror on c/x") {
		t.Errorf("Finalize = %v, want an error that names c/x", err)
	}
}

// A sync with a branch that the mirror couldn't compare and a branch that
// diverged reports CompareFailed. The GitBranch records a divergence, but
// only this condition names a branch that the mirror couldn't compare.
func TestCompareFailedComesBeforeDiverged(t *testing.T) {
	rep := &mirror.Report{
		Failed:   map[string]error{"c/x": errors.New("git merge-base: exit status 128")},
		Diverged: map[string]string{"c/y": "0123456789abcdef0123456789abcdef01234567"},
	}
	if c := syncedCondition(poll{}, rep); c.Reason != "CompareFailed" || !strings.Contains(c.Message, "c/x (") {
		t.Errorf("ExternalSynced = %+v, want the reason CompareFailed, naming c/x", c)
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
		r := &repositories{mirror: &mirror.Mirror{Git: &git.Git{}, Dir: t.TempDir()}}
		if err := r.Reconcile(ctx, repo); !kube.IsPermanent(err) {
			t.Errorf("err = %v, want a permanent error", err)
		}
	}
}

// A when expression that names a check that its rule doesn't list makes the
// GitRepository not Ready, instead of holding branches back later.
func TestRejectsWhenForUnlistedCheck(t *testing.T) {
	repo := &gitk8s.GitRepository{Object: kube.Meta("app", nil), Spec: gitk8s.GitRepositorySpec{URL: "http://127.0.0.1:1/app.git"}}
	repo.Namespace = "default"
	repo.Spec.Branches = []gitk8s.BranchRule{{Match: "main", Merge: &gitk8s.MergePolicy{Checks: []gitk8s.CheckPolicy{{Name: "gofmt"}}, When: "checks.gofmy.passed"}}}
	ctx, _ := kube.Fake(t.Context(), repo)
	r := &repositories{mirror: &mirror.Mirror{Git: &git.Git{}, Dir: t.TempDir()}}
	if err := r.Reconcile(ctx, repo); !kube.IsPermanent(err) {
		t.Errorf("err = %v, want a permanent error", err)
	}
	want := `branches rule "main": when: 1:7: the merge policy doesn't list a check named 'gofmy'`
	if c := kube.FindCondition(repo.Status.Conditions, "Ready"); c == nil || c.Status != kube.False || c.Reason != "InvalidMergePolicy" || c.Message != want {
		t.Errorf("Ready = %+v, want False, InvalidMergePolicy, and %q", c, want)
	}
}

// A branch that changes in the mirror and in the external repository stays
// as it is on each side, and doesn't land, until a commit that contains
// both heads resolves it.
func TestRecordsDivergence(t *testing.T) {
	f := newFixture(t)
	b := f.branches()
	synced := b.Spec.Head
	w := f.work
	w.Write("fix.txt", "fix\n")
	fix := w.Commit("a check's fix")
	f.pushToMirror("c/x")
	w.Branch("person", b.Spec.Head)
	w.Write("person.txt", "person\n")
	person := w.Commit("a person's change")
	w.Push("c/x")

	rec := f.fetch(b)
	if c := f.condition("ExternalSynced"); c.Status != kube.False || c.Reason != "Diverged" || !strings.HasPrefix(c.Message, "c/x changed both") {
		t.Errorf("ExternalSynced = %+v", c)
	}
	if got := owned(rec)["c/x"]; got == nil || got.Spec.Head != fix {
		t.Errorf("c/x = %+v, want the mirror's head %s", got, fix)
	}
	if got, want := kube.Triggered[gitk8s.GitBranch](rec), []kube.Key{{Namespace: "default", Name: b.Name}}; !slices.Equal(got, want) {
		t.Errorf("triggered GitBranches %v, want %v", got, want)
	}
	if got := f.srv.Heads(t, "app")["c/x"]; got != person {
		t.Errorf("the external repository has c/x at %s, want the person's %s", got, person)
	}
	if got := f.mirrorGit("ls-remote", f.mirrorURL, "refs/git-k8s/downstream/heads/c/x"); !strings.HasPrefix(got, person) {
		t.Errorf("the mirror advertises %q, want the external repository's head %s", got, person)
	}

	t.Log("The merge controller records the divergence and holds the branch.")
	b.Spec.Head = fix
	pass(b)
	if _, err := f.merge(b); err != nil {
		t.Fatal(err)
	}
	want := &gitk8s.Divergence{Commit: person, Ref: "refs/git-k8s/downstream/heads/c/x", Base: synced}
	if d := b.Status.Diverged; d == nil || *d != *want || b.Status.State != gitk8s.MergeStateDiverged {
		t.Errorf("diverged = %+v, state = %q; want %+v and %s", d, b.Status.State, want, gitk8s.MergeStateDiverged)
	}
	if got := f.mirrorHeads()["main"]; got != b.Spec.ParentHead {
		t.Errorf("landed a diverged branch: main = %s", got)
	}

	t.Log("A commit that contains both heads resolves it, and the mirror fast-forwards the external repository to it.")
	w.Branch("resolve", fix)
	w.Git("merge", "--quiet", "--no-edit", person)
	resolved := w.Git("rev-parse", "HEAD")
	f.pushToMirror("c/x")
	f.now = f.now.Add(time.Second)
	rec = f.reconcile(b)
	if got := f.srv.Heads(t, "app")["c/x"]; got != resolved {
		t.Errorf("the external repository has c/x at %s, want the resolution %s", got, resolved)
	}
	if c := f.condition("ExternalSynced"); c.Status != kube.True {
		t.Errorf("ExternalSynced = %+v", c)
	}
	if got := kube.Triggered[gitk8s.GitBranch](rec); len(got) != 1 {
		t.Errorf("triggered GitBranches %v, want c/x's, whose divergence ended", got)
	}
	b.Spec.Head = resolved
	pass(b)
	if _, err := f.merge(b); err != nil {
		t.Fatal(err)
	}
	if b.Status.Diverged != nil || b.Status.State != gitk8s.MergeStateLanded {
		t.Errorf("diverged = %+v, state = %q; want nil and %s", b.Status.Diverged, b.Status.State, gitk8s.MergeStateLanded)
	}
}

// A branch that changes in the mirror while a person deletes it in the
// external repository diverges too, and the GitBranch says so.
func TestRecordsDeletionAsDivergence(t *testing.T) {
	f := newFixture(t)
	b := f.branches()
	synced := b.Spec.Head
	f.work.Write("fix.txt", "fix\n")
	b.Spec.Head = f.work.Commit("a check's fix")
	f.pushToMirror("c/x")
	f.work.Delete("c/x")

	rec := f.fetch(b)
	if c := f.condition("ExternalSynced"); c.Reason != "Diverged" || !strings.HasPrefix(c.Message, "c/x changed both") {
		t.Errorf("ExternalSynced = %+v", c)
	}
	if got, want := kube.Triggered[gitk8s.GitBranch](rec), []kube.Key{{Namespace: "default", Name: b.Name}}; !slices.Equal(got, want) {
		t.Errorf("triggered GitBranches %v, want %v", got, want)
	}
	if _, ok := f.srv.Heads(t, "app")["c/x"]; ok {
		t.Error("the mirror pushed c/x back to the external repository, which deleted it")
	}
	pass(b)
	if _, err := f.merge(b); err != nil {
		t.Fatal(err)
	}
	if d := b.Status.Diverged; d == nil || *d != (gitk8s.Divergence{Base: synced}) || b.Status.State != gitk8s.MergeStateDiverged {
		t.Errorf("diverged = %+v, state = %q; want only the base %s, and %s", d, b.Status.State, synced, gitk8s.MergeStateDiverged)
	}
	if c := kube.FindCondition(b.Status.Conditions, "Landed"); c == nil || !strings.Contains(c.Message, "external repository, which deleted it") {
		t.Errorf("Landed = %+v, want a message that says the external repository deleted c/x", c)
	}
}

// Branches land on a parent that diverged, and a branch without a parent
// records its divergence too.
func TestLandsOnDivergedParent(t *testing.T) {
	f := newFixture(t)
	w := f.work
	base := w.Commit("main")
	w.Push("main")
	f.fetch()
	w.Write("person.txt", "person\n")
	w.Commit("a person's push to main")
	w.Push("main")
	w.Branch("landed", base)
	w.Write("landed.txt", "landed\n")
	landed := w.Commit("a landing in the mirror")
	f.landInMirror(landed)
	w.Write("x.txt", "x\n")
	head := w.Commit("add x")
	f.pushToMirror("c/x")
	rec := f.fetch()
	if c := f.condition("ExternalSynced"); c.Reason != "Diverged" || !strings.HasPrefix(c.Message, "main changed both") {
		t.Errorf("ExternalSynced = %+v", c)
	}

	b := owned(rec)["c/x"]
	if b == nil || b.Spec.ParentHead != landed || b.Spec.Head != head {
		t.Fatalf("c/x = %+v", b)
	}
	pass(b)
	if _, err := f.merge(b); err != nil {
		t.Fatal(err)
	}
	if b.Status.State != gitk8s.MergeStateLanded || b.Status.Diverged != nil {
		t.Errorf("state = %q, diverged = %+v; want %s and nil", b.Status.State, b.Status.Diverged, gitk8s.MergeStateLanded)
	}

	main := owned(rec)["main"]
	if _, err := f.merge(main); err != nil {
		t.Fatal(err)
	}
	if d := main.Status.Diverged; d == nil || d.Ref != "refs/git-k8s/downstream/heads/main" || main.Status.State != "" {
		t.Errorf("main's diverged = %+v, state = %q", d, main.Status.State)
	}
}

func TestLandsAndDeletesBranch(t *testing.T) {
	f := newFixture(t)
	b := f.branches()
	rec, err := f.merge(b)
	if err != nil {
		t.Fatal(err)
	}
	heads := f.mirrorHeads()
	if heads["main"] != b.Spec.Head {
		t.Errorf("main = %s in the mirror, want %s", heads["main"], b.Spec.Head)
	}
	if _, ok := heads["c/x"]; ok {
		t.Error("c/x wasn't deleted after it landed")
	}
	c := kube.FindCondition(b.Status.Conditions, "Landed")
	if c == nil || c.Status != kube.True || c.Reason != string(gitk8s.MergeStateLanded) || b.Status.State != gitk8s.MergeStateLanded {
		t.Errorf("Landed = %+v, state %q", c, b.Status.State)
	}
	if b.Status.Checks != nil {
		t.Error("the merge controller must leave status.checks out of its status write")
	}
	if got, want := kube.Triggered[gitk8s.GitRepository](rec), []kube.Key{{Namespace: "default", Name: "app"}}; !slices.Equal(got, want) {
		t.Errorf("triggered GitRepositories %v, want %v", got, want)
	}

	t.Log("The reconcile that the landing triggered pushes it to the external repository.")
	f.now = f.now.Add(time.Second)
	f.reconcile()
	heads = f.srv.Heads(t, "app")
	if heads["main"] != b.Spec.Head {
		t.Errorf("main = %s in the external repository, want %s", heads["main"], b.Spec.Head)
	}
	if _, ok := heads["c/x"]; ok {
		t.Error("c/x wasn't deleted from the external repository")
	}
}

// A fast-forward and the deletion of the landed branch are one update, so a
// failure that stops the deletion doesn't land the branch either, and the
// next try does both.
func TestLandsAndDeletesInOneUpdate(t *testing.T) {
	f := newFixture(t)
	b := f.branches()
	lock := filepath.Join(f.copyDir(), "refs", "heads", "c", "x.lock")
	if err := os.WriteFile(lock, nil, 0o644); err != nil {
		t.Fatal(err)
	}
	if _, err := f.merge(b); err == nil || !strings.Contains(err.Error(), "x.lock") {
		t.Errorf("err = %v, want one that names the lock", err)
	}
	if heads := f.mirrorHeads(); heads["main"] != b.Spec.ParentHead || heads["c/x"] != b.Spec.Head {
		t.Errorf("main = %s, c/x = %s in the mirror; want main still at %s and c/x at %s", heads["main"], heads["c/x"], b.Spec.ParentHead, b.Spec.Head)
	}

	t.Log("Once the lock is gone, the next reconcile lands c/x and deletes it.")
	if err := os.Remove(lock); err != nil {
		t.Fatal(err)
	}
	pass(b)
	if _, err := f.merge(b); err != nil {
		t.Fatal(err)
	}
	heads := f.mirrorHeads()
	if heads["main"] != b.Spec.Head {
		t.Errorf("main = %s in the mirror, want %s", heads["main"], b.Spec.Head)
	}
	if _, ok := heads["c/x"]; ok {
		t.Error("c/x wasn't deleted after it landed")
	}
}

// A branch that moves or is deleted after the repositories controller lists
// it still lands at the listed head, and the merge controller leaves it as
// it is.
func TestLandsABranchThatChangedAfterListing(t *testing.T) {
	for name, change := range map[string]func(*fixture){
		"moved": func(f *fixture) {
			f.work.Write("y.txt", "y\n")
			f.work.Commit("c/x moves after the listing")
			f.pushToMirror("c/x")
		},
		"deleted": func(f *fixture) {
			f.work.Git("--git-dir="+f.copyDir(), "update-ref", "-d", "refs/heads/c/x")
		},
	} {
		t.Run(name, func(t *testing.T) {
			f := newFixture(t)
			b := f.branches()
			change(f)
			want := f.mirrorHeads()["c/x"]
			rec, err := f.merge(b)
			if err != nil {
				t.Fatal(err)
			}
			heads := f.mirrorHeads()
			if heads["main"] != b.Spec.Head {
				t.Errorf("main = %s in the mirror, want %s", heads["main"], b.Spec.Head)
			}
			if heads["c/x"] != want {
				t.Errorf("c/x = %q in the mirror, want %q", heads["c/x"], want)
			}
			if b.Status.State != gitk8s.MergeStateLanded {
				t.Errorf("state = %q, want %s", b.Status.State, gitk8s.MergeStateLanded)
			}
			for _, e := range rec.Events() {
				if e.Reason == "DeletedBranch" {
					t.Errorf("recorded %+v for a branch that the merge controller didn't delete", e)
				}
			}
		})
	}
}

func TestWaitsForFreshPassingChecks(t *testing.T) {
	for name, edit := range map[string]func(*gitk8s.GitBranch){
		"pending": func(b *gitk8s.GitBranch) { delete(b.Status.Checks, "gofmt") },
		"failed": func(b *gitk8s.GitBranch) {
			b.Status.Checks["gofmt"] = gitk8s.CheckResult{Commit: b.Spec.Head, Scope: gitk8s.ScopeHead, State: gitk8s.Failed}
		},
		"stale head": func(b *gitk8s.GitBranch) {
			b.Status.Checks["gofmt"] = gitk8s.CheckResult{Commit: "old", Scope: gitk8s.ScopeHead, State: gitk8s.Passed}
		},
		"stale parent": func(b *gitk8s.GitBranch) {
			b.Status.Checks["base"] = gitk8s.CheckResult{Commit: b.Spec.Head, Scope: gitk8s.ScopeParent, ParentCommit: "old", State: gitk8s.Passed}
		},
	} {
		t.Run(name, func(t *testing.T) {
			f := newFixture(t)
			b := f.branches()
			edit(b)
			if msg := f.mergeIn(parentOf(b), b); b.Status.State != gitk8s.MergeStateWaitingForChecks || b.Status.Queued != nil {
				t.Errorf("state = %q, queued %+v, %q; want %s, out of the queue", b.Status.State, b.Status.Queued, msg, gitk8s.MergeStateWaitingForChecks)
			}
			if got := f.mirrorHeads()["main"]; got != b.Spec.ParentHead {
				t.Errorf("main moved to %s", got)
			}
		})
	}
}

func TestGateExpression(t *testing.T) {
	f := newFixture(t)
	b := f.branches()
	p := *policy
	p.Checks = append(p.Checks[:2:2], gitk8s.CheckPolicy{Name: "risk"}, gitk8s.CheckPolicy{Name: "approval"})
	p.When = `checks.base.passed && checks.gofmt.passed && (checks.risk.outputs.level == "low" || checks.approval.passed)`
	b.Spec.Merge = &p
	b.Status.Checks["risk"] = gitk8s.CheckResult{Commit: b.Spec.Head, Scope: gitk8s.ScopeParent, ParentCommit: b.Spec.ParentHead, State: gitk8s.Passed, Outputs: map[string]string{"level": "high"}}
	b.Status.Checks["approval"] = gitk8s.CheckResult{Commit: b.Spec.Head, Scope: gitk8s.ScopeHead, State: gitk8s.Failed}
	results := b.Status.Checks
	if _, err := f.merge(b); err != nil {
		t.Fatal(err)
	}
	if b.Status.State != gitk8s.MergeStateWaitingForChecks || !strings.Contains(kube.FindCondition(b.Status.Conditions, "Landed").Message, "risk Passed (high)") {
		t.Fatalf("state = %q, conditions %+v", b.Status.State, b.Status.Conditions)
	}

	results["approval"] = gitk8s.CheckResult{Commit: b.Spec.Head, Scope: gitk8s.ScopeHead, State: gitk8s.Passed}
	b.Status.Checks = results
	if _, err := f.merge(b); err != nil {
		t.Fatal(err)
	}
	if b.Status.State != gitk8s.MergeStateLanded {
		t.Errorf("state after approval = %q, want %s", b.Status.State, gitk8s.MergeStateLanded)
	}
}

func TestLandsResultsForTheParentsHead(t *testing.T) {
	f := newFixture(t)
	b := f.branches()
	p := *policy
	p.Checks = []gitk8s.CheckPolicy{{Name: "base"}, {Name: "gofmt"}, {Name: "risk"}}
	b.Spec.Merge = &p
	low := map[string]string{"level": "low"}
	b.Status.Checks["risk"] = gitk8s.CheckResult{Commit: b.Spec.Head, Scope: gitk8s.ScopeChange, MergeBase: strings.Repeat("1", 40), State: gitk8s.Passed, Outputs: low}
	results := b.Status.Checks
	if _, err := f.merge(b); err != nil {
		t.Fatal(err)
	}
	if msg := kube.FindCondition(b.Status.Conditions, "Landed").Message; b.Status.State != gitk8s.MergeStateWaitingForChecks || msg != "checks: base Passed, gofmt Passed, risk Pending" {
		t.Fatalf("state = %q, %q; want %s, because risk's result is for the change on top of another merge base", b.Status.State, msg, gitk8s.MergeStateWaitingForChecks)
	}
	if got := f.mirrorHeads()["main"]; got != b.Spec.ParentHead {
		t.Fatalf("main moved to %s", got)
	}

	results["risk"] = gitk8s.CheckResult{Commit: b.Spec.Head, Scope: gitk8s.ScopeChange, MergeBase: b.Spec.ParentHead, State: gitk8s.Passed, Outputs: low}
	b.Status.Checks = results
	if _, err := f.merge(b); err != nil {
		t.Fatal(err)
	}
	if b.Status.State != gitk8s.MergeStateLanded {
		t.Errorf("state = %q, want %s", b.Status.State, gitk8s.MergeStateLanded)
	}
}

func TestNotFastForward(t *testing.T) {
	f := newFixture(t)
	b := f.branches()
	w := f.work
	w.Branch("main", b.Spec.ParentHead)
	w.Write("y.txt", "y\n")
	b.Spec.ParentHead = w.Commit("main moves")
	w.Push("main")
	f.fetch()
	pass(b)
	if _, err := f.merge(b); err != nil {
		t.Fatal(err)
	}
	if b.Status.State != gitk8s.MergeStateNotFastForward {
		t.Errorf("state = %q, want %s", b.Status.State, gitk8s.MergeStateNotFastForward)
	}
}

func TestParentMovedAfterListing(t *testing.T) {
	f := newFixture(t)
	b := f.branches()
	w := f.work
	w.Branch("main", b.Spec.Head)
	w.Write("z.txt", "z\n")
	moved := w.Commit("main moves past the branch")
	f.landInMirror(moved)
	if _, err := f.merge(b); !errors.Is(err, git.ErrRejected) {
		t.Errorf("err = %v, want a rejected update", err)
	}
	if got := f.mirrorHeads()["main"]; got != moved {
		t.Errorf("main = %s, want %s", got, moved)
	}
}

// A branch whose changes its parent already has, such as one just created
// from its parent, isn't Landed or deleted, because the merge controller
// didn't land it.
func TestBranchesWithNothingToLandStay(t *testing.T) {
	for name, setup := range map[string]func(*gitk8s.GitBranch, *gittest.Work){
		"at the parent's head": func(b *gitk8s.GitBranch, w *gittest.Work) {
			w.Push("main")
			b.Spec.ParentHead = b.Spec.Head
		},
		"behind the parent": func(b *gitk8s.GitBranch, w *gittest.Work) {
			w.Write("y.txt", "y\n")
			b.Spec.ParentHead = w.Commit("main moves past the branch")
			w.Push("main")
		},
	} {
		t.Run(name, func(t *testing.T) {
			f := newFixture(t)
			b := f.branches()
			setup(b, f.work)
			f.fetch()
			pass(b)
			if _, err := f.merge(b); err != nil {
				t.Fatal(err)
			}
			if c := kube.FindCondition(b.Status.Conditions, "Landed"); c == nil || c.Status != kube.False || b.Status.State != gitk8s.MergeStateNothingToLand {
				t.Errorf("Landed = %+v, state = %q; want False and %s", c, b.Status.State, gitk8s.MergeStateNothingToLand)
			}
			if _, ok := f.mirrorHeads()["c/x"]; !ok {
				t.Error("deleted a branch that the merge controller didn't land")
			}
		})
	}
}

// A branch that stays after it lands is still Landed once the repositories
// controller lists it at its parent's head, so a wait for the condition
// can't miss the landing.
func TestKeptBranchStaysLanded(t *testing.T) {
	f := newFixture(t)
	b := f.branches()
	p := *policy
	p.DeleteLandedBranches = false
	b.Spec.Merge = &p
	if _, err := f.merge(b); err != nil || b.Status.State != gitk8s.MergeStateLanded {
		t.Fatalf("err = %v, state = %q; want %s", err, b.Status.State, gitk8s.MergeStateLanded)
	}
	msg := kube.FindCondition(b.Status.Conditions, "Landed").Message

	t.Log("The repositories controller lists c/x at main's head.")
	b.Spec.ParentHead = b.Spec.Head
	b.Generation++
	if _, err := f.merge(b); err != nil {
		t.Fatal(err)
	}
	c := kube.FindCondition(b.Status.Conditions, "Landed")
	if c == nil || c.Status != kube.True || c.Message != msg || c.ObservedGeneration != b.Generation || b.Status.State != gitk8s.MergeStateLanded {
		t.Errorf("Landed = %+v, state = %q; want True at generation %d with %q", c, b.Status.State, b.Generation, msg)
	}
	if _, ok := f.mirrorHeads()["c/x"]; !ok {
		t.Error("deleted c/x, which the merge policy keeps")
	}
}

func TestInvalidGateWithFinalResults(t *testing.T) {
	f := newFixture(t)
	b := f.branches()
	p := *policy
	p.When = "checks.gofmt.outputs.level == 'low'"
	b.Spec.Merge = &p
	if _, err := f.merge(b); err != nil {
		t.Fatal(err)
	}
	if b.Status.State != gitk8s.MergeStateInvalidGate {
		t.Errorf("state = %q, want %s", b.Status.State, gitk8s.MergeStateInvalidGate)
	}
}

func TestNoParentNoState(t *testing.T) {
	b := &gitk8s.GitBranch{Object: kube.Meta("app-main", nil), Spec: gitk8s.GitBranchSpec{Repository: "app", Branch: "main", Head: "abc"}}
	b.Namespace = "default"
	repo := &gitk8s.GitRepository{Object: kube.Meta("app", nil), Spec: gitk8s.GitRepositorySpec{URL: "http://127.0.0.1:1/app.git"}}
	repo.Namespace = "default"
	ctx, _ := kube.Fake(t.Context(), b, repo)
	m := &merger{mirror: &mirror.Mirror{Git: &git.Git{}, Dir: t.TempDir()}}
	if err := m.Reconcile(ctx, b); err != nil || b.Status.State != "" || b.Status.Diverged != nil || len(b.Status.Conditions) != 0 {
		t.Errorf("before the mirror has a copy, err = %v, status = %+v", err, b.Status)
	}

	t.Log("A branch that loses its parent loses its state and its Landed condition.")
	b.Status.State = gitk8s.MergeStateWaitingForChecks
	synced := kube.Condition{Type: "Synced", Status: kube.True, Reason: "Synced"}
	b.Status.Conditions = []kube.Condition{{Type: "Landed", Status: kube.False, Reason: string(gitk8s.MergeStateWaitingForChecks)}, synced}
	ctx, _ = kube.Fake(t.Context(), b, repo)
	if err := m.Reconcile(ctx, b); err != nil || b.Status.State != "" || !slices.Equal(b.Status.Conditions, []kube.Condition{synced}) {
		t.Errorf("after losing the parent, err = %v, status = %+v", err, b.Status)
	}
}

func TestFinalize(t *testing.T) {
	t.Run("pushes the mirror's last changes, then deletes the copy", func(t *testing.T) {
		f := newFixture(t)
		f.branches()
		f.work.Write("fix.txt", "fix\n")
		fix := f.work.Commit("fix")
		f.pushToMirror("c/x")
		if err := f.finalize(); err != nil {
			t.Fatal(err)
		}
		if got := f.srv.Heads(t, "app")["c/x"]; got != fix {
			t.Errorf("the external repository has c/x at %s, want %s", got, fix)
		}
		if _, err := os.Stat(f.copyDir()); !errors.Is(err, os.ErrNotExist) {
			t.Errorf("the copy is still there: %v", err)
		}
		if len(f.r.polls) != 0 {
			t.Errorf("polls = %v, want none", f.r.polls)
		}
	})

	t.Run("keeps the copy while the external repository lacks a change", func(t *testing.T) {
		f := newFixture(t)
		f.branches()
		f.work.Write("fix.txt", "fix\n")
		fix := f.work.Commit("fix")
		f.pushToMirror("c/x")
		f.secret.Data["password"] = []byte("wrong")
		err := f.finalize()
		if err == nil || !strings.Contains(err.Error(), "changes to c/x") || !strings.Contains(err.Error(), "remove the finalizer "+finalizer) {
			t.Errorf("err = %v, want one that names c/x and the finalizer", err)
		}
		if _, err := os.Stat(f.copyDir()); err != nil {
			t.Fatalf("the copy is gone: %v", err)
		}
		f.secret.Data["password"] = []byte("pw")
		if err := f.finalize(); err != nil {
			t.Fatal(err)
		}
		if got := f.srv.Heads(t, "app")["c/x"]; got != fix {
			t.Errorf("the external repository has c/x at %s, want %s", got, fix)
		}
	})

	t.Run("keeps the copy of a diverged branch", func(t *testing.T) {
		f := newFixture(t)
		b := f.branches()
		f.work.Write("fix.txt", "fix\n")
		f.work.Commit("fix")
		f.pushToMirror("c/x")
		f.work.Branch("person", b.Spec.Head)
		f.work.Commit("a person's change")
		f.work.Push("c/x")
		f.fetch()
		if err := f.finalize(); err == nil || !strings.Contains(err.Error(), "diverged from the mirror on c/x") {
			t.Errorf("err = %v, want one that names the diverged branch", err)
		}
		if _, err := os.Stat(f.copyDir()); err != nil {
			t.Fatalf("the copy is gone: %v", err)
		}
	})

	t.Run("a repository that never synced needs no credentials", func(t *testing.T) {
		f := newFixture(t)
		f.secret = nil
		if err := f.finalize(); err != nil {
			t.Fatal(err)
		}
	})
}

// The program's one handler sends PUT requests under /results/ to the
// results endpoint and every other request to the mirror, including git's
// requests for a repository in a namespace named results.
func TestServeRoutesResultsAndMirror(t *testing.T) {
	var reached []string
	m := http.HandlerFunc(func(w http.ResponseWriter, r *http.Request) {
		reached = append(reached, r.Method+" "+r.URL.Path)
		w.WriteHeader(http.StatusTeapot)
	})
	h := serve(m, &results{timeout: time.Second, poll: time.Millisecond})
	for _, tc := range []struct {
		method, target string
		mirror         bool
	}{
		{http.MethodPut, "/results/default/app-c-x/gofmt?generation=3", false},
		{http.MethodGet, "/results/app.git/info/refs?service=git-upload-pack", true},
		{http.MethodPost, "/results/app.git/git-upload-pack", true},
		{http.MethodPost, "/results/app.git/git-receive-pack", true},
		{http.MethodGet, "/default/app.git/info/refs?service=git-receive-pack", true},
		{http.MethodGet, "/results/default/app-c-x/gofmt", true},
	} {
		reached = nil
		w := httptest.NewRecorder()
		h.ServeHTTP(w, httptest.NewRequest(tc.method, tc.target, nil))
		switch {
		case tc.mirror && (len(reached) != 1 || w.Code != http.StatusTeapot):
			t.Errorf("%s %s: got %d, and the mirror got %q; want the mirror to get it", tc.method, tc.target, w.Code, reached)
		case !tc.mirror && (len(reached) != 0 || w.Code != http.StatusUnauthorized):
			// Without a token, the results endpoint answers 401.
			t.Errorf("%s %s: got %d %q, and the mirror got %q; want 401 from the results endpoint", tc.method, tc.target, w.Code, w.Body, reached)
		}
	}
}
