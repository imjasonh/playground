package main

import (
	"errors"
	"os"
	"path/filepath"
	"slices"
	"strings"
	"testing"
	"time"

	gitk8s "github.com/imjasonh/playground/git-k8s"
	"github.com/imjasonh/playground/git-k8s/internal/git"
	"github.com/imjasonh/playground/git-k8s/internal/gittest"
	"github.com/imjasonh/playground/git-k8s/internal/mirror"
	"github.com/imjasonh/playground/kube"
	"github.com/imjasonh/playground/kube/k8s"
)

var policy = &gitk8s.MergePolicy{
	Checks:               []gitk8s.CheckPolicy{{Name: "base", MayPush: true}, {Name: "gofmt", MayPush: true}},
	DeleteMergedBranches: true,
}

func rules() []gitk8s.BranchRule {
	return []gitk8s.BranchRule{{Match: "main", Merge: policy}, {Match: "c/**", Parent: "main"}}
}

// fixture is the GitRepository default/app, its external repository on a
// git server, and the mirror's copy of it.
type fixture struct {
	t   *testing.T
	srv *gittest.Server
	// work makes commits, and pushes them to the external repository with
	// Push or to the mirror's copy with pushToMirror.
	work   *gittest.Work
	repo   *gitk8s.GitRepository
	secret *k8s.Secret
	mirror *mirror.Mirror
	r      *repositories
	now    time.Time
}

func newFixture(t *testing.T) *fixture {
	t.Helper()
	srv := gittest.NewServer(t, "pw")
	repo, secret := srv.Repository("app", rules()...)
	repo.UID = "uid-1"
	f := &fixture{
		t:      t,
		srv:    srv,
		work:   srv.NewWork(t, "app"),
		repo:   repo,
		secret: secret,
		mirror: &mirror.Mirror{Git: &git.Git{}, Dir: t.TempDir()},
		now:    time.Unix(1000, 0),
	}
	f.r = &repositories{mirror: f.mirror, now: func() time.Time { return f.now }}
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

func (f *fixture) merge(b *gitk8s.GitBranch) (*kube.Recorder, error) {
	ctx, rec := kube.Fake(f.t.Context(), b, f.world(f.repo)...)
	return rec, (&merger{mirror: f.mirror}).Reconcile(ctx, b)
}

func (f *fixture) finalize() error {
	ctx, _ := kube.Fake(f.t.Context(), f.repo, f.world()...)
	return f.r.Finalize(ctx, f.repo)
}

func (f *fixture) copyDir() string { return filepath.Join(f.mirror.Dir, "default", "app.git") }

// pushToMirror pushes the working repository's HEAD to branch in the
// mirror's copy, as a check's push through the mirror does.
func (f *fixture) pushToMirror(branch string) {
	f.t.Helper()
	f.work.Git("push", "--quiet", "--force", f.copyDir(), "HEAD:refs/heads/"+branch)
}

func (f *fixture) mirrorHeads() map[string]string {
	f.t.Helper()
	heads, err := (&git.Git{}).LsRemote(f.t.Context(), git.Remote{URL: f.copyDir()})
	if err != nil {
		f.t.Fatal(err)
	}
	return heads
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
		"base":  {Commit: b.Spec.Head, ParentCommit: b.Spec.ParentHead, State: gitk8s.Passed},
		"gofmt": {Commit: b.Spec.Head, State: gitk8s.Passed},
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
	reconcile := func(world ...any) *kube.Condition {
		t.Helper()
		f.reconcile(world...)
		return f.condition("PoliciesInstalled")
	}
	if c := reconcile(); c == nil || c.Status != kube.False || !strings.Contains(c.Message, "git-k8s-check-results and git-k8s-branches") {
		t.Errorf("without the policies, PoliciesInstalled = %+v", c)
	}

	var world []any
	var bindings []*admissionPolicyBinding
	for _, name := range policyNames {
		b := &admissionPolicyBinding{Object: kube.Meta(name, nil)}
		b.Spec.PolicyName, b.Spec.ValidationActions = name, []string{"Warn"}
		bindings = append(bindings, b)
		world = append(world, &admissionPolicy{Object: kube.Meta(name, nil)}, b)
	}
	if c := reconcile(world...); c.Status != kube.False {
		t.Errorf("with bindings that only warn, PoliciesInstalled = %+v", c)
	}
	for _, b := range bindings {
		b.Spec.ValidationActions = []string{"Deny"}
	}
	if c := reconcile(world...); c.Status != kube.True {
		t.Errorf("with the policies installed, PoliciesInstalled = %+v", c)
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
	if got := w.Git("ls-remote", f.copyDir(), "refs/git-k8s/downstream/heads/c/x"); !strings.HasPrefix(got, person) {
		t.Errorf("the mirror's copy has %q, want the external repository's head %s", got, person)
	}

	t.Log("The merge controller records the divergence and holds the branch.")
	b.Spec.Head = fix
	pass(b)
	if _, err := f.merge(b); err != nil {
		t.Fatal(err)
	}
	want := &gitk8s.Divergence{Commit: person, Ref: "refs/git-k8s/downstream/heads/c/x", Base: synced}
	if d := b.Status.Diverged; d == nil || *d != *want || b.Status.State != reasonDiverged {
		t.Errorf("diverged = %+v, state = %q; want %+v and %s", d, b.Status.State, want, reasonDiverged)
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
	if b.Status.Diverged != nil || b.Status.State != reasonLanded {
		t.Errorf("diverged = %+v, state = %q; want nil and %s", b.Status.Diverged, b.Status.State, reasonLanded)
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
	if d := b.Status.Diverged; d == nil || *d != (gitk8s.Divergence{Base: synced}) || b.Status.State != reasonDiverged {
		t.Errorf("diverged = %+v, state = %q; want only the base %s, and %s", d, b.Status.State, synced, reasonDiverged)
	}
	if c := kube.FindCondition(b.Status.Conditions, "Merged"); c == nil || !strings.Contains(c.Message, "external repository, which deleted it") {
		t.Errorf("Merged = %+v, want a message that says the external repository deleted c/x", c)
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
	f.pushToMirror("main")
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
	if b.Status.State != reasonLanded || b.Status.Diverged != nil {
		t.Errorf("state = %q, diverged = %+v; want %s and nil", b.Status.State, b.Status.Diverged, reasonLanded)
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
	c := kube.FindCondition(b.Status.Conditions, "Merged")
	if c == nil || c.Status != kube.True || c.Reason != reasonLanded || b.Status.State != reasonLanded {
		t.Errorf("Merged = %+v, state %q", c, b.Status.State)
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
			f := newFixture(t)
			b := f.branches()
			edit(b)
			if _, err := f.merge(b); err != nil {
				t.Fatal(err)
			}
			if b.Status.State != reasonWaitingForChecks {
				t.Errorf("state = %q, want %s", b.Status.State, reasonWaitingForChecks)
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
	b.Status.Checks["risk"] = gitk8s.CheckResult{Commit: b.Spec.Head, ParentCommit: b.Spec.ParentHead, State: gitk8s.Passed, Outputs: map[string]string{"level": "high"}}
	b.Status.Checks["approval"] = gitk8s.CheckResult{Commit: b.Spec.Head, State: gitk8s.Failed}
	results := b.Status.Checks
	if _, err := f.merge(b); err != nil {
		t.Fatal(err)
	}
	if b.Status.State != reasonWaitingForChecks || !strings.Contains(kube.FindCondition(b.Status.Conditions, "Merged").Message, "risk Passed (high)") {
		t.Fatalf("state = %q, conditions %+v", b.Status.State, b.Status.Conditions)
	}

	results["approval"] = gitk8s.CheckResult{Commit: b.Spec.Head, State: gitk8s.Passed}
	b.Status.Checks = results
	if _, err := f.merge(b); err != nil {
		t.Fatal(err)
	}
	if b.Status.State != reasonLanded {
		t.Errorf("state after approval = %q, want %s", b.Status.State, reasonLanded)
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
	if b.Status.State != reasonNotFastForward {
		t.Errorf("state = %q, want %s", b.Status.State, reasonNotFastForward)
	}
}

func TestParentMovedAfterListing(t *testing.T) {
	f := newFixture(t)
	b := f.branches()
	w := f.work
	w.Branch("main", b.Spec.Head)
	w.Write("z.txt", "z\n")
	moved := w.Commit("main moves past the branch")
	f.pushToMirror("main")
	if _, err := f.merge(b); !errors.Is(err, git.ErrRejected) {
		t.Errorf("err = %v, want a rejected update", err)
	}
	if got := f.mirrorHeads()["main"]; got != moved {
		t.Errorf("main = %s, want %s", got, moved)
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
			if b.Status.State != reasonMerged {
				t.Errorf("state = %q, want %s", b.Status.State, reasonMerged)
			}
			if _, ok := f.mirrorHeads()["c/x"]; !ok {
				t.Error("deleted a branch that the merge controller didn't land")
			}
		})
	}
}

func TestInvalidGateWithFinalResults(t *testing.T) {
	f := newFixture(t)
	b := f.branches()
	p := *policy
	p.When = "checks.missing.passed"
	b.Spec.Merge = &p
	if _, err := f.merge(b); err != nil {
		t.Fatal(err)
	}
	if b.Status.State != reasonInvalidGate {
		t.Errorf("state = %q, want %s", b.Status.State, reasonInvalidGate)
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
