package main

import (
	"bytes"
	"encoding/json"
	"errors"
	"fmt"
	"io"
	"slices"
	"strconv"
	"strings"
	"testing"
	"time"

	gitk8s "github.com/imjasonh/playground/git-k8s"
	"github.com/imjasonh/playground/git-k8s/config"
	"github.com/imjasonh/playground/git-k8s/internal/git"
	"github.com/imjasonh/playground/git-k8s/internal/gittest"
	"github.com/imjasonh/playground/kube"
	"go.yaml.in/yaml/v3"
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
	r := &repositories{git: &git.Git{}}
	reconcile := func(world ...any) *kube.Condition {
		t.Helper()
		ctx, _ := kube.Fake(t.Context(), repo, append([]any{secret}, world...)...)
		if err := r.Reconcile(ctx, repo); err != nil {
			t.Fatal(err)
		}
		return kube.FindCondition(repo.Status.Conditions, "PoliciesInstalled")
	}
	all := "git-k8s-check-results, git-k8s-branches, git-k8s-check-pods, and git-k8s-approvals"
	if c := reconcile(); c == nil || c.Status != kube.False || c.Reason != "Missing" ||
		c.Message != all+" aren't fully installed, so any service account that can write GitBranch status can write check results, git-k8s service accounts can approve branches, checks can change GitBranch objects, checks that own Pods can write any Pod in the cluster, anyone who can patch a GitBranch can approve it, and the approved-by annotation can name someone who didn't approve; apply config/policy.yaml" {
		t.Errorf("without the policies, PoliciesInstalled = %+v", c)
	}
	r.installPolicies = true
	if c := reconcile(); c.Status != kube.False ||
		!strings.HasSuffix(c.Message, "; run kubectl -n git-k8s rollout restart deployment/git-k8s to install config/policy.yaml again") {
		t.Errorf("without the policies that the program installs, PoliciesInstalled = %+v", c)
	}

	var world []any
	var vaps []*admissionPolicy
	var bindings []*admissionPolicyBinding
	current, later := strconv.Itoa(policyVersion), strconv.Itoa(policyVersion+1)
	for _, p := range policies {
		vap := &admissionPolicy{Object: kube.Meta(p.name, nil)}
		vap.Annotations = map[string]string{policyVersionAnnotation: current}
		if p.name == "git-k8s-check-results" || p.name == "git-k8s-branches" {
			vap.Spec.ParamKind = &struct{}{}
		}
		b := &admissionPolicyBinding{Object: kube.Meta(p.name, nil)}
		b.Spec.PolicyName, b.Spec.ValidationActions = p.name, []string{"Warn"}
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
		c.Message != all+" don't have git-k8s.imjasonh.com/policy-version=2; run kubectl -n git-k8s rollout restart deployment/git-k8s to install config/policy.yaml again" {
		t.Errorf("with policies from an earlier release, which have no version, PoliciesInstalled = %+v", c)
	}
	r.installPolicies = false
	if c := reconcile(world...); c.Status != kube.False || c.Reason != "Outdated" ||
		c.Message != all+" don't have git-k8s.imjasonh.com/policy-version=2; apply config/policy.yaml from this release" {
		t.Errorf("with policies from an earlier release that the program doesn't install, PoliciesInstalled = %+v", c)
	}
	bindings[0].Spec.ValidationActions = []string{"Warn"}
	if c := reconcile(world...); c.Status != kube.False || c.Reason != "NotDenying" ||
		c.Message != "the binding git-k8s-check-results doesn't deny every request that its policy rejects, so any service account that can write GitBranch status can write check results; "+all+" don't have git-k8s.imjasonh.com/policy-version=2; run "+fmt.Sprintf(warns, "git-k8s-check-results")+", then apply config/policy.yaml from this release" {
		t.Errorf("with one binding that only warns and policies from an earlier release, PoliciesInstalled = %+v", c)
	}
	bindings[0].Spec.ValidationActions = []string{"Deny"}
	for _, vap := range vaps {
		vap.Annotations = map[string]string{policyVersionAnnotation: current}
	}
	vaps[0].Annotations[policyVersionAnnotation] = "1"
	if c := reconcile(world...); c.Status != kube.False || c.Reason != "Outdated" ||
		c.Message != "git-k8s-check-results doesn't have git-k8s.imjasonh.com/policy-version=2; apply config/policy.yaml from this release" {
		t.Errorf("with one policy at an earlier version, PoliciesInstalled = %+v", c)
	}
	vaps[0].Annotations[policyVersionAnnotation] = later
	for _, v := range []string{"v3", "99999999999999999999"} {
		vaps[1].Annotations[policyVersionAnnotation] = v
		if c := reconcile(world...); c.Status != kube.False || c.Reason != "Outdated" ||
			c.Message != "git-k8s-branches doesn't have git-k8s.imjasonh.com/policy-version=2; git-k8s-check-results has a git-k8s.imjasonh.com/policy-version later than 2; upgrade the core program, or, if you rolled it back, apply config/policy.yaml from this release" {
			t.Errorf("with one policy at a later version and the other at %q, which doesn't parse as an int, PoliciesInstalled = %+v", v, c)
		}
	}
	vaps[1].Annotations[policyVersionAnnotation] = current
	if c := reconcile(world...); c.Status != kube.False || c.Reason != "Newer" ||
		c.Message != "git-k8s-check-results has a git-k8s.imjasonh.com/policy-version later than 2; upgrade the core program, or, if you rolled it back, apply config/policy.yaml from this release" {
		t.Errorf("with one policy at a later version, PoliciesInstalled = %+v", c)
	}
	for _, vap := range vaps {
		vap.Annotations[policyVersionAnnotation] = later
	}
	if c := reconcile(world...); c.Status != kube.False || c.Reason != "Newer" ||
		c.Message != all+" have a git-k8s.imjasonh.com/policy-version later than 2; upgrade the core program, or, if you rolled it back, apply config/policy.yaml from this release" {
		t.Errorf("with policies from a later release, PoliciesInstalled = %+v", c)
	}
	// Applying the policies from a later release installs the missing one too,
	// so the fix for the later policies replaces the fix for the missing one.
	if c := reconcile(world[2:]...); c.Status != kube.False || c.Reason != "Missing" ||
		c.Message != "git-k8s-check-results isn't fully installed, so any service account that can write GitBranch status can write check results; git-k8s-branches, git-k8s-check-pods, and git-k8s-approvals have a git-k8s.imjasonh.com/policy-version later than 2; upgrade the core program, or, if you rolled it back, apply config/policy.yaml from this release" {
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
		c.Message != "the binding git-k8s-branches doesn't deny every request that its policy rejects, so git-k8s service accounts can approve branches, and checks can change GitBranch objects; the binding git-k8s-branches warns, so the core program stops the next time it starts; run "+fmt.Sprintf(warns, "git-k8s-branches") {
		t.Errorf("with only git-k8s-branches warning, PoliciesInstalled = %+v", c)
	}
	// Another binding that denies enforces git-k8s-branches, but the next start
	// still adds Deny next to Warn in the binding from config/policy.yaml.
	admin := &admissionPolicyBinding{Object: kube.Meta("admin-branches", nil)}
	admin.Spec.PolicyName, admin.Spec.ValidationActions = "git-k8s-branches", []string{"Deny"}
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
		c.Message != `the binding git-k8s-check-results doesn't deny every request that its policy rejects, so any service account that can write GitBranch status can write check results; the binding git-k8s-branches warns, so the core program stops the next time it starts; run kubectl patch validatingadmissionpolicybinding git-k8s-check-results --type=merge -p '{"spec":{"matchResources":null}}' and `+fmt.Sprintf(warns, "git-k8s-branches") {
		t.Errorf("with git-k8s-check-results limited, and git-k8s-branches warning while admin-branches denies, PoliciesInstalled = %+v", c)
	}
	bindings[0].Spec.MatchResources = nil
	// A binding limited with matchResources doesn't enforce the policy for every
	// request, so the message gives the consequences instead.
	narrow := &admissionPolicyBinding{Object: kube.Meta("narrow-branches", nil)}
	narrow.Spec.PolicyName, narrow.Spec.ValidationActions = "git-k8s-branches", []string{"Deny"}
	narrow.Spec.MatchResources = &matchResources{ObjectSelector: &labelSelector{MatchLabels: map[string]string{"tier": "web"}}}
	if c := reconcile(append([]any{narrow}, world...)...); c.Status != kube.False || c.Reason != "NotDenying" ||
		c.Message != "the binding git-k8s-branches doesn't deny every request that its policy rejects, so git-k8s service accounts can approve branches, and checks can change GitBranch objects; the binding git-k8s-branches warns, so the core program stops the next time it starts; run "+fmt.Sprintf(warns, "git-k8s-branches") {
		t.Errorf("with git-k8s-branches warning while narrow-branches is limited, PoliciesInstalled = %+v", c)
	}
	r.installPolicies = false
	if c := reconcile(append([]any{admin}, world...)...); c.Status != kube.True {
		t.Errorf("with git-k8s-branches warning while admin-branches denies, and policies that the program doesn't install, PoliciesInstalled = %+v", c)
	}
	r.installPolicies = true
	bindings[1].Spec.ValidationActions = []string{"Deny"}
	for _, b := range bindings {
		b.Spec.ParamRef = &paramRef{ParameterNotFoundAction: "Allow"}
	}
	// The API server ignores the paramRef of a binding whose policy has no
	// paramKind, so only the bindings of the policies that read parameters let
	// requests through while the parameters are missing.
	params := `kubectl patch validatingadmissionpolicybinding %s --type=merge -p '{"spec":{"paramRef":{"parameterNotFoundAction":"Deny"}}}'`
	if c := reconcile(world...); c.Status != kube.False || c.Reason != "NotDenying" ||
		c.Message != "the bindings git-k8s-check-results and git-k8s-branches don't deny every request that their policies reject, so any service account that can write GitBranch status can write check results, git-k8s service accounts can approve branches, and checks can change GitBranch objects; run "+fmt.Sprintf(params, "git-k8s-check-results")+" and "+fmt.Sprintf(params, "git-k8s-branches") {
		t.Errorf("with bindings that allow requests while their parameters are missing, PoliciesInstalled = %+v", c)
	}
	bindings[0].Spec.ParamRef.ParameterNotFoundAction = "Deny"
	bindings[1].Spec.ParamRef.ParameterNotFoundAction = "Deny"
	if c := reconcile(world...); c.Status != kube.True {
		t.Errorf("with bindings that deny requests while their parameters are missing, PoliciesInstalled = %+v", c)
	}

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
	}
	repo := &gitk8s.GitRepository{Object: kube.Meta("app", nil)}
	repo.Namespace = "default"
	ctx, _ := kube.Fake(t.Context(), repo, world...)
	if c := policiesCondition(ctx, true); c.Status != kube.True {
		t.Errorf("with the objects in config/policy.yaml, PoliciesInstalled = %+v", c)
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

// merge reconciles b at the front of its parent's merge queue. A b that
// isn't queued joined in an earlier reconcile.
func merge(t *testing.T, srv *gittest.Server, b *gitk8s.GitBranch) error {
	t.Helper()
	_, err := mergeEvents(t, srv, b)
	return err
}

// mergeIn reconciles b with parent as its parent's GitBranch, and returns
// the Merged condition's message. Reads see the objects in world over b and
// parent. b keeps its check results, which the merge controller leaves out
// of its status write.
func mergeIn(t *testing.T, srv *gittest.Server, parent, b *gitk8s.GitBranch, world ...any) string {
	t.Helper()
	results := b.Status.Checks
	repo, secret := srv.Repository("app", rules()...)
	ctx, _ := kube.Fake(t.Context(), b, append([]any{repo, secret, parent}, world...)...)
	m := &merger{
		ident: git.Identity{Name: "git-k8s", Email: "git-k8s@example.com"},
		cache: &gitk8s.Cache{Git: &git.Git{}, Dir: t.TempDir()},
	}
	if err := m.Reconcile(ctx, b); err != nil {
		t.Fatal(err)
	}
	b.Status.Checks = results
	if c := kube.FindCondition(b.Status.Conditions, "Merged"); c != nil {
		return c.Message
	}
	return ""
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
			if msg := mergeIn(t, srv, parentOf(b), b); b.Status.State != reasonWaitingForChecks || b.Status.Queued != nil {
				t.Errorf("state = %q, queued %+v, %q; want %s, out of the queue", b.Status.State, b.Status.Queued, msg, reasonWaitingForChecks)
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
