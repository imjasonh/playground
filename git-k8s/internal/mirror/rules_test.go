package mirror

import (
	"strings"
	"testing"
	"time"

	gitk8s "github.com/imjasonh/playground/git-k8s"
	"github.com/imjasonh/playground/git-k8s/internal/caller"
	"github.com/imjasonh/playground/kube"
	"github.com/imjasonh/playground/kube/k8s"
)

func TestParsePrefix(t *testing.T) {
	for in, want := range map[string]Prefix{
		"git-k8s-deps/git-k8s-deps=deps/": {Namespace: "git-k8s-deps", ServiceAccount: "git-k8s-deps", Prefix: "deps/"},
		"bots/renovate.bot=bots/deps_1/":  {Namespace: "bots", ServiceAccount: "renovate.bot", Prefix: "bots/deps_1/"},
	} {
		got, err := ParsePrefix(in)
		if err != nil || got != want {
			t.Errorf("ParsePrefix(%q) = %+v, %v; want %+v", in, got, err, want)
		}
		if got.String() != in {
			t.Errorf("%+v.String() = %q; want %q", got, got.String(), in)
		}
	}
	for _, in := range []string{
		"",
		"deps/",
		"git-k8s-deps=deps/",
		"git-k8s-deps/git-k8s-deps",
		"Deps/git-k8s-deps=deps/",
		"git-k8s-deps/Deps=deps/",
		"git-k8s-deps/git-k8s-deps=",
		"git-k8s-deps/git-k8s-deps=deps",
		"git-k8s-deps/git-k8s-deps=/deps/",
		"git-k8s-deps/git-k8s-deps=deps//",
		"git-k8s-deps/git-k8s-deps=.deps/",
		"git-k8s-deps/git-k8s-deps=deps/.x/",
		"git-k8s-deps/git-k8s-deps=a..b/",
		"git-k8s-deps/git-k8s-deps=deps.lock/",
		"git-k8s-deps/git-k8s-deps=-deps/",
		"git-k8s-deps/git-k8s-deps=de ps/",
		"git-k8s-deps/git-k8s-deps=de*/",
	} {
		if got, err := ParsePrefix(in); err == nil {
			t.Errorf("ParsePrefix(%q) = %+v; want an error", in, got)
		}
	}
}

// rulesRepo has two parents, main and release, and branches that propose
// changes to each.
var rulesRepo = &gitk8s.Repository{Spec: gitk8s.TrackedRepositorySpec{Branches: []gitk8s.BranchRule{
	{Match: "main", Merge: &gitk8s.MergePolicy{Checks: []gitk8s.CheckPolicy{{Name: "gofmt", MayPush: true}, {Name: "risk"}}}},
	{Match: "release", Merge: &gitk8s.MergePolicy{Checks: []gitk8s.CheckPolicy{{Name: "risk", MayPush: true}}}},
	{Match: "hotfix/*", Parent: "release"},
	{Match: "standalone"},
	{Match: "**", Parent: "main"},
}}}

var (
	gofmt    = caller.Caller{Namespace: "check-gofmt", Name: "check-gofmt"}
	risk     = caller.Caller{Namespace: "check-risk", Name: "check-risk"}
	approval = caller.Caller{Namespace: "check-approval", Name: "check-approval"}
	deps     = caller.Caller{Namespace: "git-k8s-deps", Name: "git-k8s-deps"}
	builder  = caller.Caller{Namespace: "team", Name: "builder"}
	// impostor has a check's name, but not in the check's namespace.
	impostor = caller.Caller{Namespace: "team", Name: "check-gofmt"}
	// depsImpostor has the controller's name, but not in the controller's
	// namespace, and depsNeighbor is another service account in the
	// controller's namespace.
	depsImpostor = caller.Caller{Namespace: "team", Name: "git-k8s-deps"}
	depsNeighbor = caller.Caller{Namespace: "git-k8s-deps", Name: "default"}
	// bot runs the gofmt check through its entry in the git-k8s-checks
	// ConfigMap, botAsGofmt.
	bot        = caller.Caller{Namespace: "checks", Name: "bot"}
	botAsGofmt = map[string]string{"checks.bot": "gofmt"}
	core       = caller.Caller{Namespace: "git-k8s", Name: "git-k8s"}
	// registered is the git-k8s-checks ConfigMap's entries for gofmt, risk,
	// and approval, which a case that sets no entries uses.
	registered = map[string]string{"check-gofmt.check-gofmt": "gofmt", "check-risk.check-risk": "risk", "check-approval.check-approval": "approval"}
)

func TestRefuse(t *testing.T) {
	m := &Mirror{Prefixes: []Prefix{{Namespace: "git-k8s-deps", ServiceAccount: "git-k8s-deps", Prefix: "deps/"}}}
	update := func(ref string) command { return command{Old: oidA, New: oidB, Ref: ref} }
	create := func(ref string) command { return command{Old: zeroOID, New: oidB, Ref: ref} }
	remove := func(ref string) command { return command{Old: oidA, New: zeroOID, Ref: ref} }
	for _, tc := range []struct {
		name string
		who  caller.Caller
		// entries are the git-k8s-checks ConfigMap's.
		entries map[string]string
		c       command
		// want is part of the refusal, or "" if the update is allowed.
		want string
	}{
		{name: "a check updates a branch", who: gofmt, c: update("refs/heads/feature")},
		{name: "a check updates a branch of another parent", who: risk, c: update("refs/heads/hotfix/1")},
		{name: "a check updates a parent", who: gofmt, c: update("refs/heads/main"), want: "main is a parent branch, which only the merge controller updates"},
		{name: "a check updates another parent", who: risk, c: update("refs/heads/release"), want: "release is a parent branch"},
		{name: "a check updates a branch whose parent's policy doesn't list it", who: gofmt, c: update("refs/heads/hotfix/1"), want: "the merge policy of release doesn't let the gofmt check push"},
		{name: "a check updates a branch whose parent's policy doesn't let it push", who: risk, c: update("refs/heads/feature"), want: "the merge policy of main doesn't let the risk check push"},
		{name: "a check creates a branch", who: gofmt, c: create("refs/heads/feature"), want: "checks may not create branches"},
		{name: "a check deletes a branch", who: gofmt, c: remove("refs/heads/feature"), want: "checks may not delete branches"},
		{name: "a check updates a branch without a parent", who: gofmt, c: update("refs/heads/standalone"), want: "standalone has none"},
		{name: "a tag", who: gofmt, c: update("refs/tags/v1"), want: "the mirror takes only branches"},
		{name: "the mirror's refs", who: deps, c: update("refs/git-k8s/downstream/heads/deps/x"), want: "the mirror takes only branches"},
		{name: "no branch name", who: gofmt, c: update("refs/heads/"), want: "the mirror takes only branches"},
		{name: "a controller creates a branch under its prefix", who: deps, c: create("refs/heads/deps/bump")},
		{name: "a controller updates a branch under its prefix", who: deps, c: update("refs/heads/deps/go/x")},
		{name: "a controller deletes a branch under its prefix", who: deps, c: remove("refs/heads/deps/bump")},
		{name: "a controller updates a branch outside its prefix", who: deps, c: update("refs/heads/feature"), want: "git-k8s-deps/git-k8s-deps may push only branches under deps/"},
		{name: "a controller updates a branch that starts like its prefix", who: deps, c: update("refs/heads/depsx"), want: "may push only branches under deps/"},
		{name: "a controller updates a parent", who: deps, c: update("refs/heads/main"), want: "main is a parent branch"},
		{name: "another service account", who: builder, c: update("refs/heads/feature"), want: "team/builder may not push"},
		{name: "a check's name in another namespace", who: impostor, c: update("refs/heads/feature"), want: "team/check-gofmt may not push"},
		{name: "a controller's name in another namespace", who: depsImpostor, c: create("refs/heads/deps/bump"), want: "team/git-k8s-deps may not push"},
		{name: "another service account in a controller's namespace", who: depsNeighbor, c: create("refs/heads/deps/bump"), want: "git-k8s-deps/default may not push"},
		{name: "a check through its ConfigMap entry", who: bot, entries: botAsGofmt, c: update("refs/heads/feature")},
		{name: "a check through its ConfigMap entry updates a parent", who: bot, entries: botAsGofmt, c: update("refs/heads/main"), want: "main is a parent branch"},
		{name: "a service account without an entry", who: bot, c: update("refs/heads/feature"), want: "checks/bot may not push"},
		{name: "a check whose entry names another check", who: gofmt, entries: map[string]string{"check-gofmt.check-gofmt": "risk"}, c: update("refs/heads/feature"), want: "the merge policy of main doesn't let the risk check push"},
		{name: "a check whose entry is empty", who: gofmt, entries: map[string]string{"check-gofmt.check-gofmt": ""}, c: update("refs/heads/feature"), want: "check-gofmt/check-gofmt may not push"},
		{name: "the core program, whose entry names a check", who: core, entries: map[string]string{"git-k8s.git-k8s": "gofmt"}, c: update("refs/heads/feature"), want: "git-k8s/git-k8s may not push"},
		{name: "generate's account for a check that runs elsewhere", who: risk, entries: map[string]string{"checks.risk-bot": "risk"}, c: update("refs/heads/hotfix/1"), want: "check-risk/check-risk may not push"},
	} {
		t.Run(tc.name, func(t *testing.T) {
			entries := tc.entries
			if entries == nil {
				entries = registered
			}
			check, _ := tc.who.Check(entries)
			got := m.refuse(tc.who, check, rulesRepo, tc.c)
			if tc.want == "" && got != "" || !strings.Contains(got, tc.want) {
				t.Errorf("refuse = %q; want %q", got, tc.want)
			}
		})
	}
}

func TestMayFetchAndPush(t *testing.T) {
	m := &Mirror{Prefixes: []Prefix{{Namespace: "git-k8s-deps", ServiceAccount: "git-k8s-deps", Prefix: "deps/"}}}
	repo := &gitk8s.TrackedRepository{Object: kube.Meta("app", nil), Spec: rulesRepo.Spec}
	repo.Namespace = "team"
	// branch returns a branch in team whose merge policy lists check, and
	// whose result for check names pod.
	branch := func(name, repository, check, state, pod string) *gitk8s.TrackedBranch {
		b := &gitk8s.TrackedBranch{Object: kube.Meta(name, map[string]string{gitk8s.RepositoryLabel: repository})}
		b.Namespace = "team"
		b.Spec.Merge = &gitk8s.MergePolicy{Checks: []gitk8s.CheckPolicy{{Name: check}}}
		b.Status.Checks = map[string]gitk8s.CheckResult{check: {State: state, Pod: pod}}
		return b
	}
	unlisted := branch("app-review-unlisted", "app", "review", gitk8s.Running, "review-unlisted")
	unlisted.Spec.Merge.Checks[0].Name = gitk8s.GoTestCheck
	// testPod returns a Pod in team with the UID uid-NAME, and with kube's
	// controller label set to controller, unless controller is "".
	testPod := func(name, controller, phase string) *k8s.Pod {
		p := &k8s.Pod{Object: kube.Meta(name, nil)}
		p.Namespace, p.UID = "team", "uid-"+name
		if controller != "" {
			p.Labels = map[string]string{gitk8s.ControllerLabel: controller}
		}
		p.Status.Phase = phase
		return p
	}
	deleting := testPod("gotest-deleting", gitk8s.GoTestController, "Pending")
	deleting.DeletionTimestamp = &time.Time{}
	ctx, _ := kube.FakeRequest(t.Context(), repo,
		branch("app-feature", "app", gitk8s.GoTestCheck, gitk8s.Running, "gotest-1"),
		testPod("gotest-1", gitk8s.GoTestController, "Pending"),
		branch("app-done", "app", gitk8s.GoTestCheck, gitk8s.Passed, "gotest-2"),
		testPod("gotest-2", gitk8s.GoTestController, "Pending"),
		branch("other-feature", "other", gitk8s.GoTestCheck, gitk8s.Running, "gotest-3"),
		testPod("gotest-3", gitk8s.GoTestController, "Pending"),
		branch("app-squatted", "app", gitk8s.GoTestCheck, gitk8s.Running, "gotest-squatted"),
		testPod("gotest-squatted", "check-other", "Pending"),
		branch("app-unlabeled", "app", gitk8s.GoTestCheck, gitk8s.Running, "gotest-unlabeled"),
		testPod("gotest-unlabeled", "", "Pending"),
		branch("app-deleting", "app", gitk8s.GoTestCheck, gitk8s.Running, "gotest-deleting"),
		deleting,
		branch("app-running", "app", gitk8s.GoTestCheck, gitk8s.Running, "gotest-running"),
		testPod("gotest-running", gitk8s.GoTestController, "Running"),
		branch("app-succeeded", "app", gitk8s.GoTestCheck, gitk8s.Running, "gotest-succeeded"),
		testPod("gotest-succeeded", gitk8s.GoTestController, "Succeeded"),
		branch("app-failed", "app", gitk8s.GoTestCheck, gitk8s.Running, "gotest-failed"),
		testPod("gotest-failed", gitk8s.GoTestController, "Failed"),
		branch("app-unknown", "app", gitk8s.GoTestCheck, gitk8s.Running, "gotest-unknown"),
		testPod("gotest-unknown", gitk8s.GoTestController, "Unknown"),
		branch("app-starting", "app", gitk8s.GoTestCheck, gitk8s.Running, "gotest-starting"),
		branch("app-other-check", "app", "other", gitk8s.Running, "gotest-other-check"),
		testPod("gotest-other-check", gitk8s.GoTestController, "Pending"),
		branch("app-review", "app", "review", gitk8s.Running, "review-1"),
		testPod("review-1", "check-review", "Pending"),
		branch("app-review-running", "app", "review", gitk8s.Running, "review-running"),
		testPod("review-running", "check-review", "Running"),
		branch("app-review-squatted", "app", "review", gitk8s.Running, "review-squatted"),
		testPod("review-squatted", gitk8s.GoTestController, "Pending"),
		unlisted,
		testPod("review-unlisted", "check-review", "Pending"))
	pod := func(ns, name string) caller.Caller {
		return caller.Caller{Namespace: ns, Name: "default", Pod: name, PodUID: "uid-" + name}
	}
	r := &gitk8s.Repository{Object: repo.Object, Spec: repo.Spec}
	for _, tc := range []struct {
		name string
		who  caller.Caller
		// entries are the git-k8s-checks ConfigMap's.
		entries           map[string]string
		mayFetch, mayPush bool
	}{
		{name: "a check that may push", who: gofmt, mayFetch: true, mayPush: true},
		{name: "a check that may push to some branches", who: risk, mayFetch: true, mayPush: true},
		{name: "a check that the repository doesn't list", who: approval},
		{name: "a controller with a prefix", who: deps, mayFetch: true, mayPush: true},
		{name: "another service account", who: builder},
		{name: "a check's name in another namespace", who: impostor},
		{name: "a controller's name in another namespace", who: depsImpostor},
		{name: "another service account in a controller's namespace", who: depsNeighbor},
		{name: "the gotest check's Pending Pod", who: pod("team", "gotest-1"), mayFetch: true},
		{name: "a Pod whose result is final", who: pod("team", "gotest-2")},
		{name: "a Pod for another repository", who: pod("team", "gotest-3")},
		{name: "a Pod in another namespace", who: pod("elsewhere", "gotest-1")},
		{name: "a service account without a Pod", who: caller.Caller{Namespace: "team", Name: "default"}},
		{name: "a token with a Pod's name and no UID", who: caller.Caller{Namespace: "team", Name: "default", Pod: "gotest-1"}},
		{name: "a token bound to an earlier Pod with the same name", who: caller.Caller{Namespace: "team", Name: "default", Pod: "gotest-1", PodUID: "uid-earlier"}},
		{name: "a Pod with another check's label", who: pod("team", "gotest-squatted")},
		{name: "a Pod without the controller label", who: pod("team", "gotest-unlabeled")},
		{name: "a Pod that's being deleted", who: pod("team", "gotest-deleting")},
		{name: "a Pod whose tests have started", who: pod("team", "gotest-running")},
		{name: "a Pod that has succeeded", who: pod("team", "gotest-succeeded")},
		{name: "a Pod that has failed", who: pod("team", "gotest-failed")},
		{name: "a Pod in an unknown phase", who: pod("team", "gotest-unknown")},
		{name: "a Pod that doesn't exist yet", who: pod("team", "gotest-starting")},
		{name: "a Pod that another check's result names", who: pod("team", "gotest-other-check")},
		{name: "the review check's Pending Pod", who: pod("team", "review-1"), mayFetch: true},
		{name: "a review Pod whose agent has finished", who: pod("team", "review-running")},
		{name: "a Pod with the gotest label that the review result names", who: pod("team", "review-squatted")},
		{name: "a Pod that a result names on a branch whose policy doesn't list the check", who: pod("team", "review-unlisted")},
		{name: "a check through its ConfigMap entry", who: bot, entries: botAsGofmt, mayFetch: true, mayPush: true},
		{name: "a service account without an entry", who: bot},
		{name: "a check whose entry names one that the repository doesn't list", who: gofmt, entries: map[string]string{"check-gofmt.check-gofmt": "approval"}},
		{name: "a check whose entry names a check that the repository lists", who: approval, entries: map[string]string{"check-approval.check-approval": "risk"}, mayFetch: true, mayPush: true},
		{name: "a check whose entry is empty", who: gofmt, entries: map[string]string{"check-gofmt.check-gofmt": ""}},
		{name: "the core program, whose entry names a check", who: core, entries: map[string]string{"git-k8s.git-k8s": "gofmt"}},
		{name: "generate's account for a check that runs elsewhere", who: risk, entries: map[string]string{"checks.risk-bot": "risk"}},
	} {
		t.Run(tc.name, func(t *testing.T) {
			entries := tc.entries
			if entries == nil {
				entries = registered
			}
			check, _ := tc.who.Check(entries)
			got, err := m.mayFetch(ctx, tc.who, check, r)
			if err != nil || got != tc.mayFetch {
				t.Errorf("mayFetch = %v, %v; want %v", got, err, tc.mayFetch)
			}
			if got := m.mayPushAny(tc.who, check, r); got != tc.mayPush {
				t.Errorf("mayPushAny = %v; want %v", got, tc.mayPush)
			}
		})
	}
}
