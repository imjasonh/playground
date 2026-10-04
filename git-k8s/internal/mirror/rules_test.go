package mirror

import (
	"strings"
	"testing"

	gitk8s "github.com/imjasonh/playground/git-k8s"
	"github.com/imjasonh/playground/git-k8s/internal/caller"
	"github.com/imjasonh/playground/kube"
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
var rulesRepo = &gitk8s.Repository{Spec: gitk8s.GitRepositorySpec{Branches: []gitk8s.BranchRule{
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
)

func TestRefuse(t *testing.T) {
	m := &Mirror{Prefixes: []Prefix{{Namespace: "git-k8s-deps", ServiceAccount: "git-k8s-deps", Prefix: "deps/"}}}
	update := func(ref string) command { return command{Old: oidA, New: oidB, Ref: ref} }
	create := func(ref string) command { return command{Old: zeroOID, New: oidB, Ref: ref} }
	remove := func(ref string) command { return command{Old: oidA, New: zeroOID, Ref: ref} }
	for _, tc := range []struct {
		name string
		who  caller.Caller
		c    command
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
	} {
		t.Run(tc.name, func(t *testing.T) {
			got := m.refuse(tc.who, rulesRepo, tc.c)
			if tc.want == "" && got != "" || !strings.Contains(got, tc.want) {
				t.Errorf("refuse = %q; want %q", got, tc.want)
			}
		})
	}
}

func TestMayFetchAndPush(t *testing.T) {
	m := &Mirror{Prefixes: []Prefix{{Namespace: "git-k8s-deps", ServiceAccount: "git-k8s-deps", Prefix: "deps/"}}}
	repo := &gitk8s.GitRepository{Object: kube.Meta("app", nil), Spec: rulesRepo.Spec}
	repo.Namespace = "team"
	branch := func(name, repository, state, pod string) *gitk8s.GitBranch {
		b := &gitk8s.GitBranch{Object: kube.Meta(name, map[string]string{gitk8s.RepositoryLabel: repository})}
		b.Namespace = "team"
		b.Status.Checks = map[string]gitk8s.CheckResult{"gotest": {State: state, Outputs: map[string]string{"pod": pod}}}
		return b
	}
	ctx, _ := kube.FakeRequest(t.Context(), repo,
		branch("app-feature", "app", gitk8s.Running, "gotest-1"),
		branch("app-done", "app", gitk8s.Passed, "gotest-2"),
		branch("other-feature", "other", gitk8s.Running, "gotest-3"))
	pod := func(ns, name string) caller.Caller { return caller.Caller{Namespace: ns, Name: "default", Pod: name} }
	r := &gitk8s.Repository{Object: repo.Object, Spec: repo.Spec}
	for _, tc := range []struct {
		name              string
		who               caller.Caller
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
		{name: "a check's running Pod", who: pod("team", "gotest-1"), mayFetch: true},
		{name: "a Pod whose result is final", who: pod("team", "gotest-2")},
		{name: "a Pod for another repository", who: pod("team", "gotest-3")},
		{name: "a Pod in another namespace", who: pod("elsewhere", "gotest-1")},
		{name: "a service account without a Pod", who: caller.Caller{Namespace: "team", Name: "default"}},
	} {
		t.Run(tc.name, func(t *testing.T) {
			if got := m.mayFetch(ctx, tc.who, r); got != tc.mayFetch {
				t.Errorf("mayFetch = %v; want %v", got, tc.mayFetch)
			}
			if got := m.mayPushAny(tc.who, r); got != tc.mayPush {
				t.Errorf("mayPushAny = %v; want %v", got, tc.mayPush)
			}
		})
	}
}
