package main

import (
	"fmt"
	"maps"
	"net/http"
	"net/url"
	"reflect"
	"slices"
	"strconv"
	"strings"
	"sync"
	"sync/atomic"
	"testing"
	"time"
	"unicode/utf8"

	gitk8s "github.com/imjasonh/playground/git-k8s"
	"github.com/imjasonh/playground/git-k8s/internal/git"
	"github.com/imjasonh/playground/git-k8s/internal/gitserver"
	"github.com/imjasonh/playground/git-k8s/internal/gittest"
	"github.com/imjasonh/playground/kube"
)

var sts = gitk8s.OctoSTS{GitIdentity: "git", CheckRunsIdentity: "checks"}

func TestReportsCheckRunsToken(t *testing.T) {
	gh, _, _ := newGitHub(t)
	repo := gh.Repository("app", sts, rules()...)
	reconcile := func() *kube.Condition {
		t.Helper()
		ctx, _ := kube.Fake(t.Context(), repo)
		if err := (&repositories{git: &git.Git{}}).Reconcile(ctx, repo); err != nil {
			t.Fatal(err)
		}
		if c := kube.FindCondition(repo.Status.Conditions, "Ready"); c == nil || c.Status != kube.True {
			t.Errorf("Ready = %+v", c)
		}
		return kube.FindCondition(repo.Status.Conditions, "CheckRunsTokenIssued")
	}
	if c := reconcile(); c == nil || c.Status != kube.True || c.Reason != "Issued" || c.Message != "Octo STS issued a token for identity checks" {
		t.Errorf("CheckRunsTokenIssued = %+v", c)
	}
	var identities []string
	for _, ex := range gh.Fake.Exchanges() {
		identities = append(identities, ex.Identity)
	}
	if slices.Sort(identities); !slices.Equal(identities, []string{"checks", "git"}) {
		t.Errorf("exchanged tokens for %q, want checks and git", identities)
	}

	t.Log("An identity without a trust policy makes the condition False, and the repository is still ready.")
	repo.Spec.OctoSTS.CheckRunsIdentity = "missing"
	if c := reconcile(); c == nil || c.Status != kube.False || c.Reason != "ExchangeFailed" || !strings.Contains(c.Message, `unable to find trust policy for "missing"`) {
		t.Errorf("CheckRunsTokenIssued = %+v", c)
	}

	t.Log("Without a check-runs identity, the condition goes away.")
	repo.Spec.OctoSTS.CheckRunsIdentity = ""
	if c := reconcile(); c != nil {
		t.Errorf("CheckRunsTokenIssued = %+v, want none", c)
	}
}

// resultsOf returns the GitBranch of a branch of the GitRepository repo in
// namespace default, as the check-runs controller sees it, with checks.
func resultsOf(repo, branch string, checks map[string]gitk8s.CheckResult) *branchResults {
	b := &branchResults{Object: kube.Meta(gitk8s.BranchObjectName(repo, branch), map[string]string{gitk8s.RepositoryLabel: repo})}
	b.Namespace = "default"
	b.Spec.Repository = repo
	b.Status.Checks = checks
	return b
}

// publisher runs a check-runs controller on the branches of acme/app and
// returns the REST API requests that each reconcile sent.
type publisher struct {
	t    *testing.T
	gh   *gittest.GitHub
	repo *gitk8s.GitRepository
	c    *checkRuns
	// branches holds the results of each branch in the cluster.
	branches map[string]map[string]gitk8s.CheckResult
	// requeue is the last reconcile's requeue.
	requeue time.Duration
}

// publish sets the results of c/x and reconciles it.
func (p *publisher) publish(checks map[string]gitk8s.CheckResult) ([]string, error) {
	p.t.Helper()
	return p.publishOn("c/x", checks)
}

// publishOn sets the results of branch and reconciles it.
func (p *publisher) publishOn(branch string, checks map[string]gitk8s.CheckResult) ([]string, error) {
	p.t.Helper()
	p.set(branch, checks)
	return p.reconcile(branch)
}

// set sets the results of branch in the cluster, without a reconcile.
func (p *publisher) set(branch string, checks map[string]gitk8s.CheckResult) {
	if p.branches == nil {
		p.branches = map[string]map[string]gitk8s.CheckResult{}
	}
	p.branches[branch] = checks
}

// remove deletes branch from the cluster.
func (p *publisher) remove(branch string) {
	delete(p.branches, branch)
}

// reconcile reconciles branch, which is in the cluster.
func (p *publisher) reconcile(branch string) ([]string, error) {
	p.t.Helper()
	before := len(p.gh.Fake.Requests())
	var b *branchResults
	world := []any{p.repo}
	for name, checks := range p.branches {
		if o := resultsOf(p.repo.Name, name, maps.Clone(checks)); name == branch {
			b = o
		} else {
			world = append(world, o)
		}
	}
	want := maps.Clone(b.Status.Checks)
	ctx, rec := kube.Fake(p.t.Context(), b, world...)
	err := p.c.Reconcile(ctx, b)
	if !reflect.DeepEqual(b.Status.Checks, want) {
		p.t.Errorf("the check-runs controller changed the GitBranch's status to %+v", b.Status)
	}
	p.requeue = rec.RequeueAfter()
	return p.gh.Fake.Requests()[before:], err
}

// remember makes c remember that branch's result for check is for commit,
// and that check run id shows it.
func remember(c *checkRuns, branch, check, commit string, id int64, shows runState) {
	rr := c.repository("default/app")
	rr.mu.Lock()
	defer rr.mu.Unlock()
	b := gitk8s.BranchObjectName("app", branch)
	rr.seq++
	rr.results[branchCheck{b, check}] = branchResult{commit: commit, shows: shows, seq: rr.seq}
	rr.runs[commitCheck{commit, check}] = shownRun{id: id, shows: shows, by: b}
}

// runs lists acme/app's check runs as "NAME@COMMIT STATUS CONCLUSION:
// SUMMARY", without the code block around a result's message.
func runs(gh *gittest.GitHub) []string {
	var out []string
	for _, r := range gh.Fake.CheckRuns("acme/app") {
		summary := strings.TrimSuffix(strings.TrimPrefix(r.Output.Summary, "```\n"), "\n```")
		out = append(out, fmt.Sprintf("%s@%s %s %s: %s", r.Name, gitk8s.Short(r.HeadSHA), r.Status, r.Conclusion, summary))
	}
	return out
}

func TestPublishesCheckRuns(t *testing.T) {
	gh, w, main := newGitHub(t)
	w.Branch("c/x", main)
	w.Write("x.go", "package x\nvar  x = 1\n")
	head := w.Commit("add x")
	w.Write("x.go", "package x\n\nvar x = 1\n")
	fix := w.Commit("gofmt")
	w.Write("y.go", "package x\n")
	next := w.Commit("add y")
	w.Push("c/x")
	p := &publisher{t: t, gh: gh, repo: gh.Repository("app", sts, rules()...), c: &checkRuns{}}
	api := "/api/v3/repos/acme/app/"
	h, f, n := gitk8s.Short(head), gitk8s.Short(fix), gitk8s.Short(next)
	step := func(checks map[string]gitk8s.CheckResult, wantRequests, wantRuns []string) {
		t.Helper()
		got, err := p.publish(checks)
		if err != nil {
			t.Fatal(err)
		}
		if !slices.Equal(got, wantRequests) {
			t.Errorf("requests = %q, want %q", got, wantRequests)
		}
		if got := runs(gh); !slices.Equal(got, wantRuns) {
			t.Errorf("check runs:\n%s\nwant:\n%s", strings.Join(got, "\n"), strings.Join(wantRuns, "\n"))
		}
	}

	checks := map[string]gitk8s.CheckResult{
		"base":  {Commit: head, ParentCommit: main, State: gitk8s.Passed, Message: "builds on main"},
		"gofmt": {Commit: head, State: gitk8s.Running},
	}
	step(checks, []string{
		"GET " + api + "commits/" + head + "/check-runs", "POST " + api + "check-runs",
		"GET " + api + "commits/" + head + "/check-runs", "POST " + api + "check-runs",
	}, []string{
		"git-k8s/base@" + h + " completed success: builds on main",
		"git-k8s/gofmt@" + h + " in_progress : Running",
	})
	if r := gh.Fake.CheckRuns("acme/app")[0]; r.ExternalID != "default/app" || r.Output.Title != "Passed" || r.Output.Summary != "```\nbuilds on main\n```" {
		t.Errorf("check run = %+v, want external ID default/app, title Passed, and the message in a code block", r)
	}

	t.Log("Results that stay the same cost no requests.")
	step(checks, nil, runs(gh))

	t.Log("A result that changes updates its check run.")
	checks["gofmt"] = gitk8s.CheckResult{Commit: head, State: gitk8s.Failed, Message: "x.go isn't formatted"}
	step(checks, []string{"PATCH " + api + "check-runs/2"}, []string{
		"git-k8s/base@" + h + " completed success: builds on main",
		"git-k8s/gofmt@" + h + " completed failure: x.go isn't formatted",
	})

	t.Log("A check that starts again after it finished gets a new check run.")
	checks["gofmt"] = gitk8s.CheckResult{Commit: head, State: gitk8s.Running}
	step(checks, []string{"POST " + api + "check-runs"}, []string{
		"git-k8s/base@" + h + " completed success: builds on main",
		"git-k8s/gofmt@" + h + " completed failure: x.go isn't formatted",
		"git-k8s/gofmt@" + h + " in_progress : Running",
	})

	t.Log("A fix is neutral, because the check's run on the fix decides.")
	checks["gofmt"] = gitk8s.CheckResult{Commit: head, State: gitk8s.Fixed, Message: "x.go isn't formatted; pushed " + f, Outputs: map[string]string{"fix": fix}}
	step(checks, []string{"PATCH " + api + "check-runs/3"}, []string{
		"git-k8s/base@" + h + " completed success: builds on main",
		"git-k8s/gofmt@" + h + " completed failure: x.go isn't formatted",
		"git-k8s/gofmt@" + h + " completed neutral: x.go isn't formatted; pushed " + f,
	})
	if r := gh.Fake.CheckRuns("acme/app")[2]; r.Output.Text != "```\nfix: "+fix+"\n```" {
		t.Errorf("text = %q, want the fix output", r.Output.Text)
	}

	t.Log("When the branch moves before a check finishes, the old commit's check run is cancelled.")
	checks = map[string]gitk8s.CheckResult{"gofmt": {Commit: fix, State: gitk8s.Running}}
	step(checks, []string{"GET " + api + "commits/" + fix + "/check-runs", "POST " + api + "check-runs"}, []string{
		"git-k8s/base@" + h + " completed success: builds on main",
		"git-k8s/gofmt@" + h + " completed failure: x.go isn't formatted",
		"git-k8s/gofmt@" + h + " completed neutral: x.go isn't formatted; pushed " + f,
		"git-k8s/gofmt@" + f + " in_progress : Running",
	})
	checks = map[string]gitk8s.CheckResult{"gofmt": {Commit: next, State: gitk8s.Error, Message: "fetching c/x: exit status 128"}}
	step(checks, []string{"PATCH " + api + "check-runs/4", "GET " + api + "commits/" + next + "/check-runs", "POST " + api + "check-runs"}, []string{
		"git-k8s/base@" + h + " completed success: builds on main",
		"git-k8s/gofmt@" + h + " completed failure: x.go isn't formatted",
		"git-k8s/gofmt@" + h + " completed neutral: x.go isn't formatted; pushed " + f,
		"git-k8s/gofmt@" + f + " completed cancelled: The branch moved to " + n + " before the check finished.",
		"git-k8s/gofmt@" + n + " completed failure: fetching c/x: exit status 128",
	})

	t.Log("The controller forgets the check runs on a commit that the branch left, and when the branch comes back, the controller finds them on GitHub.")
	checks = map[string]gitk8s.CheckResult{"gofmt": {Commit: head, State: gitk8s.Fixed, Message: "x.go isn't formatted; pushed " + f, Outputs: map[string]string{"fix": fix}}}
	step(checks, []string{"GET " + api + "commits/" + head + "/check-runs"}, runs(gh))
}

func TestCheckRunsSurviveRestarts(t *testing.T) {
	gh, w, main := newGitHub(t)
	w.Branch("c/x", main)
	head := w.Commit("add x")
	w.Push("c/x")
	repo := gh.Repository("app", sts, rules()...)
	checks := map[string]gitk8s.CheckResult{"base": {Commit: head, ParentCommit: main, State: gitk8s.Passed}}
	if _, err := (&publisher{t: t, gh: gh, repo: repo, c: &checkRuns{}}).publish(checks); err != nil {
		t.Fatal(err)
	}
	api := "/api/v3/repos/acme/app/"
	get := "GET " + api + "commits/" + head + "/check-runs"

	t.Log("After a restart, the controller finds the check run instead of creating another.")
	got, err := (&publisher{t: t, gh: gh, repo: repo, c: &checkRuns{}}).publish(checks)
	if err != nil || !slices.Equal(got, []string{get}) {
		t.Errorf("requests = %q, err = %v; want only %s", got, err, get)
	}

	t.Log("When something else changed the check run on GitHub, the controller puts the result back.")
	if status := asAdmin(t, gh, http.MethodPatch, api+"check-runs/1", `{"conclusion": "failure", "output": {"title": "Failed", "summary": "changed on GitHub"}}`); status != http.StatusOK {
		t.Fatalf("changing the check run: %d", status)
	}
	got, err = (&publisher{t: t, gh: gh, repo: repo, c: &checkRuns{}}).publish(checks)
	if want := []string{get, "PATCH " + api + "check-runs/1"}; err != nil || !slices.Equal(got, want) {
		t.Errorf("requests = %q, err = %v; want %q", got, err, want)
	}
	if got, want := runs(gh), []string{"git-k8s/base@" + gitk8s.Short(head) + " completed success: Passed"}; !slices.Equal(got, want) {
		t.Errorf("check runs = %q, want %q", got, want)
	}

	t.Log("After a restart, a check that starts again gets a new check run, which the next restart finds.")
	running := map[string]gitk8s.CheckResult{"base": {Commit: head, ParentCommit: main, State: gitk8s.Running}}
	got, err = (&publisher{t: t, gh: gh, repo: repo, c: &checkRuns{}}).publish(running)
	if want := []string{get, "POST " + api + "check-runs"}; err != nil || !slices.Equal(got, want) {
		t.Errorf("requests = %q, err = %v; want %q", got, err, want)
	}
	got, err = (&publisher{t: t, gh: gh, repo: repo, c: &checkRuns{}}).publish(checks)
	if want := []string{get, "PATCH " + api + "check-runs/2"}; err != nil || !slices.Equal(got, want) {
		t.Errorf("requests = %q, err = %v; want %q", got, err, want)
	}

	t.Log("When something else completes a check run that the controller saw in progress, and GitHub refuses to start it again, the controller creates another.")
	p := &publisher{t: t, gh: gh, repo: repo, c: &checkRuns{}}
	got, err = p.publish(running)
	if want := []string{get, "POST " + api + "check-runs"}; err != nil || !slices.Equal(got, want) {
		t.Fatalf("requests = %q, err = %v; want %q", got, err, want)
	}
	if status := asAdmin(t, gh, http.MethodPatch, api+"check-runs/3", `{"conclusion": "cancelled", "output": {"title": "Cancelled", "summary": "cancelled on GitHub"}}`); status != http.StatusOK {
		t.Fatalf("completing the check run: %d", status)
	}
	got, err = p.publish(map[string]gitk8s.CheckResult{"base": {Commit: head, ParentCommit: main, State: gitk8s.Running, Message: "trying again"}})
	if want := []string{"PATCH " + api + "check-runs/3", "POST " + api + "check-runs"}; err != nil || !slices.Equal(got, want) {
		t.Errorf("requests = %q, err = %v; want %q", got, err, want)
	}

	t.Log("When GitHub starts it again instead, the controller keeps it.")
	gh.Fake.AcceptReopening()
	if status := asAdmin(t, gh, http.MethodPatch, api+"check-runs/4", `{"conclusion": "cancelled", "output": {"title": "Cancelled", "summary": "cancelled on GitHub"}}`); status != http.StatusOK {
		t.Fatalf("completing the check run: %d", status)
	}
	got, err = p.publish(map[string]gitk8s.CheckResult{"base": {Commit: head, ParentCommit: main, State: gitk8s.Running, Message: "trying once more"}})
	if want := []string{"PATCH " + api + "check-runs/4"}; err != nil || !slices.Equal(got, want) {
		t.Errorf("requests = %q, err = %v; want %q", got, err, want)
	}
	if got, want := runs(gh)[3], "git-k8s/base@"+gitk8s.Short(head)+" in_progress : trying once more"; got != want {
		t.Errorf("check run 4 = %s, want %s", got, want)
	}
}

// asAdmin sends a REST API request to the fake GitHub with its
// administrator's credentials, which act for another app than the tokens
// from Octo STS, and returns the response's status.
func asAdmin(t *testing.T, gh *gittest.GitHub, method, path, body string) int {
	t.Helper()
	req, err := http.NewRequest(method, strings.TrimSuffix(gh.URL, "/acme")+path, strings.NewReader(body))
	if err != nil {
		t.Fatal(err)
	}
	req.SetBasicAuth(gh.Username, gh.Password)
	resp, err := http.DefaultClient.Do(req)
	if err != nil {
		t.Fatal(err)
	}
	resp.Body.Close()
	return resp.StatusCode
}

func TestCheckRunsFromOtherApps(t *testing.T) {
	gh, w, main := newGitHub(t)
	w.Branch("c/x", main)
	head := w.Commit("add x")
	next := w.Commit("add y")
	w.Push("c/x")
	p := &publisher{t: t, gh: gh, repo: gh.Repository("app", sts, rules()...), c: &checkRuns{}}
	api := "/api/v3/repos/acme/app/"
	h, n := gitk8s.Short(head), gitk8s.Short(next)
	// spoof creates a check run on commit that looks like the
	// controller's, as another app, with the JSON fields in state.
	spoof := func(commit, state string) {
		t.Helper()
		body := `{"name": "git-k8s/gofmt", "head_sha": "` + commit + `", "external_id": "default/app", ` + state + `}`
		if status := asAdmin(t, gh, http.MethodPost, api+"check-runs", body); status != http.StatusCreated {
			t.Fatalf("creating another app's check run: %d", status)
		}
	}

	t.Log("Before the controller knows its app, it creates a check run when GitHub refuses to update another app's.")
	spoof(head, `"conclusion": "success", "output": {"title": "Passed", "summary": "spoofed"}`)
	got, err := p.publish(map[string]gitk8s.CheckResult{"gofmt": {Commit: head, State: gitk8s.Failed, Message: "x.go isn't formatted"}})
	if want := []string{"GET " + api + "commits/" + head + "/check-runs", "PATCH " + api + "check-runs/1", "POST " + api + "check-runs"}; err != nil || !slices.Equal(got, want) {
		t.Errorf("requests = %q, err = %v; want %q", got, err, want)
	}

	t.Log("Then it looks only at its app's check runs.")
	spoof(next, `"status": "in_progress", "output": {"title": "Running", "summary": "spoofed"}`)
	got, err = p.publish(map[string]gitk8s.CheckResult{"gofmt": {Commit: next, State: gitk8s.Failed, Message: "y.go isn't formatted"}})
	if want := []string{"GET " + api + "commits/" + next + "/check-runs", "POST " + api + "check-runs"}; err != nil || !slices.Equal(got, want) {
		t.Errorf("requests = %q, err = %v; want %q", got, err, want)
	}
	if got, want := runs(gh), []string{
		"git-k8s/gofmt@" + h + " completed success: spoofed",
		"git-k8s/gofmt@" + h + " completed failure: x.go isn't formatted",
		"git-k8s/gofmt@" + n + " in_progress : spoofed",
		"git-k8s/gofmt@" + n + " completed failure: y.go isn't formatted",
	}; !slices.Equal(got, want) {
		t.Errorf("check runs:\n%s\nwant:\n%s", strings.Join(got, "\n"), strings.Join(want, "\n"))
	}

	t.Log("When GitHub can't find the check run that the controller remembers, the controller creates another.")
	remember(p.c, "c/x", "gofmt", next, 99, runFor(gitk8s.CheckResult{State: gitk8s.Running}))
	got, err = p.publish(map[string]gitk8s.CheckResult{"gofmt": {Commit: next, State: gitk8s.Passed}})
	if want := []string{"PATCH " + api + "check-runs/99", "POST " + api + "check-runs"}; err != nil || !slices.Equal(got, want) {
		t.Errorf("requests = %q, err = %v; want %q", got, err, want)
	}
}

// TestCheckRunsOfSeveralApps runs against an Octo STS that issues the
// tokens of another repository, or of another identity, for another GitHub
// App, as Octo STS can when it has several.
func TestCheckRunsOfSeveralApps(t *testing.T) {
	for _, other := range []struct{ name, repo, identity string }{
		{"AnotherRepository", "lib", "checks"},
		{"AnotherIdentity", "app", "other"},
	} {
		t.Run(other.name, func(t *testing.T) {
			gh, w, main := newGitHub(t)
			w.Write(".github/chainguard/other.sts.yaml", gittest.TrustPolicy(map[string]string{"checks": "write"}))
			main = w.Commit("add the identity other")
			w.Push("main")
			w.Branch("c/x", main)
			head := w.Commit("add x")
			next := w.Commit("add y")
			w.Push("c/x")
			// lib is another GitRepository, for acme/lib or acme/app, whose
			// tokens act for another app.
			lib := gh.Repository("lib", gitk8s.OctoSTS{CheckRunsIdentity: other.identity}, rules()...)
			lib.Spec.URL = gh.Remote(other.repo).URL
			libHead := head
			if other.repo == "lib" {
				l := gh.NewWork(t, "lib")
				l.Write(".github/chainguard/checks.sts.yaml", gittest.TrustPolicy(map[string]string{"checks": "write"}))
				l.Commit("main")
				l.Push("main")
				l.Write("lib.go", "package lib\n")
				libHead = l.Commit("add lib")
				l.Push("c/x")
			}
			gh.Fake.RouteApp("acme/"+other.repo, other.identity, gitserver.SecondOctoSTSApp)
			app := gh.Repository("app", sts, rules()...)
			api := "/api/v3/repos/acme/app/"
			gotest := func(commit, state string) map[string]gitk8s.CheckResult {
				return map[string]gitk8s.CheckResult{"gotest": {Commit: commit, State: state}}
			}
			if _, err := (&publisher{t: t, gh: gh, repo: app, c: &checkRuns{}}).publish(gotest(head, gitk8s.Running)); err != nil {
				t.Fatal(err)
			}

			t.Log("After a restart, the app of lib's check runs doesn't keep the controller from finding acme/app's.")
			c := &checkRuns{}
			if _, err := (&publisher{t: t, gh: gh, repo: lib, c: c}).publish(gotest(libHead, gitk8s.Running)); err != nil {
				t.Fatal(err)
			}
			var libApps []int64
			for _, r := range gh.Fake.CheckRuns("acme/" + other.repo) {
				if r.ExternalID == "default/lib" {
					libApps = append(libApps, r.App.ID)
				}
			}
			if !slices.Equal(libApps, []int64{gitserver.SecondOctoSTSApp}) {
				t.Fatalf("lib's check runs belong to apps %v, want one of app %d", libApps, gitserver.SecondOctoSTSApp)
			}
			p := &publisher{t: t, gh: gh, repo: app, c: c}
			got, err := p.publish(gotest(head, gitk8s.Passed))
			if want := []string{"GET " + api + "commits/" + head + "/check-runs", "PATCH " + api + "check-runs/1"}; err != nil || !slices.Equal(got, want) {
				t.Errorf("requests = %q, err = %v; want %q", got, err, want)
			}

			t.Log("The update shows the controller acme/app's app, so then it looks only at that app's check runs.")
			if status := asAdmin(t, gh, http.MethodPost, api+"check-runs", `{"name": "git-k8s/gotest", "head_sha": "`+next+`", "external_id": "default/app", "status": "in_progress", "output": {"title": "Running", "summary": "spoofed"}}`); status != http.StatusCreated {
				t.Fatalf("creating another app's check run: %d", status)
			}
			got, err = p.publish(gotest(next, gitk8s.Passed))
			if want := []string{"GET " + api + "commits/" + next + "/check-runs", "POST " + api + "check-runs"}; err != nil || !slices.Equal(got, want) {
				t.Errorf("requests = %q, err = %v; want %q", got, err, want)
			}
		})
	}
}

func TestLearnsAppFromCancelling(t *testing.T) {
	gh, w, main := newGitHub(t)
	w.Branch("c/x", main)
	head := w.Commit("add x")
	next := w.Commit("add y")
	w.Push("c/x")
	repo := gh.Repository("app", sts, rules()...)
	api := "/api/v3/repos/acme/app/"
	running := func(commit string) map[string]gitk8s.CheckResult {
		return map[string]gitk8s.CheckResult{"gotest": {Commit: commit, State: gitk8s.Running}}
	}
	if _, err := (&publisher{t: t, gh: gh, repo: repo, c: &checkRuns{}}).publish(running(head)); err != nil {
		t.Fatal(err)
	}

	t.Log("After a restart, cancelling the check run on a commit that the branch left shows the controller its app.")
	p := &publisher{t: t, gh: gh, repo: repo, c: &checkRuns{}}
	if got, err := p.publish(running(head)); err != nil || len(got) != 1 {
		t.Fatalf("requests = %q, err = %v; want only the search", got, err)
	}
	if status := asAdmin(t, gh, http.MethodPost, api+"check-runs", `{"name": "git-k8s/gotest", "head_sha": "`+next+`", "external_id": "default/app", "status": "in_progress", "output": {"title": "Running", "summary": "spoofed"}}`); status != http.StatusCreated {
		t.Fatalf("creating another app's check run: %d", status)
	}
	got, err := p.publish(running(next))
	if want := []string{"PATCH " + api + "check-runs/1", "GET " + api + "commits/" + next + "/check-runs", "POST " + api + "check-runs"}; err != nil || !slices.Equal(got, want) {
		t.Errorf("requests = %q, err = %v; want %q", got, err, want)
	}
}

func TestCheckRunsWaitOutRateLimits(t *testing.T) {
	gh, w, main := newGitHub(t)
	w.Branch("c/x", main)
	head := w.Commit("add x")
	w.Push("c/x")
	at := time.Unix(1_000_000, 0)
	p := &publisher{t: t, gh: gh, repo: gh.Repository("app", sts, rules()...), c: &checkRuns{now: func() time.Time { return at }}}
	checks := map[string]gitk8s.CheckResult{"base": {Commit: head, ParentCommit: main, State: gitk8s.Passed}}
	gh.Fake.RateLimit(90 * time.Second)
	got, err := p.publish(checks)
	if err != nil || len(got) != 1 || p.requeue < 90*time.Second || p.requeue > 90*time.Second*5/4 {
		t.Fatalf("requests = %q, err = %v, requeue = %v; want one request and a requeue in 90s to a quarter longer", got, err, p.requeue)
	}

	t.Log("Until the limit ends, the owner's branches send no requests.")
	at = at.Add(30 * time.Second)
	if got, err := p.publish(checks); err != nil || len(got) != 0 || p.requeue < time.Minute || p.requeue > time.Minute*5/4 {
		t.Errorf("30s later: requests = %q, err = %v, requeue = %v; want none and a requeue in 1m to a quarter longer", got, err, p.requeue)
	}
	at = at.Add(time.Minute)
	if got, err := p.publish(checks); err != nil || len(got) != 2 || len(runs(gh)) != 1 {
		t.Errorf("after the limit: requests = %q, err = %v, check runs %q; want the check run", got, err, runs(gh))
	}
}

// TestCheckRunsSpreadRetries checks that the branches that wait out one
// rate limit don't all send requests at once, both when GitHub answers with
// the limit and when the controller already knows it.
func TestCheckRunsSpreadRetries(t *testing.T) {
	gh, w, main := newGitHub(t)
	w.Branch("c/x", main)
	head := w.Commit("add x")
	w.Push("c/x")
	at := time.Unix(1_000_000, 0)
	p := &publisher{t: t, gh: gh, repo: gh.Repository("app", sts, rules()...), c: &checkRuns{now: func() time.Time { return at }}}
	checks := map[string]gitk8s.CheckResult{"base": {Commit: head, ParentCommit: main, State: gitk8s.Passed}}
	limited, paused := map[time.Duration]bool{}, map[time.Duration]bool{}
	for range 5 {
		gh.Fake.RateLimit(time.Minute)
		if got, err := p.publish(checks); err != nil || len(got) != 1 {
			t.Fatalf("requests = %q, err = %v; want one request", got, err)
		}
		limited[p.requeue] = true
		if got, err := p.publish(checks); err != nil || len(got) != 0 {
			t.Fatalf("during the limit: requests = %q, err = %v; want none", got, err)
		}
		paused[p.requeue] = true
		at = at.Add(2 * time.Minute)
	}
	if len(limited) < 2 || len(paused) < 2 {
		t.Errorf("requeues = %v at the limit and %v during it; want different ones", slices.Sorted(maps.Keys(limited)), slices.Sorted(maps.Keys(paused)))
	}
}

func TestSpread(t *testing.T) {
	seen := map[time.Duration]bool{}
	for range 100 {
		d := spread(time.Minute)
		if d < time.Minute || d > 75*time.Second {
			t.Fatalf("spread(1m) = %v, want 1m to 1m15s", d)
		}
		seen[d] = true
	}
	if len(seen) < 2 {
		t.Errorf("spread(1m) always returned %v", seen)
	}
}

// sharing publishes the results of the check gotest on branches of
// acme/app, whose commits each add a file, and checks what each reconcile
// sends to GitHub.
type sharing struct {
	t       *testing.T
	gh      *gittest.GitHub
	p       *publisher
	commits []string
}

func newSharing(t *testing.T, commits int) *sharing {
	gh, w, main := newGitHub(t)
	w.Branch("c/x", main)
	s := &sharing{t: t, gh: gh}
	for i := range commits {
		f := fmt.Sprintf("f%d.go", i)
		w.Write(f, "package x\n")
		s.commits = append(s.commits, w.Commit("add "+f))
	}
	w.Push("c/x")
	s.p = &publisher{t: t, gh: gh, repo: gh.Repository("app", sts, rules()...), c: &checkRuns{}}
	return s
}

// The REST API requests that create and update acme/app's check runs. An
// update's path ends with the check run's ID.
const (
	post  = "POST /api/v3/repos/acme/app/check-runs"
	patch = "PATCH /api/v3/repos/acme/app/check-runs/"
)

// get returns the REST API request that lists the check runs on commit i.
func (s *sharing) get(i int) string {
	return "GET /api/v3/repos/acme/app/commits/" + s.commits[i] + "/check-runs"
}

func (s *sharing) short(i int) string { return gitk8s.Short(s.commits[i]) }

// result returns results with gotest's result on commit i.
func (s *sharing) result(i int, state, msg string) map[string]gitk8s.CheckResult {
	return map[string]gitk8s.CheckResult{"gotest": {Commit: s.commits[i], State: state, Message: msg}}
}

// step sets the results of branch, reconciles it, and checks that the
// reconcile sent want.
func (s *sharing) step(branch string, checks map[string]gitk8s.CheckResult, want ...string) {
	s.t.Helper()
	s.p.set(branch, checks)
	s.again(branch, want...)
}

// again reconciles branch and checks that the reconcile sent want.
func (s *sharing) again(branch string, want ...string) {
	s.t.Helper()
	got, err := s.p.reconcile(branch)
	if err != nil || !slices.Equal(got, want) {
		s.t.Errorf("reconciling %s: requests = %q, err = %v; want %q", branch, got, err, want)
	}
}

// failing reconciles branch and checks that the reconcile sent want and
// failed with GitHub's 502 error.
func (s *sharing) failing(branch string, want ...string) {
	s.t.Helper()
	got, err := s.p.reconcile(branch)
	if err == nil || !strings.Contains(err.Error(), "502 Bad Gateway") || !slices.Equal(got, want) {
		s.t.Errorf("reconciling %s: requests = %q, err = %v; want %q and GitHub's error", branch, got, err, want)
	}
}

func (s *sharing) wantRuns(want ...string) {
	s.t.Helper()
	if got := runs(s.gh); !slices.Equal(got, want) {
		s.t.Errorf("check runs:\n%s\nwant:\n%s", strings.Join(got, "\n"), strings.Join(want, "\n"))
	}
}

func TestCancelsSupersededCheckRuns(t *testing.T) {
	s := newSharing(t, 4)
	at := time.Unix(1_000_000, 0)
	s.p.c.now = func() time.Time { return at }
	s.step("c/x", s.result(0, gitk8s.Running, ""), s.get(0), post)

	t.Log("When GitHub's rate limit stops the controller from cancelling the old commit's check run, it tries again after the limit.")
	s.gh.Fake.RateLimit(time.Minute)
	s.step("c/x", s.result(1, gitk8s.Running, ""), patch+"1")
	if s.p.requeue < time.Minute {
		t.Fatalf("requeue = %v, want one after the limit", s.p.requeue)
	}
	at = at.Add(s.p.requeue)
	s.again("c/x", patch+"1", s.get(1), post)
	s.wantRuns(
		"git-k8s/gotest@"+s.short(0)+" completed cancelled: The branch moved to "+s.short(1)+" before the check finished.",
		"git-k8s/gotest@"+s.short(1)+" in_progress : Running",
	)

	t.Log("When GitHub fails, the controller tries again.")
	s.gh.Fake.Fail(http.StatusBadGateway)
	s.p.set("c/x", s.result(2, gitk8s.Running, ""))
	s.failing("c/x", patch+"2")
	s.again("c/x", patch+"2", s.get(2), post)

	t.Log("When GitHub refuses, the controller leaves the old commit's check run and publishes the new head's result.")
	s.gh.Fake.Fail(http.StatusUnprocessableEntity)
	s.step("c/x", s.result(3, gitk8s.Running, ""), patch+"3", s.get(3), post)
	s.wantRuns(
		"git-k8s/gotest@"+s.short(0)+" completed cancelled: The branch moved to "+s.short(1)+" before the check finished.",
		"git-k8s/gotest@"+s.short(1)+" completed cancelled: The branch moved to "+s.short(2)+" before the check finished.",
		"git-k8s/gotest@"+s.short(2)+" in_progress : Running",
		"git-k8s/gotest@"+s.short(3)+" in_progress : Running",
	)
}

// TestBranchesShareCheckRuns runs against a fake GitHub that refuses to
// start a completed check run again and against one that accepts, because
// GitHub's documentation doesn't say which GitHub does.
func TestBranchesShareCheckRuns(t *testing.T) {
	for _, accept := range []bool{false, true} {
		t.Run("AcceptReopening="+strconv.FormatBool(accept), func(t *testing.T) {
			s := newSharing(t, 5)
			if accept {
				s.gh.Fake.AcceptReopening()
			}

			t.Log("A check that starts on a commit where another branch's check finished gets a new check run.")
			s.step("c/x", s.result(0, gitk8s.Passed, "passed on c/x"), s.get(0), post)
			s.step("c/y", s.result(0, gitk8s.Running, "started Pod y"), post)
			t.Log("The other branch's result changed earlier, so its next reconcile leaves the check run.")
			s.again("c/x")

			t.Log("When that branch moves before its check finishes, the check run shows the other branch's result again.")
			s.step("c/y", s.result(1, gitk8s.Running, "started Pod y"), patch+"2", s.get(1), post)
			s.wantRuns(
				"git-k8s/gotest@"+s.short(0)+" completed success: passed on c/x",
				"git-k8s/gotest@"+s.short(0)+" completed success: passed on c/x",
				"git-k8s/gotest@"+s.short(1)+" in_progress : started Pod y",
			)
			t.Log("And the other branch writes to the check run that GitHub shows.")
			s.step("c/x", s.result(0, gitk8s.Failed, "failed on c/x"), patch+"2")
			s.wantRuns(
				"git-k8s/gotest@"+s.short(0)+" completed success: passed on c/x",
				"git-k8s/gotest@"+s.short(0)+" completed failure: failed on c/x",
				"git-k8s/gotest@"+s.short(1)+" in_progress : started Pod y",
			)

			t.Log("When another branch completes a check run while this branch's check runs, this branch's next result gets a new check run.")
			s.step("c/x", s.result(1, gitk8s.Running, "started Pod x"), patch+"3")
			s.step("c/y", s.result(1, gitk8s.Passed, "passed on c/y"), patch+"3")
			s.again("c/x")
			s.step("c/x", s.result(1, gitk8s.Running, "trying again"), post)

			t.Log("When the last branch at a commit leaves it before its check finishes, the check run is cancelled.")
			s.step("c/y", s.result(2, gitk8s.Running, "started Pod y"), s.get(2), post)
			s.step("c/x", s.result(2, gitk8s.Running, "started Pod x"), patch+"4", patch+"5")

			t.Log("When another branch at the commit is still running the check, the check run shows that branch's result.")
			s.step("c/x", s.result(3, gitk8s.Running, "started Pod x"), patch+"5", s.get(3), post)
			s.wantRuns(
				"git-k8s/gotest@"+s.short(0)+" completed success: passed on c/x",
				"git-k8s/gotest@"+s.short(0)+" completed failure: failed on c/x",
				"git-k8s/gotest@"+s.short(1)+" completed success: passed on c/y",
				"git-k8s/gotest@"+s.short(1)+" completed cancelled: The branch moved to "+s.short(2)+" before the check finished.",
				"git-k8s/gotest@"+s.short(2)+" in_progress : started Pod y",
				"git-k8s/gotest@"+s.short(3)+" in_progress : started Pod x",
			)
			s.step("c/y", s.result(2, gitk8s.Passed, "passed on c/y"), patch+"5")
			if got := runs(s.gh)[4]; got != "git-k8s/gotest@"+s.short(2)+" completed success: passed on c/y" {
				t.Errorf("check run 5 = %s, want c/y's result", got)
			}

			t.Log("A result that the controller hasn't published yet counts too, and its branch's reconcile then sends nothing.")
			s.p.set("c/y", s.result(3, gitk8s.Running, "started Pod y"))
			s.step("c/x", s.result(4, gitk8s.Running, "started Pod x"), patch+"6", s.get(4), post)
			if got := runs(s.gh)[5]; got != "git-k8s/gotest@"+s.short(3)+" in_progress : started Pod y" {
				t.Errorf("check run 6 = %s, want c/y's result", got)
			}
			s.again("c/y")
		})
	}
}

func TestCheckRunsOfDepartedBranches(t *testing.T) {
	s := newSharing(t, 2)

	t.Log("When a branch is deleted before its check finishes, the check run shows the result of another branch at the commit.")
	s.step("c/x", s.result(0, gitk8s.Passed, "passed on c/x"), s.get(0), post)
	s.step("c/y", s.result(0, gitk8s.Running, "started Pod y"), post)
	s.p.remove("c/y")
	s.again("c/x", patch+"2")

	t.Log("Without another branch at the commit, the check run is cancelled, and when GitHub fails, the controller tries again.")
	s.step("c/z", s.result(1, gitk8s.Running, "started Pod z"), s.get(1), post)
	s.p.remove("c/z")
	s.gh.Fake.Fail(http.StatusBadGateway)
	s.failing("c/x", patch+"3")
	s.again("c/x", patch+"3")

	t.Log("So is the check run of a check that a branch dropped.")
	passed := s.result(0, gitk8s.Passed, "passed on c/x")
	s.step("c/x", map[string]gitk8s.CheckResult{"gotest": passed["gotest"], "gofmt": {Commit: s.commits[0], State: gitk8s.Running}}, s.get(0), post)
	s.step("c/x", passed, patch+"4")
	s.wantRuns(
		"git-k8s/gotest@"+s.short(0)+" completed success: passed on c/x",
		"git-k8s/gotest@"+s.short(0)+" completed success: passed on c/x",
		"git-k8s/gotest@"+s.short(1)+" completed cancelled: The branch was deleted before the check finished.",
		"git-k8s/gofmt@"+s.short(0)+" completed cancelled: The branch dropped the check before it finished.",
	)
	s.again("c/x")
}

// TestCompletedCheckRunsOfDepartedBranches runs against both fakes, because
// the controller can't rely on GitHub refusing to start a completed check
// run again.
func TestCompletedCheckRunsOfDepartedBranches(t *testing.T) {
	for _, accept := range []bool{false, true} {
		t.Run("AcceptReopening="+strconv.FormatBool(accept), func(t *testing.T) {
			s := newSharing(t, 2)
			if accept {
				s.gh.Fake.AcceptReopening()
			}

			t.Log("When a branch leaves a commit where its check finished, the check run keeps the result, and another branch that's still running the check there gets a new check run.")
			s.step("c/y", s.result(0, gitk8s.Running, "started Pod y"), s.get(0), post)
			s.step("c/x", s.result(0, gitk8s.Passed, "passed on c/x"), patch+"1")
			s.step("c/x", s.result(1, gitk8s.Running, "started Pod x"), s.get(1), post)
			s.again("c/y", post)

			t.Log("When the branch whose finished result the check run shows leaves the commit, the check run shows the finished result of another branch at the commit.")
			s.step("c/y", s.result(0, gitk8s.Failed, "failed on c/y"), patch+"3")
			s.step("c/z", s.result(0, gitk8s.Passed, "passed on c/z"), patch+"3")
			s.p.remove("c/z")
			s.again("c/x", patch+"3")
			s.again("c/y")
			s.wantRuns(
				"git-k8s/gotest@"+s.short(0)+" completed success: passed on c/x",
				"git-k8s/gotest@"+s.short(1)+" in_progress : started Pod x",
				"git-k8s/gotest@"+s.short(0)+" completed failure: failed on c/y",
			)
		})
	}
}

// TestCheckRunsOfUnpublishedResults checks the check runs that show a
// result that the controller hasn't published, after the result's branch
// leaves the commit before the controller publishes the result.
func TestCheckRunsOfUnpublishedResults(t *testing.T) {
	for _, tc := range []struct {
		name string
		// leave makes c/y leave commit 0 and returns the summary of the
		// cancelled check run.
		leave func(s *sharing) string
	}{
		{"Moved", func(s *sharing) string {
			s.p.set("c/y", s.result(2, gitk8s.Running, "started Pod y"))
			return "The branch moved to " + s.short(2) + " before the check finished."
		}},
		{"Deleted", func(s *sharing) string {
			s.p.remove("c/y")
			return "The branch was deleted before the check finished."
		}},
		{"Dropped", func(s *sharing) string {
			s.p.set("c/y", map[string]gitk8s.CheckResult{})
			return "The branch dropped the check before it finished."
		}},
	} {
		t.Run(tc.name, func(t *testing.T) {
			s := newSharing(t, 3)
			t.Log("When a branch moves, the check run on the commit that it left shows another branch's result there, which the controller hasn't published.")
			s.step("c/x", s.result(0, gitk8s.Running, "started Pod x"), s.get(0), post)
			s.p.set("c/y", s.result(0, gitk8s.Running, "started Pod y"))
			s.step("c/x", s.result(1, gitk8s.Running, "started Pod x"), patch+"1", s.get(1), post)
			s.wantRuns(
				"git-k8s/gotest@"+s.short(0)+" in_progress : started Pod y",
				"git-k8s/gotest@"+s.short(1)+" in_progress : started Pod x",
			)

			t.Log("When the other branch leaves the commit before the controller publishes its result, the check run is cancelled, and when GitHub fails, the controller tries again.")
			why := tc.leave(s)
			s.gh.Fake.Fail(http.StatusBadGateway)
			s.failing("c/x", patch+"1")
			s.again("c/x", patch+"1")
			s.wantRuns(
				"git-k8s/gotest@"+s.short(0)+" completed cancelled: "+why,
				"git-k8s/gotest@"+s.short(1)+" in_progress : started Pod x",
			)
			s.again("c/x")
		})
	}

	t.Run("FromBranchWithoutChecks", func(t *testing.T) {
		s := newSharing(t, 1)
		t.Log("When a branch drops a check, the check run shows another branch's result at the commit, which the controller hasn't published.")
		s.step("c/x", s.result(0, gitk8s.Running, "started Pod x"), s.get(0), post)
		s.p.set("c/y", s.result(0, gitk8s.Running, "started Pod y"))
		s.step("c/x", map[string]gitk8s.CheckResult{}, patch+"1")

		t.Log("When the other branch is deleted, the reconcile of a branch without checks cancels the check run.")
		s.p.remove("c/y")
		s.again("c/x", patch+"1")
		s.wantRuns("git-k8s/gotest@" + s.short(0) + " completed cancelled: The branch was deleted before the check finished.")
		s.again("c/x")
	})
}

func TestCheckRunsSurviveFailedReads(t *testing.T) {
	s := newSharing(t, 2)
	s.step("c/x", s.result(0, gitk8s.Running, ""), s.get(0), post)

	t.Log("A reconcile that can't read the cluster sends nothing and forgets nothing.")
	b := resultsOf("app", "c/x", s.result(1, gitk8s.Running, ""))
	ctx, rec := kube.Fake(t.Context(), b, s.p.repo)
	kube.List[branchResults](ctx, kube.MatchingSelector("=broken"))
	if rec.Err() == nil {
		t.Fatal("the selector didn't fail the reconcile's reads")
	}
	before := len(s.gh.Fake.Requests())
	s.p.c.Reconcile(ctx, b)
	if got := s.gh.Fake.Requests()[before:]; len(got) > 0 {
		t.Errorf("a reconcile that couldn't read sent %q", got)
	}
	s.step("c/x", s.result(1, gitk8s.Running, ""), patch+"1", s.get(1), post)
	s.wantRuns(
		"git-k8s/gotest@"+s.short(0)+" completed cancelled: The branch moved to "+s.short(1)+" before the check finished.",
		"git-k8s/gotest@"+s.short(1)+" in_progress : Running",
	)
}

// front puts handler in front of the fake GitHub and points the programs at
// it until the test ends. It returns acme/app's GitRepository at the front's
// URL. handler passes a request on to the fake by calling next.
func front(t *testing.T, gh *gittest.GitHub, handler func(w http.ResponseWriter, r *http.Request, next http.Handler)) *gitk8s.GitRepository {
	t.Helper()
	base := gittest.Serve(t, http.HandlerFunc(func(w http.ResponseWriter, r *http.Request) {
		handler(w, r, gh.Fake)
	}))
	repo := gh.Repository("app", sts, rules()...)
	repo.Spec.URL = base + "/acme/app.git"
	return repo
}

func TestBranchesTakeTurns(t *testing.T) {
	gh, w, main := newGitHub(t)
	w.Branch("c/x", main)
	var commits []string
	for _, f := range []string{"a", "b", "c"} {
		w.Write(f+".go", "package x\n")
		commits = append(commits, w.Commit("add "+f))
	}
	w.Push("c/x")
	// In a round, GitHub holds the first request until another request
	// arrives, or for 200ms, so that reconciles that don't wait for each
	// other send requests at the same time.
	type round struct {
		held, arrived         chan struct{}
		heldOnce, arrivedOnce sync.Once
		hold, overlapped      atomic.Bool
		inFlight              atomic.Int32
	}
	var current atomic.Pointer[round]
	repo := front(t, gh, func(w http.ResponseWriter, r *http.Request, next http.Handler) {
		rd := current.Load()
		if rd == nil || !strings.HasPrefix(r.URL.Path, "/api/") {
			next.ServeHTTP(w, r)
			return
		}
		if rd.inFlight.Add(1) > 1 {
			rd.overlapped.Store(true)
			rd.arrivedOnce.Do(func() { close(rd.arrived) })
		}
		defer rd.inFlight.Add(-1)
		if rd.hold.CompareAndSwap(true, false) {
			rd.heldOnce.Do(func() { close(rd.held) })
			select {
			case <-rd.arrived:
			case <-time.After(200 * time.Millisecond):
			}
		}
		next.ServeHTTP(w, r)
	})
	// together runs first and second at once, starting second when GitHub
	// holds first's first request.
	together := func(first, second func() error) {
		t.Helper()
		rd := &round{held: make(chan struct{}), arrived: make(chan struct{})}
		rd.hold.Store(true)
		current.Store(rd)
		defer current.Store(nil)
		done := make(chan error, 1)
		go func() { done <- first() }()
		select {
		case <-rd.held:
		case err := <-done:
			t.Fatalf("the first reconcile sent no request: %v", err)
		}
		if err := second(); err != nil {
			t.Error(err)
		}
		if err := <-done; err != nil {
			t.Error(err)
		}
		if rd.overlapped.Load() {
			t.Error("the reconciles sent requests to GitHub at the same time")
		}
	}
	c := &checkRuns{}
	// reconcile reconciles branch in a cluster where acme/app's branches
	// have the results in cluster.
	reconcile := func(branch string, cluster map[string]map[string]gitk8s.CheckResult) error {
		var b *branchResults
		world := []any{repo}
		for name, checks := range cluster {
			if o := resultsOf("app", name, checks); name == branch {
				b = o
			} else {
				world = append(world, o)
			}
		}
		ctx, _ := kube.Fake(t.Context(), b, world...)
		return c.Reconcile(ctx, b)
	}
	result := func(i int, state, msg string) map[string]gitk8s.CheckResult {
		return map[string]gitk8s.CheckResult{"gotest": {Commit: commits[i], State: state, Message: msg}}
	}
	short := func(i int) string { return gitk8s.Short(commits[i]) }

	t.Log("A branch leaves a commit while another branch's check on the commit passes.")
	runningY := result(0, gitk8s.Running, "started Pod y")
	if err := reconcile("c/y", map[string]map[string]gitk8s.CheckResult{"c/y": runningY}); err != nil {
		t.Fatal(err)
	}
	if err := reconcile("c/x", map[string]map[string]gitk8s.CheckResult{"c/x": result(0, gitk8s.Running, "started Pod x"), "c/y": runningY}); err != nil {
		t.Fatal(err)
	}
	movedX := result(1, gitk8s.Running, "started Pod x")
	together(
		func() error {
			return reconcile("c/x", map[string]map[string]gitk8s.CheckResult{"c/x": movedX, "c/y": runningY})
		},
		func() error {
			return reconcile("c/y", map[string]map[string]gitk8s.CheckResult{"c/x": movedX, "c/y": result(0, gitk8s.Passed, "passed on c/y")})
		},
	)
	if got, want := runs(gh), []string{
		"git-k8s/gotest@" + short(0) + " completed success: passed on c/y",
		"git-k8s/gotest@" + short(1) + " in_progress : started Pod x",
	}; !slices.Equal(got, want) {
		t.Errorf("check runs:\n%s\nwant:\n%s", strings.Join(got, "\n"), strings.Join(want, "\n"))
	}

	t.Log("Two branches publish their first results on a commit at once, and GitHub shows the later one's next result.")
	atC := map[string]map[string]gitk8s.CheckResult{"c/x": result(2, gitk8s.Running, "started Pod x"), "c/y": result(2, gitk8s.Passed, "passed on c/y")}
	together(
		func() error { return reconcile("c/x", atC) },
		func() error { return reconcile("c/y", atC) },
	)
	if err := reconcile("c/x", map[string]map[string]gitk8s.CheckResult{"c/x": result(2, gitk8s.Failed, "failed on c/x"), "c/y": atC["c/y"]}); err != nil {
		t.Fatal(err)
	}
	if got, want := runs(gh), []string{
		"git-k8s/gotest@" + short(0) + " completed success: passed on c/y",
		"git-k8s/gotest@" + short(1) + " completed cancelled: The branch moved to " + short(2) + " before the check finished.",
		"git-k8s/gotest@" + short(2) + " completed failure: failed on c/x",
	}; !slices.Equal(got, want) {
		t.Errorf("check runs:\n%s\nwant:\n%s", strings.Join(got, "\n"), strings.Join(want, "\n"))
	}
}

func TestCheckRunErrors(t *testing.T) {
	gh, w, main := newGitHub(t)
	w.Branch("c/x", main)
	head := w.Commit("add x")
	w.Push("c/x")
	checks := map[string]gitk8s.CheckResult{"base": {Commit: head, ParentCommit: main, State: gitk8s.Passed}}
	publish := func(sts gitk8s.OctoSTS) ([]string, error) {
		t.Helper()
		return (&publisher{t: t, gh: gh, repo: gh.Repository("app", sts, rules()...), c: &checkRuns{}}).publish(checks)
	}

	t.Log("An identity without checks: write gets GitHub's error.")
	list, err := url.Parse(strings.TrimSuffix(gh.URL, "/acme") + "/api/v3/repos/acme/app/commits/" + head + "/check-runs")
	if err != nil {
		t.Fatal(err)
	}
	_, err = publish(gitk8s.OctoSTS{GitIdentity: "git", CheckRunsIdentity: "git"})
	if want := "publishing the base check run: GitHub answered GET " + list.Path + " with 403 Forbidden: Resource not accessible by integration"; err == nil || err.Error() != want {
		t.Errorf("err = %v, want %s", err, want)
	}
	_, err = publish(gitk8s.OctoSTS{CheckRunsIdentity: "missing"})
	if err == nil || !strings.Contains(err.Error(), `unable to find trust policy for "missing"`) {
		t.Errorf("err = %v, want the exchange's error", err)
	}

	t.Log("Without a check-runs identity, the controller does nothing.")
	before := len(gh.Fake.Exchanges())
	if got, err := publish(gitk8s.OctoSTS{GitIdentity: "git"}); err != nil || len(got) != 0 || len(gh.Fake.Exchanges()) != before {
		t.Errorf("requests = %q, err = %v, %d new exchanges; want nothing", got, err, len(gh.Fake.Exchanges())-before)
	}
	b := resultsOf("app", "c/x", checks)
	ctx, _ := kube.Fake(t.Context(), b)
	if err := (&checkRuns{}).Reconcile(ctx, b); err != nil {
		t.Errorf("without the GitRepository: %v", err)
	}
}

func TestRunFor(t *testing.T) {
	for _, tc := range []struct {
		res                         gitk8s.CheckResult
		status, conclusion, summary string
	}{
		{gitk8s.CheckResult{State: gitk8s.Running}, "in_progress", "", "Running"},
		{gitk8s.CheckResult{State: gitk8s.Passed, Message: "ok"}, "completed", "success", "```\nok\n```"},
		{gitk8s.CheckResult{State: gitk8s.Failed}, "completed", "failure", "Failed"},
		{gitk8s.CheckResult{State: gitk8s.Error, Message: "boom"}, "completed", "failure", "```\nboom\n```"},
		{gitk8s.CheckResult{State: gitk8s.Fixed}, "completed", "neutral", "Fixed"},
	} {
		s := runFor(tc.res)
		if s.Status != tc.status || s.Conclusion != tc.conclusion || s.Output.Title != tc.res.State || s.Output.Summary != tc.summary || s.Output.Text != "" {
			t.Errorf("runFor(%+v) = %+v", tc.res, s)
		}
	}
	s := runFor(gitk8s.CheckResult{State: gitk8s.Passed, Outputs: map[string]string{"level": "low", "files": "3"}})
	if s.Output.Text != "```\nfiles: 3\nlevel: low\n```" {
		t.Errorf("text = %q", s.Output.Text)
	}
}

func TestCodeBlock(t *testing.T) {
	for _, tc := range []struct{ in, want string }{
		{"x.go isn't formatted", "```\nx.go isn't formatted\n```"},
		{"run `gofmt -w x.go`", "```\nrun `gofmt -w x.go`\n```"},
		{"```go\nvar x = 1\n```", "````\n```go\nvar x = 1\n```\n````"},
		{"[a link](https://example.com) and `````", "``````\n[a link](https://example.com) and `````\n``````"},
	} {
		if got := codeBlock(tc.in); got != tc.want {
			t.Errorf("codeBlock(%q) = %q, want %q", tc.in, got, tc.want)
		}
	}

	t.Log("A long string is cut to fit, and its fence is still longer than any run of backticks in it.")
	for _, s := range []string{strings.Repeat("é", 40_000), strings.Repeat("ab``` ", 20_000), strings.Repeat("`", 70_000)} {
		got := codeBlock(s)
		fence, _, _ := strings.Cut(got, "\n")
		body, ok := strings.CutPrefix(got, fence+"\n")
		body, ok2 := strings.CutSuffix(body, "\n"+fence)
		cut, ok3 := strings.CutSuffix(body, "...")
		if len(got) > maxOutput || !utf8.ValidString(got) || len(fence) < 3 || strings.Trim(fence, "`") != "" ||
			!ok || !ok2 || !ok3 || strings.Contains(body, fence) || !strings.HasPrefix(s, cut) {
			t.Errorf("codeBlock of %d bytes starting %q: %d bytes, a fence of %d, valid UTF-8 %v", len(s), s[:6], len(got), len(fence), utf8.ValidString(got))
		}
	}
}

func TestRateLimitWait(t *testing.T) {
	now := time.Unix(1_000_000, 0)
	for _, tc := range []struct {
		status  int
		headers map[string]string
		message string
		wait    time.Duration
	}{
		{status: http.StatusForbidden, headers: map[string]string{"Retry-After": "120"}, wait: 2 * time.Minute},
		{status: http.StatusTooManyRequests, wait: time.Minute},
		{status: http.StatusForbidden, headers: map[string]string{"X-RateLimit-Remaining": "0", "X-RateLimit-Reset": strconv.FormatInt(now.Unix()+300, 10)}, wait: 5 * time.Minute},
		{status: http.StatusForbidden, headers: map[string]string{"X-RateLimit-Remaining": "0", "X-RateLimit-Reset": strconv.FormatInt(now.Unix()-5, 10)}, wait: time.Second},
		{status: http.StatusForbidden, message: "You have exceeded a secondary rate limit.", wait: time.Minute},
		{status: http.StatusForbidden, headers: map[string]string{"X-RateLimit-Remaining": "4999"}, message: "Resource not accessible by integration"},
		{status: http.StatusInternalServerError, headers: map[string]string{"Retry-After": "120"}},
	} {
		resp := &http.Response{StatusCode: tc.status, Header: http.Header{}}
		for k, v := range tc.headers {
			resp.Header.Set(k, v)
		}
		wait, ok := rateLimitWait(resp, tc.message, now)
		if wait != tc.wait || ok != (tc.wait > 0) {
			t.Errorf("%d %v %q: wait %v, %v; want %v", tc.status, tc.headers, tc.message, wait, ok, tc.wait)
		}
	}
}
