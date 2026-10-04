package main

import (
	"fmt"
	"net/http"
	"reflect"
	"slices"
	"strconv"
	"strings"
	"testing"
	"time"
	"unicode/utf8"

	gitk8s "github.com/imjasonh/playground/git-k8s"
	"github.com/imjasonh/playground/git-k8s/internal/git"
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

// resultsOf returns c/x's GitBranch, as the check-runs controller sees it,
// with checks.
func resultsOf(checks map[string]gitk8s.CheckResult) *branchResults {
	b := &branchResults{Object: kube.Meta(gitk8s.BranchObjectName("app", "c/x"), nil)}
	b.Namespace = "default"
	b.Spec.Repository = "app"
	b.Status.Checks = checks
	return b
}

// publisher runs a check-runs controller on c/x for a repository and
// returns the REST API requests that each reconcile sent.
type publisher struct {
	t    *testing.T
	gh   *gittest.GitHub
	repo *gitk8s.GitRepository
	c    *checkRuns
	// requeue is the last reconcile's requeue.
	requeue time.Duration
}

func (p *publisher) publish(checks map[string]gitk8s.CheckResult) ([]string, error) {
	p.t.Helper()
	before := len(p.gh.Fake.Requests())
	b := resultsOf(checks)
	want := b.Status
	ctx, rec := kube.Fake(p.t.Context(), b, p.repo)
	err := p.c.Reconcile(ctx, b)
	if !reflect.DeepEqual(b.Status, want) {
		p.t.Errorf("the check-runs controller changed the GitBranch's status to %+v", b.Status)
	}
	p.requeue = rec.RequeueAfter()
	return p.gh.Fake.Requests()[before:], err
}

// runs lists acme/app's check runs as "NAME@COMMIT STATUS CONCLUSION:
// SUMMARY".
func runs(gh *gittest.GitHub) []string {
	var out []string
	for _, r := range gh.Fake.CheckRuns("acme/app") {
		out = append(out, fmt.Sprintf("%s@%s %s %s: %s", r.Name, gitk8s.Short(r.HeadSHA), r.Status, r.Conclusion, r.Output.Summary))
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
	if r := gh.Fake.CheckRuns("acme/app")[0]; r.ExternalID != "default/app" || r.Output.Title != "Passed" {
		t.Errorf("check run = %+v, want external ID default/app and title Passed", r)
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
	if r := gh.Fake.CheckRuns("acme/app")[2]; r.Output.Text != "- fix: "+fix {
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
	req, err := http.NewRequest(http.MethodPatch, strings.TrimSuffix(gh.URL, "/acme")+api+"check-runs/1", strings.NewReader(`{"conclusion": "failure", "output": {"title": "Failed", "summary": "changed on GitHub"}}`))
	if err != nil {
		t.Fatal(err)
	}
	req.SetBasicAuth(gh.Username, gh.Password)
	resp, err := http.DefaultClient.Do(req)
	if err != nil {
		t.Fatal(err)
	}
	resp.Body.Close()
	if resp.StatusCode != http.StatusOK {
		t.Fatalf("changing the check run: %s", resp.Status)
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
	if err != nil || len(got) != 1 || p.requeue != 90*time.Second {
		t.Fatalf("requests = %q, err = %v, requeue = %v; want one request and a requeue in 90s", got, err, p.requeue)
	}

	t.Log("Until the limit ends, the owner's branches send no requests.")
	at = at.Add(30 * time.Second)
	if got, err := p.publish(checks); err != nil || len(got) != 0 || p.requeue != time.Minute {
		t.Errorf("30s later: requests = %q, err = %v, requeue = %v; want none and a requeue in 1m", got, err, p.requeue)
	}
	at = at.Add(time.Minute)
	if got, err := p.publish(checks); err != nil || len(got) != 2 || len(runs(gh)) != 1 {
		t.Errorf("after the limit: requests = %q, err = %v, check runs %q; want the check run", got, err, runs(gh))
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
	_, err := publish(gitk8s.OctoSTS{GitIdentity: "git", CheckRunsIdentity: "git"})
	if want := "publishing the base check run: GitHub answered GET /api/v3/repos/acme/app/commits/" + head + "/check-runs with 403 Forbidden: Resource not accessible by integration"; err == nil || err.Error() != want {
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
	b := resultsOf(checks)
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
		{gitk8s.CheckResult{State: gitk8s.Passed, Message: "ok"}, "completed", "success", "ok"},
		{gitk8s.CheckResult{State: gitk8s.Failed}, "completed", "failure", "Failed"},
		{gitk8s.CheckResult{State: gitk8s.Error, Message: "boom"}, "completed", "failure", "boom"},
		{gitk8s.CheckResult{State: gitk8s.Fixed}, "completed", "neutral", "Fixed"},
	} {
		s := runFor(tc.res)
		if s.Status != tc.status || s.Conclusion != tc.conclusion || s.Output.Title != tc.res.State || s.Output.Summary != tc.summary {
			t.Errorf("runFor(%+v) = %+v", tc.res, s)
		}
	}
	s := runFor(gitk8s.CheckResult{State: gitk8s.Passed, Outputs: map[string]string{"level": "low", "files": "3"}})
	if s.Output.Text != "- files: 3\n- level: low" {
		t.Errorf("text = %q", s.Output.Text)
	}
	s = runFor(gitk8s.CheckResult{State: gitk8s.Passed, Outputs: map[string]string{"log": strings.Repeat("é", 40_000)}})
	if len(s.Output.Text) > 65535 || !utf8.ValidString(s.Output.Text) || !strings.HasSuffix(s.Output.Text, "...") {
		t.Errorf("long text has %d bytes, valid UTF-8 %v", len(s.Output.Text), utf8.ValidString(s.Output.Text))
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
