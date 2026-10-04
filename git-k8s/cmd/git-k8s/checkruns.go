package main

import (
	"bytes"
	"cmp"
	"context"
	"encoding/json"
	"errors"
	"fmt"
	"io"
	"log/slog"
	"maps"
	"math/rand/v2"
	"net/http"
	"net/url"
	"path"
	"slices"
	"strconv"
	"strings"
	"sync"
	"sync/atomic"
	"time"

	gitk8s "github.com/imjasonh/playground/git-k8s"
	"github.com/imjasonh/playground/git-k8s/credentials"
	"github.com/imjasonh/playground/kube"
)

// branchResults is the check-runs controller's view of a GitBranch.
// Reconcile never changes Status, so the controller never writes it.
type branchResults struct {
	kube.Object `kube:"apiVersion=git-k8s.imjasonh.com/v1alpha1,kind=GitBranch,plural=gitbranches,scope=Namespaced"`
	Spec        struct {
		Repository string `json:"repository"`
	} `json:"spec"`
	Status struct {
		Checks map[string]gitk8s.CheckResult `json:"checks,omitempty"`
	} `json:"status,omitzero"`
}

// checkRuns copies the check results on each GitBranch to GitHub as check
// runs on the commits that they're for, for repositories that name an Octo
// STS identity for check runs. A check's check run on a commit is named
// git-k8s/CHECK. The controller updates it as the result changes, and
// creates another when a check that finished starts again. Nothing on GitHub
// changes a result.
type checkRuns struct {
	// now is time.Now, except in tests.
	now func() time.Time

	// app is the ID of the GitHub App that the controller's tokens act for,
	// or 0 until the controller creates a check run. Every token from Octo
	// STS acts for the Octo STS app, and GitHub lets only the app that
	// created a check run update it, so the controller looks only for its
	// app's check runs.
	app atomic.Int64

	mu sync.Mutex
	// runs holds the check run that the controller last wrote or found for
	// each check on each branch, so that a result that stays the same costs
	// no requests.
	runs map[runKey]publishedRun
	// paused holds when each repository owner's rate limit ends. GitHub
	// limits each installation of a GitHub App, and an installation is one
	// owner's.
	paused map[string]time.Time
}

type runKey struct{ namespace, branch, check string }

type publishedRun struct {
	commit string
	id     int64
	shows  runState
	at     time.Time
}

// runState is what a check run shows.
type runState struct {
	Status     string    `json:"status"`
	Conclusion string    `json:"conclusion,omitempty"`
	Output     runOutput `json:"output"`
}

type runOutput struct {
	Title   string `json:"title"`
	Summary string `json:"summary"`
	Text    string `json:"text"`
}

// checkRun is a check run as the REST API sends and receives it.
type checkRun struct {
	ID         int64  `json:"id,omitempty"`
	Name       string `json:"name,omitempty"`
	HeadSHA    string `json:"head_sha,omitempty"`
	ExternalID string `json:"external_id,omitempty"`
	App        struct {
		ID int64 `json:"id"`
	} `json:"app,omitzero"`
	runState
}

// forgetAfter is how long the controller remembers a check run that it
// hasn't written or found since.
const forgetAfter = 24 * time.Hour

var githubClient = &http.Client{Timeout: 30 * time.Second}

func (c *checkRuns) clock() time.Time {
	if c.now != nil {
		return c.now()
	}
	return time.Now()
}

func (c *checkRuns) Reconcile(ctx context.Context, b *branchResults) error {
	repo := kube.Get[gitk8s.Repository](ctx, b.Namespace, b.Spec.Repository)
	if repo == nil || repo.Spec.OctoSTS == nil || repo.Spec.OctoSTS.CheckRunsIdentity == "" || len(b.Status.Checks) == 0 {
		return nil
	}
	apiURL, token, err := credentials.GitHubAPI(ctx, repo, repo.Spec.OctoSTS.CheckRunsIdentity)
	if err != nil {
		return err
	}
	owner := apiURL[:strings.LastIndex(apiURL, "/")]
	if wait := c.pausedFor(owner); wait > 0 {
		kube.RequeueAfter(ctx, spread(wait))
		return nil
	}
	gh := &githubAPI{repo: apiURL, token: token, now: c.clock}
	var errs []error
	for _, name := range slices.Sorted(maps.Keys(b.Status.Checks)) {
		err := c.publish(ctx, gh, b, name, b.Status.Checks[name])
		var limited *rateLimited
		if errors.As(err, &limited) {
			slog.Info("pausing check runs for GitHub's rate limit", "owner", path.Base(owner), "for", limited.wait)
			c.pause(owner, limited.wait)
			kube.RequeueAfter(ctx, spread(limited.wait))
			return nil
		}
		if err != nil {
			errs = append(errs, fmt.Errorf("publishing the %s check run: %w", name, err))
		}
	}
	return errors.Join(errs...)
}

// publish makes the check run for one check's result on a branch show it.
func (c *checkRuns) publish(ctx context.Context, gh *githubAPI, b *branchResults, check string, res gitk8s.CheckResult) error {
	if res.Commit == "" {
		return nil
	}
	k := runKey{b.Namespace, b.Name, check}
	want := runFor(res)
	last, ok := c.last(k)
	if ok && last.commit == res.Commit && last.shows == want {
		return nil
	}
	if ok && last.commit != res.Commit && last.shows.Status != "completed" {
		if err := c.supersede(ctx, gh, k, last, res.Commit); err != nil {
			return err
		}
	}

	run := checkRun{Name: "git-k8s/" + check, HeadSHA: res.Commit, ExternalID: b.Namespace + "/" + b.Spec.Repository, runState: want}
	var old *checkRun
	if ok && last.commit == res.Commit {
		old = &checkRun{ID: last.id, runState: last.shows}
	} else {
		found, err := gh.find(ctx, run, c.app.Load())
		if err != nil {
			return err
		}
		if found != nil && found.runState == want {
			c.remember(k, publishedRun{commit: res.Commit, id: found.ID, shows: want})
			return nil
		}
		old = found
	}
	// GitHub doesn't support starting a completed check run again, so a
	// check that starts again gets a new check run, which GitHub shows
	// instead of the old one.
	if old != nil && (old.Status != "completed" || want.Status == "completed") {
		err := gh.update(ctx, old.ID, want)
		if err == nil {
			c.remember(k, publishedRun{commit: res.Commit, id: old.ID, shows: want})
			return nil
		}
		// Until the controller knows its app, it can find another app's
		// check run, which only that app can update.
		if !notOurs(err) {
			return err
		}
	}
	created, err := gh.create(ctx, run)
	if err != nil {
		return err
	}
	c.app.Store(created.App.ID)
	c.remember(k, publishedRun{commit: res.Commit, id: created.ID, shows: want})
	return nil
}

// supersede completes the check run for a commit that the branch moved
// away from before the check finished. Check controllers don't finish
// checks on old commits, so the run would otherwise stay in progress.
func (c *checkRuns) supersede(ctx context.Context, gh *githubAPI, k runKey, last publishedRun, commit string) error {
	last.shows = runState{Status: "completed", Conclusion: "cancelled", Output: runOutput{
		Title:   "Superseded",
		Summary: fmt.Sprintf("The branch moved to %s before the check finished.", gitk8s.Short(commit)),
	}}
	switch err := gh.update(ctx, last.id, last.shows); {
	case notOurs(err):
		// GitHub won't change this check run, so trying again can't help.
		slog.Warn("couldn't cancel a superseded check run", "namespace", k.namespace, "gitbranch", k.branch, "check", k.check, "id", last.id, "error", err)
	case err != nil:
		return fmt.Errorf("cancelling the check run on %s: %w", gitk8s.Short(last.commit), err)
	}
	c.remember(k, last)
	return nil
}

// runFor returns what the check run for a result shows.
func runFor(res gitk8s.CheckResult) runState {
	s := runState{Status: "completed", Output: runOutput{Title: res.State, Summary: limit(cmp.Or(res.Message, res.State))}}
	switch res.State {
	case gitk8s.Running:
		s.Status = "in_progress"
	case gitk8s.Passed:
		s.Conclusion = "success"
	case gitk8s.Failed, gitk8s.Error:
		s.Conclusion = "failure"
	default:
		// A Fixed result's check also runs on the fix, and that run
		// decides.
		s.Conclusion = "neutral"
	}
	var outputs []string
	for _, k := range slices.Sorted(maps.Keys(res.Outputs)) {
		outputs = append(outputs, fmt.Sprintf("- %s: %s", k, res.Outputs[k]))
	}
	s.Output.Text = limit(strings.Join(outputs, "\n"))
	return s
}

// limit cuts s to the length that GitHub allows in a check run's summary
// and text.
func limit(s string) string {
	const maxLen = 65535
	if len(s) <= maxLen {
		return s
	}
	return strings.ToValidUTF8(s[:maxLen-3], "") + "..."
}

func (c *checkRuns) last(k runKey) (publishedRun, bool) {
	c.mu.Lock()
	defer c.mu.Unlock()
	r, ok := c.runs[k]
	return r, ok
}

func (c *checkRuns) remember(k runKey, r publishedRun) {
	c.mu.Lock()
	defer c.mu.Unlock()
	now := c.clock()
	for key, old := range c.runs {
		if now.Sub(old.at) >= forgetAfter {
			delete(c.runs, key)
		}
	}
	if c.runs == nil {
		c.runs = map[runKey]publishedRun{}
	}
	r.at = now
	c.runs[k] = r
}

func (c *checkRuns) pausedFor(owner string) time.Duration {
	c.mu.Lock()
	defer c.mu.Unlock()
	return c.paused[owner].Sub(c.clock())
}

func (c *checkRuns) pause(owner string, d time.Duration) {
	c.mu.Lock()
	defer c.mu.Unlock()
	if c.paused == nil {
		c.paused = map[string]time.Time{}
	}
	c.paused[owner] = c.clock().Add(d)
}

// spread returns a time from d to a quarter longer than d, so that the
// branches that wait out one rate limit don't all send requests at once.
func spread(d time.Duration) time.Duration {
	return d + rand.N(d/4+1) // #nosec G404 -- jitter needs no cryptographic randomness.
}

// githubAPI sends requests to GitHub's REST API for one repository.
type githubAPI struct {
	// repo is the repository's URL, such as
	// https://api.github.com/repos/OWNER/REPO.
	repo  string
	token string
	now   func() time.Time
}

// rateLimited is a response that says to wait before the next request.
type rateLimited struct {
	wait time.Duration
}

func (e *rateLimited) Error() string {
	return fmt.Sprintf("GitHub's rate limit asks to wait %v", e.wait)
}

// githubError is an answer from GitHub that's neither a success nor a rate
// limit.
type githubError struct {
	status int
	msg    string
}

func (e *githubError) Error() string { return e.msg }

// notOurs reports whether err is GitHub refusing to update a check run, as
// it does when another app created the check run or the check run doesn't
// exist.
func notOurs(err error) bool {
	var e *githubError
	return errors.As(err, &e) && (e.status == http.StatusForbidden || e.status == http.StatusNotFound)
}

// find returns the newest check run that has run's name, commit, and
// external ID, or nil. Unless app is 0, it looks only at app's check runs.
func (gh *githubAPI) find(ctx context.Context, run checkRun, app int64) (*checkRun, error) {
	q := url.Values{"check_name": {run.Name}, "filter": {"all"}, "per_page": {"100"}}
	if app != 0 {
		q.Set("app_id", strconv.FormatInt(app, 10))
	}
	var list struct {
		CheckRuns []checkRun `json:"check_runs"`
	}
	if err := gh.do(ctx, http.MethodGet, "/commits/"+url.PathEscape(run.HeadSHA)+"/check-runs?"+q.Encode(), nil, &list); err != nil {
		return nil, err
	}
	var found *checkRun
	for i, r := range list.CheckRuns {
		if r.ExternalID == run.ExternalID && (found == nil || r.ID > found.ID) {
			found = &list.CheckRuns[i]
		}
	}
	return found, nil
}

func (gh *githubAPI) create(ctx context.Context, run checkRun) (checkRun, error) {
	var created checkRun
	err := gh.do(ctx, http.MethodPost, "/check-runs", run, &created)
	return created, err
}

func (gh *githubAPI) update(ctx context.Context, id int64, s runState) error {
	return gh.do(ctx, http.MethodPatch, "/check-runs/"+strconv.FormatInt(id, 10), s, nil)
}

// do sends a request with in as its JSON body, unless in is nil, and
// decodes the JSON response into out, unless out is nil.
func (gh *githubAPI) do(ctx context.Context, method, path string, in, out any) error {
	var body io.Reader
	if in != nil {
		b, err := json.Marshal(in)
		if err != nil {
			return err
		}
		body = bytes.NewReader(b)
	}
	req, err := http.NewRequestWithContext(ctx, method, gh.repo+path, body)
	if err != nil {
		return err
	}
	req.Header.Set("Accept", "application/vnd.github+json")
	req.Header.Set("Authorization", "Bearer "+gh.token)
	req.Header.Set("User-Agent", "git-k8s")
	req.Header.Set("X-GitHub-Api-Version", "2026-03-10")
	if in != nil {
		req.Header.Set("Content-Type", "application/json")
	}
	resp, err := githubClient.Do(req)
	if err != nil {
		return err
	}
	defer resp.Body.Close()
	b, err := io.ReadAll(io.LimitReader(resp.Body, 4<<20))
	if err != nil {
		return err
	}
	if resp.StatusCode/100 == 2 {
		if out == nil {
			return nil
		}
		return json.Unmarshal(b, out)
	}
	var e struct {
		Message string `json:"message"`
	}
	json.Unmarshal(b, &e)
	if wait, ok := rateLimitWait(resp, e.Message, gh.now()); ok {
		return &rateLimited{wait: wait}
	}
	return &githubError{resp.StatusCode, fmt.Sprintf("GitHub answered %s %s with %s: %s", method, req.URL.Path, resp.Status, e.Message)}
}

// rateLimitWait reports whether resp is a rate limit error, and how long
// GitHub asks to wait before the next request.
func rateLimitWait(resp *http.Response, message string, now time.Time) (time.Duration, bool) {
	if resp.StatusCode != http.StatusForbidden && resp.StatusCode != http.StatusTooManyRequests {
		return 0, false
	}
	if s, err := strconv.Atoi(resp.Header.Get("Retry-After")); err == nil {
		return max(time.Duration(s)*time.Second, time.Second), true
	}
	exhausted := resp.Header.Get("X-RateLimit-Remaining") == "0"
	if reset, err := strconv.ParseInt(resp.Header.Get("X-RateLimit-Reset"), 10, 64); exhausted && err == nil {
		return max(time.Unix(reset, 0).Sub(now), time.Second), true
	}
	if exhausted || resp.StatusCode == http.StatusTooManyRequests || strings.Contains(strings.ToLower(message), "rate limit") {
		// Without a time, GitHub says to wait at least a minute.
		return time.Minute, true
	}
	return 0, false
}

// reportCheckRuns sets the CheckRunsTokenIssued condition, which says
// whether Octo STS issues a token for the repository's check-runs identity,
// or removes it when the repository has no such identity. The check-runs
// controller's errors don't block landings and appear only in its logs, so
// this shows a trust policy that doesn't work.
func reportCheckRuns(ctx context.Context, repo *gitk8s.GitRepository) {
	const typ = "CheckRunsTokenIssued"
	sts := repo.Spec.OctoSTS
	if sts == nil || sts.CheckRunsIdentity == "" {
		repo.Status.Conditions = slices.DeleteFunc(repo.Status.Conditions, func(c kube.Condition) bool { return c.Type == typ })
		return
	}
	c := kube.Condition{Type: typ, Status: kube.True, Reason: "Issued", Message: "Octo STS issued a token for identity " + sts.CheckRunsIdentity}
	if _, _, err := credentials.GitHubAPI(ctx, &gitk8s.Repository{Object: repo.Object, Spec: repo.Spec}, sts.CheckRunsIdentity); err != nil {
		c.Status, c.Reason, c.Message = kube.False, "ExchangeFailed", err.Error()
	}
	kube.SetCondition(&repo.Status.Conditions, c)
}
