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
// git-k8s/CHECK, and branches at the same commit share it, so it shows the
// result that changed last. The controller updates it as the result
// changes, and creates another when a check that finished starts again.
// Nothing on GitHub changes a result.
type checkRuns struct {
	// now is time.Now, except in tests.
	now func() time.Time

	mu sync.Mutex
	// repos holds what the controller knows of each repository's check
	// runs, by namespace and name, until the GitRepository is gone or names
	// no check-runs identity.
	repos map[string]*repoRuns
	// paused holds when each repository owner's rate limit ends. GitHub
	// limits each installation of a GitHub App, and an installation is one
	// owner's. With several apps, the limit of one app's installation
	// pauses the owner's check runs for every app.
	paused map[string]time.Time
}

// appKey is a repository's REST API URL and an Octo STS identity. Octo STS
// issues their tokens for one GitHub App at a time.
type appKey struct{ repo, identity string }

// repoRuns is what the controller knows of one repository's check runs,
// which it keeps only in memory. So one replica has to reconcile all of
// the repository's branches, and the program can't run with -shards. A
// reconcile holds the lock from its first request to GitHub to its last,
// because the repository's branches share check runs, and a reconcile
// decides what to send from what the others sent.
type repoRuns struct {
	// locked holds a value while a reconcile holds the lock. Unlike a
	// mutex, a channel lets a reconcile stop waiting when its context ends.
	locked chan struct{}
	// app is the ID of the GitHub App that the tokens for appKey act for,
	// once the controller creates or updates a check run with them, or 0.
	// GitHub lets only the app that created a check run update it, so the
	// controller looks only for that app's check runs. Octo STS with
	// several GitHub Apps can route each repository and identity to a
	// different app, and to another app later.
	app    int64
	appKey appKey
	// results holds the result that each branch last published for each
	// check.
	results map[branchCheck]branchResult
	// runs holds the check run that GitHub shows for each check on each
	// commit, and what the controller last wrote or found there, so that a
	// result that stays the same costs no requests.
	runs map[commitCheck]shownRun
	// seq counts the changes to results.
	seq int64
}

type branchCheck struct{ branch, check string }

type commitCheck struct{ commit, check string }

type branchResult struct {
	commit string
	shows  runState
	// seq is the repository's seq when the result last changed, so a
	// result with a higher seq changed later.
	seq int64
}

type shownRun struct {
	id    int64
	shows runState
	// by is the branch whose result the check run shows, so that the check
	// run is settled when that branch leaves the commit, or "" when nothing
	// has to settle the check run, as after a cancellation.
	by string
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

var githubClient = &http.Client{Timeout: 30 * time.Second}

func (c *checkRuns) clock() time.Time {
	if c.now != nil {
		return c.now()
	}
	return time.Now()
}

func (c *checkRuns) Reconcile(ctx context.Context, b *branchResults) error {
	key := b.Namespace + "/" + b.Spec.Repository
	repo := kube.Get[gitk8s.Repository](ctx, b.Namespace, b.Spec.Repository)
	publishing := repo != nil && repo.Spec.OctoSTS != nil && repo.Spec.OctoSTS.CheckRunsIdentity != ""
	var rr *repoRuns
	var listed []*branchResults
	if publishing {
		var err error
		if rr, err = c.lock(ctx, key); err != nil {
			return err
		}
		defer rr.unlock()
		// What a shared check run shows depends on every branch at its
		// commit, and listing the branches reconciles this one again when
		// any of them changes or goes away.
		listed = kube.List[branchResults](ctx, kube.InNamespace(b.Namespace), kube.MatchingLabels(map[string]string{gitk8s.RepositoryLabel: b.Spec.Repository}))
	}
	if ctx.Err() != nil {
		// When kube.Get or kube.List can't read, it returns nothing and
		// the framework tries the reconcile again. The reconcile stops so
		// that it doesn't forget the check runs of objects that it
		// couldn't read.
		return ctx.Err()
	}
	if !publishing {
		return c.forget(ctx, key)
	}
	branches := map[string]map[string]gitk8s.CheckResult{}
	for _, o := range listed {
		if o.Spec.Repository == b.Spec.Repository {
			branches[o.Name] = o.Status.Checks
		}
	}
	branches[b.Name] = b.Status.Checks
	if len(b.Status.Checks) == 0 && len(rr.results) == 0 && len(rr.runs) == 0 {
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
	if k := (appKey{apiURL, repo.Spec.OctoSTS.CheckRunsIdentity}); rr.appKey != k {
		rr.appKey, rr.app = k, 0
	}
	s := &runSync{repoRuns: rr, gh: &githubAPI{repo: apiURL, token: token, now: c.clock}, external: key, branches: branches}
	err = s.sync(ctx, b.Name)
	var limited *rateLimited
	if errors.As(err, &limited) {
		slog.Info("pausing check runs for GitHub's rate limit", "owner", path.Base(owner), "for", limited.wait)
		c.pause(owner, limited.wait)
		kube.RequeueAfter(ctx, spread(limited.wait))
		return nil
	}
	return err
}

// runSync makes one repository's check runs show its branches' results,
// while the reconcile holds the repository's lock.
type runSync struct {
	*repoRuns
	gh *githubAPI
	// external is the check runs' external ID, the repository's namespace
	// and name.
	external string
	// branches holds the check results of each of the repository's
	// GitBranches, by name.
	branches map[string]map[string]gitk8s.CheckResult
}

// sync publishes branch's results, and then settles the check runs of the
// branches that were deleted or dropped a check, and the check runs that
// show a result that the controller never published before its branch left
// the commit. It returns early at a rate limit or a request that GitHub
// didn't answer.
func (s *runSync) sync(ctx context.Context, branch string) error {
	var errs []error
	checks := s.branches[branch]
	for _, check := range slices.Sorted(maps.Keys(checks)) {
		if err := s.publish(ctx, branch, check, checks[check]); err != nil {
			errs = append(errs, fmt.Errorf("publishing the %s check run: %w", check, err))
			if stops(err) {
				return errors.Join(errs...)
			}
		}
	}
	departed := slices.SortedFunc(maps.Keys(s.results), func(a, b branchCheck) int {
		return cmp.Or(cmp.Compare(a.branch, b.branch), cmp.Compare(a.check, b.check))
	})
	for _, k := range departed {
		if s.branches[k.branch][k.check].Commit != "" {
			continue
		}
		if err := s.settle(ctx, commitCheck{s.results[k].commit, k.check}, s.left(k.branch, k.check)); err != nil {
			errs = append(errs, fmt.Errorf("completing %s's %s check run: %w", k.branch, k.check, err))
			if stops(err) {
				return errors.Join(errs...)
			}
			continue
		}
		delete(s.results, k)
	}
	orphans := slices.SortedFunc(maps.Keys(s.runs), func(a, b commitCheck) int {
		return cmp.Or(cmp.Compare(a.commit, b.commit), cmp.Compare(a.check, b.check))
	})
	for _, cc := range orphans {
		// settle can make a check run show the result of a branch that the
		// controller hasn't published yet, and then nothing in results
		// settles the check run when that branch leaves the commit.
		run := s.runs[cc]
		if run.by == "" || s.has(run.by, cc) || s.results[branchCheck{run.by, cc.check}].commit == cc.commit {
			continue
		}
		if err := s.settle(ctx, cc, s.left(run.by, cc.check)); err != nil {
			errs = append(errs, fmt.Errorf("completing the %s check run on %s: %w", cc.check, gitk8s.Short(cc.commit), err))
			if stops(err) {
				return errors.Join(errs...)
			}
		}
	}
	s.forgetRuns()
	return errors.Join(errs...)
}

// stops reports whether err ends a reconcile early, as a rate limit or a
// request that GitHub didn't answer does, so that a GitHub that doesn't
// answer holds the repository's lock for one request's timeout instead of
// one for each check.
func stops(err error) bool {
	var e *githubError
	return err != nil && !errors.As(err, &e)
}

// left returns why the check run that showed branch's result for check
// stops showing it, when the result is no longer for the check run's
// commit.
func (s *runSync) left(branch, check string) string {
	checks, ok := s.branches[branch]
	switch {
	case !ok:
		return "The branch was deleted before the check finished."
	case checks[check].Commit == "":
		return "The branch dropped the check before it finished."
	default:
		return fmt.Sprintf("The branch moved to %s before the check finished.", gitk8s.Short(checks[check].Commit))
	}
}

// publish makes the check run for one check's result on a branch show it,
// unless the result stayed the same and another branch's result at the
// commit changed later.
func (s *runSync) publish(ctx context.Context, branch, check string, res gitk8s.CheckResult) error {
	if res.Commit == "" {
		return nil
	}
	k, cc, want := branchCheck{branch, check}, commitCheck{res.Commit, check}, runFor(res)
	last, ok := s.results[k]
	if ok && last.commit != res.Commit {
		if err := s.settle(ctx, commitCheck{last.commit, check}, s.left(branch, check)); err != nil {
			return err
		}
	}
	changed := !ok || last.commit != res.Commit || last.shows != want
	run, known := s.runs[cc]
	// Until the controller knows its app, the check run that it finds can
	// be another app's, so the controller updates the check run even when
	// it shows want, and creates its own if GitHub refuses.
	trusted := known
	if !known {
		found, err := s.gh.find(ctx, checkRun{Name: "git-k8s/" + check, HeadSHA: res.Commit, ExternalID: s.external}, s.app)
		if err != nil {
			return err
		}
		if found != nil {
			run, known, trusted = shownRun{id: found.ID, shows: found.runState}, true, s.app != 0
		}
	}
	switch {
	case trusted && run.shows == want:
		s.runs[cc] = shownRun{id: run.id, shows: want, by: branch}
	case !changed && s.latest(cc) != branch:
		// Another branch at the commit changed its result later.
	default:
		if err := s.write(ctx, cc, run, known, want, branch); err != nil {
			return err
		}
	}
	if changed {
		s.seq++
		s.results[k] = branchResult{commit: res.Commit, shows: want, seq: s.seq}
	}
	return nil
}

// write makes the check run on cc's commit show want, which is branch's
// result. It updates run, if the controller knows it, or creates a check
// run.
func (s *runSync) write(ctx context.Context, cc commitCheck, run shownRun, known bool, want runState, branch string) error {
	// A check that starts again after it finished gets a new check run,
	// which GitHub shows instead of the old one, so the old one keeps its
	// result.
	if known && (run.shows.Status != "completed" || want.Status == "completed") {
		updated, err := s.gh.update(ctx, run.id, want)
		if err == nil {
			s.learnApp(updated.App.ID)
			s.runs[cc] = shownRun{id: run.id, shows: want, by: branch}
			return nil
		}
		// Until the controller knows its app, it can find another app's
		// check run, which only that app can update, and Octo STS can
		// issue later tokens for another app. And something else, such as
		// another replica, can complete a check run that the controller
		// last saw in progress, and GitHub's documentation doesn't say
		// whether GitHub starts it again.
		if !notOurs(err) && !reopening(err, want) {
			return err
		}
	}
	created, err := s.gh.create(ctx, checkRun{Name: "git-k8s/" + cc.check, HeadSHA: cc.commit, ExternalID: s.external, runState: want})
	if err != nil {
		return err
	}
	s.learnApp(created.App.ID)
	s.runs[cc] = shownRun{id: created.ID, shows: want, by: branch}
	return nil
}

// settle updates the check run on cc's commit after a branch left the
// commit or the check. Check controllers don't finish a check on a commit
// that the branch left, so the check run would otherwise stay in progress.
// It shows the result that changed last of the branches still at the
// commit, or is cancelled, with why as its summary, when none of them has
// a result for the check. settle returns the errors that trying again can
// fix, and logs the others.
func (s *runSync) settle(ctx context.Context, cc commitCheck, why string) error {
	run, ok := s.runs[cc]
	if !ok || s.has(run.by, cc) {
		return nil
	}
	by := s.latest(cc)
	want := runState{Status: "completed", Conclusion: "cancelled", Output: runOutput{Title: "Cancelled", Summary: why}}
	if by != "" {
		want = runFor(s.branches[by][cc.check])
	}
	switch {
	case run.shows == want:
	case run.shows.Status == "completed" && (by == "" || want.Status != "completed"):
		// A finished check's result still holds for the commit. A check run
		// doesn't start again, so for a result in progress, the other
		// branch's next reconcile creates one.
		by, want = "", run.shows
	default:
		updated, err := s.gh.update(ctx, run.id, want)
		if retryable(err) {
			return fmt.Errorf("updating the check run on %s: %w", gitk8s.Short(cc.commit), err)
		}
		if err != nil {
			slog.Warn("couldn't update a check run that a branch left", "repository", s.external, "check", cc.check, "commit", cc.commit, "id", run.id, "error", err)
			by, want = "", run.shows
			break
		}
		s.learnApp(updated.App.ID)
	}
	s.runs[cc] = shownRun{id: run.id, shows: want, by: by}
	return nil
}

// latest returns the branch at cc's commit whose result for cc's check
// changed last, or "" when no branch at the commit has a result for the
// check. A result that the controller hasn't published yet counts as the
// oldest, and of several such results, the one of the branch whose name
// sorts first counts.
func (s *runSync) latest(cc commitCheck) string {
	branch, seq := "", int64(-1)
	for _, name := range slices.Sorted(maps.Keys(s.branches)) {
		if !s.has(name, cc) {
			continue
		}
		var n int64
		if r, ok := s.results[branchCheck{name, cc.check}]; ok && r.commit == cc.commit {
			n = r.seq
		}
		if n > seq {
			branch, seq = name, n
		}
	}
	return branch
}

// has reports whether branch's result for cc's check is for cc's commit.
func (s *runSync) has(branch string, cc commitCheck) bool {
	return s.branches[branch][cc.check].Commit == cc.commit
}

// forgetRuns forgets the check runs on commits that no branch's result is
// for, unless a branch still has to settle them. If a result is for the
// commit again, the controller finds its check run on GitHub.
func (s *runSync) forgetRuns() {
	keep := map[commitCheck]bool{}
	for k, r := range s.results {
		keep[commitCheck{r.commit, k.check}] = true
	}
	for _, checks := range s.branches {
		for check, res := range checks {
			keep[commitCheck{res.Commit, check}] = true
		}
	}
	maps.DeleteFunc(s.runs, func(cc commitCheck, run shownRun) bool { return !keep[cc] && run.by == "" })
}

// runFor returns what the check run for a result shows.
func runFor(res gitk8s.CheckResult) runState {
	s := runState{Status: "completed", Output: runOutput{Title: res.State, Summary: res.State}}
	if res.Message != "" {
		s.Output.Summary = codeBlock(res.Message)
	}
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
		outputs = append(outputs, fmt.Sprintf("%s: %s", k, res.Outputs[k]))
	}
	if len(outputs) > 0 {
		s.Output.Text = codeBlock(strings.Join(outputs, "\n"))
	}
	return s
}

// maxOutput is the length that GitHub allows in a check run's summary and
// text. GitHub counts characters, so maxOutput bytes always fit.
const maxOutput = 65535

// codeBlock returns s as a Markdown code block that fits in a check run's
// summary or text, so that GitHub shows s as it is. The fence is longer than
// any run of backticks in s, so nothing in s can end the block.
func codeBlock(s string) string {
	longest, run := 0, 0
	for i := range len(s) {
		run++
		if s[i] != '`' {
			run = 0
		}
		longest = max(longest, run)
	}
	fence := strings.Repeat("`", max(longest+1, 3))
	if room := maxOutput - 2*len(fence) - 2; len(s) > room {
		// Cutting s can shorten its runs of backticks, and so the fence.
		n := max(room, len(s)/2)
		return codeBlock(strings.ToValidUTF8(s[:n-3], "") + "...")
	}
	return fence + "\n" + s + "\n" + fence
}

// repository returns what the controller knows of a repository's check
// runs, by namespace and name.
func (c *checkRuns) repository(key string) *repoRuns {
	c.mu.Lock()
	defer c.mu.Unlock()
	if c.repos == nil {
		c.repos = map[string]*repoRuns{}
	}
	if c.repos[key] == nil {
		c.repos[key] = &repoRuns{locked: make(chan struct{}, 1), results: map[branchCheck]branchResult{}, runs: map[commitCheck]shownRun{}}
	}
	return c.repos[key]
}

// lock returns what the controller knows of a repository's check runs, by
// namespace and name, once it holds the repository's lock.
func (c *checkRuns) lock(ctx context.Context, key string) (*repoRuns, error) {
	for {
		rr := c.repository(key)
		if err := rr.lock(ctx); err != nil {
			return nil, err
		}
		c.mu.Lock()
		current := c.repos[key] == rr
		c.mu.Unlock()
		if current {
			return rr, nil
		}
		// forget dropped rr while the reconcile waited for its lock.
		rr.unlock()
	}
}

// lock waits for rr's lock until ctx ends.
func (rr *repoRuns) lock(ctx context.Context) error {
	select {
	case rr.locked <- struct{}{}:
		return nil
	case <-ctx.Done():
		return ctx.Err()
	}
}

func (rr *repoRuns) unlock() { <-rr.locked }

// forget forgets a repository's check runs, when its GitRepository is gone
// or names no check-runs identity.
func (c *checkRuns) forget(ctx context.Context, key string) error {
	c.mu.Lock()
	_, known := c.repos[key]
	c.mu.Unlock()
	if !known {
		return nil
	}
	// The reconcile that holds the lock keeps using what the controller
	// knows, so forget drops it only once it holds the lock. Otherwise
	// another reconcile of the repository could start before that one ends.
	rr, err := c.lock(ctx, key)
	if err != nil {
		return err
	}
	defer rr.unlock()
	c.mu.Lock()
	defer c.mu.Unlock()
	delete(c.repos, key)
	return nil
}

// learnApp records that the tokens for rr's appKey act for app, the app of
// a check run that one of them created or updated.
func (rr *repoRuns) learnApp(app int64) {
	if app != 0 {
		rr.app = app
	}
}

func (c *checkRuns) pausedFor(owner string) time.Duration {
	c.mu.Lock()
	defer c.mu.Unlock()
	return c.paused[owner].Sub(c.clock())
}

func (c *checkRuns) pause(owner string, d time.Duration) {
	c.mu.Lock()
	defer c.mu.Unlock()
	now := c.clock()
	maps.DeleteFunc(c.paused, func(_ string, until time.Time) bool { return !until.After(now) })
	if c.paused == nil {
		c.paused = map[string]time.Time{}
	}
	c.paused[owner] = now.Add(d)
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

// reopening reports whether err is GitHub refusing to update a check run
// to want because want would start the completed check run again.
func reopening(err error, want runState) bool {
	var e *githubError
	return want.Status != "completed" && errors.As(err, &e) && e.status == http.StatusUnprocessableEntity
}

// retryable reports whether trying again can fix err, as for a rate limit,
// an error on GitHub's side, or a request that didn't reach GitHub.
func retryable(err error) bool {
	var e *githubError
	return err != nil && (!errors.As(err, &e) || e.status >= http.StatusInternalServerError)
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

func (gh *githubAPI) update(ctx context.Context, id int64, s runState) (checkRun, error) {
	var updated checkRun
	err := gh.do(ctx, http.MethodPatch, "/check-runs/"+strconv.FormatInt(id, 10), s, &updated)
	return updated, err
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
