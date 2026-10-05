package gitserver

import (
	"bytes"
	"cmp"
	"context"
	"crypto/rand"
	"crypto/subtle"
	"encoding/hex"
	"encoding/json"
	"fmt"
	"net/http"
	"os"
	"os/exec"
	"path/filepath"
	"regexp"
	"slices"
	"strconv"
	"strings"
	"sync"
	"time"
)

// GitHub fakes what git-k8s uses of GitHub and Octo STS, for tests: git over
// HTTP with installation tokens, Octo STS's token exchange at
// /sts/exchange, and the REST API for check runs under /api/v3. The
// repository OWNER/REPO is at Root/OWNER/REPO.git and URL path
// /OWNER/REPO.git. As with Server, a push creates a repository that doesn't
// exist yet, but only with the administrator's credentials.
//
// The exchange reads trust policies from the main branch. It reads them as
// JSON, which is also YAML that Octo STS reads, and supports the fields
// issuer, subject, subject_pattern, audience, and permissions.
//
// The tokens from the exchange act for the GitHub App OctoSTSApp, unless
// RouteApp routes them to another app, and the administrator acts for
// OtherApp. As on GitHub, a token can update only its app's check runs, but
// the administrator can update any.
type GitHub struct {
	// Root holds the repositories.
	Root string
	// Username and Password are an administrator's credentials, which can
	// fetch and push, and read and write check runs, in every repository.
	Username, Password string
	// AllowedSigners makes the repositories that the fake creates require
	// signed commits, as it does for Server.
	AllowedSigners string
	// Verify checks a bearer token that the exchange receives and returns
	// its claims.
	Verify func(ctx context.Context, token string) (Claims, error)

	mu        sync.Mutex
	grants    map[string]grant
	apps      map[route]int64
	runs      []*CheckRun
	exchanges []Exchange
	requests  []string
	limited   time.Duration
	failing   int
	reopen    bool
}

// Claims are what the exchange checks against a trust policy.
type Claims struct {
	Issuer, Subject string
	Audiences       []string
}

// Exchange is a token that the exchange issued.
type Exchange struct {
	Scope, Identity, Token string
}

// CheckRun is a check run, as the REST API sends it.
type CheckRun struct {
	ID         int64          `json:"id"`
	Name       string         `json:"name"`
	HeadSHA    string         `json:"head_sha"`
	ExternalID string         `json:"external_id"`
	Status     string         `json:"status"`
	Conclusion string         `json:"conclusion"`
	Output     CheckRunOutput `json:"output"`
	App        CheckRunApp    `json:"app"`
	repo       string
}

// CheckRunApp is the GitHub App that created a check run.
type CheckRunApp struct {
	ID int64 `json:"id"`
}

// The GitHub Apps that check runs belong to. SecondOctoSTSApp is for
// RouteApp.
const (
	OctoSTSApp       int64 = 1
	OtherApp         int64 = 2
	SecondOctoSTSApp int64 = 3
)

// CheckRunOutput is what a check run shows.
type CheckRunOutput struct {
	Title   string `json:"title"`
	Summary string `json:"summary"`
	Text    string `json:"text,omitempty"`
}

type grant struct {
	repo        string
	permissions map[string]string
	expires     time.Time
	app         int64
}

// route is the scope and identity of a token exchange.
type route struct{ scope, identity string }

const githubName = `[A-Za-z0-9][-A-Za-z0-9_.]*`

var (
	nameRE      = regexp.MustCompile(`^` + githubName + `$`)
	githubGitRE = regexp.MustCompile(`^/(` + githubName + `)/(` + githubName + `\.git)/(info/refs|git-upload-pack|git-receive-pack)$`)
	githubAPIRE = regexp.MustCompile(`^/api/v3/repos/(` + githubName + `)/(` + githubName + `)/(?:check-runs(?:/([0-9]+))?|commits/([0-9a-f]{40})/check-runs)$`)
	gitEnv      = []string{"GIT_CONFIG_NOSYSTEM=1", "GIT_CONFIG_GLOBAL=" + os.DevNull, "GIT_ALLOW_PROTOCOL=http:https:git:ssh"}
)

func (g *GitHub) ServeHTTP(w http.ResponseWriter, r *http.Request) {
	switch {
	case r.URL.Path == "/sts/exchange":
		g.exchange(w, r)
	case strings.HasPrefix(r.URL.Path, "/api/"):
		g.api(w, r)
	default:
		g.git(w, r)
	}
}

// Exchanges lists the tokens that the exchange issued, in order.
func (g *GitHub) Exchanges() []Exchange {
	g.mu.Lock()
	defer g.mu.Unlock()
	return slices.Clone(g.exchanges)
}

// CheckRuns lists the check runs of repo, OWNER/REPO, oldest first.
func (g *GitHub) CheckRuns(repo string) []CheckRun {
	g.mu.Lock()
	defer g.mu.Unlock()
	var out []CheckRun
	for _, c := range g.runs {
		if c.repo == repo {
			out = append(out, *c)
		}
	}
	return out
}

// Requests lists the REST API requests that the server received, as
// "METHOD PATH".
func (g *GitHub) Requests() []string {
	g.mu.Lock()
	defer g.mu.Unlock()
	return slices.Clone(g.requests)
}

// RateLimit makes the server answer the next REST API request with
// GitHub's secondary rate limit error, which says to retry after d.
func (g *GitHub) RateLimit(d time.Duration) {
	g.mu.Lock()
	defer g.mu.Unlock()
	g.limited = d
}

// Fail makes the server answer the next REST API request with status.
func (g *GitHub) Fail(status int) {
	g.mu.Lock()
	defer g.mu.Unlock()
	g.failing = status
}

// RouteApp makes the exchange's tokens for scope, OWNER/REPO, and identity
// act for app, as Octo STS can route them when it has several GitHub Apps.
func (g *GitHub) RouteApp(scope, identity string, app int64) {
	g.mu.Lock()
	defer g.mu.Unlock()
	if g.apps == nil {
		g.apps = map[route]int64{}
	}
	g.apps[route{scope, identity}] = app
}

// AcceptReopening makes the server accept an update that starts a
// completed check run again, which clears the check run's conclusion.
// GitHub's documentation doesn't say whether GitHub accepts one, so the
// server refuses one unless a test calls AcceptReopening, and tests can run
// both ways.
func (g *GitHub) AcceptReopening() {
	g.mu.Lock()
	defer g.mu.Unlock()
	g.reopen = true
}

type trustPolicy struct {
	Issuer         string            `json:"issuer"`
	Subject        string            `json:"subject"`
	SubjectPattern string            `json:"subject_pattern"`
	Audience       string            `json:"audience"`
	Permissions    map[string]string `json:"permissions"`
}

// exchange answers as Octo STS does, with its messages.
func (g *GitHub) exchange(w http.ResponseWriter, r *http.Request) {
	q := r.URL.Query()
	scope, identity := cmp.Or(q.Get("scopes"), q.Get("scope")), q.Get("identity")
	auth := r.Header.Values("Authorization")
	if len(auth) != 1 {
		stsError(w, http.StatusUnauthorized, "expected exactly one authorization header")
		return
	}
	claims, err := g.Verify(r.Context(), strings.TrimPrefix(auth[0], "Bearer "))
	if err != nil {
		fmt.Fprintf(os.Stderr, "gitserver: exchange for %s %s: %v\n", scope, identity, err)
		stsError(w, http.StatusUnauthorized, "unable to verify bearer token")
		return
	}
	owner, repo, _ := strings.Cut(scope, "/")
	if !nameRE.MatchString(owner) || !nameRE.MatchString(repo) || !nameRE.MatchString(identity) {
		stsError(w, http.StatusBadRequest, "scope must be OWNER/REPO, and identity must be a single path segment")
		return
	}
	cmd := exec.Command("git", "--git-dir", filepath.Join(g.Root, owner, repo+".git"),
		"show", "--end-of-options", "refs/heads/main:.github/chainguard/"+identity+".sts.yaml")
	cmd.Env = append(os.Environ(), gitEnv...)
	b, err := cmd.Output()
	if err != nil {
		stsError(w, http.StatusNotFound, fmt.Sprintf("unable to find trust policy for %q", identity))
		return
	}
	d := json.NewDecoder(bytes.NewReader(b))
	d.DisallowUnknownFields()
	var p trustPolicy
	if err := d.Decode(&p); err != nil {
		stsError(w, http.StatusNotFound, fmt.Sprintf("unable to parse trust policy found for %q", identity))
		return
	}
	if msg := p.check(claims); msg != "" {
		stsError(w, http.StatusForbidden, msg)
		return
	}
	token := "ghs_" + randomHex()
	g.mu.Lock()
	if g.grants == nil {
		g.grants = map[string]grant{}
	}
	g.grants[token] = grant{repo: scope, permissions: p.Permissions, expires: time.Now().Add(time.Hour), app: cmp.Or(g.apps[route{scope, identity}], OctoSTSApp)}
	g.exchanges = append(g.exchanges, Exchange{Scope: scope, Identity: identity, Token: token})
	g.mu.Unlock()
	writeJSON(w, http.StatusOK, map[string]any{"token": token})
}

// check returns why claims don't satisfy the policy, or "".
func (p *trustPolicy) check(c Claims) string {
	if c.Issuer != p.Issuer {
		return fmt.Sprintf("trust policy: issuer %q did not match %q", c.Issuer, p.Issuer)
	}
	if p.SubjectPattern != "" {
		re, err := regexp.Compile("^(?:" + p.SubjectPattern + ")$")
		if err != nil || !re.MatchString(c.Subject) {
			return fmt.Sprintf("trust policy: subject %q did not match pattern %q", c.Subject, p.SubjectPattern)
		}
	} else if c.Subject != p.Subject {
		return fmt.Sprintf("trust policy: subject %q did not match %q", c.Subject, p.Subject)
	}
	if aud := cmp.Or(p.Audience, "octo-sts.dev"); !slices.Contains(c.Audiences, aud) {
		return fmt.Sprintf("trust policy: audience %q did not match any of %q", aud, c.Audiences)
	}
	return ""
}

func (g *GitHub) admin(r *http.Request) bool {
	user, pass, ok := r.BasicAuth()
	return ok && g.Password != "" &&
		subtle.ConstantTimeCompare([]byte(user), []byte(g.Username)) == 1 &&
		subtle.ConstantTimeCompare([]byte(pass), []byte(g.Password)) == 1
}

// allowed reports whether token may use permission at level, read or write,
// in repo. If not, it returns the HTTP status and message to answer with.
func (g *GitHub) allowed(token, repo, permission, level string) (int, string) {
	g.mu.Lock()
	gr, ok := g.grants[token]
	g.mu.Unlock()
	switch have := gr.permissions[permission]; {
	case token == "" || !ok || time.Now().After(gr.expires):
		return http.StatusUnauthorized, "Bad credentials"
	case gr.repo != repo:
		return http.StatusNotFound, "Not Found"
	case have != "write" && (level == "write" || have != "read"):
		return http.StatusForbidden, "Resource not accessible by integration"
	}
	return 0, ""
}

func (g *GitHub) git(w http.ResponseWriter, r *http.Request) {
	m := githubGitRE.FindStringSubmatch(r.URL.Path)
	if m == nil {
		http.NotFound(w, r)
		return
	}
	if !g.admin(r) {
		level := "read"
		if m[3] == "git-receive-pack" || r.URL.Query().Get("service") == "git-receive-pack" {
			level = "write"
		}
		user, token, _ := r.BasicAuth()
		if user != "x-access-token" {
			token = ""
		}
		if status, msg := g.allowed(token, m[1]+"/"+strings.TrimSuffix(m[2], ".git"), "contents", level); status != 0 {
			if status == http.StatusUnauthorized {
				w.Header().Set("WWW-Authenticate", `Basic realm="GitHub"`)
			}
			http.Error(w, msg, status)
			return
		}
		if _, err := os.Stat(filepath.Join(g.Root, m[1], m[2], "HEAD")); err != nil {
			http.NotFound(w, r)
			return
		}
	}
	r = r.Clone(r.Context())
	r.URL.Path, r.URL.RawPath = "/"+m[2]+"/"+m[3], ""
	(&Server{Root: filepath.Join(g.Root, m[1]), AllowedSigners: g.AllowedSigners}).ServeHTTP(w, r)
}

type checkRunRequest struct {
	Name       *string         `json:"name"`
	HeadSHA    string          `json:"head_sha"`
	ExternalID *string         `json:"external_id"`
	Status     *string         `json:"status"`
	Conclusion *string         `json:"conclusion"`
	Output     *CheckRunOutput `json:"output"`
}

func (g *GitHub) api(w http.ResponseWriter, r *http.Request) {
	g.mu.Lock()
	g.requests = append(g.requests, r.Method+" "+r.URL.Path)
	limited, failing := g.limited, g.failing
	g.limited, g.failing = 0, 0
	g.mu.Unlock()
	if limited > 0 {
		w.Header().Set("Retry-After", strconv.Itoa(int(limited.Seconds())))
		apiError(w, http.StatusForbidden, "You have exceeded a secondary rate limit. Please wait a few minutes before you try again.")
		return
	}
	if failing != 0 {
		apiError(w, failing, http.StatusText(failing))
		return
	}
	m := githubAPIRE.FindStringSubmatch(r.URL.Path)
	if m == nil {
		apiError(w, http.StatusNotFound, "Not Found")
		return
	}
	repo, id, sha := m[1]+"/"+m[2], m[3], m[4]
	level := "write"
	if r.Method == http.MethodGet {
		level = "read"
	}
	admin, app := g.admin(r), OctoSTSApp
	if admin {
		app = OtherApp
	} else {
		auth := r.Header.Get("Authorization")
		token, ok := strings.CutPrefix(auth, "Bearer ")
		if !ok {
			token, _ = strings.CutPrefix(auth, "token ")
		}
		if status, msg := g.allowed(token, repo, "checks", level); status != 0 {
			apiError(w, status, msg)
			return
		}
		g.mu.Lock()
		app = g.grants[token].app
		g.mu.Unlock()
	}
	switch {
	case sha != "" && r.Method == http.MethodGet:
		g.listCheckRuns(w, r, repo, sha)
	case sha == "" && id == "" && r.Method == http.MethodPost:
		g.writeCheckRun(w, r, repo, app, nil)
	case id != "" && r.Method == http.MethodPatch:
		n, _ := strconv.ParseInt(id, 10, 64)
		var old *CheckRun
		var owner int64
		g.mu.Lock()
		if i := slices.IndexFunc(g.runs, func(c *CheckRun) bool { return c.ID == n && c.repo == repo }); i >= 0 {
			old, owner = g.runs[i], g.runs[i].App.ID
		}
		g.mu.Unlock()
		switch {
		case old == nil:
			apiError(w, http.StatusNotFound, "Not Found")
		case !admin && owner != app:
			apiError(w, http.StatusForbidden, "Resource not accessible by integration")
		default:
			g.writeCheckRun(w, r, repo, app, old)
		}
	default:
		apiError(w, http.StatusNotFound, "Not Found")
	}
}

// writeCheckRun creates a check run for app, or updates old, with GitHub's
// validation of the request. Unless a test called AcceptReopening, it
// refuses an update that starts a completed check run again.
func (g *GitHub) writeCheckRun(w http.ResponseWriter, r *http.Request, repo string, app int64, old *CheckRun) {
	var in checkRunRequest
	if err := json.NewDecoder(r.Body).Decode(&in); err != nil {
		apiError(w, http.StatusBadRequest, "Problems parsing JSON")
		return
	}
	g.mu.Lock()
	defer g.mu.Unlock()
	c := &CheckRun{Status: "queued", App: CheckRunApp{ID: app}, repo: repo}
	if old != nil {
		c = new(CheckRun)
		*c = *old
	} else {
		cmd := exec.Command("git", "--git-dir", filepath.Join(g.Root, repo+".git"), "cat-file", "-e", "--end-of-options", in.HeadSHA+"^{commit}")
		cmd.Env = append(os.Environ(), gitEnv...)
		if in.Name == nil || *in.Name == "" || cmd.Run() != nil {
			apiError(w, http.StatusUnprocessableEntity, fmt.Sprintf("No commit found for SHA: %s", in.HeadSHA))
			return
		}
		c.ID, c.HeadSHA = int64(len(g.runs)+1), in.HeadSHA
	}
	set := func(field *string, value *string) {
		if value != nil {
			*field = *value
		}
	}
	set(&c.Name, in.Name)
	set(&c.ExternalID, in.ExternalID)
	set(&c.Status, in.Status)
	set(&c.Conclusion, in.Conclusion)
	switch {
	case in.Conclusion != nil:
		c.Status = "completed"
	case in.Status != nil && *in.Status != "completed":
		// A check run that's queued or in progress has no conclusion.
		c.Conclusion = ""
	}
	if in.Output != nil {
		c.Output = *in.Output
	}
	switch {
	case in.Status != nil && *in.Status == "completed" && in.Conclusion == nil:
		apiError(w, http.StatusUnprocessableEntity, "conclusion is required when status is completed")
	case old != nil && old.Status == "completed" && c.Status != "completed" && !g.reopen:
		apiError(w, http.StatusUnprocessableEntity, "a completed check run can't start again")
	case !slices.Contains([]string{"queued", "in_progress", "completed"}, c.Status):
		apiError(w, http.StatusUnprocessableEntity, fmt.Sprintf("status %q isn't valid", c.Status))
	case (c.Status == "completed") != (c.Conclusion != ""),
		c.Conclusion != "" && !slices.Contains([]string{"success", "failure", "neutral", "cancelled", "skipped", "timed_out", "action_required"}, c.Conclusion):
		apiError(w, http.StatusUnprocessableEntity, fmt.Sprintf("status %q and conclusion %q don't go together", c.Status, c.Conclusion))
	case in.Output != nil && (c.Output.Title == "" || c.Output.Summary == ""):
		apiError(w, http.StatusUnprocessableEntity, "output needs a title and a summary")
	case len(c.Output.Summary) > 65535 || len(c.Output.Text) > 65535:
		apiError(w, http.StatusUnprocessableEntity, "output.summary and output.text are limited to 65535 characters")
	case old != nil:
		*old = *c
		writeJSON(w, http.StatusOK, c)
	default:
		g.runs = append(g.runs, c)
		writeJSON(w, http.StatusCreated, c)
	}
}

func (g *GitHub) listCheckRuns(w http.ResponseWriter, r *http.Request, repo, sha string) {
	q := r.URL.Query()
	g.mu.Lock()
	defer g.mu.Unlock()
	runs := []*CheckRun{}
	seen := map[string]bool{}
	for _, c := range slices.Backward(g.runs) {
		if c.repo != repo || c.HeadSHA != sha || (q.Has("check_name") && c.Name != q.Get("check_name")) ||
			(q.Has("app_id") && strconv.FormatInt(c.App.ID, 10) != q.Get("app_id")) {
			continue
		}
		if q.Get("filter") != "all" && seen[c.Name] {
			continue
		}
		seen[c.Name] = true
		runs = append(runs, c)
	}
	// GitHub doesn't document the list's order. Listing the oldest first
	// catches a client that takes the first match as the newest.
	slices.Reverse(runs)
	writeJSON(w, http.StatusOK, map[string]any{"total_count": len(runs), "check_runs": runs})
}

func writeJSON(w http.ResponseWriter, status int, v any) {
	b, err := json.Marshal(v)
	if err != nil {
		http.Error(w, err.Error(), http.StatusInternalServerError)
		return
	}
	w.Header().Set("Content-Type", "application/json; charset=utf-8")
	w.WriteHeader(status)
	w.Write(append(b, '\n'))
}

// stsError answers with an error as Octo STS's gRPC gateway does.
func stsError(w http.ResponseWriter, status int, msg string) {
	codes := map[int]int{http.StatusBadRequest: 3, http.StatusUnauthorized: 16, http.StatusForbidden: 7, http.StatusNotFound: 5}
	writeJSON(w, status, map[string]any{"code": codes[status], "message": msg, "details": []any{}})
}

func apiError(w http.ResponseWriter, status int, msg string) {
	writeJSON(w, status, map[string]string{"message": msg, "documentation_url": "https://docs.github.com/rest"})
}

func randomHex() string {
	b := make([]byte, 18)
	rand.Read(b)
	return hex.EncodeToString(b)
}
