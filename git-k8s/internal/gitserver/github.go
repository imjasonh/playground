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
	"strings"
	"sync"
	"time"
)

// GitHub fakes what git-k8s uses of GitHub and Octo STS, for tests: git over
// HTTP with installation tokens, and Octo STS's token exchange at
// /sts/exchange. The repository OWNER/REPO is at Root/OWNER/REPO.git and URL
// path /OWNER/REPO.git. As with Server, a push creates a repository that
// doesn't exist yet, but only with the administrator's credentials.
//
// The exchange reads trust policies from the main branch. It reads them as
// JSON, which is also YAML that Octo STS reads, and supports the fields
// issuer, subject, subject_pattern, audience, and permissions.
type GitHub struct {
	// Root holds the repositories.
	Root string
	// Username and Password are an administrator's credentials, which can
	// fetch and push in every repository.
	Username, Password string
	// Verify checks a bearer token that the exchange receives and returns
	// its claims.
	Verify func(ctx context.Context, token string) (Claims, error)

	mu        sync.Mutex
	grants    map[string]grant
	exchanges []Exchange
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

type grant struct {
	repo        string
	permissions map[string]string
	expires     time.Time
}

const githubName = `[A-Za-z0-9][-A-Za-z0-9_.]*`

var (
	nameRE      = regexp.MustCompile(`^` + githubName + `$`)
	githubGitRE = regexp.MustCompile(`^/(` + githubName + `)/(` + githubName + `\.git)/(info/refs|git-upload-pack|git-receive-pack)$`)
)

func (g *GitHub) ServeHTTP(w http.ResponseWriter, r *http.Request) {
	switch {
	case r.URL.Path == "/sts/exchange":
		g.exchange(w, r)
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
		"show", "refs/heads/main:.github/chainguard/"+identity+".sts.yaml")
	cmd.Env = append(os.Environ(), "GIT_CONFIG_NOSYSTEM=1", "GIT_CONFIG_GLOBAL="+os.DevNull)
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
	g.grants[token] = grant{repo: scope, permissions: p.Permissions, expires: time.Now().Add(time.Hour)}
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
	(&Server{Root: filepath.Join(g.Root, m[1])}).ServeHTTP(w, r)
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

func randomHex() string {
	b := make([]byte, 18)
	rand.Read(b)
	return hex.EncodeToString(b)
}
