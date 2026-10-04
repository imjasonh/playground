package credentials

import (
	"context"
	"encoding/json"
	"errors"
	"flag"
	"fmt"
	"io"
	"net/http"
	"net/url"
	"regexp"
	"strings"
	"sync"
	"time"

	gitk8s "github.com/imjasonh/playground/git-k8s"
	"github.com/imjasonh/playground/git-k8s/internal/git"
	"github.com/imjasonh/playground/kube"
)

// fakeGitHub is a flag and not a GitRepository field so that only whoever
// installs a program, and no tenant, can send its service account tokens to
// another server.
var fakeGitHub = flag.String("fake-github", "", "base URL of a fake GitHub and Octo STS, for tests")

// The audience of the service account tokens that a program sends to Octo
// STS is audiencePrefix and the GitRepository's namespace. A program's
// tokens are otherwise the same for every GitRepository, so a trust policy
// that requires one namespace's audience keeps GitRepositories in other
// namespaces from using its identity.
const audiencePrefix = "octo-sts.dev/"

const (
	// GitHub's installation tokens last an hour, and Octo STS doesn't say
	// when the ones it issues expire.
	tokenLifetime = time.Hour
	// A token is replaced when it has less than refreshBefore left. When
	// the exchange fails, a token with more than minRemaining left is used
	// until it succeeds.
	refreshBefore = 10 * time.Minute
	minRemaining  = time.Minute
	// A failed exchange is reported again for retryAfter instead of asking
	// Octo STS on every reconcile of a misconfigured repository.
	retryAfter = 30 * time.Second
)

var client = &http.Client{Timeout: 30 * time.Second}

// now is time.Now, except in tests.
var now = time.Now

// github is where a program finds GitHub and Octo STS.
type github struct {
	// web is the base URL of repositories, exchange is Octo STS's token
	// exchange, and api is the base URL of GitHub's REST API.
	web, exchange, api string
}

func endpoints() github {
	if base := strings.TrimSuffix(*fakeGitHub, "/"); base != "" {
		return github{web: base, exchange: base + "/sts/exchange", api: base + "/api/v3"}
	}
	return github{web: "https://github.com", exchange: "https://octo-sts.dev/sts/exchange", api: "https://api.github.com"}
}

var namePattern = regexp.MustCompile(`^[A-Za-z0-9_.-]+$`)

func validName(s string) bool {
	return namePattern.MatchString(s) && s != "." && s != ".."
}

// scope returns the OWNER/REPO of a repository's URL, which is what Octo
// STS scopes a token to.
func (gh github) scope(rawURL string) (string, error) {
	path, ok := strings.CutPrefix(rawURL, gh.web+"/")
	owner, repo, _ := strings.Cut(strings.TrimSuffix(strings.TrimSuffix(path, "/"), ".git"), "/")
	if !ok || !validName(owner) || !validName(repo) {
		return "", fmt.Errorf("Octo STS needs a URL of the form %s/OWNER/REPO, not %s", gh.web, rawURL)
	}
	return owner + "/" + repo, nil
}

// GitHubAPI returns the REST API URL of a repository on GitHub, such as
// https://api.github.com/repos/OWNER/REPO, and a token for an Octo STS
// identity, the name of a trust policy in the repository. Like Remote, it
// must run in a reconcile.
func GitHubAPI(ctx context.Context, repo *gitk8s.Repository, identity string) (apiURL, token string, err error) {
	gh := endpoints()
	scope, err := gh.scope(repo.Spec.URL)
	if err != nil {
		return "", "", kube.Permanent(err)
	}
	if token, err = gitHubToken(ctx, gh, tokenKey{gh.exchange, audiencePrefix + repo.Namespace, scope, identity}); err != nil {
		return "", "", fmt.Errorf("getting a GitHub token for Octo STS identity %s in %s: %w", identity, scope, err)
	}
	return gh.api + "/repos/" + scope, token, nil
}

func octoSTSRemote(ctx context.Context, repo *gitk8s.Repository) (git.Remote, error) {
	r := git.Remote{URL: repo.Spec.URL}
	if repo.Spec.SecretRef != nil {
		return r, kube.Permanent(errors.New("set secretRef or octoSTS.gitIdentity, not both"))
	}
	_, token, err := GitHubAPI(ctx, repo, repo.Spec.OctoSTS.GitIdentity)
	if err != nil {
		return r, err
	}
	r.Auth = &git.Auth{Username: "x-access-token", Password: token}
	return r, nil
}

type tokenKey struct{ exchange, audience, scope, identity string }

// cachedToken is a GitHub token and the last failed exchange for one key.
type cachedToken struct {
	mu      sync.Mutex
	value   string
	expires time.Time
	err     error
	retry   time.Time
}

var tokens struct {
	sync.Mutex
	m map[tokenKey]*cachedToken
}

// gitHubToken returns a GitHub token from Octo STS, exchanging one only
// when the last one is about to expire.
func gitHubToken(ctx context.Context, gh github, k tokenKey) (string, error) {
	tokens.Lock()
	t := tokens.m[k]
	if t == nil {
		for key, old := range tokens.m {
			if old.mu.TryLock() {
				if at := now(); !at.Before(old.expires) && !at.Before(old.retry) {
					delete(tokens.m, key)
				}
				old.mu.Unlock()
			}
		}
		if tokens.m == nil {
			tokens.m = map[tokenKey]*cachedToken{}
		}
		t = &cachedToken{}
		tokens.m[k] = t
	}
	tokens.Unlock()

	t.mu.Lock()
	defer t.mu.Unlock()
	at := now()
	if t.value != "" && at.Before(t.expires.Add(-refreshBefore)) {
		return t.value, nil
	}
	err := t.err
	if !at.Before(t.retry) {
		var value string
		var expires time.Time
		if value, expires, err = exchange(ctx, gh, k); err == nil {
			t.value, t.expires, t.err, t.retry = value, expires, nil, time.Time{}
			return value, nil
		}
		if ctx.Err() == nil {
			t.err, t.retry = err, at.Add(retryAfter)
		}
	}
	if t.value != "" && at.Before(t.expires.Add(-minRemaining)) {
		return t.value, nil
	}
	return "", err
}

// exchange sends Octo STS a new token for the program's service account and
// returns the GitHub token that it answers with.
func exchange(ctx context.Context, gh github, k tokenKey) (string, time.Time, error) {
	start := now()
	sa, _, err := kube.RequestToken(ctx, k.audience)
	if err != nil {
		return "", time.Time{}, err
	}
	u := gh.exchange + "?" + url.Values{"scopes": {k.scope}, "identity": {k.identity}}.Encode()
	req, err := http.NewRequestWithContext(ctx, http.MethodGet, u, nil)
	if err != nil {
		return "", time.Time{}, err
	}
	req.Header.Set("Authorization", "Bearer "+sa)
	req.Header.Set("User-Agent", "git-k8s")
	resp, err := client.Do(req)
	if err != nil {
		return "", time.Time{}, err
	}
	defer resp.Body.Close()
	body, err := io.ReadAll(io.LimitReader(resp.Body, 1<<20))
	if err != nil {
		return "", time.Time{}, err
	}
	if resp.StatusCode != http.StatusOK {
		return "", time.Time{}, fmt.Errorf("Octo STS answered %s: %s", resp.Status, errorMessage(body))
	}
	var out struct {
		Token  string    `json:"token"`
		Expiry time.Time `json:"expiry"`
	}
	if err := json.Unmarshal(body, &out); err != nil || out.Token == "" {
		return "", time.Time{}, errors.New("Octo STS answered without a token")
	}
	expires := start.Add(tokenLifetime)
	if !out.Expiry.IsZero() && out.Expiry.Before(expires) {
		expires = out.Expiry
	}
	return out.Token, expires, nil
}

// errorMessage returns the message of an error that Octo STS answered with,
// which is JSON unless something in between answered instead.
func errorMessage(body []byte) string {
	var e struct {
		Message string `json:"message"`
	}
	if json.Unmarshal(body, &e) == nil && e.Message != "" {
		return e.Message
	}
	msg := strings.TrimSpace(string(body))
	if len(msg) > 300 {
		msg = strings.ToValidUTF8(msg[:300], "") + "..."
	}
	return msg
}
