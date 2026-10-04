package gittest

import (
	"context"
	"encoding/json"
	"errors"
	"flag"
	"net/http/httptest"
	"os/exec"
	"strings"
	"testing"

	gitk8s "github.com/imjasonh/playground/git-k8s"
	"github.com/imjasonh/playground/git-k8s/internal/gitserver"
)

// The claims that a GitHub's token exchange finds in every token that
// kube.Fake's RequestToken returns.
const (
	Issuer   = "https://kubernetes.default.svc.cluster.local"
	Subject  = "system:serviceaccount:default:test"
	Audience = "octo-sts.dev/default"
)

// GitHub is a fake GitHub and Octo STS for one test. Its repositories
// belong to the owner acme, and its Server fetches and pushes with an
// administrator's credentials.
type GitHub struct {
	*Server
	// Fake is the server, which records the tokens it issued.
	Fake *gitserver.GitHub
}

// NewGitHub starts a fake GitHub and points the -fake-github flag at it
// until the test ends, so the test binary must link package credentials.
// The fake can't ask kube.Fake who a token belongs to, so its exchange
// takes any token that kube.Fake's RequestToken returns as one with the
// claims Issuer, Subject, and Audience. A test checks the audience that a
// token really has with kube.ReviewToken.
func NewGitHub(t testing.TB) *GitHub {
	t.Helper()
	if _, err := exec.LookPath("git"); err != nil {
		t.Skip("git isn't installed")
	}
	f := flag.Lookup("fake-github")
	if f == nil {
		t.Fatal("no -fake-github flag; the test must link package credentials")
	}
	fake := &gitserver.GitHub{
		Root:     t.TempDir(),
		Username: "git-k8s",
		Password: "pw",
		Verify: func(_ context.Context, token string) (gitserver.Claims, error) {
			if !strings.HasPrefix(token, "fake-token-") {
				return gitserver.Claims{}, errors.New("not a token from kube.Fake")
			}
			return gitserver.Claims{Issuer: Issuer, Subject: Subject, Audiences: []string{Audience}}, nil
		},
	}
	hs := httptest.NewServer(fake)
	t.Cleanup(hs.Close)
	old := f.Value.String()
	if err := f.Value.Set(hs.URL); err != nil {
		t.Fatal(err)
	}
	t.Cleanup(func() { f.Value.Set(old) })
	return &GitHub{Server: &Server{URL: hs.URL + "/acme", Username: fake.Username, Password: fake.Password}, Fake: fake}
}

// Repository returns a GitRepository in namespace default for acme/repo,
// with rules, that gets its credentials from the Octo STS identities in
// sts.
func (g *GitHub) Repository(repo string, sts gitk8s.OctoSTS, rules ...gitk8s.BranchRule) *gitk8s.GitRepository {
	r, _ := g.Server.Repository(repo, rules...)
	r.Spec.SecretRef = nil
	r.Spec.OctoSTS = &sts
	return r
}

// TrustPolicy returns a trust policy that grants permissions, such as
// {"contents": "write"}, to the tokens that kube.Fake's RequestToken
// returns for namespace default. Commit it to
// .github/chainguard/IDENTITY.sts.yaml on main.
func TrustPolicy(permissions map[string]string) string {
	b, err := json.Marshal(map[string]any{"issuer": Issuer, "subject": Subject, "audience": Audience, "permissions": permissions})
	if err != nil {
		panic(err)
	}
	return string(b)
}
