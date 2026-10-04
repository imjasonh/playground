// Package gittest runs a git server and makes commits for tests.
package gittest

import (
	"context"
	"fmt"
	"net/http/httptest"
	"net/url"
	"os"
	"os/exec"
	"path/filepath"
	"strings"
	"testing"

	gitk8s "github.com/imjasonh/playground/git-k8s"
	"github.com/imjasonh/playground/git-k8s/internal/git"
	"github.com/imjasonh/playground/git-k8s/internal/gitserver"
	"github.com/imjasonh/playground/kube"
	"github.com/imjasonh/playground/kube/k8s"
)

// Server is a smart HTTP git server for one test.
type Server struct {
	// URL is the server's base URL, without credentials.
	URL string
	// Username and Password are the credentials it requires, if Password
	// is set.
	Username, Password string
	// Root holds the repositories, each at Root/NAME.git from the first
	// push to it.
	Root string
}

// NewServer starts a git server that requires password, unless password is
// empty. The test's cleanup stops it.
func NewServer(t testing.TB, password string) *Server {
	t.Helper()
	if _, err := exec.LookPath("git"); err != nil {
		t.Skip("git isn't installed")
	}
	s := &gitserver.Server{Root: t.TempDir(), Username: "git-k8s", Password: password}
	hs := httptest.NewServer(s)
	t.Cleanup(hs.Close)
	return &Server{URL: hs.URL, Username: s.Username, Password: password, Root: s.Root}
}

// Remote returns the URL and credentials of a repository on the server.
func (s *Server) Remote(repo string) git.Remote {
	r := git.Remote{URL: s.URL + "/" + repo + ".git"}
	if s.Password != "" {
		r.Auth = &git.Auth{Username: s.Username, Password: s.Password}
	}
	return r
}

// RemoteFor returns the remote of the repository on the server with the
// GitRepository's name. In tests, set checks.Check.Remote to it in place of
// the mirror.
func (s *Server) RemoteFor(_ context.Context, repo *gitk8s.Repository) (git.Remote, error) {
	return s.Remote(repo.Name), nil
}

// Repository returns a GitRepository in namespace default for repo on the
// server, with rules, and the Secret that holds its credentials.
func (s *Server) Repository(repo string, rules ...gitk8s.BranchRule) (*gitk8s.GitRepository, *k8s.Secret) {
	r := &gitk8s.GitRepository{
		Object: kube.Meta(repo, nil),
		Spec:   gitk8s.GitRepositorySpec{URL: s.Remote(repo).URL, PollInterval: "30s", Branches: rules},
	}
	r.Namespace = "default"
	secret := &k8s.Secret{
		Object: kube.Meta(repo+"-creds", nil),
		Data:   map[string][]byte{"username": []byte(s.Username), "password": []byte(s.Password)},
	}
	secret.Namespace = "default"
	if s.Password != "" {
		r.Spec.SecretRef = &gitk8s.SecretRef{Name: secret.Name}
	}
	return r, secret
}

// Heads lists a repository's branches.
func (s *Server) Heads(t testing.TB, repo string) map[string]string {
	t.Helper()
	heads, err := (&git.Git{}).LsRemote(t.Context(), s.Remote(repo))
	if err != nil {
		t.Fatal(err)
	}
	return heads
}

// Work is a working repository that pushes to one repository on a server.
type Work struct {
	t      testing.TB
	Dir    string
	remote string
}

// NewWork returns an empty working repository whose origin is repo on s.
func (s *Server) NewWork(t testing.TB, repo string) *Work {
	t.Helper()
	u, err := url.Parse(s.URL + "/" + repo + ".git")
	if err != nil {
		t.Fatal(err)
	}
	if s.Password != "" {
		u.User = url.UserPassword(s.Username, s.Password)
	}
	w := &Work{t: t, Dir: t.TempDir(), remote: u.String()}
	w.Git("init", "--quiet", "--initial-branch=main")
	return w
}

// Git runs git in the working repository and returns its trimmed output.
func (w *Work) Git(args ...string) string {
	w.t.Helper()
	out, err := w.TryGit(args...)
	if err != nil {
		w.t.Fatal(err)
	}
	return out
}

// TryGit runs git in the working repository and returns its trimmed output,
// and an error that holds the output if git fails.
func (w *Work) TryGit(args ...string) (string, error) {
	cmd := exec.Command("git", args...)
	cmd.Dir = w.Dir
	cmd.Env = append(os.Environ(),
		"GIT_CONFIG_NOSYSTEM=1", "GIT_CONFIG_GLOBAL="+os.DevNull, "GIT_TERMINAL_PROMPT=0",
		"GIT_AUTHOR_NAME=Test Author", "GIT_AUTHOR_EMAIL=author@example.com",
		"GIT_COMMITTER_NAME=Test Author", "GIT_COMMITTER_EMAIL=author@example.com",
		"GIT_AUTHOR_DATE=2026-01-02T03:04:05Z", "GIT_COMMITTER_DATE=2026-01-02T03:04:05Z",
	)
	out, err := cmd.CombinedOutput()
	if err != nil {
		return "", fmt.Errorf("git %s: %v\n%s", strings.Join(args, " "), err, out)
	}
	return strings.TrimSpace(string(out)), nil
}

// Write writes a file in the working tree.
func (w *Work) Write(path, content string) {
	w.t.Helper()
	full := filepath.Join(w.Dir, path)
	if err := os.MkdirAll(filepath.Dir(full), 0o755); err != nil {
		w.t.Fatal(err)
	}
	if err := os.WriteFile(full, []byte(content), 0o644); err != nil {
		w.t.Fatal(err)
	}
}

// Commit commits every change in the working tree and returns the commit.
func (w *Work) Commit(message string) string {
	w.t.Helper()
	w.Git("add", "-A")
	w.Git("commit", "--quiet", "--allow-empty", "-m", message)
	return w.Git("rev-parse", "HEAD")
}

// Branch switches to a new branch that starts at from.
func (w *Work) Branch(name, from string) {
	w.t.Helper()
	w.Git("checkout", "--quiet", "-B", name, from)
}

// Push pushes the current commit to a branch, forcing the update.
func (w *Work) Push(branch string) {
	w.t.Helper()
	w.Git("push", "--quiet", "--force", w.remote, "HEAD:refs/heads/"+branch)
}

// Delete deletes a branch from the repository.
func (w *Work) Delete(branch string) {
	w.t.Helper()
	w.Git("push", "--quiet", w.remote, ":refs/heads/"+branch)
}

// Fetch fetches a branch and returns the commit it points to.
func (w *Work) Fetch(branch string) string {
	w.t.Helper()
	w.Git("fetch", "--quiet", w.remote, "+refs/heads/"+branch+":refs/remotes/origin/"+branch)
	return w.Git("rev-parse", "refs/remotes/origin/"+branch)
}

// Show returns a file's contents at a commit.
func (w *Work) Show(commit, path string) string {
	w.t.Helper()
	return w.Git("show", commit+":"+path)
}
