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

// Config sets an option in the configuration of a repository on the
// server, such as receive.denyDeletes. The repository must exist.
func (s *Server) Config(t testing.TB, repo, key, value string) {
	t.Helper()
	cmd := exec.Command("git", "-C", filepath.Join(s.Root, repo+".git"), "config", key, value)
	cmd.Env = append(os.Environ(), "GIT_CONFIG_NOSYSTEM=1", "GIT_CONFIG_GLOBAL="+os.DevNull)
	if out, err := cmd.CombinedOutput(); err != nil {
		t.Fatalf("git config %s: %v\n%s", key, err, out)
	}
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
	// Commands such as commit and fetch start automatic maintenance, which
	// runs in the background and can still be writing to the repository
	// when the test's cleanup removes it.
	w.Git("config", "maintenance.auto", "false")
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
		"GIT_ALLOW_PROTOCOL="+git.AllowProtocol,
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

// Bomb commits a tree on top of HEAD that adds 10^(depth+1) Go files under
// dir, a directory at the top, and returns the commit. Each file has the
// same small contents and a name of about 120 bytes. The new objects take
// a few kilobytes, because each level of the tree lists one subtree ten
// times. Bomb leaves the index and the working tree as they are, so commit
// nothing on top of it.
func (w *Work) Bomb(dir string, depth int) string {
	w.t.Helper()
	blob := filepath.Join(w.t.TempDir(), "bomb.go")
	if err := os.WriteFile(blob, []byte("package bomb\n"), 0o644); err != nil {
		w.t.Fatal(err)
	}
	mktree := func(lines string) string {
		cmd := exec.Command("git", "mktree")
		cmd.Dir, cmd.Stdin = w.Dir, strings.NewReader(lines)
		cmd.Env = append(os.Environ(), "GIT_CONFIG_NOSYSTEM=1", "GIT_CONFIG_GLOBAL="+os.DevNull)
		out, err := cmd.Output()
		if err != nil {
			w.t.Fatalf("git mktree: %v", err)
		}
		return strings.TrimSpace(string(out))
	}
	ten := func(format, sha string) string {
		var lines strings.Builder
		for i := range 10 {
			fmt.Fprintf(&lines, format, sha, i)
		}
		return mktree(lines.String())
	}
	tree := ten("100644 blob %s\t"+strings.Repeat("x", 120)+"%d.go\n", w.Git("hash-object", "-w", blob))
	for range depth {
		tree = ten("040000 tree %s\td%d\n", tree)
	}
	top := w.Git("ls-tree", "HEAD")
	if top != "" {
		top += "\n"
	}
	commit := w.Git("commit-tree", "-p", "HEAD", "-m", "bomb", mktree(top+"040000 tree "+tree+"\t"+dir+"\n"))
	w.Git("update-ref", "HEAD", commit)
	return commit
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

// PushRef pushes the current commit to any ref, such as one under
// refs/git-k8s/, forcing the update.
func (w *Work) PushRef(ref string) {
	w.t.Helper()
	w.Git("push", "--quiet", "--force", "--end-of-options", w.remote, "HEAD:"+ref)
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
