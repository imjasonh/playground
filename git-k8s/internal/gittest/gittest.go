// Package gittest runs a git server and makes commits for tests.
package gittest

import (
	"crypto/ed25519"
	"crypto/rand"
	"encoding/pem"
	"net"
	"net/http/httptest"
	"net/url"
	"os"
	"os/exec"
	"path/filepath"
	"strings"
	"testing"

	"golang.org/x/crypto/ssh"
	"golang.org/x/crypto/ssh/knownhosts"

	gitk8s "github.com/imjasonh/playground/git-k8s"
	"github.com/imjasonh/playground/git-k8s/internal/git"
	"github.com/imjasonh/playground/git-k8s/internal/gitserver"
	"github.com/imjasonh/playground/kube"
	"github.com/imjasonh/playground/kube/k8s"
)

// Server is a git server for one test, which serves smart HTTP or SSH.
type Server struct {
	// URL is the server's base URL, without credentials.
	URL string
	// Username and Password are the credentials it requires, if Password
	// is set.
	Username, Password string
	// SSH, for an SSH server, is the only client key that it accepts, and
	// its host key.
	SSH *git.SSHKey

	// sshCommand is a GIT_SSH_COMMAND that uses SSH.
	sshCommand string
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
	return &Server{URL: hs.URL, Username: s.Username, Password: password}
}

// NewSSHServer starts a git server that serves over SSH, with a new host
// key, and accepts only a new client key. The test's cleanup stops it.
func NewSSHServer(t testing.TB) *Server {
	t.Helper()
	for _, bin := range []string{"git", "ssh"} {
		if _, err := exec.LookPath(bin); err != nil {
			t.Skipf("%s isn't installed", bin)
		}
	}
	host, client := newKey(t), newKey(t)
	hostSigner, err := ssh.NewSignerFromKey(host)
	if err != nil {
		t.Fatal(err)
	}
	clientPublic, err := ssh.NewPublicKey(client.Public())
	if err != nil {
		t.Fatal(err)
	}
	block, err := ssh.MarshalPrivateKey(client, "")
	if err != nil {
		t.Fatal(err)
	}
	l, err := net.Listen("tcp", "127.0.0.1:0")
	if err != nil {
		t.Fatal(err)
	}
	t.Cleanup(func() { l.Close() })
	s := &gitserver.SSHServer{Root: t.TempDir(), HostKey: hostSigner, AuthorizedKeys: []ssh.PublicKey{clientPublic}}
	go s.Serve(l)

	key := &git.SSHKey{
		PrivateKey: pem.EncodeToMemory(block),
		KnownHosts: []byte(knownhosts.Line([]string{l.Addr().String()}, hostSigner.PublicKey()) + "\n"),
	}
	dir := t.TempDir()
	keyFile, hostsFile := filepath.Join(dir, "key"), filepath.Join(dir, "known_hosts")
	for file, data := range map[string][]byte{keyFile: key.PrivateKey, hostsFile: key.KnownHosts} {
		if err := os.WriteFile(file, data, 0o600); err != nil {
			t.Fatal(err)
		}
	}
	return &Server{URL: "ssh://git@" + l.Addr().String(), SSH: key, sshCommand: git.SSHCommand(keyFile, hostsFile)}
}

func newKey(t testing.TB) ed25519.PrivateKey {
	t.Helper()
	_, key, err := ed25519.GenerateKey(rand.Reader)
	if err != nil {
		t.Fatal(err)
	}
	return key
}

// Remote returns the URL and credentials of a repository on the server.
func (s *Server) Remote(repo string) git.Remote {
	r := git.Remote{URL: s.URL + "/" + repo + ".git"}
	if s.Password != "" {
		r.Auth = &git.Auth{Username: s.Username, Password: s.Password}
	}
	if s.SSH != nil {
		key := *s.SSH
		r.SSH = &key
	}
	return r
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
	if s.SSH != nil {
		secret.Data = map[string][]byte{"ssh-privatekey": s.SSH.PrivateKey, "known_hosts": s.SSH.KnownHosts}
	}
	secret.Namespace = "default"
	if s.Password != "" || s.SSH != nil {
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
	env    []string
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
	if s.sshCommand != "" {
		w.env = []string{"GIT_SSH_COMMAND=" + s.sshCommand}
	}
	w.Git("init", "--quiet", "--initial-branch=main")
	return w
}

// Git runs git in the working repository and returns its trimmed output.
func (w *Work) Git(args ...string) string {
	w.t.Helper()
	cmd := exec.Command("git", args...)
	cmd.Dir = w.Dir
	cmd.Env = append(os.Environ(),
		"GIT_CONFIG_NOSYSTEM=1", "GIT_CONFIG_GLOBAL="+os.DevNull,
		"GIT_AUTHOR_NAME=Test Author", "GIT_AUTHOR_EMAIL=author@example.com",
		"GIT_COMMITTER_NAME=Test Author", "GIT_COMMITTER_EMAIL=author@example.com",
		"GIT_AUTHOR_DATE=2026-01-02T03:04:05Z", "GIT_COMMITTER_DATE=2026-01-02T03:04:05Z",
	)
	cmd.Env = append(cmd.Env, w.env...)
	out, err := cmd.CombinedOutput()
	if err != nil {
		w.t.Fatalf("git %s: %v\n%s", strings.Join(args, " "), err, out)
	}
	return strings.TrimSpace(string(out))
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
