package gittest

import (
	"fmt"
	"os"
	"os/exec"
	"path/filepath"
	"strings"
	"testing"

	gitk8s "github.com/imjasonh/playground/git-k8s"
	"github.com/imjasonh/playground/kube"
	"github.com/imjasonh/playground/kube/k8s"
)

// Signer is an SSH key that signs commits, and an allowed signers file that
// trusts it.
type Signer struct {
	// Email is the principal that the allowed signers file trusts the key
	// for.
	Email string
	// Key is the private key in OpenSSH format.
	Key []byte
	// AllowedSigners is the path of the allowed signers file.
	AllowedSigners string
}

// NewSigner generates an Ed25519 key with ssh-keygen. It skips the test if
// ssh-keygen isn't installed.
func NewSigner(t testing.TB, email string) *Signer {
	t.Helper()
	if _, err := exec.LookPath("ssh-keygen"); err != nil {
		t.Skip("ssh-keygen isn't installed")
	}
	dir := t.TempDir()
	path := filepath.Join(dir, "key")
	if out, err := exec.Command("ssh-keygen", "-q", "-t", "ed25519", "-N", "", "-C", email, "-f", path).CombinedOutput(); err != nil {
		t.Fatalf("ssh-keygen: %v\n%s", err, out)
	}
	key, err := os.ReadFile(path)
	if err != nil {
		t.Fatal(err)
	}
	pub, err := os.ReadFile(path + ".pub")
	if err != nil {
		t.Fatal(err)
	}
	s := &Signer{Email: email, Key: key, AllowedSigners: filepath.Join(dir, "allowed_signers")}
	line := fmt.Sprintf("%s namespaces=\"git\" %s\n", email, strings.TrimSpace(string(pub)))
	if err := os.WriteFile(s.AllowedSigners, []byte(line), 0o644); err != nil {
		t.Fatal(err)
	}
	return s
}

// Sign returns a Secret in repo's namespace that holds the key, and points
// repo's signingKeyRef at it.
func (s *Signer) Sign(repo *gitk8s.GitRepository) *k8s.Secret {
	secret := &k8s.Secret{
		Object: kube.Meta(repo.Name+"-signing", nil),
		Type:   "kubernetes.io/ssh-auth",
		Data:   map[string][]byte{"ssh-privatekey": s.Key},
	}
	secret.Namespace = repo.Namespace
	repo.Spec.SigningKeyRef = &gitk8s.SecretRef{Name: secret.Name}
	return secret
}

// Verify checks commit in the repository at dir with git verify-commit and
// the allowed signers file. It returns an error unless the commit has a good
// signature from the key and its committer email is s.Email, which forges
// such as GitHub require to mark a commit verified.
func (s *Signer) Verify(dir, commit string) error {
	cfg := "gpg.ssh.allowedSignersFile=" + s.AllowedSigners
	if out, err := s.git(dir, "-c", cfg, "verify-commit", commit); err != nil {
		return fmt.Errorf("git verify-commit %s: %v: %s", commit, err, out)
	}
	got, err := s.git(dir, "-c", cfg, "log", "-1", "--format=%GS %ce", commit)
	if err != nil {
		return fmt.Errorf("git log %s: %v: %s", commit, err, got)
	}
	if want := s.Email + " " + s.Email; got != want {
		return fmt.Errorf("commit %s has signer and committer %q, want %q", commit, got, want)
	}
	return nil
}

func (s *Signer) git(dir string, args ...string) (string, error) {
	cmd := exec.Command("git", append([]string{"-C", dir}, args...)...)
	cmd.Env = append(os.Environ(), "GIT_CONFIG_NOSYSTEM=1", "GIT_CONFIG_GLOBAL="+os.DevNull)
	out, err := cmd.CombinedOutput()
	return strings.TrimSpace(string(out)), err
}
