package git_test

import (
	"bytes"
	"encoding/base64"
	"encoding/pem"
	"errors"
	"fmt"
	"os"
	"os/exec"
	"path/filepath"
	"slices"
	"strings"
	"testing"

	"github.com/imjasonh/playground/git-k8s/internal/git"
	"github.com/imjasonh/playground/git-k8s/internal/gittest"
)

// fetchedCommit pushes a commit to a test server and returns a local
// repository that has fetched it, and the commit.
func fetchedCommit(t *testing.T) (*git.Repo, git.Commit, string) {
	t.Helper()
	srv := gittest.NewServer(t, "")
	w := srv.NewWork(t, "app")
	w.Write("a.txt", "one\n")
	head := w.Commit("base")
	w.Push("main")
	repo := fetched(t, srv, "main")
	c, err := repo.Commit(t.Context(), head)
	if err != nil {
		t.Fatal(err)
	}
	return repo, c, head
}

func TestCommitTreeSigns(t *testing.T) {
	signer := gittest.NewSigner(t, "git-k8s@example.com")
	repo, c, head := fetchedCommit(t)
	ctx := t.Context()
	id := git.Identity{Name: "git-k8s", Email: signer.Email}
	commit := func(key *git.SigningKey) string {
		t.Helper()
		sha, err := repo.CommitTree(ctx, c.Tree, []string{head}, "fix\n", id, c.Time, key)
		if err != nil {
			t.Fatal(err)
		}
		return sha
	}
	key, err := git.NewSigningKey(signer.Key)
	if err != nil {
		t.Fatal(err)
	}
	signed := commit(key)
	if err := signer.Verify(repo.Dir, signed); err != nil {
		t.Error(err)
	}
	if again := commit(key); again != signed {
		t.Errorf("signing isn't deterministic: %s then %s", signed, again)
	}

	// A key pasted with Windows line endings and no final newline is the
	// same key.
	pasted := strings.TrimSpace(strings.ReplaceAll(string(signer.Key), "\n", "\r\n"))
	if key, err := git.NewSigningKey([]byte(pasted)); err != nil {
		t.Error(err)
	} else if got := commit(key); got != signed {
		t.Errorf("the pasted key signed %s, want %s", got, signed)
	}

	if unsigned := commit(nil); unsigned == signed || signer.Verify(repo.Dir, unsigned) == nil {
		t.Errorf("the commit without a key, %s, verified", unsigned)
	}
	other, err := git.NewSigningKey(gittest.NewSigner(t, signer.Email).Key)
	if err != nil {
		t.Fatal(err)
	}
	if sha := commit(other); signer.Verify(repo.Dir, sha) == nil {
		t.Errorf("the commit signed with another key, %s, verified", sha)
	}
}

// A forge verifies a signature against the committer, so a commit that
// another person wrote, such as a rebased one, verifies too.
func TestWriteCommitSigns(t *testing.T) {
	signer := gittest.NewSigner(t, "git-k8s@example.com")
	repo, c, head := fetchedCommit(t)
	key, err := git.NewSigningKey(signer.Key)
	if err != nil {
		t.Fatal(err)
	}
	sha, err := repo.WriteCommit(t.Context(), git.NewCommit{
		Tree:      c.Tree,
		Parents:   []string{head},
		Author:    git.Signature{Name: "Ana Lima", Email: "ana@example.com", Date: "1700000000 -0800"},
		Committer: git.Signature{Name: "git-k8s", Email: signer.Email, Date: fmt.Sprintf("%d +0000", c.Time)},
		Message:   "Add y\n",
	}, key)
	if err != nil {
		t.Fatal(err)
	}
	if err := signer.Verify(repo.Dir, sha); err != nil {
		t.Error(err)
	}
}

// A replay keeps the author of the commit that it replays, and verifies
// against its committer, as a rebased commit does.
func TestReplaySigns(t *testing.T) {
	signer := gittest.NewSigner(t, "git-k8s@example.com")
	repo, c, head := fetchedCommit(t)
	key, err := git.NewSigningKey(signer.Key)
	if err != nil {
		t.Fatal(err)
	}
	id := git.Identity{Name: "git-k8s", Email: signer.Email}
	replay, err := repo.Replay(t.Context(), head, head, c.Tree, id, key)
	if err != nil {
		t.Fatal(err)
	}
	if err := signer.Verify(repo.Dir, replay); err != nil {
		t.Error(err)
	}
	if again, err := repo.Replay(t.Context(), head, head, c.Tree, id, key); err != nil || again != replay {
		t.Errorf("Replay again = %s, %v; want the same commit %s", again, err, replay)
	}
	if unsigned, err := repo.Replay(t.Context(), head, head, c.Tree, id, nil); err != nil || signer.Verify(repo.Dir, unsigned) == nil {
		t.Errorf("the replay without a key, %s, verified (%v)", unsigned, err)
	}
}

func TestSigningKeyStaysPrivate(t *testing.T) {
	signer := gittest.NewSigner(t, "git-k8s@example.com")
	repo, c, head := fetchedCommit(t)

	// Record what git hands ssh-keygen, and the permissions of the key file
	// and its directory while ssh-keygen runs.
	keygen, err := exec.LookPath("ssh-keygen")
	if err != nil {
		t.Fatal(err)
	}
	bin, log := t.TempDir(), filepath.Join(t.TempDir(), "ssh-keygen.log")
	wrapper := fmt.Sprintf(`#!/bin/sh
{
  echo "args: $*"
  env
  prev=
  for a in "$@"; do
    [ "$prev" = -f ] && ls -ld "$a" "$(dirname "$a")"
    prev=$a
  done
} >>%q
exec %q "$@"
`, log, keygen)
	if err := os.WriteFile(filepath.Join(bin, "ssh-keygen"), []byte(wrapper), 0o755); err != nil {
		t.Fatal(err)
	}
	t.Setenv("PATH", bin+string(os.PathListSeparator)+os.Getenv("PATH"))
	tmp := t.TempDir()
	t.Setenv("TMPDIR", tmp)

	key, err := git.NewSigningKey(signer.Key)
	if err != nil {
		t.Fatal(err)
	}
	id := git.Identity{Name: "git-k8s", Email: signer.Email}
	sha, err := repo.CommitTree(t.Context(), c.Tree, []string{head}, "fix\n", id, c.Time, key)
	if err != nil {
		t.Fatal(err)
	}
	if left, err := os.ReadDir(tmp); err != nil || len(left) > 0 {
		t.Errorf("TMPDIR holds %v after signing (%v), want nothing", left, err)
	}

	recorded, err := os.ReadFile(log)
	if err != nil {
		t.Fatal(err)
	}
	if !bytes.Contains(recorded, []byte("args: -Y sign -n git -f "+filepath.Join(tmp, "git-k8s-signing-"))) {
		t.Errorf("git didn't sign with a key file in a git-k8s-signing-* directory in TMPDIR:\n%s", recorded)
	}
	block, _ := pem.Decode(signer.Key)
	unwrapped := strings.Join(strings.Fields(string(recorded)), "")
	if bytes.Contains(recorded, []byte("PRIVATE KEY")) || strings.Contains(unwrapped, base64.StdEncoding.EncodeToString(block.Bytes)) {
		t.Errorf("ssh-keygen's arguments or environment hold the key:\n%s", recorded)
	}
	var modes []string
	for line := range strings.Lines(string(recorded)) {
		if mode, _, ok := strings.Cut(line, " "); ok && strings.Contains(line, tmp) && len(mode) >= 10 {
			modes = append(modes, mode[:10])
		}
	}
	if slices.Sort(modes); strings.Join(modes, " ") != "-rw------- drwx------" {
		t.Errorf("the key file and its directory have modes %v, want [-rw------- drwx------]", modes)
	}
	if err := signer.Verify(repo.Dir, sha); err != nil {
		t.Error(err)
	}
}

func TestRemoveSigningKeys(t *testing.T) {
	tmp := t.TempDir()
	t.Setenv("TMPDIR", tmp)
	// A process that's killed while git signs leaves a directory like this.
	left := filepath.Join(tmp, "git-k8s-signing-123")
	if err := os.Mkdir(left, 0o700); err != nil {
		t.Fatal(err)
	}
	if err := os.WriteFile(filepath.Join(left, "key"), []byte("key"), 0o600); err != nil {
		t.Fatal(err)
	}
	other := filepath.Join(tmp, "other")
	if err := os.Mkdir(other, 0o700); err != nil {
		t.Fatal(err)
	}
	if err := git.RemoveSigningKeys(); err != nil {
		t.Fatal(err)
	}
	if _, err := os.Stat(left); !errors.Is(err, os.ErrNotExist) {
		t.Errorf("%s is still there (%v)", left, err)
	}
	if _, err := os.Stat(other); err != nil {
		t.Errorf("removed %s, which doesn't hold a signing key: %v", other, err)
	}
}

func TestNewSigningKey(t *testing.T) {
	signer := gittest.NewSigner(t, "git-k8s@example.com")
	encrypted := filepath.Join(t.TempDir(), "key")
	if out, err := exec.Command("ssh-keygen", "-q", "-t", "ed25519", "-N", "a passphrase", "-f", encrypted).CombinedOutput(); err != nil {
		t.Fatalf("ssh-keygen: %v\n%s", err, out)
	}
	encryptedKey, err := os.ReadFile(encrypted)
	if err != nil {
		t.Fatal(err)
	}
	pub, err := os.ReadFile(encrypted + ".pub")
	if err != nil {
		t.Fatal(err)
	}
	notOpenSSH := "isn't a private key in OpenSSH format"
	armored := func(typ string) string {
		return string(pem.EncodeToMemory(&pem.Block{Type: typ, Bytes: []byte("hunter2")}))
	}
	for _, tc := range []struct {
		name, data, err string
	}{
		{"empty", "", notOpenSSH},
		{"text", "hunter2", notOpenSSH},
		{"public key", string(pub), notOpenSSH},
		{"PEM RSA key", armored("RSA PRIVATE KEY"), notOpenSSH},
		{"bad magic", armored("OPENSSH PRIVATE KEY"), notOpenSSH},
		{"encrypted", string(encryptedKey), "encrypted"},
	} {
		_, err := git.NewSigningKey([]byte(tc.data))
		if err == nil || !strings.Contains(err.Error(), tc.err) {
			t.Errorf("%s: err = %v, want one that says %q", tc.name, err, tc.err)
		}
		if err != nil && strings.Contains(err.Error(), "hunter2") {
			t.Errorf("%s: err = %v, which holds the key", tc.name, err)
		}
	}
	if _, err := git.NewSigningKey(signer.Key); err != nil {
		t.Errorf("NewSigningKey(ssh-keygen's key) = %v", err)
	}
}

func TestSigningKeyIsRedacted(t *testing.T) {
	signer := gittest.NewSigner(t, "git-k8s@example.com")
	key, err := git.NewSigningKey(signer.Key)
	if err != nil {
		t.Fatal(err)
	}
	holder := struct{ Key *git.SigningKey }{key}
	for _, s := range []string{
		fmt.Sprint(key, *key),
		fmt.Sprintf("%v %+v %#v %s %q %x %X %d", key, key, key, key, key, key, key, key),
		fmt.Sprintf("%v %+v", holder, holder),
	} {
		if strings.Contains(s, "OPENSSH") || strings.Contains(strings.ToLower(s), "2d2d2d2d2d") || !strings.Contains(s, "SigningKey(redacted)") {
			t.Errorf("formatted key = %q, want only placeholders", s)
		}
	}
}
