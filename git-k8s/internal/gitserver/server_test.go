package gitserver_test

import (
	"errors"
	"net/http"
	"net/http/httptest"
	"path/filepath"
	"strings"
	"testing"

	"github.com/imjasonh/playground/git-k8s/internal/git"
	"github.com/imjasonh/playground/git-k8s/internal/gitserver"
	"github.com/imjasonh/playground/git-k8s/internal/gittest"
)

func TestCloneAndPush(t *testing.T) {
	srv := gittest.NewServer(t, "pw")
	w := srv.NewWork(t, "repo")
	w.Write("README.md", "hello\n")
	first := w.Commit("first")
	w.Push("main")

	other := srv.NewWork(t, "repo")
	if got := other.Fetch("main"); got != first {
		t.Errorf("fetched %s, want %s", got, first)
	}
	if got := other.Show(first, "README.md"); got != "hello" {
		t.Errorf("README.md = %q", got)
	}
}

func TestRequiresCredentials(t *testing.T) {
	srv := gittest.NewServer(t, "pw")
	resp, err := http.Get(srv.URL + "/repo.git/info/refs?service=git-upload-pack")
	if err != nil {
		t.Fatal(err)
	}
	resp.Body.Close()
	if resp.StatusCode != http.StatusUnauthorized {
		t.Errorf("status = %d, want 401", resp.StatusCode)
	}
}

func TestRequiresSignatures(t *testing.T) {
	signer := gittest.NewSigner(t, "git-k8s@example.com")
	hs := httptest.NewServer(&gitserver.Server{Root: t.TempDir(), AllowedSigners: signer.AllowedSigners})
	t.Cleanup(hs.Close)
	srv := &gittest.Server{URL: hs.URL}
	w := srv.NewWork(t, "app")
	w.Write("a.txt", "one\n")
	unsigned := w.Commit("unsigned")

	ctx := t.Context()
	repo, err := (&git.Git{}).Open(ctx, filepath.Join(w.Dir, ".git"))
	if err != nil {
		t.Fatal(err)
	}
	c, err := repo.Commit(ctx, unsigned)
	if err != nil {
		t.Fatal(err)
	}
	key, err := git.NewSigningKey(signer.Key)
	if err != nil {
		t.Fatal(err)
	}
	other, err := git.NewSigningKey(gittest.NewSigner(t, signer.Email).Key)
	if err != nil {
		t.Fatal(err)
	}
	commit := func(parents []string, email string, key *git.SigningKey) string {
		t.Helper()
		sha, err := repo.CommitTree(ctx, c.Tree, parents, "commit\n", git.Identity{Name: "git-k8s", Email: email}, c.Time, key)
		if err != nil {
			t.Fatal(err)
		}
		return sha
	}
	push := func(update git.RefUpdate) error {
		return repo.Push(ctx, srv.Remote("app"), update)
	}

	signed := commit(nil, signer.Email, key)
	for _, tc := range []struct{ branch, commit string }{
		{"unsigned", unsigned},
		{"unsigned-parent", commit([]string{unsigned}, signer.Email, key)},
		{"another-committer", commit([]string{signed}, "someone@example.com", key)},
		{"unknown-key", commit([]string{signed}, signer.Email, other)},
	} {
		err := push(git.RefUpdate{Ref: "refs/heads/" + tc.branch, New: tc.commit})
		if !errors.Is(err, git.ErrRejected) || !strings.Contains(err.Error(), "remote: refs/heads/"+tc.branch+": commit ") {
			t.Errorf("pushing %s: err = %v, want a rejected push that gives the server's reason", tc.branch, err)
		}
	}
	if err := push(git.RefUpdate{Ref: "refs/heads/main", New: signed}); err != nil {
		t.Fatalf("pushing a signed commit: %v", err)
	}
	if err := push(git.RefUpdate{Ref: "refs/heads/copy", New: signed}); err != nil {
		t.Errorf("pointing a new branch at a pushed commit: %v", err)
	}
	if err := push(git.RefUpdate{Ref: "refs/heads/copy", Old: signed}); err != nil {
		t.Errorf("deleting a branch: %v", err)
	}
	if heads := srv.Heads(t, "app"); len(heads) != 1 || heads["main"] != signed {
		t.Errorf("heads = %v, want main at the signed commit %s", heads, signed)
	}
}

func TestRejectsBadPaths(t *testing.T) {
	srv := gittest.NewServer(t, "")
	for _, path := range []string{"/../etc.git/info/refs", "/repo/info/refs", "/repo.git/objects/info/packs"} {
		resp, err := http.Get(srv.URL + path + "?service=git-upload-pack")
		if err != nil {
			t.Fatal(err)
		}
		resp.Body.Close()
		if resp.StatusCode != http.StatusNotFound {
			t.Errorf("GET %s: status = %d, want 404", path, resp.StatusCode)
		}
	}
}
