package gitserver_test

import (
	"errors"
	"net/http/httptest"
	"path/filepath"
	"strings"
	"testing"

	"github.com/imjasonh/playground/git-k8s/internal/git"
	"github.com/imjasonh/playground/git-k8s/internal/gitserver"
	"github.com/imjasonh/playground/git-k8s/internal/gittest"
)

func TestGitHubRequiresSignatures(t *testing.T) {
	signer := gittest.NewSigner(t, "author@example.com")
	hs := httptest.NewServer(&gitserver.GitHub{Root: t.TempDir(), Username: "git-k8s", Password: "pw", AllowedSigners: signer.AllowedSigners})
	t.Cleanup(hs.Close)
	srv := &gittest.Server{URL: hs.URL + "/acme", Username: "git-k8s", Password: "pw"}
	w := srv.NewWork(t, "app")
	w.Write("a.txt", "one\n")
	unsigned := w.Commit("unsigned")

	ctx := t.Context()
	repo, err := (&git.Git{}).Open(ctx, filepath.Join(w.Dir, ".git"))
	if err != nil {
		t.Fatal(err)
	}
	err = repo.Push(ctx, srv.Remote("app"), git.RefUpdate{Ref: "refs/heads/main", New: unsigned})
	if !errors.Is(err, git.ErrRejected) || !strings.Contains(err.Error(), "isn't signed with its committer's key") {
		t.Fatalf("pushing an unsigned commit: err = %v, want a rejected push that gives the server's reason", err)
	}

	w.SignWith(signer)
	w.Git("commit", "--quiet", "--amend", "--no-edit")
	w.Push("main")
	if heads, signed := srv.Heads(t, "app"), w.Git("rev-parse", "HEAD"); len(heads) != 1 || heads["main"] != signed {
		t.Errorf("heads = %v, want main at the signed commit %s", heads, signed)
	}
}
