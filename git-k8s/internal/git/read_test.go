package git_test

import (
	"errors"
	"path/filepath"
	"strings"
	"testing"

	"github.com/imjasonh/playground/git-k8s/internal/git"
	"github.com/imjasonh/playground/git-k8s/internal/gittest"
)

func TestReadersStopAtTheirLimits(t *testing.T) {
	srv := gittest.NewServer(t, "")
	w := srv.NewWork(t, "app")
	w.Write("fits.txt", strings.Repeat("x", git.MaxBlobBytes))
	w.Write("big.txt", strings.Repeat("x", git.MaxBlobBytes+1))
	base := w.Commit("base")
	w.Push("main")
	// 100,000 files, whose list takes about 19 MiB, from a few kilobytes.
	bomb := w.Bomb("bomb", 4)
	w.Push("bomb")

	ctx := t.Context()
	repo, err := (&git.Git{}).Open(ctx, filepath.Join(t.TempDir(), "app.git"))
	if err != nil {
		t.Fatal(err)
	}
	if err := repo.Fetch(ctx, srv.Remote("app"), "main", "bomb"); err != nil {
		t.Fatal(err)
	}
	if b, err := repo.ReadBlob(ctx, mustEntry(t, repo, base, "fits.txt")); err != nil || len(b) != git.MaxBlobBytes {
		t.Errorf("ReadBlob of a %d-byte blob = %d bytes, %v", git.MaxBlobBytes, len(b), err)
	}
	if b, err := repo.ReadBlob(ctx, mustEntry(t, repo, base, "big.txt")); !errors.Is(err, git.ErrTooBig) {
		t.Errorf("ReadBlob of a %d-byte blob = %d bytes, %v; want ErrTooBig", git.MaxBlobBytes+1, len(b), err)
	}
	if entries, err := repo.LsTree(ctx, bomb); !errors.Is(err, git.ErrTooBig) {
		t.Errorf("LsTree of 100,000 files = %d entries, %v; want ErrTooBig", len(entries), err)
	}
	if stats, err := repo.Numstat(ctx, base, bomb); !errors.Is(err, git.ErrTooBig) {
		t.Errorf("Numstat of 100,000 new files = %d files, %v; want ErrTooBig", len(stats), err)
	}
	if entries, err := repo.LsTree(ctx, base); err != nil || len(entries) != 2 {
		t.Errorf("LsTree of 2 files = %+v, %v", entries, err)
	}
}

func TestBlobSizes(t *testing.T) {
	srv := gittest.NewServer(t, "")
	w := srv.NewWork(t, "app")
	w.Write("a.txt", "a\n")
	w.Write("dir/b.txt", "bb\n")
	head := w.Commit("files")
	w.Push("main")

	ctx := t.Context()
	repo, err := (&git.Git{}).Open(ctx, filepath.Join(t.TempDir(), "app.git"))
	if err != nil {
		t.Fatal(err)
	}
	if err := repo.Fetch(ctx, srv.Remote("app"), "main"); err != nil {
		t.Fatal(err)
	}
	a, b := mustEntry(t, repo, head, "a.txt"), mustEntry(t, repo, head, "dir/b.txt")
	sizes, err := repo.BlobSizes(ctx, []string{a, b, a})
	if err != nil || len(sizes) != 2 || sizes[a] != 2 || sizes[b] != 3 {
		t.Errorf("BlobSizes = %v, %v; want %s: 2 and %s: 3", sizes, err, a, b)
	}
	if sizes, err := repo.BlobSizes(ctx, nil); err != nil || len(sizes) != 0 {
		t.Errorf("BlobSizes of no blobs = %v, %v", sizes, err)
	}
	c, err := repo.Commit(ctx, head)
	if err != nil {
		t.Fatal(err)
	}
	for _, sha := range []string{c.Tree, strings.Repeat("0", 40), "HEAD", "--batch"} {
		if sizes, err := repo.BlobSizes(ctx, []string{a, sha}); err == nil {
			t.Errorf("BlobSizes(%q) = %v; want an error", sha, sizes)
		}
	}
}
