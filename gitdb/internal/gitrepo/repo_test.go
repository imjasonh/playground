package gitrepo

import (
	"os"
	"path/filepath"
	"testing"
	"time"

	"github.com/go-git/go-git/v5"
	"github.com/go-git/go-git/v5/plumbing"
	"github.com/go-git/go-git/v5/plumbing/object"
)

func TestClassifySpec(t *testing.T) {
	// A real directory on disk is always local.
	dir := t.TempDir()

	cases := []struct {
		spec    string
		wantURL string
		wantKey string
		wantLoc bool
	}{
		{spec: "owner/repo", wantURL: "https://github.com/owner/repo", wantKey: "github.com/owner/repo"},
		{spec: "https://github.com/foo/bar.git", wantURL: "https://github.com/foo/bar.git", wantKey: "github.com/foo/bar"},
		{spec: "https://example.com/a/b/c", wantURL: "https://example.com/a/b/c", wantKey: "example.com/a/b/c"},
		{spec: "git@github.com:foo/bar.git", wantURL: "git@github.com:foo/bar.git", wantKey: "github.com/foo/bar"},
		{spec: dir, wantLoc: true},
		{spec: "./nope-not-a-repo", wantLoc: true},
	}

	for _, tc := range cases {
		t.Run(tc.spec, func(t *testing.T) {
			url, key, local, err := classifySpec(tc.spec)
			if err != nil {
				t.Fatalf("classifySpec(%q): %v", tc.spec, err)
			}
			if local != tc.wantLoc {
				t.Errorf("local = %v, want %v", local, tc.wantLoc)
			}
			if !tc.wantLoc {
				if url != tc.wantURL {
					t.Errorf("url = %q, want %q", url, tc.wantURL)
				}
				if key != tc.wantKey {
					t.Errorf("key = %q, want %q", key, tc.wantKey)
				}
			}
			if tc.wantLoc && !filepath.IsAbs(key) {
				t.Errorf("local key %q is not absolute", key)
			}
		})
	}
}

func TestClassifySpecEmpty(t *testing.T) {
	if _, _, _, err := classifySpec(""); err != nil {
		// classifySpec itself doesn't reject empty; Resolve does. Just ensure no panic.
		_ = err
	}
}

func TestResolveEmpty(t *testing.T) {
	m, err := NewManager(Options{CacheDir: t.TempDir()})
	if err != nil {
		t.Fatal(err)
	}
	if _, err := m.Resolve("   "); err == nil {
		t.Errorf("expected error resolving empty spec")
	}
}

func TestRemoteKeySanitizes(t *testing.T) {
	got := remoteKey("https://example.com/weird path/repo.git")
	if got == "" || filepath.IsAbs(got) {
		t.Errorf("unexpected key %q", got)
	}
	// No spaces should survive sanitization.
	for _, r := range got {
		if r == ' ' {
			t.Errorf("key %q contains a space", got)
		}
	}
}

// buildRenameRepo creates a repo whose second commit renames foo.txt to
// bar.txt (identical content). It returns the repo dir and the rename commit.
func buildRenameRepo(t *testing.T) (string, plumbing.Hash) {
	t.Helper()
	dir := t.TempDir()
	repo, err := git.PlainInit(dir, false)
	if err != nil {
		t.Fatal(err)
	}
	wt, err := repo.Worktree()
	if err != nil {
		t.Fatal(err)
	}
	sig := &object.Signature{Name: "T", Email: "t@x", When: time.Unix(1700000000, 0)}
	body := "one\ntwo\nthree\nfour\n"
	if err := os.WriteFile(filepath.Join(dir, "foo.txt"), []byte(body), 0o644); err != nil {
		t.Fatal(err)
	}
	if _, err := wt.Add("foo.txt"); err != nil {
		t.Fatal(err)
	}
	if _, err := wt.Commit("add foo", &git.CommitOptions{Author: sig}); err != nil {
		t.Fatal(err)
	}
	if err := os.Rename(filepath.Join(dir, "foo.txt"), filepath.Join(dir, "bar.txt")); err != nil {
		t.Fatal(err)
	}
	if _, err := wt.Add("foo.txt"); err != nil { // stage the deletion
		t.Fatal(err)
	}
	if _, err := wt.Add("bar.txt"); err != nil {
		t.Fatal(err)
	}
	h, err := wt.Commit("rename foo to bar", &git.CommitOptions{Author: sig})
	if err != nil {
		t.Fatal(err)
	}
	return dir, h
}

func TestCommitChangesRenameDetection(t *testing.T) {
	dir, renameCommit := buildRenameRepo(t)

	// With rename detection on (default), the rename is a single change.
	on, err := NewManager(Options{CacheDir: t.TempDir()})
	if err != nil {
		t.Fatal(err)
	}
	r1, err := on.Resolve(dir)
	if err != nil {
		t.Fatal(err)
	}
	c, err := r1.Git().CommitObject(renameCommit)
	if err != nil {
		t.Fatal(err)
	}
	changes, err := r1.CommitChanges(c)
	if err != nil {
		t.Fatal(err)
	}
	if len(changes) != 1 || changes[0].Change != "rename" ||
		changes[0].OldPath != "foo.txt" || changes[0].Path != "bar.txt" {
		t.Errorf("with renames on, got %+v, want one rename foo.txt->bar.txt", changes)
	}

	// With rename detection off, it's a delete plus an add.
	off, err := NewManager(Options{CacheDir: t.TempDir(), DisableRenames: true})
	if err != nil {
		t.Fatal(err)
	}
	r2, err := off.Resolve(dir)
	if err != nil {
		t.Fatal(err)
	}
	c2, _ := r2.Git().CommitObject(renameCommit)
	changes2, err := r2.CommitChanges(c2)
	if err != nil {
		t.Fatal(err)
	}
	var adds, dels int
	for _, ch := range changes2 {
		switch ch.Change {
		case "add":
			adds++
		case "delete":
			dels++
		}
	}
	if adds != 1 || dels != 1 {
		t.Errorf("with renames off, got %+v, want one add and one delete", changes2)
	}
}

func TestManagerCacheDirDefault(t *testing.T) {
	t.Setenv("XDG_CACHE_HOME", t.TempDir())
	m, err := NewManager(Options{})
	if err != nil {
		t.Fatal(err)
	}
	if m.CacheDir() == "" {
		t.Errorf("expected a non-empty default cache dir")
	}
	if _, err := os.Stat(filepath.Dir(m.CacheDir())); err != nil {
		t.Errorf("cache parent should exist: %v", err)
	}
}
