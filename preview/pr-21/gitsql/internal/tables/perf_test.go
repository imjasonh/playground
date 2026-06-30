package tables_test

import (
	"os"
	"path/filepath"
	"testing"
	"time"

	"github.com/go-git/go-git/v5"
	"github.com/go-git/go-git/v5/plumbing"
	"github.com/go-git/go-git/v5/plumbing/object"
)

// buildMergeRepo builds a repo whose HEAD is a merge commit:
//
//	c1 (a.txt) ── c2 (+b.txt) ─────┐
//	   └──────── c3 (+t.txt) ──────┴── merge (a,b,t)
//
// The merge introduces t.txt relative to its first parent (c2), and c3 also
// introduces t.txt — so a naive full scan would count t.txt's addition twice.
func buildMergeRepo(t *testing.T) (dir string, merge plumbing.Hash) {
	t.Helper()
	dir = t.TempDir()
	repo, err := git.PlainInit(dir, false)
	if err != nil {
		t.Fatalf("init: %v", err)
	}
	wt, err := repo.Worktree()
	if err != nil {
		t.Fatalf("worktree: %v", err)
	}
	when := time.Date(2022, 1, 1, 12, 0, 0, 0, time.UTC)
	sig := func() *object.Signature {
		return &object.Signature{Name: "T", Email: "t@example.com", When: when}
	}
	add := func(name, body string) {
		if err := os.WriteFile(filepath.Join(dir, name), []byte(body), 0o644); err != nil {
			t.Fatal(err)
		}
		if _, err := wt.Add(name); err != nil {
			t.Fatal(err)
		}
	}

	add("a.txt", "a\n")
	c1, err := wt.Commit("c1", &git.CommitOptions{Author: sig()})
	if err != nil {
		t.Fatalf("c1: %v", err)
	}
	add("b.txt", "b\n")
	c2, err := wt.Commit("c2", &git.CommitOptions{Author: sig()})
	if err != nil {
		t.Fatalf("c2: %v", err)
	}

	// topic branch off c1 that adds t.txt
	if err := wt.Checkout(&git.CheckoutOptions{Hash: c1}); err != nil {
		t.Fatalf("checkout c1: %v", err)
	}
	add("t.txt", "t\n")
	c3, err := wt.Commit("c3", &git.CommitOptions{Author: sig(), Parents: []plumbing.Hash{c1}})
	if err != nil {
		t.Fatalf("c3: %v", err)
	}

	// merge: tree a+b+t, parents [c2, c3]
	if err := wt.Checkout(&git.CheckoutOptions{Hash: c2}); err != nil {
		t.Fatalf("checkout c2: %v", err)
	}
	add("t.txt", "t\n")
	merge, err = wt.Commit("merge", &git.CommitOptions{Author: sig(), Parents: []plumbing.Hash{c2, c3}})
	if err != nil {
		t.Fatalf("merge: %v", err)
	}
	return dir, merge
}

func TestCommitFilesSkipsMerges(t *testing.T) {
	dir, merge := buildMergeRepo(t)
	db := open(t, dir)

	// Full scan visits the 3 non-merge commits (c1, c2, c3), not the merge.
	if got := scalar(t, db, "SELECT count(DISTINCT commit_hash) FROM commit_files"); got != int64(3) {
		t.Errorf("distinct commits in scan = %v, want 3 (merge excluded)", got)
	}
	// t.txt's addition is counted once (c3), not twice (c3 + merge).
	if got := scalar(t, db, "SELECT count(*) FROM commit_files WHERE path='t.txt' AND change='add'"); got != int64(1) {
		t.Errorf("t.txt add count = %v, want 1 (no merge double-count)", got)
	}
	// But an explicit query on the merge hash still returns its first-parent diff.
	if got := scalar(t, db, "SELECT count(*) FROM commit_files WHERE commit_hash=? AND path='t.txt'", merge.String()); got != int64(1) {
		t.Errorf("explicit merge query for t.txt = %v, want 1", got)
	}
}

func TestFilesPathPushdownMatchesScan(t *testing.T) {
	dir, _, _ := buildRepo(t)
	db := open(t, dir)

	// path= (pushed down, direct lookup) must agree with the full-walk result.
	push := query(t, db, "SELECT size, lines, is_binary FROM files WHERE path='a.txt'")
	walk := query(t, db, "SELECT size, lines, is_binary FROM files WHERE path LIKE 'a.txt'")
	if len(push) != 1 || len(walk) != 1 {
		t.Fatalf("expected one row each, got push=%d walk=%d", len(push), len(walk))
	}
	for i := range push[0] {
		if push[0][i] != walk[0][i] {
			t.Errorf("col %d differs: pushdown=%v walk=%v", i, push[0][i], walk[0][i])
		}
	}
	// A path that doesn't exist yields no rows (not an error).
	if got := scalar(t, db, "SELECT count(*) FROM files WHERE path='does/not/exist'"); got != int64(0) {
		t.Errorf("missing path count = %v, want 0", got)
	}
}
