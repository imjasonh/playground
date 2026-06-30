package tables_test

import (
	"database/sql"
	"os"
	"path/filepath"
	"testing"
	"time"

	"github.com/go-git/go-git/v5"
	"github.com/go-git/go-git/v5/plumbing"
	"github.com/go-git/go-git/v5/plumbing/object"
	_ "modernc.org/sqlite"

	"github.com/imjasonh/playground/gitsql/internal/gitrepo"
	"github.com/imjasonh/playground/gitsql/internal/tables"
)

// buildRepo creates a small non-bare repository with two commits by different
// authors, a binary file, a lightweight and an annotated tag, and a "feature"
// branch pointing at the first commit. It returns the repo path and the two
// commit hashes.
func buildRepo(t *testing.T) (string, plumbing.Hash, plumbing.Hash) {
	t.Helper()
	dir := t.TempDir()
	repo, err := git.PlainInit(dir, false)
	if err != nil {
		t.Fatalf("init: %v", err)
	}
	wt, err := repo.Worktree()
	if err != nil {
		t.Fatalf("worktree: %v", err)
	}

	write := func(name, content string) {
		if err := os.WriteFile(filepath.Join(dir, name), []byte(content), 0o644); err != nil {
			t.Fatalf("write %s: %v", name, err)
		}
		if _, err := wt.Add(name); err != nil {
			t.Fatalf("add %s: %v", name, err)
		}
	}

	t1 := time.Date(2021, 1, 1, 10, 0, 0, 0, time.UTC)
	write("README.md", "# Demo\nline two\n")
	write("a.txt", "alpha\nbeta\ngamma\n")
	c1, err := wt.Commit("first commit", &git.CommitOptions{
		Author: &object.Signature{Name: "Alice", Email: "alice@example.com", When: t1},
	})
	if err != nil {
		t.Fatalf("commit1: %v", err)
	}

	// Second commit by Bob in a +05:00 zone: 14:30 local is the wall-clock hour.
	t2 := time.Date(2021, 1, 2, 14, 30, 0, 0, time.FixedZone("UTC+5", 5*3600))
	write("a.txt", "alpha\nBETA\ngamma\ndelta\n") // 1 add, 1 del (modify)
	write("b.txt", "new file\n")                  // add
	if err := os.WriteFile(filepath.Join(dir, "bin.dat"), []byte{0x00, 0x01, 0x02, 0x00}, 0o644); err != nil {
		t.Fatalf("write bin: %v", err)
	}
	if _, err := wt.Add("bin.dat"); err != nil {
		t.Fatalf("add bin: %v", err)
	}
	c2, err := wt.Commit("second commit", &git.CommitOptions{
		Author: &object.Signature{Name: "Bob", Email: "bob@example.com", When: t2},
	})
	if err != nil {
		t.Fatalf("commit2: %v", err)
	}

	// Tags: lightweight v1 -> c1, annotated v2 -> c2.
	if _, err := repo.CreateTag("v1", c1, nil); err != nil {
		t.Fatalf("tag v1: %v", err)
	}
	if _, err := repo.CreateTag("v2", c2, &git.CreateTagOptions{
		Tagger:  &object.Signature{Name: "Tagger", Email: "tag@example.com", When: t2},
		Message: "release two\n",
	}); err != nil {
		t.Fatalf("tag v2: %v", err)
	}

	// feature branch points at the first commit.
	if err := repo.Storer.SetReference(plumbing.NewHashReference(
		plumbing.NewBranchReferenceName("feature"), c1)); err != nil {
		t.Fatalf("branch: %v", err)
	}

	return dir, c1, c2
}

// open registers the tables (once, process-global) and creates them for the
// given repo on a fresh in-memory database.
func open(t *testing.T, repoPath string) *sql.DB {
	t.Helper()
	mgr, err := gitrepo.NewManager(gitrepo.Options{CacheDir: t.TempDir()})
	if err != nil {
		t.Fatalf("manager: %v", err)
	}
	tables.Init(mgr)

	db, err := sql.Open("sqlite", ":memory:")
	if err != nil {
		t.Fatalf("open db: %v", err)
	}
	db.SetMaxOpenConns(1)
	t.Cleanup(func() { db.Close() })

	if err := tables.Register(db); err != nil {
		t.Fatalf("register: %v", err)
	}
	if err := tables.CreateAll(db, repoPath); err != nil {
		t.Fatalf("create: %v", err)
	}
	return db
}

func query(t *testing.T, db *sql.DB, q string, args ...any) [][]any {
	t.Helper()
	rows, err := db.Query(q, args...)
	if err != nil {
		t.Fatalf("query %q: %v", q, err)
	}
	defer rows.Close()
	cols, _ := rows.Columns()
	var out [][]any
	for rows.Next() {
		cell := make([]any, len(cols))
		ptr := make([]any, len(cols))
		for i := range cell {
			ptr[i] = &cell[i]
		}
		if err := rows.Scan(ptr...); err != nil {
			t.Fatalf("scan: %v", err)
		}
		out = append(out, cell)
	}
	if err := rows.Err(); err != nil {
		t.Fatalf("rows: %v", err)
	}
	return out
}

// columns returns the result column names of a query.
func columns(t *testing.T, db *sql.DB, q string, args ...any) []string {
	t.Helper()
	rows, err := db.Query(q, args...)
	if err != nil {
		t.Fatalf("query %q: %v", q, err)
	}
	defer rows.Close()
	cols, err := rows.Columns()
	if err != nil {
		t.Fatalf("columns: %v", err)
	}
	return cols
}

// scalar runs a query expected to return a single row/column.
func scalar(t *testing.T, db *sql.DB, q string, args ...any) any {
	t.Helper()
	rows := query(t, db, q, args...)
	if len(rows) != 1 || len(rows[0]) != 1 {
		t.Fatalf("query %q: expected 1x1 result, got %d rows", q, len(rows))
	}
	return rows[0][0]
}

func TestCommits(t *testing.T) {
	dir, _, c2 := buildRepo(t)
	db := open(t, dir)

	if got := scalar(t, db, "SELECT count(*) FROM commits"); got != int64(2) {
		t.Errorf("commit count = %v, want 2", got)
	}
	// HEAD is the second commit, newest first.
	row := query(t, db, "SELECT hash, author_name, summary, is_merge, parents FROM commits LIMIT 1")[0]
	if row[0] != c2.String() {
		t.Errorf("first row hash = %v, want %v", row[0], c2)
	}
	if row[1] != "Bob" {
		t.Errorf("author = %v, want Bob", row[1])
	}
	if row[2] != "second commit" {
		t.Errorf("summary = %v", row[2])
	}
	if row[3] != int64(0) || row[4] != int64(1) {
		t.Errorf("is_merge/parents = %v/%v, want 0/1", row[3], row[4])
	}

	// hash pushdown returns exactly one row.
	if got := scalar(t, db, "SELECT count(*) FROM commits WHERE hash = ?", c2.String()); got != int64(1) {
		t.Errorf("hash pushdown count = %v, want 1", got)
	}
	// unknown hash -> empty.
	if got := scalar(t, db, "SELECT count(*) FROM commits WHERE hash = ?", "deadbeef"); got != int64(0) {
		t.Errorf("unknown hash count = %v, want 0", got)
	}

	// Bob committed in +05:00; wall-clock hour should read 14, not 09 (UTC).
	if got := scalar(t, db, "SELECT strftime('%H', author_when) FROM commits WHERE author_name='Bob'"); got != "14" {
		t.Errorf("Bob wall-clock hour = %v, want 14", got)
	}
}

func TestCommitsRefFilter(t *testing.T) {
	dir, _, _ := buildRepo(t)
	db := open(t, dir)
	// feature points at the first commit, so only one commit is reachable.
	if got := scalar(t, db, "SELECT count(*) FROM commits WHERE ref = 'feature'"); got != int64(1) {
		t.Errorf("commits on feature = %v, want 1", got)
	}
}

func TestRefs(t *testing.T) {
	dir, _, _ := buildRepo(t)
	db := open(t, dir)

	if got := scalar(t, db, "SELECT count(*) FROM refs WHERE short_name='feature' AND is_branch=1"); got != int64(1) {
		t.Errorf("feature branch not found")
	}
	if got := scalar(t, db, "SELECT count(*) FROM refs WHERE is_tag=1"); got != int64(2) {
		t.Errorf("tag refs = %v, want 2", got)
	}
	if got := scalar(t, db, "SELECT count(*) FROM refs WHERE is_head=1"); got.(int64) < 1 {
		t.Errorf("expected at least one is_head ref, got %v", got)
	}
}

func TestTags(t *testing.T) {
	dir, c1, c2 := buildRepo(t)
	db := open(t, dir)

	v2 := query(t, db, "SELECT type, target, tagger_name, message FROM tags WHERE name='v2'")
	if len(v2) != 1 {
		t.Fatalf("v2 not found")
	}
	if v2[0][0] != "annotated" || v2[0][1] != c2.String() || v2[0][2] != "Tagger" {
		t.Errorf("v2 row = %v", v2[0])
	}

	v1 := query(t, db, "SELECT type, target, tagger_name FROM tags WHERE name='v1'")
	if len(v1) != 1 || v1[0][0] != "lightweight" || v1[0][1] != c1.String() || v1[0][2] != nil {
		t.Errorf("v1 row = %v, want lightweight/%v/nil", v1[0], c1)
	}
}

func TestFiles(t *testing.T) {
	dir, _, _ := buildRepo(t)
	db := open(t, dir)

	// a.txt at HEAD has 4 lines and is not binary.
	a := query(t, db, "SELECT size, lines, is_binary, type FROM files WHERE path='a.txt'")
	if len(a) != 1 {
		t.Fatalf("a.txt not found")
	}
	if a[0][1] != int64(4) || a[0][2] != int64(0) {
		t.Errorf("a.txt lines/binary = %v/%v, want 4/0", a[0][1], a[0][2])
	}

	// bin.dat is binary; lines is NULL.
	bin := query(t, db, "SELECT is_binary, lines FROM files WHERE path='bin.dat'")
	if len(bin) != 1 || bin[0][0] != int64(1) || bin[0][1] != nil {
		t.Errorf("bin.dat row = %v, want binary=1 lines=NULL", bin[0])
	}

	// The feature ref only has README.md and a.txt (no b.txt yet).
	if got := scalar(t, db, "SELECT count(*) FROM files WHERE ref='feature' AND path='b.txt'"); got != int64(0) {
		t.Errorf("b.txt should not exist on feature")
	}
}

func TestFileContents(t *testing.T) {
	dir, _, _ := buildRepo(t)
	db := open(t, dir)

	// The contents column returns the blob text.
	if got := scalar(t, db, "SELECT contents FROM files WHERE path='a.txt'"); got != "alpha\nBETA\ngamma\ndelta\n" {
		t.Errorf("a.txt contents = %q", got)
	}
	// Binary files have NULL contents.
	if got := scalar(t, db, "SELECT contents FROM files WHERE path='bin.dat'"); got != nil {
		t.Errorf("bin.dat contents = %v, want NULL", got)
	}
	// Content search across the tree.
	rows := query(t, db, "SELECT path FROM files WHERE contents LIKE '%BETA%' ORDER BY path")
	if len(rows) != 1 || rows[0][0] != "a.txt" {
		t.Errorf("content search = %v, want [a.txt]", rows)
	}
	// contents is hidden: SELECT * must not include it (only the 8 visible columns).
	cols := columns(t, db, "SELECT * FROM files LIMIT 1")
	for _, c := range cols {
		if c == "contents" || c == "ref" {
			t.Errorf("SELECT * exposed hidden column %q (cols=%v)", c, cols)
		}
	}

	// Search a specific revision via the hidden ref column: README.md on the
	// feature branch contains "two", b.txt does not exist there.
	if got := scalar(t, db, "SELECT count(*) FROM files WHERE ref='feature' AND contents LIKE '%line two%'"); got != int64(1) {
		t.Errorf("feature content search = %v, want 1", got)
	}
}

func TestCommitFiles(t *testing.T) {
	dir, _, c2 := buildRepo(t)
	db := open(t, dir)

	// Single-commit pushdown: c2 added b.txt and bin.dat, modified a.txt.
	b := query(t, db, "SELECT change, additions FROM commit_files WHERE commit_hash=? AND path='b.txt'", c2.String())
	if len(b) != 1 || b[0][0] != "add" || b[0][1].(int64) < 1 {
		t.Errorf("b.txt change row = %v, want add/>=1", b[0])
	}
	a := query(t, db, "SELECT change, additions, deletions FROM commit_files WHERE commit_hash=? AND path='a.txt'", c2.String())
	if len(a) != 1 || a[0][0] != "modify" {
		t.Errorf("a.txt change = %v, want modify", a[0])
	}
	if a[0][1].(int64) < 1 || a[0][2].(int64) < 1 {
		t.Errorf("a.txt add/del = %v/%v, want both >=1", a[0][1], a[0][2])
	}

	// Full scan: total rows across both commits.
	if got := scalar(t, db, "SELECT count(DISTINCT commit_hash) FROM commit_files"); got != int64(2) {
		t.Errorf("distinct commits in commit_files = %v, want 2", got)
	}
}

func TestBlame(t *testing.T) {
	dir, _, _ := buildRepo(t)
	db := open(t, dir)

	rows := query(t, db, "SELECT line_no, author_name FROM blame WHERE path='a.txt' ORDER BY line_no")
	if len(rows) != 4 {
		t.Fatalf("blame lines = %d, want 4", len(rows))
	}
	// Line 2 was changed in c2 by Bob; line 1 still Alice's.
	if rows[0][1] != "Alice" {
		t.Errorf("line 1 author = %v, want Alice", rows[0][1])
	}
	if rows[1][1] != "Bob" {
		t.Errorf("line 2 author = %v, want Bob", rows[1][1])
	}

	// Blame without a path constraint must fail loudly.
	if _, err := db.Query("SELECT count(*) FROM blame"); err == nil {
		t.Errorf("expected error blaming without a path")
	}
}

func TestJoinAcrossTables(t *testing.T) {
	dir, _, _ := buildRepo(t)
	db := open(t, dir)

	rows := query(t, db, `
		SELECT c.author_name, sum(cf.additions) AS added
		FROM commit_files cf
		JOIN commits c ON c.hash = cf.commit_hash
		GROUP BY c.author_name
		ORDER BY c.author_name`)
	if len(rows) != 2 {
		t.Fatalf("join groups = %d, want 2 (Alice, Bob)", len(rows))
	}
	if rows[0][0] != "Alice" || rows[1][0] != "Bob" {
		t.Errorf("authors = %v / %v", rows[0][0], rows[1][0])
	}
	if rows[0][1].(int64) < 1 || rows[1][1].(int64) < 1 {
		t.Errorf("expected positive additions for both authors")
	}
}
