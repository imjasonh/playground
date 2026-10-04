package git_test

import (
	"errors"
	"fmt"
	"os"
	"path/filepath"
	"slices"
	"strings"
	"testing"

	"github.com/imjasonh/playground/git-k8s/internal/git"
	"github.com/imjasonh/playground/git-k8s/internal/gittest"
)

func TestLogAndReplay(t *testing.T) {
	srv := gittest.NewServer(t, "")
	w := srv.NewWork(t, "app")
	w.Write("a.txt", "one\n")
	base := w.Commit("base")
	w.Push("main")
	w.Branch("c/x", base)
	w.Write("b.txt", "b\n")
	w.Git("add", "-A")
	w.Git("commit", "--quiet", "--author=Ana Lima <ana@example.com>", "--date=1700000000 -0800", "-m", "Add b\n\nWith a body.\n\nSigned-off-by: Ana Lima\n <ana@example.com>")
	x1 := w.Git("rev-parse", "HEAD")
	w.Branch("main", base)
	w.Write("a.txt", "two\n")
	parent := w.Commit("main edit")
	w.Push("main")
	w.Branch("c/x", x1)
	w.Git("merge", "--quiet", "--no-edit", parent)
	merge := w.Git("rev-parse", "HEAD")
	w.Write("c.txt", "c\n")
	head := w.Commit("Add c\n\n" + git.FixerTrailer + ": touch")
	w.Push("c/x")

	ctx := t.Context()
	repo, err := (&git.Git{}).Open(ctx, filepath.Join(t.TempDir(), "app.git"))
	if err != nil {
		t.Fatal(err)
	}
	remote := srv.Remote("app")
	if err := repo.Fetch(ctx, remote, "main", "c/x"); err != nil {
		t.Fatal(err)
	}
	log, err := repo.Log(ctx, parent, head, 3)
	if err != nil {
		t.Fatal(err)
	}
	var shas []string
	for _, e := range log {
		shas = append(shas, e.SHA)
	}
	if !slices.Equal(shas, []string{x1, merge, head}) {
		t.Fatalf("Log = %v, want x1, the merge, and the head in order", shas)
	}
	first := log[0]
	if want := (git.Signature{Name: "Ana Lima", Email: "ana@example.com", Date: "1700000000 -0800"}); first.Author != want {
		t.Errorf("author = %+v, want %+v", first.Author, want)
	}
	if want := (git.Identity{Name: "Test Author", Email: "author@example.com"}); first.Committer != want || first.Time != 1767323045 {
		t.Errorf("committer = %+v at %d, want %+v at 1767323045", first.Committer, first.Time, want)
	}
	message := "Add b\n\nWith a body.\n\nSigned-off-by: Ana Lima\n <ana@example.com>\n"
	if first.Message != message || first.Subject() != "Add b" || first.Fixer() {
		t.Errorf("first commit = %q, subject %q, fixer %v", first.Message, first.Subject(), first.Fixer())
	}
	if !slices.Equal(first.Trailers, []string{"Signed-off-by: Ana Lima <ana@example.com>"}) || len(log[1].Trailers) != 0 {
		t.Errorf("trailers = %q and %q", first.Trailers, log[1].Trailers)
	}
	if !slices.Equal(first.Parents, []string{base}) || !slices.Equal(log[1].Parents, []string{x1, parent}) {
		t.Errorf("parents = %v and %v", first.Parents, log[1].Parents)
	}
	if !log[2].Fixer() || !slices.Equal(log[2].Trailers, []string{git.FixerTrailer + ": touch"}) || log[2].Tree != w.Git("rev-parse", head+"^{tree}") {
		t.Errorf("head = %+v, want a fixer commit with the head's tree", log[2])
	}
	if none, err := repo.Log(ctx, head, head, 3); err != nil || len(none) != 0 {
		t.Errorf("Log(head, head) = %v, %v; want nothing", none, err)
	}
	for _, tt := range []struct {
		base, head string
		want       bool
	}{{parent, head, true}, {merge, head, false}, {base, x1, false}} {
		if got, err := repo.HasMerge(ctx, tt.base, tt.head); err != nil || got != tt.want {
			t.Errorf("HasMerge(%s, %s) = %v, %v; want %v", tt.base, tt.head, got, err, tt.want)
		}
	}
	if parents, err := repo.Parents(ctx, merge); err != nil || !slices.Equal(parents, []string{x1, parent}) {
		t.Errorf("Parents(merge) = %v, %v; want x1 and the parent", parents, err)
	}

	tree, conflicts, err := repo.CherryPick(ctx, x1, base, parent)
	if err != nil || len(conflicts) > 0 {
		t.Fatalf("CherryPick = %q, %v, %v", tree, conflicts, err)
	}
	c := git.NewCommit{
		Tree:      tree,
		Parents:   []string{parent},
		Author:    first.Author,
		Committer: git.Signature{Name: "git-k8s", Email: "git-k8s@example.com", Date: "1700000500 +0000"},
		Message:   first.Message,
	}
	replayed, err := repo.WriteCommit(ctx, c)
	if err != nil {
		t.Fatal(err)
	}
	if again, err := repo.WriteCommit(ctx, c); err != nil || again != replayed {
		t.Errorf("WriteCommit isn't deterministic: %s then %s (%v)", replayed, again, err)
	}
	if err := repo.Push(ctx, remote, git.RefUpdate{Ref: "refs/heads/replayed", New: replayed}); err != nil {
		t.Fatal(err)
	}
	w.Fetch("replayed")
	got := w.Git("log", "-1", "--date=raw", "--format=%an <%ae> %ad|%cn <%ce> %cd|%P|%B", replayed)
	if want := "Ana Lima <ana@example.com> 1700000000 -0800|git-k8s <git-k8s@example.com> 1700000500 +0000|" + parent + "|" + strings.TrimSpace(message); got != want {
		t.Errorf("replayed commit = %q, want %q", got, want)
	}
	if w.Show(replayed, "a.txt") != "two" || w.Show(replayed, "b.txt") != "b" {
		t.Error("the replayed commit doesn't have the parent's a.txt and the commit's b.txt")
	}

	// A change that onto already has applies cleanly and changes nothing.
	if again, conflicts, err := repo.CherryPick(ctx, x1, base, replayed); err != nil || len(conflicts) > 0 || again != tree {
		t.Errorf("CherryPick onto a commit with the change = %q, %v, %v; want %q", again, conflicts, err, tree)
	}
}

func TestLogLimits(t *testing.T) {
	srv := gittest.NewServer(t, "")
	w := srv.NewWork(t, "app")
	base := w.Commit("base")
	w.Push("main")
	var commits []string
	for i := range 3 {
		commits = append(commits, w.Commit(fmt.Sprintf("commit %d", i)))
	}
	message := filepath.Join(t.TempDir(), "message")
	if err := os.WriteFile(message, []byte("Big\n\n"+strings.Repeat("x", git.MaxLogBytes)+"\n"), 0o644); err != nil {
		t.Fatal(err)
	}
	w.Git("commit", "--quiet", "--allow-empty", "-F", message)
	big := w.Git("rev-parse", "HEAD")
	w.Push("c/x")

	ctx := t.Context()
	repo, err := (&git.Git{}).Open(ctx, filepath.Join(t.TempDir(), "app.git"))
	if err != nil {
		t.Fatal(err)
	}
	if err := repo.Fetch(ctx, srv.Remote("app"), "main", "c/x"); err != nil {
		t.Fatal(err)
	}
	for _, tt := range []struct {
		limit int
		want  []string
	}{{3, commits}, {2, commits[1:]}} {
		log, err := repo.Log(ctx, base, commits[2], tt.limit)
		var shas []string
		for _, e := range log {
			shas = append(shas, e.SHA)
		}
		if err != nil || !slices.Equal(shas, tt.want) {
			t.Errorf("Log with limit %d = %v, %v; want %v", tt.limit, shas, err, tt.want)
		}
	}
	if log, err := repo.Log(ctx, base, big, 10); !errors.Is(err, git.ErrLogTooBig) {
		t.Errorf("Log of a commit with a %d-byte message = %d commits, %v; want ErrLogTooBig", git.MaxLogBytes, len(log), err)
	}
}

func TestCherryPickConflicts(t *testing.T) {
	srv := gittest.NewServer(t, "")
	w := srv.NewWork(t, "app")
	w.Write("a.txt", "one\n")
	base := w.Commit("base")
	w.Write("a.txt", "main\n")
	parent := w.Commit("main edit")
	w.Push("main")
	w.Branch("c/x", base)
	w.Write("a.txt", "branch\n")
	head := w.Commit("branch edit")
	w.Push("c/x")

	ctx := t.Context()
	repo, err := (&git.Git{}).Open(ctx, filepath.Join(t.TempDir(), "app.git"))
	if err != nil {
		t.Fatal(err)
	}
	if err := repo.Fetch(ctx, srv.Remote("app"), "main", "c/x"); err != nil {
		t.Fatal(err)
	}
	if tree, conflicts, err := repo.CherryPick(ctx, head, base, parent); err != nil || tree != "" || !slices.Equal(conflicts, []string{"a.txt"}) {
		t.Errorf("CherryPick = %q, %v, %v; want conflicts in a.txt", tree, conflicts, err)
	}
}
