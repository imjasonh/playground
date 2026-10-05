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
	w.Write("b.txt", "1\n2\n3\n")
	base := w.Commit("base")
	w.Write("a.txt", "main\n")
	w.Write("b.txt", "one\n2\n3\n")
	parent := w.Commit("main edit")
	w.Push("main")
	w.Branch("c/x", base)
	// The branch's own attributes would hide the conflict in a.txt and make
	// one in b.txt, whose edits don't overlap.
	w.Write(".gitattributes", "a.txt merge=union\nb.txt merge=binary\n")
	w.Write("a.txt", "branch\n")
	w.Write("b.txt", "1\n2\nthree\n")
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
	if err := os.WriteFile(filepath.Join(repo.Dir, "HEAD"), []byte("ref: refs/remotes/origin/c/x\n"), 0o644); err != nil {
		t.Fatal(err)
	}
	readAttributesFrom(t, repo, head)
	if tree, conflicts, err := repo.CherryPick(ctx, head, base, parent); err != nil || tree != "" || !slices.Equal(conflicts, []string{"a.txt"}) {
		t.Errorf("CherryPick = %q, %v, %v; want conflicts in a.txt", tree, conflicts, err)
	}
}

// fetched returns a new repository with the branches of the server's
// repository app.
func fetched(t *testing.T, srv *gittest.Server, branches ...string) *git.Repo {
	t.Helper()
	repo, err := (&git.Git{}).Open(t.Context(), filepath.Join(t.TempDir(), "app.git"))
	if err != nil {
		t.Fatal(err)
	}
	if err := repo.Fetch(t.Context(), srv.Remote("app"), branches...); err != nil {
		t.Fatal(err)
	}
	return repo
}

// readAttributesFrom sets attr.tree in the repository's config, which makes
// git read attributes from tree, as some versions do from HEAD in a bare
// repository.
func readAttributesFrom(t *testing.T, repo *git.Repo, tree string) {
	t.Helper()
	config := filepath.Join(repo.Dir, "config")
	b, err := os.ReadFile(config)
	if err != nil {
		t.Fatal(err)
	}
	if err := os.WriteFile(config, append(b, "[attr]\n\ttree = "+tree+"\n"...), 0o644); err != nil {
		t.Fatal(err)
	}
}

// wrap opens repo's directory with a git that runs script before it runs
// git with the same arguments.
func wrap(t *testing.T, repo *git.Repo, script string) *git.Repo {
	t.Helper()
	bin := filepath.Join(t.TempDir(), "git")
	if err := os.WriteFile(bin, []byte("#!/bin/sh\n"+script+"\nexec git \"$@\"\n"), 0o755); err != nil {
		t.Fatal(err)
	}
	wrapped, err := (&git.Git{Bin: bin}).Open(t.Context(), repo.Dir)
	if err != nil {
		t.Fatal(err)
	}
	return wrapped
}

// logged opens repo's directory with a git that logs each command. The
// function that it returns checks that each command ran with
// GIT_ALLOW_PROTOCOL=http:https:git:ssh, and returns their arguments.
func logged(t *testing.T, repo *git.Repo) (*git.Repo, func() []string) {
	t.Helper()
	log := filepath.Join(t.TempDir(), "log")
	logging := wrap(t, repo, `printf '%s\t%s\n' "$GIT_ALLOW_PROTOCOL" "$*" >>'`+log+`'`)
	return logging, func() []string {
		t.Helper()
		b, err := os.ReadFile(log)
		if err != nil {
			t.Fatal(err)
		}
		var commands []string
		for _, line := range strings.Split(strings.TrimSuffix(string(b), "\n"), "\n") {
			protocols, args, _ := strings.Cut(line, "\t")
			if protocols != "http:https:git:ssh" {
				t.Errorf("git %s ran with GIT_ALLOW_PROTOCOL=%q, want http:https:git:ssh", args, protocols)
			}
			commands = append(commands, args)
		}
		return commands
	}
}

func TestRevsAndPatchIDs(t *testing.T) {
	srv := gittest.NewServer(t, "")
	w := srv.NewWork(t, "app")
	w.Write("a.txt", "1\n2\n3\n")
	base := w.Commit("base")
	w.Write("a.txt", "1\ntwo\n3\n")
	change := w.Commit("change")
	empty := w.Commit("change nothing")
	w.Branch("side", base)
	w.Write("b.txt", "b\n")
	side := w.Commit("side")
	w.Branch("main", empty)
	w.Git("merge", "--quiet", "--no-edit", "--end-of-options", side)
	merge := w.Git("rev-parse", "--verify", "--end-of-options", "HEAD")
	w.Push("main")
	// The same change, below a line that base doesn't have.
	w.Branch("moved", base)
	w.Write("a.txt", "0\n1\n2\n3\n")
	moved := w.Commit("add a line")
	w.Write("a.txt", "0\n1\ntwo\n3\n")
	again := w.Commit("change again")
	w.Push("moved")
	w.Branch("attributes", base)
	w.Write(".gitattributes", "*.txt -diff\n")
	binary := w.Commit("mark text files binary")
	w.Push("attributes")
	ctx := t.Context()
	repo := fetched(t, srv, "main", "moved")

	revs, err := repo.Revs(ctx, merge, base, "")
	if err != nil {
		t.Fatal(err)
	}
	parents := map[string][]string{change: {base}, empty: {change}, side: {base}, merge: {empty, side}}
	seen := map[string]bool{}
	for _, r := range revs {
		if want, ok := parents[r.Commit]; !ok || !slices.Equal(r.Parents, want) {
			t.Errorf("Revs listed %s with the parents %v, want %v", r.Commit, r.Parents, want)
		}
		for _, p := range r.Parents {
			if _, listed := parents[p]; listed && !seen[p] {
				t.Errorf("Revs listed %s before its parent %s", r.Commit, p)
			}
		}
		seen[r.Commit] = true
	}
	if len(revs) != len(parents) {
		t.Errorf("Revs = %+v, want the %d commits after base", revs, len(parents))
	}
	if revs, err := repo.Revs(ctx, merge, empty, side); err != nil || len(revs) != 1 || revs[0].Commit != merge {
		t.Errorf("Revs excluding both parents = %+v, %v; want only the merge", revs, err)
	}

	ids, err := repo.PatchIDs(ctx, []string{change, empty, side, merge, moved, again})
	if err != nil {
		t.Fatal(err)
	}
	if ids[change] == "" || ids[change] != ids[again] {
		t.Errorf("patch IDs of the same change at other lines = %q and %q, want the same ID", ids[change], ids[again])
	}
	if ids[side] == "" || ids[side] == ids[change] || ids[moved] == "" || ids[moved] == ids[change] {
		t.Errorf("patch IDs = %v, want other changes to have other IDs", ids)
	}
	if ids[empty] != "" || ids[merge] != "" {
		t.Errorf("patch IDs of an empty commit and a merge = %q and %q, want none", ids[empty], ids[merge])
	}
	if ids, err := repo.PatchIDs(ctx, nil); err != nil || len(ids) != 0 {
		t.Errorf("PatchIDs(nil) = %v, %v", ids, err)
	}

	t.Run("a diff attribute that marks the text files binary", func(t *testing.T) {
		repo := fetched(t, srv, "main", "moved", "attributes")
		readAttributesFrom(t, repo, binary)
		ids, err := repo.PatchIDs(t.Context(), []string{change, again})
		if err != nil || ids[change] == "" || ids[change] != ids[again] {
			t.Errorf("patch IDs of the same change at other lines = %q and %q, %v; want the same ID", ids[change], ids[again], err)
		}
	})
}

func TestPatchIDsReportsDiffTreeFailures(t *testing.T) {
	srv := gittest.NewServer(t, "")
	w := srv.NewWork(t, "app")
	w.Write("a.txt", "a\n")
	change := w.Commit("add a.txt")
	w.Push("main")
	// The wrapper fails each diff-tree, as git does when a commit's tree is
	// missing.
	repo := wrap(t, fetched(t, srv, "main"), `case " $* " in *" diff-tree "*) echo "fatal: unable to read tree" >&2; exit 128 ;; esac`)

	if ids, err := repo.PatchIDs(t.Context(), []string{change}); err == nil || err.Error() != "git diff-tree: exit status 128: fatal: unable to read tree" {
		t.Errorf("PatchIDs when diff-tree fails = %v, %v; want diff-tree's exit status", ids, err)
	}
}

func TestPatchIDsAllowOnlyRemoteTransports(t *testing.T) {
	srv := gittest.NewServer(t, "")
	w := srv.NewWork(t, "app")
	w.Write("a.txt", "a\n")
	change := w.Commit("add a.txt")
	w.Push("main")
	repo, commands := logged(t, fetched(t, srv, "main"))

	if _, err := repo.PatchIDs(t.Context(), []string{change}); err != nil {
		t.Fatal(err)
	}
	if got := commands(); len(got) != 3 {
		t.Errorf("PatchIDs ran git %q; want hash-object, diff-tree, and patch-id", got)
	}
}

func TestReplay(t *testing.T) {
	srv := gittest.NewServer(t, "")
	w := srv.NewWork(t, "app")
	w.Write("a.txt", "1\n2\n3\n")
	base := w.Commit("base")
	w.Write("a.txt", "1\ntwo\n3\n")
	w.Git("add", "-A")
	w.Git("commit", "--quiet", "--author=Ann Author <ann@example.com>", "--date=2020-01-02T03:04:05+01:00", "-m", "Change two\n\nIt was 2.\n")
	original := w.Git("rev-parse", "--verify", "--end-of-options", "HEAD")
	w.Push("main")
	ctx := t.Context()
	repo := fetched(t, srv, "main")
	id := git.Identity{Name: "git-k8s", Email: "git-k8s@example.com"}
	// The parent that the replay goes on adds a file, and is newer than the
	// original.
	c, err := repo.Commit(ctx, base)
	if err != nil {
		t.Fatal(err)
	}
	blob, err := repo.WriteBlob(ctx, []byte("b\n"))
	if err != nil {
		t.Fatal(err)
	}
	ontoTree, err := repo.ReplaceFiles(ctx, c.Tree, []git.TreeEntry{{Mode: "100644", SHA: blob, Path: "b.txt"}})
	if err != nil {
		t.Fatal(err)
	}
	onto, err := repo.CommitTree(ctx, ontoTree, []string{base}, "Add b\n", id, 1900000000)
	if err != nil {
		t.Fatal(err)
	}
	tree, conflicts, err := repo.Merge(ctx, onto, original, git.MergeOptions{Base: base})
	if err != nil || len(conflicts) != 0 {
		t.Fatalf("Merge = %v, %v", conflicts, err)
	}

	replay, err := repo.Replay(ctx, original, onto, tree, id)
	if err != nil {
		t.Fatal(err)
	}
	if again, err := repo.Replay(ctx, original, onto, tree, id); err != nil || again != replay {
		t.Errorf("Replay again = %s, %v; want the same commit %s", again, err, replay)
	}
	if err := repo.Push(ctx, srv.Remote("app"), git.RefUpdate{Ref: "refs/heads/replay", New: replay}); err != nil {
		t.Fatal(err)
	}
	w.Fetch("replay")
	const format = "--format=%P%n%T%n%an <%ae> %ad%n%cn <%ce> %cd%n%B"
	got := w.Git("log", "-1", "--date=raw", format, "--end-of-options", replay)
	authored := w.Git("log", "-1", "--date=raw", "--format=%an <%ae> %ad%n%B", "--end-of-options", original)
	want := onto + "\n" + tree + "\n" + firstLine(authored) + "\ngit-k8s <git-k8s@example.com> 1900000000 +0000\nChange two\n\nIt was 2."
	if got != want {
		t.Errorf("replay =\n%s\nwant\n%s", got, want)
	}
	if firstLine(authored) != "Ann Author <ann@example.com> 1577930645 +0100" {
		t.Errorf("original's author = %q", firstLine(authored))
	}
}

func firstLine(s string) string {
	for line := range strings.Lines(s) {
		return strings.TrimSuffix(line, "\n")
	}
	return ""
}
