package git_test

import (
	"os"
	"path/filepath"
	"slices"
	"strings"
	"testing"

	"github.com/imjasonh/playground/git-k8s/internal/git"
	"github.com/imjasonh/playground/git-k8s/internal/gittest"
)

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
