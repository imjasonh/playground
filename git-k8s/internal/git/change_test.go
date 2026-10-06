package git_test

import (
	"os"
	"path/filepath"
	"strconv"
	"strings"
	"testing"

	"github.com/imjasonh/playground/git-k8s/internal/git"
	"github.com/imjasonh/playground/git-k8s/internal/gittest"
)

func TestSameChange(t *testing.T) {
	ctx := t.Context()
	srv := gittest.NewServer(t, "")
	w := srv.NewWork(t, "app")
	var branches []string
	// keep pushes the current commit, so that the repository that
	// SameChange reads can fetch it, and returns the commit.
	keep := func() string {
		t.Helper()
		branches = append(branches, "keep"+strconv.Itoa(len(branches)))
		w.Push(branches[len(branches)-1])
		return w.Git("rev-parse", "--verify", "--end-of-options", "HEAD")
	}
	// write writes files in the working tree. An empty content removes the
	// file.
	write := func(files map[string]string) {
		t.Helper()
		for path, content := range files {
			if content == "" {
				w.Git("rm", "--quiet", "--end-of-options", path)
			} else {
				w.Write(path, content)
			}
		}
	}
	commit := func(from, message string, files map[string]string) string {
		t.Helper()
		w.Branch("work", from)
		write(files)
		w.Commit(message)
		return keep()
	}
	pick := func(from string, commits ...string) string {
		t.Helper()
		w.Branch("work", from)
		for _, c := range commits {
			w.Git("cherry-pick", "--end-of-options", c)
		}
		return keep()
	}
	merge := func(from, other string, args ...string) string {
		t.Helper()
		w.Branch("work", from)
		w.Git(append(append([]string{"merge", "--quiet", "--no-edit"}, args...), "--end-of-options", other)...)
		return keep()
	}
	// resolve merges other into from, then commits the merge with files
	// changed, whether the merge conflicted or not.
	resolve := func(from, other string, files map[string]string) string {
		t.Helper()
		w.Branch("work", from)
		_, _ = w.TryGit("merge", "--quiet", "--no-commit", "--no-ff", "--end-of-options", other)
		write(files)
		w.Commit("merge " + other[:7])
		return keep()
	}
	move := func(from, path, to string) string {
		t.Helper()
		w.Branch("work", from)
		w.Git("mv", "--end-of-options", path, to)
		w.Commit("move " + path + " to " + to)
		return keep()
	}
	chmod := func(from, path string, mode os.FileMode) string {
		t.Helper()
		w.Branch("work", from)
		if err := os.Chmod(filepath.Join(w.Dir, path), mode); err != nil {
			t.Fatal(err)
		}
		w.Commit("change " + path + "'s mode")
		return keep()
	}
	symlink := func(from, path, target string) string {
		t.Helper()
		w.Branch("work", from)
		full := filepath.Join(w.Dir, path)
		if err := os.Remove(full); err != nil && !os.IsNotExist(err) {
			t.Fatal(err)
		}
		if err := os.Symlink(target, full); err != nil {
			t.Fatal(err)
		}
		w.Commit("point " + path + " at " + target)
		return keep()
	}
	// gitlink points a submodule at a commit. Commit would remove it,
	// because no repository is checked out there.
	gitlink := func(from, path, target string) string {
		t.Helper()
		w.Branch("work", from)
		w.Git("update-index", "--add", "--cacheinfo", "160000,"+target+","+path)
		w.Git("commit", "--quiet", "-m", "point "+path+" at "+target[:7])
		return keep()
	}
	// text is a.txt's nine lines, with some changed.
	text := func(changed map[int]string) string {
		var b strings.Builder
		for i := 1; i <= 9; i++ {
			line, ok := changed[i]
			if !ok {
				line = strconv.Itoa(i)
			}
			b.WriteString(line + "\n")
		}
		return b.String()
	}

	w.Write("a.txt", text(nil))
	w.Write("b.txt", "b\n")
	w.Write("old.txt", "old\n")
	w.Write("run.sh", "echo hi\n")
	w.Write("img.bin", "\x00\x01\x02\x03")
	w.Write("dir/x.txt", "x\n")
	w.Write("dir/y.txt", "y\n")
	if err := os.Symlink("a.txt", filepath.Join(w.Dir, "link")); err != nil {
		t.Fatal(err)
	}
	w.Commit("start")
	start := keep()
	// Most cases move the parent from start to parent, which changes a line
	// that the heads don't.
	parent := commit(start, "change 9", map[string]string{"a.txt": text(map[int]string{9: "nine"})})
	head := commit(start, "change 1", map[string]string{"a.txt": text(map[int]string{1: "one"})})
	two := commit(head, "change 2", map[string]string{"a.txt": text(map[int]string{1: "one", 2: "two"})})
	merged := merge(head, parent)
	rebased := pick(parent, head)
	rebasedTwo := pick(parent, head, two)
	squashed := commit(parent, "change 1 and 2", map[string]string{"a.txt": text(map[int]string{1: "one", 2: "two", 9: "nine"})})
	reworded := commit(start, "change the first line", map[string]string{"a.txt": text(map[int]string{1: "one"})})
	w.Branch("work", head)
	for i := range 100 {
		w.Git("commit", "--quiet", "--allow-empty", "-m", "later "+strconv.Itoa(i))
	}
	later := keep()
	mergedLater := merge(later, parent)
	both := commit(start, "change a.txt and b.txt", map[string]string{"a.txt": text(map[int]string{1: "one"}), "b.txt": "bee\n"})
	parentB := commit(start, "change b.txt", map[string]string{"b.txt": "bee\n"})
	mergedBoth := merge(both, parentB)
	parentAll := commit(start, "change 1 on the parent", map[string]string{"a.txt": text(map[int]string{1: "one"})})
	mergedAll := merge(head, parentAll)
	parentMoved := move(start, "run.sh", "start.sh")
	mergedMoved := merge(head, parentMoved)
	renamed := move(start, "b.txt", "bee.txt")
	renamedRebased := pick(parent, renamed)
	mode := chmod(start, "run.sh", 0o755)
	modeRebased := pick(parent, mode)
	script := commit(start, "change run.sh", map[string]string{"run.sh": "echo hello\n"})
	modeOnScript := pick(script, mode)
	bin := commit(start, "change img.bin", map[string]string{"img.bin": "\x00\x09\x09\x09"})
	binRebased := pick(parent, bin)
	del := commit(start, "remove old.txt", map[string]string{"old.txt": ""})
	delRebased := pick(parent, del)
	retarget := symlink(start, "link", "b.txt")
	retargetRebased := pick(parent, retarget)
	sub := gitlink(start, "sub", start)
	subRebased := pick(parent, sub)

	amended := commit(parent, "change 1 and 5", map[string]string{"a.txt": text(map[int]string{1: "one", 5: "five", 9: "nine"})})
	amendedInPlace := commit(start, "change 1 and 5", map[string]string{"a.txt": text(map[int]string{1: "one", 5: "five"})})
	extra := commit(rebased, "add c.txt", map[string]string{"c.txt": "c\n"})
	extraAfterMerge := commit(merged, "add c.txt", map[string]string{"c.txt": "c\n"})
	evil := resolve(head, parent, map[string]string{"c.txt": "c\n"})
	undone := resolve(head, parent, map[string]string{"a.txt": text(map[int]string{1: "one"})})
	// conflict changes the line that head does.
	conflict := commit(start, "change 1 too", map[string]string{"a.txt": text(map[int]string{1: "uno"})})
	kept := merge(head, conflict, "-X", "ours")
	rewritten := resolve(head, conflict, map[string]string{"a.txt": text(map[int]string{1: "one uno"})})
	union := commit(start, "change 1 and union-merge a.txt",
		map[string]string{"a.txt": text(map[int]string{1: "one"}), ".gitattributes": "a.txt merge=union\n"})
	unioned := merge(union, conflict)
	modeDropped := commit(parent, "leave run.sh's mode", nil)
	parentMode := chmod(start, "run.sh", 0o755)
	scriptOnMode := merge(script, parentMode)
	otherBin := commit(start, "change img.bin too", map[string]string{"img.bin": "\x00\x07\x07\x07"})
	binKept := merge(bin, otherBin, "-X", "ours")
	delDropped := commit(parent, "leave old.txt", nil)
	older := commit(start, "change old.txt", map[string]string{"old.txt": "older\n"})
	delResolved := resolve(del, older, map[string]string{"old.txt": ""})
	otherTarget := symlink(start, "link", "old.txt")
	retargetKept := merge(retarget, otherTarget, "-X", "ours")
	otherSub := gitlink(start, "sub", parent)
	subMoved := gitlink(otherSub, "sub", start)
	parentRenamed := move(start, "a.txt", "z.txt")
	followed := pick(parentRenamed, head)
	parentDir := move(start, "dir", "lib")
	added := commit(start, "add dir/new.txt", map[string]string{"dir/new.txt": "new\n"})
	placed := commit(parentDir, "add lib/new.txt", map[string]string{"lib/new.txt": "new\n"})
	w.Git("checkout", "--quiet", "--orphan", "lone")
	w.Commit("start over")
	lone := keep()

	repo, err := (&git.Git{}).Open(ctx, filepath.Join(t.TempDir(), "app.git"))
	if err != nil {
		t.Fatal(err)
	}
	if err := repo.Fetch(ctx, srv.Remote("app"), branches...); err != nil {
		t.Fatal(err)
	}
	change := func(base, head string) git.Change { return git.Change{Base: base, Head: head} }
	for _, c := range []struct {
		name string
		a, b git.Change
		want bool
	}{
		{"the same change", change(start, head), change(start, head), true},
		{"a merge of a newer parent, as the base check makes", change(start, head), change(parent, merged), true},
		{"a rebase onto a newer parent", change(start, head), change(parent, rebased), true},
		{"a rebase of two commits", change(start, two), change(parent, rebasedTwo), true},
		{"a squash onto a newer parent", change(start, two), change(parent, squashed), true},
		{"another commit with the same files on the same merge base", change(start, head), change(start, reworded), true},
		{"a merge of a newer parent into 101 commits", change(start, later), change(parent, mergedLater), true},
		{"a merge of a parent that has part of the change", change(start, both), change(parentB, mergedBoth), true},
		{"a merge of a parent that has all of the change", change(start, head), change(parentAll, mergedAll), true},
		{"a merge of a parent that renamed another file", change(start, head), change(parentMoved, mergedMoved), true},
		{"a head that takes back a merge of a newer parent", change(parent, merged), change(start, head), true},
		{"the same head after the parent lands part of it", change(start, rebased), change(parent, rebased), true},
		{"a rebase of a rename", change(start, renamed), change(parent, renamedRebased), true},
		{"a rebase of a mode change", change(start, mode), change(parent, modeRebased), true},
		{"a rebase of a mode change onto a parent that changed the file", change(start, mode), change(script, modeOnScript), true},
		{"a rebase of a binary file's change", change(start, bin), change(parent, binRebased), true},
		{"a rebase of a deletion", change(start, del), change(parent, delRebased), true},
		{"a rebase of a symbolic link's change", change(start, retarget), change(parent, retargetRebased), true},
		{"a rebase of a submodule", change(start, sub), change(parent, subRebased), true},

		{"amended code", change(start, head), change(parent, amended), false},
		{"amended code on the same merge base", change(start, head), change(start, amendedInPlace), false},
		{"an extra commit", change(start, head), change(parent, extra), false},
		{"an extra commit after a merge of a newer parent", change(start, head), change(parent, extraAfterMerge), false},
		{"a merge of a newer parent that adds a file", change(start, head), change(parent, evil), false},
		{"a merge of a newer parent that undoes the parent's change", change(start, head), change(parent, undone), false},
		{"a merge that resolves a conflict with the head's side", change(start, head), change(conflict, kept), false},
		{"a merge that resolves a conflict with new code", change(start, head), change(conflict, rewritten), false},
		{"a merge that a union attribute makes clean", change(start, union), change(conflict, unioned), false},
		{"a rebase that drops a mode change", change(start, mode), change(parent, modeDropped), false},
		{"a merge of a parent that made the changed file executable", change(start, script), change(parentMode, scriptOnMode), false},
		{"a merge that resolves a conflict in a binary file", change(start, bin), change(otherBin, binKept), false},
		{"a rebase that drops a deletion", change(start, del), change(parent, delDropped), false},
		{"a deletion of a file that the parent changed", change(start, del), change(older, delResolved), false},
		{"a merge that resolves a conflict in a symbolic link", change(start, retarget), change(otherTarget, retargetKept), false},
		{"a submodule that the parent added too", change(start, sub), change(otherSub, subMoved), false},
		{"a change that lands in a file that the parent renamed", change(start, head), change(parentRenamed, followed), false},
		{"a file that lands in a directory that the parent renamed", change(start, added), change(parentDir, placed), false},
		{"the same head after the parent rewinds past a commit that the head has", change(parent, rebased), change(start, rebased), false},
		{"a head without a merge base", change(start, head), change("", lone), false},
		{"the same head without a merge base", change("", lone), change("", lone), false},
	} {
		t.Run(c.name, func(t *testing.T) {
			if got, err := repo.SameChange(t.Context(), c.a, c.b); err != nil || got != c.want {
				t.Errorf("SameChange(%.7s..%.7s, %.7s..%.7s) = %t, %v; want %t", c.a.Base, c.a.Head, c.b.Base, c.b.Head, got, err, c.want)
			}
		})
	}

	t.Run("names that aren't object names", func(t *testing.T) {
		if got, err := repo.SameChange(t.Context(), change("main", head), change(parent, rebased)); err == nil {
			t.Errorf("SameChange = %t, want an error", got)
		}
	})

	t.Run("a commit that the repository doesn't have", func(t *testing.T) {
		missing := strings.Repeat("1", 40)
		if got, err := repo.SameChange(t.Context(), change(start, missing), change(parent, rebased)); err == nil {
			t.Errorf("SameChange with another merge base = %t, want an error", got)
		}
		if got, err := repo.SameChange(t.Context(), change(start, missing), change(start, head)); err == nil {
			t.Errorf("SameChange with the same merge base = %t, want an error", got)
		}
	})

	t.Run("five git commands for any number of commits", func(t *testing.T) {
		repo, commands := logged(t, repo)
		if got, err := repo.SameChange(t.Context(), change(start, later), change(parent, mergedLater)); err != nil || !got {
			t.Fatalf("SameChange = %t, %v; want true", got, err)
		}
		if ran := commands(); len(ran) > 5 {
			t.Errorf("SameChange ran %d git commands, want at most 5:\n%s", len(ran), strings.Join(ran, "\n"))
		}
	})

	t.Run("a union attribute that the repository's config reads", func(t *testing.T) {
		repo, err := (&git.Git{}).Open(t.Context(), filepath.Join(t.TempDir(), "app.git"))
		if err != nil {
			t.Fatal(err)
		}
		if err := repo.Fetch(t.Context(), srv.Remote("app"), branches...); err != nil {
			t.Fatal(err)
		}
		config := filepath.Join(repo.Dir, "config")
		b, err := os.ReadFile(config)
		if err != nil {
			t.Fatal(err)
		}
		if err := os.WriteFile(config, append(b, "[attr]\n\ttree = "+union+"\n"...), 0o644); err != nil {
			t.Fatal(err)
		}
		if got, err := repo.SameChange(t.Context(), change(start, union), change(conflict, unioned)); err != nil || got {
			t.Errorf("SameChange = %t, %v; want false", got, err)
		}
	})
}

func TestFetchCommits(t *testing.T) {
	ctx := t.Context()
	srv := gittest.NewServer(t, "")
	w := srv.NewWork(t, "app")
	w.Write("a.txt", "a\n")
	w.Commit("start")
	w.Push("main")
	w.Write("a.txt", "b\n")
	gone := w.Commit("change a.txt")
	w.Push("gone")
	w.Delete("gone")

	repo, err := (&git.Git{}).Open(ctx, filepath.Join(t.TempDir(), "app.git"))
	if err != nil {
		t.Fatal(err)
	}
	if err := repo.Fetch(ctx, srv.Remote("app"), "main"); err != nil {
		t.Fatal(err)
	}
	if ok, err := repo.HasCommit(ctx, gone); err != nil || ok {
		t.Fatalf("HasCommit before FetchCommits = %t, %v; want false", ok, err)
	}
	if err := repo.FetchCommits(ctx, srv.Remote("app"), gone); err != nil {
		t.Fatalf("FetchCommits of a commit that no branch has: %v", err)
	}
	if ok, err := repo.HasCommit(ctx, gone); err != nil || !ok {
		t.Errorf("HasCommit after FetchCommits = %t, %v; want true", ok, err)
	}
	if err := repo.FetchCommits(ctx, srv.Remote("app")); err != nil {
		t.Errorf("FetchCommits of no commits: %v", err)
	}
	if err := repo.FetchCommits(ctx, srv.Remote("app"), strings.Repeat("1", 40)); err == nil {
		t.Error("FetchCommits of a commit that the remote doesn't have succeeded, want an error")
	}
	if err := repo.FetchCommits(ctx, srv.Remote("app"), "main"); err == nil {
		t.Error("FetchCommits of a branch name succeeded, want an error")
	}
}
