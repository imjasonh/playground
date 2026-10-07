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

func TestMergeListsConflicts(t *testing.T) {
	srv := gittest.NewServer(t, "")
	w := srv.NewWork(t, "app")
	// The branch's own attributes don't decide how its conflicts merge.
	w.Write(".gitattributes", "*.txt merge=union\n")
	w.Write("notes.txt", "a\nb\nc\n")
	w.Write("go.sum", "x v1\n")
	w.Write("gone.txt", "old\n")
	base := w.Commit("base")
	w.Write("notes.txt", "a\nTHEIRS\nc\n")
	w.Write("go.sum", "x v1\ny v2\n")
	w.Write("gone.txt", "changed\n")
	theirs := w.Commit("theirs")
	w.Push("main")
	w.Branch("c/x", base)
	w.Write("notes.txt", "a\nOURS\nc\n")
	w.Write("go.sum", "x v1\nz v3\n")
	w.Git("rm", "--quiet", "--end-of-options", "gone.txt")
	ours := w.Commit("ours")
	w.Push("c/x")

	ctx := t.Context()
	repo, err := (&git.Git{}).Open(ctx, filepath.Join(t.TempDir(), "app.git"))
	if err != nil {
		t.Fatal(err)
	}
	if err := repo.Fetch(ctx, srv.Remote("app"), "main", "c/x"); err != nil {
		t.Fatal(err)
	}
	// Some versions, such as 2.43, read a bare repository's attributes from
	// HEAD's tree. Later versions read them only from the tree that
	// attr.tree names.
	if err := os.WriteFile(filepath.Join(repo.Dir, "HEAD"), []byte("ref: refs/remotes/origin/c/x\n"), 0o644); err != nil {
		t.Fatal(err)
	}
	readAttributesFrom(t, repo, ours)

	tree, conflicts, err := repo.Merge(ctx, ours, theirs, git.MergeOptions{Base: base})
	if err != nil {
		t.Fatal(err)
	}
	byPath := map[string]git.Conflict{}
	for _, c := range conflicts {
		byPath[c.Path] = c
	}
	if len(byPath) != 3 || len(conflicts) != 3 {
		t.Fatalf("conflicts = %+v; want go.sum, gone.txt, and notes.txt once each", conflicts)
	}
	if c := byPath["notes.txt"]; c.Base == nil || c.Ours == nil || c.Theirs == nil || c.Ours.Mode != "100644" || c.Ours.Type != "blob" {
		t.Errorf("notes.txt conflict = %+v; want every side, as a regular file", c)
	}
	if c := byPath["gone.txt"]; c.Base == nil || c.Ours != nil || c.Theirs == nil {
		t.Errorf("gone.txt conflict = %+v; want no version on our side, which deleted it", c)
	}
	got, err := repo.ReadBlob(ctx, mustEntry(t, repo, tree, "notes.txt"))
	if err != nil {
		t.Fatal(err)
	}
	want := "a\n<<<<<<< " + ours + "\nOURS\n||||||| " + base + "\nb\n=======\nTHEIRS\n>>>>>>> " + theirs + "\nc\n"
	if string(got) != want {
		t.Errorf("merged notes.txt =\n%s\nwant\n%s", got, want)
	}

	_, found, err := repo.Merge(ctx, ours, theirs, git.MergeOptions{})
	if err != nil || len(found) != 3 {
		t.Errorf("Merge without a base found conflicts %+v, %v; want the same three", found, err)
	}

	tree, conflicts, err = repo.Merge(ctx, ours, theirs, git.MergeOptions{Base: base, Union: []string{"go.sum"}})
	if err != nil {
		t.Fatal(err)
	}
	var paths []string
	for _, c := range conflicts {
		paths = append(paths, c.Path)
	}
	if !slices.Equal(paths, []string{"gone.txt", "notes.txt"}) {
		t.Errorf("conflicts with go.sum union-merged = %v; want [gone.txt notes.txt]", paths)
	}
	if got, err := repo.ReadBlob(ctx, mustEntry(t, repo, tree, "go.sum")); err != nil || string(got) != "x v1\nz v3\ny v2\n" {
		t.Errorf("union-merged go.sum = %q, %v; want both sides' lines", got, err)
	}

	if _, _, err := repo.Merge(ctx, ours, theirs, git.MergeOptions{Union: []string{"go sum"}}); err == nil {
		t.Error("Merge with a union pattern that holds a space succeeded")
	}
}

func TestUnionAttributes(t *testing.T) {
	got, err := git.UnionAttributes([]string{"go.sum", "**/go.sum", "CHANGELOG.md"})
	if want := "go.sum merge=union\n**/go.sum merge=union\nCHANGELOG.md merge=union\n"; err != nil || got != want {
		t.Errorf("UnionAttributes = %q, %v; want %q", got, err, want)
	}
	for _, p := range []string{"", "go sum", "go.sum\tmerge=binary", "a\nb", "!go.sum", "#go.sum", `"go.sum"`, "[attr]x"} {
		if _, err := git.UnionAttributes([]string{p}); err == nil {
			t.Errorf("UnionAttributes(%q) succeeded", p)
		}
	}
}

func TestMergeBases(t *testing.T) {
	srv := gittest.NewServer(t, "")
	w := srv.NewWork(t, "app")
	root := w.Commit("root")
	w.Write("a.txt", "a\n")
	a := w.Commit("a")
	w.Branch("b", root)
	w.Write("b.txt", "b\n")
	b := w.Commit("b")
	w.Git("merge", "--quiet", "--no-edit", "--end-of-options", a)
	ba := w.Git("rev-parse", "--verify", "--end-of-options", "HEAD")
	w.Branch("a", a)
	w.Git("merge", "--quiet", "--no-edit", "--end-of-options", b)
	ab := w.Git("rev-parse", "--verify", "--end-of-options", "HEAD")
	w.Git("checkout", "--quiet", "--orphan", "unrelated")
	unrelated := w.Commit("unrelated")
	for _, c := range []string{ba, ab, unrelated} {
		w.Git("switch", "--quiet", "--detach", "--end-of-options", c)
		w.Push("x/" + c)
	}

	ctx := t.Context()
	repo, err := (&git.Git{}).Open(ctx, filepath.Join(t.TempDir(), "app.git"))
	if err != nil {
		t.Fatal(err)
	}
	if err := repo.Fetch(ctx, srv.Remote("app"), "x/"+ba, "x/"+ab, "x/"+unrelated); err != nil {
		t.Fatal(err)
	}
	for _, tc := range []struct {
		a, b string
		want []string
	}{
		{a, b, []string{root}},
		{ba, ab, []string{a, b}},
		{a, unrelated, nil},
	} {
		got, err := repo.MergeBases(ctx, tc.a, tc.b)
		slices.Sort(got)
		slices.Sort(tc.want)
		if err != nil || !slices.Equal(got, tc.want) {
			t.Errorf("MergeBases(%s, %s) = %v, %v; want %v", tc.a, tc.b, got, err, tc.want)
		}
	}
}

func TestFetchRef(t *testing.T) {
	srv := gittest.NewServer(t, "s3cret")
	w := srv.NewWork(t, "app")
	main := w.Commit("main")
	w.Push("main")
	external := w.Commit("external")
	w.PushRef("refs/git-k8s/downstream/heads/main")

	ctx := t.Context()
	repo, err := (&git.Git{}).Open(ctx, filepath.Join(t.TempDir(), "app.git"))
	if err != nil {
		t.Fatal(err)
	}
	remote := srv.Remote("app")
	for ref, want := range map[string]string{
		"refs/git-k8s/downstream/heads/main": external,
		"refs/heads/main":                    main,
	} {
		if got, err := repo.FetchRef(ctx, remote, ref); err != nil || got != want {
			t.Errorf("FetchRef(%s) = %s, %v; want %s", ref, got, err, want)
		}
	}
	if ok, err := repo.IsAncestor(ctx, "refs/remotes/origin/main", main); err != nil || !ok {
		t.Errorf("refs/remotes/origin/main isn't %s after fetching refs/heads/main: %v", main, err)
	}
	if ok, err := repo.IsAncestor(ctx, "refs/git-k8s/downstream/heads/main", external); err != nil || !ok {
		t.Errorf("refs/git-k8s/downstream/heads/main isn't %s after fetching it: %v", external, err)
	}
	for _, ref := range []string{"main", "refs/heads/a:refs/heads/b", "refs/heads/*", "refs/heads/missing"} {
		if got, err := repo.FetchRef(ctx, remote, ref); err == nil {
			t.Errorf("FetchRef(%q) = %s; want an error", ref, got)
		}
	}
	for _, url := range []string{w.Dir, "file://" + w.Dir} {
		if got, err := repo.FetchRef(ctx, git.Remote{URL: url}, "refs/heads/main"); err == nil || !strings.Contains(err.Error(), "not allowed") {
			t.Errorf("FetchRef from %s = %s, %v; want git to refuse the transport, because it fetches only over the network", url, got, err)
		}
	}
}

func TestMergeCommandsAllowOnlyRemoteTransports(t *testing.T) {
	srv := gittest.NewServer(t, "")
	w := srv.NewWork(t, "app")
	w.Write("go.sum", "x v1\n")
	base := w.Commit("base")
	w.Write("go.sum", "x v1\ny v2\n")
	theirs := w.Commit("theirs")
	w.Push("main")
	w.Branch("c/x", base)
	w.Write("go.sum", "x v1\nz v3\n")
	ours := w.Commit("ours")
	w.Push("c/x")

	ctx := t.Context()
	dir := filepath.Join(t.TempDir(), "app.git")
	if _, err := (&git.Git{}).Open(ctx, dir); err != nil {
		t.Fatal(err)
	}
	// The wrapper logs each command's GIT_ALLOW_PROTOCOL and arguments.
	log, bin := filepath.Join(t.TempDir(), "log"), filepath.Join(t.TempDir(), "git")
	script := "#!/bin/sh\nprintf '%s\\t%s\\n' \"$GIT_ALLOW_PROTOCOL\" \"$*\" >>'" + log + "'\nexec git \"$@\"\n"
	if err := os.WriteFile(bin, []byte(script), 0o755); err != nil {
		t.Fatal(err)
	}
	repo, err := (&git.Git{Bin: bin}).Open(ctx, dir)
	if err != nil {
		t.Fatal(err)
	}
	for _, ref := range []string{"refs/heads/main", "refs/heads/c/x"} {
		if _, err := repo.FetchRef(ctx, srv.Remote("app"), ref); err != nil {
			t.Fatal(err)
		}
	}
	if _, err := repo.MergeBases(ctx, ours, theirs); err != nil {
		t.Fatal(err)
	}
	for _, o := range []git.MergeOptions{{}, {Base: base, Union: []string{"go.sum"}}} {
		if _, _, err := repo.Merge(ctx, ours, theirs, o); err != nil {
			t.Fatal(err)
		}
	}

	b, err := os.ReadFile(log)
	if err != nil {
		t.Fatal(err)
	}
	lines := strings.Split(strings.TrimSuffix(string(b), "\n"), "\n")
	if len(lines) != 11 {
		t.Errorf("git ran %d times, want 3 times for each FetchRef, once for MergeBases, and twice for each Merge:\n%s", len(lines), b)
	}
	for _, line := range lines {
		protocols, args, _ := strings.Cut(line, "\t")
		if protocols != "http:https" {
			t.Errorf("git %s ran with GIT_ALLOW_PROTOCOL=%q, want http:https", args, protocols)
		}
		// check-ref-format takes no --end-of-options, and hash-object
		// names no ref or commit.
		if !strings.Contains(args, " check-ref-format ") && !strings.Contains(args, " hash-object ") && !strings.Contains(args, " --end-of-options ") {
			t.Errorf("git %s names a ref or a commit without --end-of-options before it", args)
		}
	}
}
