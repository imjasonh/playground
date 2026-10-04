package git_test

import (
	"errors"
	"path/filepath"
	"slices"
	"strings"
	"testing"

	"github.com/imjasonh/playground/git-k8s/internal/git"
	"github.com/imjasonh/playground/git-k8s/internal/gittest"
)

func TestLsRemoteNeedsCredentials(t *testing.T) {
	srv := gittest.NewServer(t, "s3cret")
	w := srv.NewWork(t, "app")
	main := w.Commit("first")
	w.Push("main")
	w.Branch("c/add", "main")
	add := w.Commit("second")
	w.Push("c/add")

	g := &git.Git{}
	heads, err := g.LsRemote(t.Context(), srv.Remote("app"))
	if err != nil {
		t.Fatal(err)
	}
	if heads["main"] != main || heads["c/add"] != add || len(heads) != 2 {
		t.Errorf("heads = %v", heads)
	}

	wrong := srv.Remote("app")
	wrong.Auth.Password = "nope"
	if _, err := g.LsRemote(t.Context(), wrong); err == nil {
		t.Error("ls-remote with the wrong password succeeded")
	}
}

func TestFetchMergePush(t *testing.T) {
	srv := gittest.NewServer(t, "")
	w := srv.NewWork(t, "app")
	w.Write("a.txt", "one\n")
	base := w.Commit("base")
	w.Push("main")
	w.Write("b.txt", "two\n")
	parent := w.Commit("parent change")
	w.Push("main")
	w.Branch("c/x", base)
	w.Write("c.txt", "three\n")
	head := w.Commit("branch change")
	w.Push("c/x")

	ctx := t.Context()
	g := &git.Git{}
	repo, err := g.Open(ctx, filepath.Join(t.TempDir(), "cache", "app.git"))
	if err != nil {
		t.Fatal(err)
	}
	remote := srv.Remote("app")
	if err := repo.Fetch(ctx, remote, "main", "c/x"); err != nil {
		t.Fatal(err)
	}
	if ok, err := repo.HasCommit(ctx, head); err != nil || !ok {
		t.Fatalf("HasCommit(head) = %v, %v", ok, err)
	}
	if ok, _ := repo.IsAncestor(ctx, parent, head); ok {
		t.Error("the branch doesn't contain the parent yet")
	}
	if mb, err := repo.MergeBase(ctx, parent, head); err != nil || mb != base {
		t.Errorf("MergeBase = %q, %v; want %q", mb, err, base)
	}

	tree, conflicts, err := repo.MergeTree(ctx, head, parent)
	if err != nil || len(conflicts) > 0 {
		t.Fatalf("MergeTree = %q, %v, %v", tree, conflicts, err)
	}
	id := git.Identity{Name: "git-k8s", Email: "git-k8s@example.com"}
	msg := "Merge main into c/x\n\n" + git.FixerTrailer + ": base\n"
	merge, err := repo.CommitTree(ctx, tree, []string{head, parent}, msg, id, 1700000000)
	if err != nil {
		t.Fatal(err)
	}
	again, err := repo.CommitTree(ctx, tree, []string{head, parent}, msg, id, 1700000000)
	if err != nil || again != merge {
		t.Errorf("CommitTree isn't deterministic: %s then %s (%v)", merge, again, err)
	}
	if n, err := repo.CountFixerCommits(ctx, base, merge); err != nil || n != 1 {
		t.Errorf("CountFixerCommits = %d, %v; want 1", n, err)
	}

	// A lease on a stale head fails without changing the branch.
	err = repo.Push(ctx, remote, git.RefUpdate{Ref: "refs/heads/c/x", New: merge, Old: base})
	if !errors.Is(err, git.ErrRejected) {
		t.Fatalf("push with a stale lease: err = %v, want ErrRejected", err)
	}
	var rejected *git.PushError
	if !errors.As(err, &rejected) || rejected.Rejected["refs/heads/c/x"] != "[rejected] (stale info)" || rejected.Refused("refs/heads/c/x") {
		t.Errorf("push with a stale lease: err = %#v, want a stale lease that the remote didn't refuse", err)
	}
	if err := repo.Push(ctx, remote, git.RefUpdate{Ref: "refs/heads/c/x", New: merge, Old: head}); err != nil {
		t.Fatal(err)
	}
	if got := srv.Heads(t, "app")["c/x"]; got != merge {
		t.Errorf("c/x = %s, want %s", got, merge)
	}

	// A remote that refuses one update of an atomic push rejects the others
	// too, but refuses only that one.
	srv.Config(t, "app", "receive.denyDeletes", "true")
	err = repo.Push(ctx, remote, git.RefUpdate{Ref: "refs/heads/main", New: merge, Old: parent}, git.RefUpdate{Ref: "refs/heads/c/x", Old: merge})
	if !errors.As(err, &rejected) || !rejected.Refused("refs/heads/c/x") || rejected.Refused("refs/heads/main") ||
		rejected.Rejected["refs/heads/c/x"] != "[remote rejected] (deletion prohibited)" {
		t.Errorf("push that deletes a branch the remote won't delete: err = %v, want the remote to refuse only the deletion", err)
	}
	if heads := srv.Heads(t, "app"); heads["main"] != parent || heads["c/x"] != merge {
		t.Errorf("heads = %v, want them as they were", heads)
	}
	srv.Config(t, "app", "receive.denyDeletes", "false")

	// Deleting with a lease.
	if err := repo.Push(ctx, remote, git.RefUpdate{Ref: "refs/heads/c/x", Old: merge}); err != nil {
		t.Fatal(err)
	}
	if _, ok := srv.Heads(t, "app")["c/x"]; ok {
		t.Error("c/x still exists after the delete")
	}
}

func TestMergeTreeConflicts(t *testing.T) {
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
	_, conflicts, err := repo.MergeTree(ctx, head, parent)
	if err != nil || !slices.Equal(conflicts, []string{"a.txt"}) {
		t.Errorf("MergeTree conflicts = %v, %v; want [a.txt]", conflicts, err)
	}
}

func TestTreeEditing(t *testing.T) {
	srv := gittest.NewServer(t, "")
	w := srv.NewWork(t, "app")
	w.Write("main.go", "package main\n")
	w.Write("pkg/x.go", "package pkg\n")
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
	entries, err := repo.LsTree(ctx, head)
	if err != nil {
		t.Fatal(err)
	}
	if len(entries) != 2 || entries[1].Path != "pkg/x.go" || entries[1].Mode != "100644" {
		t.Fatalf("LsTree = %+v", entries)
	}
	blob, err := repo.WriteBlob(ctx, []byte("package pkg // edited\n"))
	if err != nil {
		t.Fatal(err)
	}
	c, err := repo.Commit(ctx, head)
	if err != nil {
		t.Fatal(err)
	}
	tree, err := repo.ReplaceFiles(ctx, c.Tree, []git.TreeEntry{{Mode: "100644", SHA: blob, Path: "pkg/x.go"}})
	if err != nil {
		t.Fatal(err)
	}
	commit, err := repo.CommitTree(ctx, tree, []string{head}, "edit", git.Identity{Name: "a", Email: "a@example.com"}, c.Time)
	if err != nil {
		t.Fatal(err)
	}
	got, err := repo.ReadBlob(ctx, mustEntry(t, repo, commit, "pkg/x.go"))
	if err != nil || !strings.Contains(string(got), "edited") {
		t.Errorf("pkg/x.go = %q, %v", got, err)
	}
	stats, err := repo.Numstat(ctx, head, commit)
	if err != nil || len(stats) != 1 || stats[0] != (git.FileStat{Path: "pkg/x.go", Added: 1, Removed: 1}) {
		t.Errorf("Numstat = %+v, %v", stats, err)
	}
}

func TestWrittenIdentity(t *testing.T) {
	srv := gittest.NewServer(t, "")
	w := srv.NewWork(t, "app")
	base := w.Commit("base")
	w.Push("main")

	ctx := t.Context()
	repo, err := (&git.Git{}).Open(ctx, filepath.Join(t.TempDir(), "app.git"))
	if err != nil {
		t.Fatal(err)
	}
	if err := repo.Fetch(ctx, srv.Remote("app"), "main"); err != nil {
		t.Fatal(err)
	}
	c, err := repo.Commit(ctx, base)
	if err != nil {
		t.Fatal(err)
	}
	for _, id := range []git.Identity{
		{Name: "git-k8s", Email: "git-k8s@example.com"},
		{Name: "Zoë Lima", Email: "zoë@example.com"},
		{Name: "git-k8s ", Email: "<git-k8s@example.com>"},
		{Name: `"git-k8s"`, Email: " git-k8s@example.com\n"},
		{Name: "'git-k8s',", Email: ";git-k8s@example.com:"},
		{Name: "git\n-k8s", Email: "git-k8s@<example>.com"},
		{Name: "\tgit, k8s\\", Email: "git-k8s@example.com\x7f"},
		{Name: "Ana Lima\xff", Email: "\x01ana@example.com"},
		{Name: "\xc3<\xa9", Email: "\xef\xbf\xbe@example.com"},
		{Name: "git-k8s", Email: ""},
	} {
		raw, err := repo.CommitTree(ctx, c.Tree, []string{base}, "edit", id, c.Time)
		if err != nil {
			t.Errorf("CommitTree as %q: %v", id, err)
			continue
		}
		if written, err := repo.CommitTree(ctx, c.Tree, []string{base}, "edit", id.Written(), c.Time); err != nil || written != raw {
			t.Errorf("CommitTree as %q = %s, %v; want %s, the commit as %q", id.Written(), written, err, raw, id)
		}
		log, err := repo.Log(ctx, base, raw, 1)
		if err != nil || len(log) != 1 {
			t.Fatalf("Log = %+v, %v", log, err)
		}
		if got := log[0].Committer; got != id.Written() {
			t.Errorf("git writes %q as %q, but Written returns %q", id, got, id.Written())
		}
	}
}

func mustEntry(t *testing.T, repo *git.Repo, commit, path string) string {
	t.Helper()
	entries, err := repo.LsTree(t.Context(), commit)
	if err != nil {
		t.Fatal(err)
	}
	for _, e := range entries {
		if e.Path == path {
			return e.SHA
		}
	}
	t.Fatalf("%s has no %s", commit, path)
	return ""
}
