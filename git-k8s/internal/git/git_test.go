package git_test

import (
	"bytes"
	"errors"
	"maps"
	"net/http"
	"net/http/httptest"
	"os"
	"path/filepath"
	"slices"
	"strings"
	"testing"

	"github.com/imjasonh/playground/git-k8s/internal/git"
	"github.com/imjasonh/playground/git-k8s/internal/gittest"
)

func TestBearerToken(t *testing.T) {
	headers := make(chan string, 1)
	hs := httptest.NewServer(http.HandlerFunc(func(w http.ResponseWriter, r *http.Request) {
		select {
		case headers <- r.Header.Get("Authorization"):
		default:
		}
		http.Error(w, "no", http.StatusForbidden)
	}))
	defer hs.Close()
	remote := git.Remote{URL: hs.URL + "/app.git", Auth: &git.Auth{Username: "u", Password: "p", Token: "t0ken"}}
	if _, err := (&git.Git{}).LsRemote(t.Context(), remote); err == nil {
		t.Fatal("ls-remote succeeded against a server that refuses everything")
	}
	if got := <-headers; got != "Bearer t0ken" {
		t.Errorf("Authorization = %q, want the bearer token instead of basic auth", got)
	}
}

func TestRefTransactions(t *testing.T) {
	srv := gittest.NewServer(t, "")
	w := srv.NewWork(t, "app")
	one := w.Commit("one")
	two := w.Commit("two")
	w.Push("main")

	ctx := t.Context()
	repo, err := (&git.Git{}).Open(ctx, filepath.Join(t.TempDir(), "app.git"))
	if err != nil {
		t.Fatal(err)
	}
	if err := repo.Fetch(ctx, srv.Remote("app"), "main"); err != nil {
		t.Fatal(err)
	}
	if err := repo.UpdateRefs(ctx,
		git.RefUpdate{Ref: "refs/heads/a", New: one},
		git.RefUpdate{Ref: "refs/heads/a/b", New: two},
	); err == nil || errors.Is(err, git.ErrRejected) {
		t.Fatalf("creating refs/heads/a and refs/heads/a/b together: err = %v, want an error that isn't ErrRejected", err)
	}
	if err := repo.UpdateRefs(ctx, git.RefUpdate{Ref: "refs/heads/a", New: one}, git.RefUpdate{Ref: "refs/x/b", New: two}); err != nil {
		t.Fatal(err)
	}
	want := map[string]string{"refs/heads/a": one, "refs/x/b": two, "refs/remotes/origin/main": two}
	if refs, err := repo.Refs(ctx); err != nil || !maps.Equal(refs, want) {
		t.Fatalf("Refs() = %v, %v; want %v", refs, err, want)
	}
	if refs, err := repo.Refs(ctx, "refs/heads", "refs/x/b"); err != nil || len(refs) != 2 || refs["refs/x/b"] != two {
		t.Errorf("Refs(refs/heads, refs/x/b) = %v, %v", refs, err)
	}

	t.Log("A ref can't add a command to the transaction.")
	if err := repo.UpdateRefs(ctx, git.RefUpdate{Ref: "refs/heads/c " + one + "\ncreate refs/heads/d", New: one}); err == nil {
		t.Error("UpdateRefs took a ref with a newline in it")
	}
	if refs, _ := repo.Refs(ctx); !maps.Equal(refs, want) {
		t.Fatalf("after a ref with a newline, refs = %v, want %v", refs, want)
	}

	t.Log("One stale lease leaves every ref as it was.")
	err = repo.UpdateRefs(ctx,
		git.RefUpdate{Ref: "refs/heads/a", New: two, Old: one},
		git.RefUpdate{Ref: "refs/x/b", Old: one},
	)
	if !errors.Is(err, git.ErrRejected) {
		t.Fatalf("err = %v, want ErrRejected", err)
	}
	for _, u := range []git.RefUpdate{{Ref: "refs/x/b", New: one}, {Ref: "refs/heads/a"}, {Ref: "refs/heads/missing", Old: one}} {
		if err := repo.UpdateRefs(ctx, u); !errors.Is(err, git.ErrRejected) {
			t.Errorf("UpdateRefs(%+v) = %v, want ErrRejected", u, err)
		}
	}

	t.Log("A lock that a killed git left isn't a lease that failed.")
	lock := filepath.Join(repo.Dir, "refs", "heads", "a.lock")
	if err := os.WriteFile(lock, nil, 0o644); err != nil {
		t.Fatal(err)
	}
	err = repo.UpdateRefs(ctx, git.RefUpdate{Ref: "refs/heads/a", New: two, Old: one})
	if err == nil || errors.Is(err, git.ErrRejected) || !strings.Contains(err.Error(), "a.lock") {
		t.Errorf("with a stale lock, err = %v; want one about the lock that doesn't wrap ErrRejected", err)
	}
	if err := os.Remove(lock); err != nil {
		t.Fatal(err)
	}

	if err := repo.UpdateRefs(ctx, git.RefUpdate{Ref: "refs/heads/missing"}, git.RefUpdate{Ref: "refs/heads/a", New: two, Old: one}, git.RefUpdate{Ref: "refs/x/b", Old: two}); err != nil {
		t.Fatal(err)
	}
	if refs, _ := repo.Refs(ctx, "refs/heads", "refs/x"); !maps.Equal(refs, map[string]string{"refs/heads/a": two}) {
		t.Errorf("refs = %v, want only refs/heads/a at %s", refs, two)
	}

	if v, ok, err := repo.Config(ctx, "gitk8s.uid"); err != nil || ok || v != "" {
		t.Errorf("Config of an unset key = %q, %v, %v", v, ok, err)
	}
	if err := repo.SetConfig(ctx, "gitk8s.uid", "1234"); err != nil {
		t.Fatal(err)
	}
	if v, ok, err := repo.Config(ctx, "gitk8s.uid"); err != nil || !ok || v != "1234" {
		t.Errorf("Config = %q, %v, %v; want 1234", v, ok, err)
	}
	if err := repo.SetConfig(ctx, "gitk8s.url", "--upload-pack=x"); err != nil {
		t.Fatal(err)
	}
	if v, _, err := repo.Config(ctx, "gitk8s.url"); err != nil || v != "--upload-pack=x" {
		t.Errorf("Config = %q, %v; want --upload-pack=x", v, err)
	}
}

func TestFetchPruneAndPushEach(t *testing.T) {
	srv := gittest.NewServer(t, "pw")
	w := srv.NewWork(t, "app")
	main := w.Commit("main")
	w.Push("main")
	w.Push("old")

	ctx := t.Context()
	repo, err := (&git.Git{}).Open(ctx, filepath.Join(t.TempDir(), "app.git"))
	if err != nil {
		t.Fatal(err)
	}
	remote := srv.Remote("app")
	const refspec = "+refs/heads/*:refs/copy/heads/*"
	if err := repo.FetchPrune(ctx, remote, refspec); err != nil {
		t.Fatal(err)
	}
	if refs, _ := repo.Refs(ctx); !maps.Equal(refs, map[string]string{"refs/copy/heads/main": main, "refs/copy/heads/old": main}) {
		t.Fatalf("after fetching, refs = %v", refs)
	}
	if err := repo.Push(ctx, remote, git.RefUpdate{Ref: "refs/heads/old", Old: main}); err != nil {
		t.Fatal(err)
	}
	w.Write("next.txt", "next\n")
	next := w.Commit("next")
	w.Push("main")
	if err := repo.FetchPrune(ctx, remote, refspec); err != nil {
		t.Fatal(err)
	}
	if refs, _ := repo.Refs(ctx); !maps.Equal(refs, map[string]string{"refs/copy/heads/main": next}) {
		t.Fatalf("after the remote deleted old, refs = %v", refs)
	}

	t.Log("A stale lease rejects only its own update.")
	rejected, err := repo.PushEach(ctx, remote,
		git.RefUpdate{Ref: "refs/heads/main", New: main, Old: main},
		git.RefUpdate{Ref: "refs/heads/new", New: next},
		git.RefUpdate{Ref: "refs/heads/gone", Old: main},
	)
	if err != nil {
		t.Fatal(err)
	}
	if len(rejected) != 2 || rejected["refs/heads/main"] == "" || rejected["refs/heads/gone"] == "" {
		t.Errorf("rejected = %v, want main and gone", rejected)
	}
	if heads := srv.Heads(t, "app"); !maps.Equal(heads, map[string]string{"main": next, "new": next}) {
		t.Errorf("heads = %v", heads)
	}
	rejected, err = repo.PushEach(ctx, remote, git.RefUpdate{Ref: "refs/heads/new", Old: next}, git.RefUpdate{Ref: "refs/heads/main", New: main, Old: next})
	if err != nil || len(rejected) != 0 {
		t.Fatalf("PushEach = %v, %v", rejected, err)
	}
	if heads := srv.Heads(t, "app"); !maps.Equal(heads, map[string]string{"main": main}) {
		t.Errorf("heads = %v, want main moved back and new deleted", heads)
	}

	bad := remote
	bad.Auth = &git.Auth{Username: "git-k8s", Password: "wrong"}
	if _, err := repo.PushEach(ctx, bad, git.RefUpdate{Ref: "refs/heads/main", New: next, Old: main}); err == nil {
		t.Error("PushEach with the wrong password succeeded")
	}
}

func TestFetchPruneAndPushEachReachOnlyTheNetwork(t *testing.T) {
	srv := gittest.NewServer(t, "")
	w := srv.NewWork(t, "app")
	main := w.Commit("main")
	w.Push("main")

	ctx := t.Context()
	repo, err := (&git.Git{}).Open(ctx, filepath.Join(t.TempDir(), "copy.git"))
	if err != nil {
		t.Fatal(err)
	}
	if err := repo.Fetch(ctx, srv.Remote("app"), "main"); err != nil {
		t.Fatal(err)
	}
	dir := filepath.Join(srv.Root, "app.git")
	marker := filepath.Join(t.TempDir(), "ran")
	for _, url := range []string{
		dir,
		"file://" + dir,
		"--upload-pack=touch " + marker + ";false",
		"--receive-pack=touch " + marker + ";false",
	} {
		if err := repo.FetchPrune(ctx, git.Remote{URL: url}, "+refs/heads/*:refs/stolen/*"); err == nil {
			t.Errorf("FetchPrune from %q succeeded", url)
		}
		if _, err := repo.PushEach(ctx, git.Remote{URL: url}, git.RefUpdate{Ref: "refs/heads/planted", New: main}); err == nil {
			t.Errorf("PushEach to %q succeeded", url)
		}
	}
	if refs, _ := repo.Refs(ctx, "refs/stolen"); len(refs) != 0 {
		t.Errorf("fetched %v from a repository on the local disk", refs)
	}
	if heads := srv.Heads(t, "app"); !maps.Equal(heads, map[string]string{"main": main}) {
		t.Errorf("heads = %v, want only main", heads)
	}
	if _, err := os.Stat(marker); !errors.Is(err, os.ErrNotExist) {
		t.Errorf("git ran a command from a URL: %v", err)
	}
}

func TestServe(t *testing.T) {
	srv := gittest.NewServer(t, "")
	w := srv.NewWork(t, "app")
	main := w.Commit("main")
	w.Push("main")
	ctx := t.Context()
	g := &git.Git{}
	repo, err := g.Open(ctx, filepath.Join(t.TempDir(), "app.git"))
	if err != nil {
		t.Fatal(err)
	}
	if err := repo.Fetch(ctx, srv.Remote("app"), "main"); err != nil {
		t.Fatal(err)
	}
	var out bytes.Buffer
	if err := g.Advertise(ctx, "upload-pack", repo.Dir, "", &out); err != nil {
		t.Fatal(err)
	}
	if !strings.Contains(out.String(), main+" refs/remotes/origin/main") {
		t.Errorf("advertisement = %q, want refs/remotes/origin/main", out.String())
	}
	if err := g.Serve(ctx, "http-backend", repo.Dir, "", strings.NewReader(""), &out); err == nil {
		t.Error("Serve ran a service other than upload-pack and receive-pack")
	}
}

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
	if err := repo.Push(ctx, remote, git.RefUpdate{Ref: "refs/heads/c/x", New: merge, Old: head}); err != nil {
		t.Fatal(err)
	}
	if got := srv.Heads(t, "app")["c/x"]; got != merge {
		t.Errorf("c/x = %s, want %s", got, merge)
	}

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
