package git_test

import (
	"context"
	"errors"
	"fmt"
	"io"
	"io/fs"
	"maps"
	"net"
	"net/http"
	"net/http/httptest"
	"os"
	"path/filepath"
	"slices"
	"strconv"
	"strings"
	"testing"
	"time"

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

func TestOptionURLsDontRunCommands(t *testing.T) {
	srv := gittest.NewServer(t, "")
	w := srv.NewWork(t, "app")
	head := w.Commit("first")
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
	for name, run := range map[string]func(command string) error{
		"ls-remote": func(command string) error {
			_, err := g.LsRemote(ctx, git.Remote{URL: "--upload-pack=" + command})
			return err
		},
		"fetch": func(command string) error {
			return repo.Fetch(ctx, git.Remote{URL: "--upload-pack=" + command}, "main")
		},
		"push": func(command string) error {
			return repo.Push(ctx, git.Remote{URL: "--receive-pack=" + command}, git.RefUpdate{Ref: "refs/heads/x", New: head})
		},
	} {
		t.Run(name, func(t *testing.T) {
			marker := filepath.Join(t.TempDir(), "ran")
			err := run("touch " + marker + "; false")
			if _, statErr := os.Stat(marker); statErr == nil {
				t.Fatal("git ran the command in the URL")
			}
			if err == nil || !strings.Contains(err.Error(), "blocked") {
				t.Errorf("err = %v, want git to block the URL", err)
			}
		})
	}
}

func TestOtherTransportsDontRun(t *testing.T) {
	marker := filepath.Join(t.TempDir(), "ran")
	bin := t.TempDir()
	if err := os.WriteFile(filepath.Join(bin, "git-remote-evil"), []byte("#!/bin/sh\ntouch "+marker+"\n"), 0o755); err != nil {
		t.Fatal(err)
	}
	t.Setenv("PATH", bin+string(os.PathListSeparator)+os.Getenv("PATH"))
	g := &git.Git{}
	local, err := g.Open(t.Context(), filepath.Join(t.TempDir(), "app.git"))
	if err != nil {
		t.Fatal(err)
	}
	for _, url := range []string{"evil::x", local.Dir, "file://" + local.Dir} {
		_, err := g.LsRemote(t.Context(), git.Remote{URL: url})
		if _, statErr := os.Stat(marker); statErr == nil {
			t.Fatal("git ran the remote helper")
		}
		if err == nil || !strings.Contains(err.Error(), "not allowed") {
			t.Errorf("ls-remote %s: err = %v, want git to refuse the transport", url, err)
		}
	}
}

func TestLsRemoteSkipsUnsafeBranches(t *testing.T) {
	srv := gittest.NewServer(t, "")
	w := srv.NewWork(t, "app")
	main := w.Commit("first")
	w.Push("main")
	// git branch refuses this name, but a server accepts a push to it.
	w.Push("-x")
	if heads := srv.Heads(t, "app"); !maps.Equal(heads, map[string]string{"main": main}) {
		t.Errorf("heads = %q, want only main", heads)
	}

	sha := strings.Repeat("1", 40)
	url := serveRefs(t, sha,
		"refs/heads/main",
		"refs/heads/-x",
		"refs/heads/main\n--output=/tmp/pwned\trefs/heads/injected",
		"refs/heads/a b",
		"refs/heads/a..b",
	)
	heads, err := (&git.Git{}).LsRemote(t.Context(), git.Remote{URL: url})
	if err != nil {
		t.Fatal(err)
	}
	if !maps.Equal(heads, map[string]string{"main": sha}) {
		t.Errorf("heads from a malicious server = %q, want only main", heads)
	}
}

// serveRefs runs a git daemon whose one repository has refs, all pointing at
// sha, and returns the repository's URL. It sends the ref names as they are,
// as a malicious server can.
func serveRefs(t *testing.T, sha string, refs ...string) string {
	t.Helper()
	l, err := net.Listen("tcp", "127.0.0.1:0")
	if err != nil {
		t.Fatal(err)
	}
	t.Cleanup(func() { l.Close() })
	var ad strings.Builder
	for i, ref := range refs {
		line := sha + " " + ref
		if i == 0 {
			line += "\x00"
		}
		fmt.Fprintf(&ad, "%04x%s\n", len(line)+5, line)
	}
	ad.WriteString("0000")
	go func() {
		for {
			c, err := l.Accept()
			if err != nil {
				return
			}
			go func() {
				defer c.Close()
				var size [4]byte
				if _, err := io.ReadFull(c, size[:]); err != nil {
					return
				}
				n, _ := strconv.ParseUint(string(size[:]), 16, 16)
				if _, err := io.CopyN(io.Discard, c, int64(n)-4); err != nil {
					return
				}
				// A client that asks for protocol version 2 accepts this
				// version 0 advertisement, and sends a flush packet after it.
				io.WriteString(c, ad.String())
				io.Copy(io.Discard, c)
			}()
		}
	}()
	return "git://" + l.Addr().String() + "/app.git"
}

// Killing git leaves its remote helper running, holding git's stderr, until
// the server responds.
func TestLsRemoteReturnsWhenCanceled(t *testing.T) {
	ctx, cancel := context.WithCancel(t.Context())
	release := make(chan struct{})
	srv := httptest.NewServer(http.HandlerFunc(func(w http.ResponseWriter, r *http.Request) {
		cancel()
		select {
		case <-release:
		case <-time.After(20 * time.Second):
		}
		http.NotFound(w, r)
	}))
	defer srv.Close()
	defer close(release)

	start := time.Now()
	_, err := (&git.Git{}).LsRemote(ctx, git.Remote{URL: srv.URL + "/app.git"})
	if d := time.Since(start); d > 10*time.Second {
		t.Errorf("ls-remote returned %v after it started", d.Round(time.Second))
	}
	if !errors.Is(err, context.Canceled) {
		t.Errorf("err = %v, want %v", err, context.Canceled)
	}
}

// Commands in a repository run git with -C and the repository's directory
// before the subcommand.
func TestErrorsNameTheSubcommand(t *testing.T) {
	dir := filepath.Join(t.TempDir(), "app.git")
	if _, err := (&git.Git{}).Open(t.Context(), dir); err != nil {
		t.Fatal(err)
	}
	for name, tt := range map[string]struct {
		git  *git.Git
		want error
	}{
		"timeout":        {&git.Git{Timeout: time.Nanosecond}, context.DeadlineExceeded},
		"missing binary": {&git.Git{Bin: filepath.Join(t.TempDir(), "git")}, fs.ErrNotExist},
	} {
		t.Run(name, func(t *testing.T) {
			// Open doesn't run git for a repository that exists.
			repo, err := tt.git.Open(t.Context(), dir)
			if err != nil {
				t.Fatal(err)
			}
			err = repo.Fetch(t.Context(), git.Remote{URL: "http://127.0.0.1:1/app.git"}, "main")
			if !errors.Is(err, tt.want) || !strings.HasPrefix(err.Error(), "git fetch: ") {
				t.Errorf("err = %v, want an error that starts with %q and wraps %v", err, "git fetch: ", tt.want)
			}
		})
	}
}

// Merge puts --attr-source, and -c with its value, before merge-tree.
func TestErrorsNameTheSubcommandAfterOptions(t *testing.T) {
	repo, err := (&git.Git{}).Open(t.Context(), filepath.Join(t.TempDir(), "app.git"))
	if err != nil {
		t.Fatal(err)
	}
	stalled := wrap(t, repo, `case " $* " in *" merge-tree "*) exec sleep 60 ;; esac`)
	ctx, cancel := context.WithTimeout(t.Context(), 2*time.Second)
	defer cancel()
	_, _, err = stalled.Merge(ctx, "HEAD", "HEAD", git.MergeOptions{})
	if !errors.Is(err, context.DeadlineExceeded) || !strings.HasPrefix(err.Error(), "git merge-tree: ") {
		t.Errorf("err = %v, want an error that starts with %q and wraps %v", err, "git merge-tree: ", context.DeadlineExceeded)
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
	if got, err := repo.Fetched(ctx, "main"); err != nil || got != parent {
		t.Errorf("Fetched(main) = %q, %v; want %s", got, err, parent)
	}
	if got, err := repo.Fetched(ctx, "c/missing"); err == nil {
		t.Errorf("Fetched(c/missing) = %q, want an error", got)
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
	merge, err := repo.CommitTree(ctx, tree, []string{head, parent}, msg, id, 1700000000, nil)
	if err != nil {
		t.Fatal(err)
	}
	again, err := repo.CommitTree(ctx, tree, []string{head, parent}, msg, id, 1700000000, nil)
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
	if got, want := rejected.Reason("refs/heads/c/x"), "[remote rejected] (deletion prohibited); remote: error: denying ref deletion for refs/heads/c/x"; got != want {
		t.Errorf("Reason = %q, want %q", got, want)
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

func TestCountCommits(t *testing.T) {
	srv := gittest.NewServer(t, "")
	w := srv.NewWork(t, "app")
	base := w.Commit("base")
	w.Commit("Update a module\n\nGit-K8s-Deps: go example.com/a v1.0.1")
	w.Commit("Fix the tests\n\n" + git.FixerTrailer + ": deps\n" + git.AgentTrailer + ": deps")
	head := w.Commit("Edit by hand\n\nThis isn't a " + git.AgentTrailer + ": trailer.")
	w.Push("main")

	ctx := t.Context()
	repo, err := (&git.Git{}).Open(ctx, filepath.Join(t.TempDir(), "app.git"))
	if err != nil {
		t.Fatal(err)
	}
	if err := repo.Fetch(ctx, srv.Remote("app"), "main"); err != nil {
		t.Fatal(err)
	}
	for _, c := range []struct {
		base     string
		trailers []string
		want     int
	}{
		{base: base, want: 3},
		{want: 4},
		{base: base, trailers: []string{git.AgentTrailer}, want: 1},
		{base: base, trailers: []string{"Git-K8s-Deps", git.FixerTrailer}, want: 2},
		{base: head, want: 0},
	} {
		if n, err := repo.CountCommits(ctx, c.base, head, c.trailers...); err != nil || n != c.want {
			t.Errorf("CountCommits(%.7s, %v) = %d, %v; want %d", c.base, c.trailers, n, err, c.want)
		}
	}
	if n, err := repo.CountCommits(ctx, "", "--all"); err == nil {
		t.Errorf("CountCommits of --all = %d, want an error for a revision that doesn't exist", n)
	}
}

func TestListCommits(t *testing.T) {
	srv := gittest.NewServer(t, "")
	w := srv.NewWork(t, "app")
	base := w.Commit("base")
	update := w.Commit("Update a module\n\nGit-K8s-Deps: go example.com/a v1.0.1")
	fix := w.Commit("Fix the tests\n\n" + git.FixerTrailer + ": deps\n" + git.AgentTrailer + ": deps\n  agent")
	head := w.Commit("Edit by hand\n\n" + git.FixerTrailer + ": deps\n\nThis paragraph isn't a trailer.")
	w.Push("main")

	ctx := t.Context()
	repo, err := (&git.Git{}).Open(ctx, filepath.Join(t.TempDir(), "app.git"))
	if err != nil {
		t.Fatal(err)
	}
	if err := repo.Fetch(ctx, srv.Remote("app"), "main"); err != nil {
		t.Fatal(err)
	}
	author := git.Identity{Name: "Test Author", Email: "author@example.com"}
	want := []git.ListedCommit{
		{SHA: head, Committer: author},
		{SHA: fix, Committer: author, Trailers: []string{git.FixerTrailer + ": deps", git.AgentTrailer + ": deps agent"}},
		{SHA: update, Committer: author, Trailers: []string{"Git-K8s-Deps: go example.com/a v1.0.1"}},
	}
	for limit, want := range map[int][]git.ListedCommit{4: want, 3: want, 2: want[:2]} {
		got, err := repo.ListCommits(ctx, base, head, limit)
		if err != nil || !slices.EqualFunc(got, want, func(a, b git.ListedCommit) bool {
			return a.SHA == b.SHA && a.Committer == b.Committer && slices.Equal(a.Trailers, b.Trailers)
		}) {
			t.Errorf("ListCommits(limit %d) = %+v, %v; want %+v", limit, got, err, want)
		}
	}
	if got, err := repo.ListCommits(ctx, head, head, 1); err != nil || len(got) != 0 {
		t.Errorf("ListCommits of no commits = %+v, %v", got, err)
	}
	if got, err := repo.ListCommits(ctx, base, "--all", 4); err == nil {
		t.Errorf("ListCommits of --all = %+v, want an error for a revision that doesn't exist", got)
	}

	c, err := repo.Commit(ctx, head)
	if err != nil {
		t.Fatal(err)
	}
	for _, id := range []git.Identity{
		{Name: "git-k8s", Email: "git-k8s@example.com"},
		{Name: "git-k8s ", Email: "<git-k8s@example.com>"},
		{Name: `"git-k8s"`, Email: " git-k8s@example.com\n"},
		{Name: "git\n-k8s", Email: "git-k8s@<example>.com"},
		{Name: "Ana Lima\xff", Email: "\x01ana@example.com"},
		{Name: "git-k8s", Email: "git-k8s\ufffd\ufffe\uffff\U0001fffe@example.com"},
		{Name: "git-k8s", Email: "git-k8s\ufdcf\ufdd0\ufdef\ufdf0@example.com"},
		{Name: "git-k8s", Email: ""},
	} {
		commit, err := repo.CommitTree(ctx, c.Tree, []string{head}, "edit", id, c.Time, nil)
		if err != nil {
			t.Fatalf("CommitTree as %q: %v", id, err)
		}
		got, err := repo.ListCommits(ctx, head, commit, 1)
		if err != nil || len(got) != 1 || got[0].SHA != commit || got[0].Committer != id.Written() {
			t.Errorf("ListCommits of a commit as %q = %+v, %v; want the committer %q", id, got, err, id.Written())
		}
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

func TestOnlyFixerCommits(t *testing.T) {
	srv := gittest.NewServer(t, "")
	w := srv.NewWork(t, "app")
	base := w.Commit("base")
	w.Branch("c/x", base)
	head := w.Commit("branch change")
	w.Branch("main", base)
	parent := w.Commit("parent change")
	w.Push("main")
	w.Branch("c/x", head)
	w.Git("merge", "--quiet", "--no-ff", "-m", "Merge main into c/x\n\n"+git.FixerTrailer+": base", "main")
	merge := w.Git("rev-parse", "HEAD")
	fix := w.Commit("Format\n\n" + git.FixerTrailer + ": gofmt")
	person := w.Commit("more work")
	w.Push("c/x")

	ctx := t.Context()
	repo, err := (&git.Git{}).Open(ctx, filepath.Join(t.TempDir(), "app.git"))
	if err != nil {
		t.Fatal(err)
	}
	if err := repo.Fetch(ctx, srv.Remote("app"), "main", "c/x"); err != nil {
		t.Fatal(err)
	}
	for _, tc := range []struct {
		name       string
		base, head string
		want       bool
	}{
		{"a merge of the parent and a fix", head, fix, true},
		{"a merge of the parent", head, merge, true},
		{"a person's commit after the fix", head, person, false},
		{"a person's commit alone", fix, person, false},
		{"a base that's only a second parent", parent, fix, false},
		{"a base that's not an ancestor", fix, head, false},
	} {
		if got, err := repo.OnlyFixerCommits(ctx, tc.base, tc.head); err != nil || got != tc.want {
			t.Errorf("%s: OnlyFixerCommits = %v, %v; want %v", tc.name, got, err, tc.want)
		}
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
	commit, err := repo.CommitTree(ctx, tree, []string{head}, "edit", git.Identity{Name: "a", Email: "a@example.com"}, c.Time, nil)
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
	for _, path := range []string{".g\u200cit/hooks/post-checkout", "GIT~1/hooks/post-checkout"} {
		if _, err := repo.ReplaceFiles(ctx, c.Tree, []git.TreeEntry{{Mode: "100644", SHA: blob, Path: path}}); err == nil {
			t.Errorf("ReplaceFiles(%q) succeeded; want an error for a path that macOS or Windows reads as .git", path)
		}
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
		{Name: "\u00a0git-k8s Jr.\r", Email: "\rgit-k8s@example.com\u3000"},
		{Name: "git\ufdd0k8s\uffff", Email: "\U0001fffe@example.com"},
	} {
		raw, err := repo.CommitTree(ctx, c.Tree, []string{base}, "edit", id, c.Time, nil)
		if err != nil {
			t.Errorf("CommitTree as %q: %v", id, err)
			continue
		}
		if written, err := repo.CommitTree(ctx, c.Tree, []string{base}, "edit", id.Written(), c.Time, nil); err != nil || written != raw {
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
