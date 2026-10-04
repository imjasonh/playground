package git_test

import (
	"context"
	"errors"
	"io"
	"net"
	"net/url"
	"os"
	"path/filepath"
	"slices"
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

func TestSSH(t *testing.T) {
	srv := gittest.NewSSHServer(t)
	w := srv.NewWork(t, "app")
	main := w.Commit("first")
	w.Push("main")
	u, err := url.Parse(srv.URL)
	if err != nil {
		t.Fatal(err)
	}
	scp := srv.Remote("app")
	scp.URL = u.User.Username() + "@[" + u.Host + "]:app.git"

	ctx := t.Context()
	g := &git.Git{}
	for _, r := range []git.Remote{srv.Remote("app"), scp} {
		if heads, err := g.LsRemote(ctx, r); err != nil || heads["main"] != main || len(heads) != 1 {
			t.Errorf("LsRemote(%s) = %v, %v; want main at %s", r.URL, heads, err, main)
		}
	}
	repo, err := g.Open(ctx, filepath.Join(t.TempDir(), "app.git"))
	if err != nil {
		t.Fatal(err)
	}
	if err := repo.Fetch(ctx, scp, "main"); err != nil {
		t.Fatal(err)
	}
	if err := repo.Push(ctx, srv.Remote("app"), git.RefUpdate{Ref: "refs/heads/c/x", New: main}); err != nil {
		t.Fatal(err)
	}
	if got := srv.Heads(t, "app")["c/x"]; got != main {
		t.Errorf("c/x = %q after the push, want %s", got, main)
	}
}

func TestSSHChecksKeys(t *testing.T) {
	srv, other := gittest.NewSSHServer(t), gittest.NewSSHServer(t)
	w := srv.NewWork(t, "app")
	w.Commit("first")
	w.Push("main")

	// Each known_hosts line is a host, a key type, and a key.
	ours, theirs := strings.Fields(string(srv.SSH.KnownHosts)), strings.Fields(string(other.SSH.KnownHosts))
	changed, unknown, wrongKey := srv.Remote("app"), srv.Remote("app"), srv.Remote("app")
	changed.SSH.KnownHosts = []byte(ours[0] + " " + theirs[1] + " " + theirs[2] + "\n")
	unknown.SSH.KnownHosts = other.SSH.KnownHosts
	wrongKey.SSH.PrivateKey = other.SSH.PrivateKey
	for name, tc := range map[string]struct {
		remote git.Remote
		want   string
	}{
		"a changed host key":  {changed, "REMOTE HOST IDENTIFICATION HAS CHANGED"},
		"an unknown host":     {unknown, "Host key verification failed"},
		"an unauthorized key": {wrongKey, "Permission denied (publickey)"},
	} {
		_, err := (&git.Git{}).LsRemote(t.Context(), tc.remote)
		if err == nil || !strings.Contains(err.Error(), tc.want) {
			t.Errorf("%s: err = %v, want one that says %q", name, err, tc.want)
			continue
		}
		if _, again := (&git.Git{}).LsRemote(t.Context(), tc.remote); again == nil || again.Error() != err.Error() {
			t.Errorf("%s: the error changed from %q to %q", name, err, again)
		}
		for _, key := range [][]byte{srv.SSH.PrivateKey, other.SSH.PrivateKey} {
			for line := range strings.SplitSeq(string(key), "\n") {
				if len(line) > 16 && !strings.HasPrefix(line, "-") && strings.Contains(err.Error(), line) {
					t.Errorf("%s: the error includes a private key", name)
				}
			}
		}
	}
}

func TestSSHKeyFiles(t *testing.T) {
	bin, tmp, log := t.TempDir(), t.TempDir(), filepath.Join(t.TempDir(), "ssh.log")
	// This ssh logs its arguments and the modes of the key's directory and
	// the files in it, then fails.
	script := `#!/bin/sh
echo "$*" >"$FAKE_SSH_LOG"
while [ $# -gt 0 ]; do
  if [ "$1" = -i ]; then key=$2; fi
  shift
done
dir=$(dirname "$key")
ls -ld "$dir" "$key" "$dir/known_hosts" >>"$FAKE_SSH_LOG"
exit 255
`
	if err := os.WriteFile(filepath.Join(bin, "ssh"), []byte(script), 0o755); err != nil {
		t.Fatal(err)
	}
	t.Setenv("PATH", bin+string(os.PathListSeparator)+os.Getenv("PATH"))
	t.Setenv("TMPDIR", tmp)
	t.Setenv("FAKE_SSH_LOG", log)

	key := &git.SSHKey{PrivateKey: []byte("private key\n"), KnownHosts: []byte("known hosts\n")}
	if _, err := (&git.Git{}).LsRemote(t.Context(), git.Remote{URL: "git@example.com:app.git", SSH: key}); err == nil {
		t.Fatal("ls-remote succeeded with an ssh that fails")
	}
	out, err := os.ReadFile(log)
	if err != nil {
		t.Fatal(err)
	}
	lines := strings.Split(strings.TrimSpace(string(out)), "\n")
	if len(lines) != 4 || strings.Contains(lines[0], "private key") {
		t.Fatalf("ssh log = %q, want the arguments, without the key, and three files", lines)
	}
	for i, mode := range []string{"drwx------", "-rw-------", "-rw-------"} {
		if f := strings.Fields(lines[i+1]); !strings.HasPrefix(f[0], mode) || !strings.HasPrefix(f[len(f)-1], tmp) {
			t.Errorf("ssh saw %q, want mode %s in %s", lines[i+1], mode, tmp)
		}
	}
	if left, err := os.ReadDir(tmp); err != nil || len(left) != 0 {
		t.Errorf("%s holds %v, %v after the command; want nothing", tmp, left, err)
	}
}

func TestSSHNeedsPlainTMPDIR(t *testing.T) {
	key := &git.SSHKey{PrivateKey: []byte("private key\n"), KnownHosts: []byte("known hosts\n")}
	for _, c := range []string{`"`, `\`, "%", "$"} {
		tmp := filepath.Join(t.TempDir(), "a"+c+"b")
		if err := os.Mkdir(tmp, 0o700); err != nil {
			t.Fatal(err)
		}
		t.Setenv("TMPDIR", tmp)
		_, err := (&git.Git{}).LsRemote(t.Context(), git.Remote{URL: "ssh://git@127.0.0.1:1/app.git", SSH: key})
		if err == nil || !strings.Contains(err.Error(), "ssh can't use key files in "+tmp+",") {
			t.Errorf("TMPDIR %s: err = %v, want one that names it", tmp, err)
		}
		if left, err := os.ReadDir(tmp); err != nil || len(left) != 0 {
			t.Errorf("%s holds %v, %v after the command; want nothing", tmp, left, err)
		}
	}
}

func TestTimeoutWithSilentServer(t *testing.T) {
	// This server accepts connections and never answers.
	l, err := net.Listen("tcp", "127.0.0.1:0")
	if err != nil {
		t.Fatal(err)
	}
	t.Cleanup(func() { l.Close() })
	conns := make(chan net.Conn, 8)
	go func() {
		for {
			c, err := l.Accept()
			if err != nil {
				return
			}
			conns <- c
		}
	}()
	tmp := t.TempDir()
	t.Setenv("TMPDIR", tmp)

	ctx, timeout := t.Context(), time.Second
	key := &git.SSHKey{PrivateKey: []byte("private key\n"), KnownHosts: []byte("known hosts\n")}
	for _, r := range []git.Remote{
		{URL: "ssh://git@" + l.Addr().String() + "/app.git", SSH: key},
		{URL: "http://" + l.Addr().String() + "/app.git"},
	} {
		start, done := time.Now(), make(chan error, 1)
		go func() {
			_, err := (&git.Git{Timeout: timeout}).LsRemote(ctx, r)
			done <- err
		}()
		select {
		case err := <-done:
			if elapsed := time.Since(start); !errors.Is(err, context.DeadlineExceeded) || elapsed > timeout+2*time.Second {
				t.Errorf("LsRemote(%s) = %v after %v, want a timeout after %v", r.URL, err, elapsed, timeout)
			}
		case <-time.After(10 * time.Second):
			t.Fatalf("LsRemote(%s) is still running after 10s", r.URL)
		}
		if left, err := os.ReadDir(tmp); err != nil || len(left) != 0 {
			t.Errorf("%s holds %v, %v after the command; want nothing", tmp, left, err)
		}
		select {
		case c := <-conns:
			// The connection ends when no process has it open.
			c.SetReadDeadline(time.Now().Add(5 * time.Second))
			if _, err := io.Copy(io.Discard, c); err != nil {
				t.Errorf("LsRemote(%s) left a process connected: %v", r.URL, err)
			}
			c.Close()
		case <-time.After(5 * time.Second):
			t.Errorf("LsRemote(%s) never connected", r.URL)
		}
	}
}

func TestIsSSH(t *testing.T) {
	for u, want := range map[string]bool{
		"ssh://git@example.com/app.git":  true,
		"ssh://example.com:2222/app.git": true,
		"git+ssh://example.com/app.git":  true,
		"git@example.com:org/app.git":    true,
		"example.com:app.git":            true,
		"git@[example.com:2222]:app.git": true,
		"https://example.com/app.git":    false,
		"http://127.0.0.1:8418/app.git":  false,
		"git://example.com/app.git":      false,
		"file:///srv/app.git":            false,
		"/srv/app.git":                   false,
		"./dir:with-colon/app.git":       false,
	} {
		if got := git.IsSSH(u); got != want {
			t.Errorf("IsSSH(%q) = %v, want %v", u, got, want)
		}
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
