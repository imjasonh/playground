package gitk8s_test

import (
	"maps"
	"os"
	"os/exec"
	"path/filepath"
	"slices"
	"testing"
	"time"

	gitk8s "github.com/imjasonh/playground/git-k8s"
	"github.com/imjasonh/playground/git-k8s/internal/git"
	"github.com/imjasonh/playground/git-k8s/internal/gittest"
	"github.com/imjasonh/playground/kube"
)

// open opens repo's local repository in c and unlocks it.
func open(t *testing.T, c *gitk8s.Cache, repo *gitk8s.Repository) *git.Repo {
	t.Helper()
	r, unlock, err := c.Open(t.Context(), repo)
	if err != nil {
		t.Fatal(err)
	}
	unlock()
	return r
}

func TestCacheRemovesUnusedRepositories(t *testing.T) {
	if _, err := exec.LookPath("git"); err != nil {
		t.Skip("git isn't installed")
	}
	dir := t.TempDir()
	repository := func(namespace, name string) *gitk8s.Repository {
		r := &gitk8s.Repository{Object: kube.Meta(name, nil), Spec: gitk8s.TrackedRepositorySpec{URL: "https://git.example.com/" + name + ".git"}}
		r.Namespace = namespace
		return r
	}
	lastWeek := time.Now().Add(-8 * 24 * time.Hour)
	unopened := func(paths ...string) {
		t.Helper()
		for _, p := range paths {
			if err := os.Chtimes(p, lastWeek, lastWeek); err != nil {
				t.Fatal(err)
			}
		}
	}
	exists := func(path string) bool {
		_, err := os.Stat(path)
		return err == nil
	}

	c := &gitk8s.Cache{Git: &git.Git{}, Dir: dir}
	deleted := open(t, c, repository("gone", "deleted")).Dir
	recent := open(t, c, repository("default", "recent")).Dir
	app := repository("default", "app")
	// Open would make a new repository in place of one that it removed.
	kept := filepath.Join(open(t, c, app).Dir, "kept")
	if err := os.WriteFile(kept, nil, 0o644); err != nil {
		t.Fatal(err)
	}
	other := filepath.Join(dir, ".parents", "default", "deleted-01234567.git")
	if err := os.MkdirAll(other, 0o755); err != nil {
		t.Fatal(err)
	}
	unopened(deleted, filepath.Dir(kept), other)

	// A process looks for unused repositories when it first opens one.
	c = &gitk8s.Cache{Git: c.Git, Dir: dir}
	open(t, c, app)
	if exists(deleted) {
		t.Errorf("%s is still there, though no reconcile opened it for a week", deleted)
	}
	for _, path := range []string{recent, kept, other} {
		if !exists(path) {
			t.Errorf("%s was removed", path)
		}
	}

	// It looks again an hour later, not on each Open.
	unopened(recent)
	open(t, c, app)
	if !exists(recent) {
		t.Errorf("%s was removed within an hour of the last look", recent)
	}
	open(t, &gitk8s.Cache{Git: c.Git, Dir: dir}, app)
	if exists(recent) {
		t.Errorf("%s is still there, though no reconcile opened it for a week", recent)
	}
}

func TestCacheTidiesRepositories(t *testing.T) {
	ctx := t.Context()
	srv := gittest.NewServer(t, "")
	w := srv.NewWork(t, "app")
	w.Write("a.txt", "one\n")
	w.Commit("one")
	w.Push("main")
	w.Push("gone")
	w.PushRef("refs/git-k8s/synced/heads/main")
	g, _ := srv.Repository("app")
	repo := &gitk8s.Repository{Object: g.Object, Spec: g.Spec}
	remote := srv.Remote("app")
	dir := t.TempDir()

	c := &gitk8s.Cache{Git: &git.Git{}, Dir: dir, Remote: srv.RemoteFor}
	r, unlock, err := c.Open(ctx, repo)
	if err != nil {
		t.Fatal(err)
	}
	if v, _, err := r.Config(ctx, "maintenance.auto"); err != nil || v != "false" {
		t.Errorf("maintenance.auto = %q, %v; want false, so that fetches don't run maintenance", v, err)
	}
	// Keep each fetch's objects in a pack of its own, and let maintenance
	// repack once there are two packs.
	for _, kv := range [][2]string{{"fetch.unpackLimit", "1"}, {"gc.autoPackLimit", "1"}} {
		if err := r.SetConfig(ctx, kv[0], kv[1]); err != nil {
			t.Fatal(err)
		}
	}
	if err := r.Fetch(ctx, remote, "main", "gone"); err != nil {
		t.Fatal(err)
	}
	if _, err := r.FetchRef(ctx, remote, "refs/git-k8s/synced/heads/main"); err != nil {
		t.Fatal(err)
	}
	w.Write("a.txt", "two\n")
	w.Commit("two")
	w.Push("main")
	if err := r.Fetch(ctx, remote, "main"); err != nil {
		t.Fatal(err)
	}
	unlock()
	w.Delete("gone")

	all := []string{"refs/git-k8s/synced/heads/main", "refs/remotes/origin/gone", "refs/remotes/origin/main"}
	check := func(c *gitk8s.Cache, refs []string, packs int) {
		t.Helper()
		r := open(t, c, repo)
		got, err := r.Refs(ctx)
		if err != nil {
			t.Fatal(err)
		}
		if names := slices.Sorted(maps.Keys(got)); !slices.Equal(names, refs) {
			t.Errorf("refs = %q, want %q", names, refs)
		}
		if got, _ := filepath.Glob(filepath.Join(r.Dir, "objects", "pack", "*.pack")); len(got) != packs {
			t.Errorf("%d packs, want %d", len(got), packs)
		}
	}
	// Open tidies each repository at most once an hour.
	check(c, all, 2)
	// Without Remote, it runs maintenance and keeps every ref.
	check(&gitk8s.Cache{Git: c.Git, Dir: dir}, all, 1)
	check(&gitk8s.Cache{Git: c.Git, Dir: dir, Remote: srv.RemoteFor}, []string{"refs/remotes/origin/main"}, 1)
}
