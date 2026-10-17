package gitk8s

import (
	"context"
	"crypto/sha256"
	"encoding/hex"
	"fmt"
	"log/slog"
	"os"
	"path/filepath"
	"strings"
	"sync"
	"time"

	"github.com/imjasonh/playground/git-k8s/internal/git"
)

// DefaultCacheDir is the default of the -cache-dir flags. The Deployments
// that kube's generate writes have a read-only root file system and a
// writable /tmp.
var DefaultCacheDir = filepath.Join(os.TempDir(), "git-k8s")

const (
	// cacheIdle is how long a local repository goes unopened before Open
	// removes it, such as the repository of a Repository object that no longer
	// exists.
	cacheIdle = 7 * 24 * time.Hour
	// cacheTidy is how often Open looks for idle repositories, and how
	// often it tidies each repository that it opens.
	cacheTidy = time.Hour
)

// Cache keeps a local bare repository for each Repository object, so that
// controllers fetch only objects they don't have yet. Open maintains the
// repositories, and removes the ones that go unopened for a week.
type Cache struct {
	Git *git.Git
	// Dir holds the repositories, in a directory for each namespace. It
	// must be writable. Open leaves alone the directories in Dir whose
	// names start with a dot, where another Cache can keep its own.
	Dir string
	// Remote reaches a Repository object's repository, so that Open can tell
	// which refs a local repository still needs. If Remote is nil, Open
	// keeps every ref.
	Remote func(context.Context, *RepositoryView) (git.Remote, error)

	mu      sync.Mutex
	entries map[string]*cacheEntry
	swept   time.Time
}

// cacheEntry locks a local repository. users counts the reconciles that
// hold the lock or wait for it, and tidied is when Open last tidied the
// repository. Cache.mu guards users, and the lock guards tidied.
type cacheEntry struct {
	mu     sync.Mutex
	users  int
	tidied time.Time
}

// Open returns the local repository for repo, locked so that no other
// reconcile in this process uses it until unlock is called. At most once
// an hour, Open removes the repositories that no reconcile opened for a
// week, and tidies the repository that it returns.
func (c *Cache) Open(ctx context.Context, repo *RepositoryView) (r *git.Repo, unlock func(), err error) {
	sum := sha256.Sum256([]byte(repo.Spec.URL))
	dir := filepath.Join(c.Dir, repo.Namespace, repo.Name+"-"+hex.EncodeToString(sum[:4])+".git")
	c.mu.Lock()
	if c.entries == nil {
		c.entries = map[string]*cacheEntry{}
	}
	e := c.entries[dir]
	if e == nil {
		e = &cacheEntry{}
		c.entries[dir] = e
	}
	e.users++
	c.mu.Unlock()
	unlock = func() {
		e.mu.Unlock()
		c.mu.Lock()
		e.users--
		c.mu.Unlock()
	}

	c.sweep()
	e.mu.Lock()
	if r, err = c.Git.Open(ctx, dir); err != nil {
		unlock()
		return nil, nil, fmt.Errorf("opening a local repository under %s, which must be writable: %w", c.Dir, err)
	}
	now := time.Now()
	// sweep reads when a reconcile last opened a repository from the
	// modification time of its directory, which outlasts the process.
	_ = os.Chtimes(dir, now, now)
	if now.Sub(e.tidied) >= cacheTidy {
		e.tidied = now
		c.tidy(ctx, r, repo)
	}
	return r, unlock, nil
}

// sweep removes the repositories that no reconcile opened for cacheIdle,
// at most once every cacheTidy. It holds c.mu, so no reconcile starts to
// open a repository while sweep removes it.
func (c *Cache) sweep() {
	now := time.Now()
	c.mu.Lock()
	defer c.mu.Unlock()
	if now.Sub(c.swept) < cacheTidy {
		return
	}
	c.swept = now
	namespaces, _ := os.ReadDir(c.Dir)
	for _, ns := range namespaces {
		if !ns.IsDir() || strings.HasPrefix(ns.Name(), ".") {
			continue
		}
		repos, _ := os.ReadDir(filepath.Join(c.Dir, ns.Name()))
		for _, d := range repos {
			dir := filepath.Join(c.Dir, ns.Name(), d.Name())
			if e := c.entries[dir]; !d.IsDir() || !strings.HasSuffix(dir, ".git") || e != nil && e.users > 0 {
				continue
			}
			if info, err := d.Info(); err != nil || now.Sub(info.ModTime()) < cacheIdle {
				continue
			}
			if err := os.RemoveAll(dir); err != nil {
				slog.Warn("removing an unused local repository failed", "path", dir, "err", err)
				continue
			}
			delete(c.entries, dir)
		}
	}
}

// tidy turns off the maintenance that a fetch would run: the fetch waits
// for it, under the fetch's timeout, so a long repack would fail the
// fetch. Then tidy deletes the refs that r no longer needs, which keep
// their objects, and runs maintenance if git says that r needs it. It only
// logs what fails, because r works without it.
func (c *Cache) tidy(ctx context.Context, r *git.Repo, repo *RepositoryView) {
	log := slog.With("namespace", repo.Namespace, "repository", repo.Name)
	if err := r.SetConfig(ctx, "maintenance.auto", "false"); err != nil {
		log.Warn("configuring a local repository failed", "err", err)
		return
	}
	refs, err := r.Refs(ctx)
	if err != nil {
		log.Warn("listing the refs of a local repository failed", "err", err)
		return
	}
	// A new repository has nothing to delete or pack.
	if len(refs) == 0 {
		return
	}
	if err := c.pruneRefs(ctx, r, repo, refs); err != nil {
		log.Warn("deleting unneeded refs from a local repository failed", "err", err)
	}
	if err := r.Maintain(ctx); err != nil {
		log.Warn("maintaining a local repository failed", "err", err)
	}
}

// pruneRefs deletes refs, which r holds, except those of the branches that
// repo's repository has, which Fetch keeps under refs/remotes/origin/.
// Controllers fetch any other ref again when they need it.
func (c *Cache) pruneRefs(ctx context.Context, r *git.Repo, repo *RepositoryView, refs map[string]string) error {
	if c.Remote == nil {
		return nil
	}
	remote, err := c.Remote(ctx, repo)
	if err != nil {
		return err
	}
	heads, err := c.Git.LsRemote(ctx, remote)
	if err != nil {
		return err
	}
	var gone []git.RefUpdate
	for ref, sha := range refs {
		if b, ok := strings.CutPrefix(ref, "refs/remotes/origin/"); !ok || heads[b] == "" {
			gone = append(gone, git.RefUpdate{Ref: ref, Old: sha})
		}
	}
	if len(gone) == 0 {
		return nil
	}
	return r.UpdateRefs(ctx, gone...)
}
