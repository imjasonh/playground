package gitk8s

import (
	"context"
	"crypto/sha256"
	"encoding/hex"
	"fmt"
	"os"
	"path/filepath"
	"sync"

	"github.com/imjasonh/playground/git-k8s/internal/git"
)

// DefaultCacheDir is the default of the -cache-dir flags. The Deployments
// that kube's generate writes have a read-only root file system and a
// writable /tmp.
var DefaultCacheDir = filepath.Join(os.TempDir(), "git-k8s")

// Cache keeps a local bare repository for each GitRepository, so that
// controllers fetch only objects they don't have yet.
type Cache struct {
	Git *git.Git
	// Dir holds the repositories. It must be writable.
	Dir string

	mu    sync.Mutex
	locks map[string]*sync.Mutex
}

// Open returns the local repository for repo, locked so that no other
// reconcile in this process uses it until unlock is called.
func (c *Cache) Open(ctx context.Context, repo *Repository) (r *git.Repo, unlock func(), err error) {
	sum := sha256.Sum256([]byte(repo.Spec.URL))
	dir := filepath.Join(c.Dir, repo.Namespace, repo.Name+"-"+hex.EncodeToString(sum[:4])+".git")
	c.mu.Lock()
	if c.locks == nil {
		c.locks = map[string]*sync.Mutex{}
	}
	l := c.locks[dir]
	if l == nil {
		l = &sync.Mutex{}
		c.locks[dir] = l
	}
	c.mu.Unlock()

	l.Lock()
	if r, err = c.Git.Open(ctx, dir); err != nil {
		l.Unlock()
		return nil, nil, fmt.Errorf("opening a local repository under %s, which must be writable: %w", c.Dir, err)
	}
	return r, l.Unlock, nil
}
