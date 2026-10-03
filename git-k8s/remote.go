package gitk8s

import (
	"context"
	"crypto/sha256"
	"encoding/hex"
	"fmt"
	"path/filepath"
	"sync"

	"github.com/imjasonh/playground/git-k8s/internal/git"
	"github.com/imjasonh/playground/kube"
	"github.com/imjasonh/playground/kube/k8s"
)

// RemoteFor returns a repository's URL and credentials. It reads the
// Secret that SecretRef names with kube.Fetch, so it must run in a
// reconcile, and the Secret isn't cached.
func RemoteFor(ctx context.Context, repo *GitRepository) (git.Remote, error) {
	r := git.Remote{URL: repo.Spec.URL}
	if repo.Spec.SecretRef == nil {
		return r, nil
	}
	name := repo.Spec.SecretRef.Name
	s, err := kube.Fetch[k8s.Secret](ctx, repo.Namespace, name)
	if err != nil {
		return r, fmt.Errorf("reading Secret %s: %w", name, err)
	}
	if s == nil {
		return r, fmt.Errorf("Secret %s doesn't exist", name)
	}
	password := string(s.Data["password"])
	if password == "" {
		return r, fmt.Errorf("Secret %s has no password key", name)
	}
	username := string(s.Data["username"])
	if username == "" {
		username = "git"
	}
	r.Auth = &git.Auth{Username: username, Password: password}
	return r, nil
}

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
func (c *Cache) Open(ctx context.Context, repo *GitRepository) (r *git.Repo, unlock func(), err error) {
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
