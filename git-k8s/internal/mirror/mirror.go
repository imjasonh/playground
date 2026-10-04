// Package mirror keeps a copy of each GitRepository and serves the copies
// over git's smart HTTP protocol.
//
// The copy is the repository's source of truth. Checks and controllers fetch
// from it and push to it, and Sync pushes their changes to the external
// repository and takes the changes that people push there. A branch that
// changed on both sides since they last agreed, where neither side's head
// keeps the other side's changes, stays as it is on each side. The copy
// keeps the external repository's head under refs/git-k8s/downstream/heads/
// and the head where they last agreed under refs/git-k8s/synced/heads/.
package mirror

import (
	"context"
	"errors"
	"fmt"
	"io/fs"
	"log/slog"
	"os"
	"path/filepath"
	"strconv"
	"strings"
	"sync"
	"sync/atomic"
	"time"

	gitk8s "github.com/imjasonh/playground/git-k8s"
	"github.com/imjasonh/playground/git-k8s/internal/git"
)

// Refs in each copy. A branch B is refs/heads/B, the external repository's
// head of B as last fetched is downstream B, and the commit where the two
// last agreed is synced B.
const (
	headsPrefix      = "refs/heads/"
	downstreamPrefix = "refs/git-k8s/downstream/heads/"
	syncedPrefix     = "refs/git-k8s/synced/heads/"
)

// maxPushSize is the largest pack, in bytes, that a copy takes in a push.
const maxPushSize = 256 << 20

// ErrNotSynced is wrapped by errors about a copy that hasn't fetched the
// external repository yet, which the mirror doesn't serve.
var ErrNotSynced = errors.New("the mirror hasn't fetched the repository from its external repository yet")

// Mirror keeps a bare repository for each GitRepository, at
// Dir/NAMESPACE/NAME.git. Its methods are safe for concurrent use. Only one
// process at a time may use Dir.
type Mirror struct {
	Git *git.Git
	Dir string
	// Prefixes let controllers other than checks start branches.
	Prefixes []Prefix

	// readTimeout is the longest that the mirror waits for the body of a
	// request. Zero means Git.MaxDuration, by when git has stopped reading
	// the body anyway.
	readTimeout time.Duration

	mu      sync.Mutex
	entries map[string]*entry
}

type entry struct {
	// mu is held for writing while the copy is created, replaced, or
	// deleted, and for reading while it's used.
	mu sync.RWMutex
	// syncing is held for the whole of a Sync.
	syncing sync.Mutex
	dir     string
	// repo is the copy, or nil if it isn't loaded. uid and url are the
	// GitRepository's UID and the URL that the copy last synced with.
	repo     *git.Repo
	uid, url string
	seeded   atomic.Bool
}

func (m *Mirror) entry(repo *gitk8s.Repository) *entry {
	m.mu.Lock()
	defer m.mu.Unlock()
	key := repo.Namespace + "/" + repo.Name
	e := m.entries[key]
	if e == nil {
		if m.entries == nil {
			m.entries = map[string]*entry{}
		}
		e = &entry{dir: filepath.Join(m.Dir, repo.Namespace, repo.Name+".git")}
		m.entries[key] = e
	}
	return e
}

// Repository is an open copy. Close it when done.
type Repository struct {
	*git.Repo
	close func()
}

// Close releases the copy.
func (r *Repository) Close() { r.close() }

// Open returns repo's copy. It fails with ErrNotSynced until Sync has
// fetched the external repository into it.
func (m *Mirror) Open(ctx context.Context, repo *gitk8s.Repository) (*Repository, error) {
	e := m.entry(repo)
	e.mu.RLock()
	if e.repo == nil || e.uid != repo.UID {
		e.mu.RUnlock()
		if _, err := m.load(ctx, e, repo, false); err != nil {
			return nil, err
		}
		e.mu.RLock()
	}
	if e.repo == nil || e.uid != repo.UID || !e.seeded.Load() {
		e.mu.RUnlock()
		return nil, fmt.Errorf("%s/%s: %w", repo.Namespace, repo.Name, ErrNotSynced)
	}
	return &Repository{Repo: e.repo, close: e.mu.RUnlock}, nil
}

// load reads repo's copy from disk into e if e doesn't hold it. With create,
// it creates the copy if there's none, or replaces one that belongs to
// another GitRepository with the same name, and adopts a new URL by
// forgetting what it knew of the old external repository. It reports
// whether the copy needs a fetch because it's new or its URL changed.
func (m *Mirror) load(ctx context.Context, e *entry, repo *gitk8s.Repository, create bool) (bool, error) {
	// Waiting for the write lock waits for every fetch and push of the
	// copy, so take it only for a change.
	e.mu.RLock()
	current := e.repo != nil && e.uid == repo.UID && (!create || e.url == repo.Spec.URL)
	e.mu.RUnlock()
	if current {
		return false, nil
	}
	e.mu.Lock()
	defer e.mu.Unlock()
	if e.repo == nil || e.uid != repo.UID {
		if _, err := m.read(ctx, e, repo.UID); err != nil {
			return false, err
		}
	}
	switch {
	case e.repo == nil && !create:
		return false, fmt.Errorf("%s/%s: %w", repo.Namespace, repo.Name, ErrNotSynced)
	case e.repo == nil:
		return true, m.create(ctx, e, repo)
	case !create || e.url == repo.Spec.URL:
		return false, nil
	}
	refs, err := e.repo.Refs(ctx, "refs/git-k8s")
	if err != nil {
		return false, err
	}
	var forget []git.RefUpdate
	for ref, sha := range refs {
		forget = append(forget, git.RefUpdate{Ref: ref, Old: sha})
	}
	if len(forget) > 0 {
		if err := e.repo.UpdateRefs(ctx, forget...); err != nil {
			return false, err
		}
	}
	if err := e.repo.SetConfig(ctx, "gitk8s.url", repo.Spec.URL); err != nil {
		return false, err
	}
	e.url = repo.Spec.URL
	return true, nil
}

// read sets e to the copy on disk if it belongs to the GitRepository with
// uid, and clears e otherwise. It returns the UID that the copy on disk
// belongs to, or "" if there's no complete copy.
func (m *Mirror) read(ctx context.Context, e *entry, uid string) (string, error) {
	e.repo, e.uid, e.url = nil, "", ""
	e.seeded.Store(false)
	if _, err := os.Stat(filepath.Join(e.dir, "HEAD")); errors.Is(err, fs.ErrNotExist) {
		return "", nil
	} else if err != nil {
		return "", err
	}
	r, err := m.Git.Open(ctx, e.dir)
	if err != nil {
		return "", err
	}
	config := map[string]string{}
	for _, key := range []string{"gitk8s.uid", "gitk8s.url", "gitk8s.seeded"} {
		if config[key], _, err = r.Config(ctx, key); err != nil {
			return "", err
		}
	}
	if have := config["gitk8s.uid"]; have != uid {
		return have, nil
	}
	e.repo, e.uid, e.url = r, uid, config["gitk8s.url"]
	e.seeded.Store(config["gitk8s.seeded"] == "true")
	return uid, nil
}

// create makes an empty copy for repo, replacing whatever is at e.dir.
func (m *Mirror) create(ctx context.Context, e *entry, repo *gitk8s.Repository) error {
	if err := os.RemoveAll(e.dir); err != nil {
		return err
	}
	r, err := m.Git.Open(ctx, e.dir)
	if err != nil {
		return fmt.Errorf("creating a repository under %s, which must be writable: %w", m.Dir, err)
	}
	// The UID goes last: a copy without one is incomplete, and the next
	// load replaces it.
	for _, kv := range [][2]string{
		// Pushes can't see or change the mirror's own refs. Fetches see
		// them, to resolve a divergence.
		{"receive.hideRefs", "refs/git-k8s"},
		{"receive.fsckObjects", "true"},
		{"receive.maxInputSize", strconv.Itoa(maxPushSize)},
		// Fetches and pushes would start maintenance in the background,
		// where git's timeout doesn't apply. Sync runs it instead.
		{"maintenance.auto", "false"},
		{"receive.autogc", "false"},
		{"gitk8s.url", repo.Spec.URL},
		{"gitk8s.uid", repo.UID},
	} {
		if err := r.SetConfig(ctx, kv[0], kv[1]); err != nil {
			return err
		}
	}
	e.repo, e.uid, e.url = r, repo.UID, repo.Spec.URL
	return nil
}

// removeStaleLocks removes the lock files that a killed git left in the
// copy at dir, which keep git from changing the refs, packed-refs, or
// config that they lock, and make maintenance skip the copy without an
// error. A lock is stale once it's older than the longest that a git
// command can take. A newer one may belong to a git that's still running,
// in this process or in the one that it replaces, which can run beside it
// for a few seconds.
func (m *Mirror) removeStaleLocks(dir string) {
	// A network volume's clock can differ from the node's.
	cutoff := time.Now().Add(-m.Git.MaxDuration() - time.Minute)
	remove := func(path string, d fs.DirEntry) {
		if d.IsDir() || !strings.HasSuffix(d.Name(), ".lock") {
			return
		}
		info, err := d.Info()
		if err != nil || info.ModTime().After(cutoff) {
			return
		}
		if err := os.Remove(path); err != nil {
			if !errors.Is(err, fs.ErrNotExist) {
				slog.Warn("removing a stale lock failed", "path", path, "err", err)
			}
			return
		}
		slog.Warn("removed a stale lock", "path", path, "modified", info.ModTime())
	}
	top, err := os.ReadDir(dir)
	if err != nil {
		return
	}
	for _, d := range top {
		remove(filepath.Join(dir, d.Name()), d)
	}
	for _, sub := range []string{"refs", "objects"} {
		_ = filepath.WalkDir(filepath.Join(dir, sub), func(path string, d fs.DirEntry, err error) error {
			switch {
			case err != nil:
			case d.IsDir() && sub == "objects" && isLooseObjectDir(d.Name()):
				// Thousands of loose objects, and never a lock.
				return filepath.SkipDir
			default:
				remove(path, d)
			}
			return nil
		})
	}
}

// isLooseObjectDir reports whether name is one of the directories under
// objects/ that hold loose objects, 00 to ff.
func isLooseObjectDir(name string) bool {
	return len(name) == 2 && strings.Trim(name, "0123456789abcdef") == ""
}

// markSeeded records that e's copy has fetched the external repository, so
// Open serves it, now and after a restart.
func (e *entry) markSeeded(ctx context.Context) error {
	if e.seeded.Load() {
		return nil
	}
	if err := e.repo.SetConfig(ctx, "gitk8s.seeded", "true"); err != nil {
		return err
	}
	e.seeded.Store(true)
	return nil
}

// Delete deletes repo's copy, unless the copy belongs to another
// GitRepository with the same name.
func (m *Mirror) Delete(ctx context.Context, repo *gitk8s.Repository) error {
	e := m.entry(repo)
	e.mu.Lock()
	defer e.mu.Unlock()
	if e.repo == nil || e.uid != repo.UID {
		have, err := m.read(ctx, e, repo.UID)
		if err != nil {
			return err
		}
		if have != "" && have != repo.UID {
			return nil
		}
	}
	e.repo, e.uid, e.url = nil, "", ""
	e.seeded.Store(false)
	if err := os.RemoveAll(e.dir); err != nil {
		return err
	}
	// The namespace's directory goes with its last copy; while it holds
	// another, removing it fails, which is fine.
	_ = os.Remove(filepath.Dir(e.dir))
	return nil
}
