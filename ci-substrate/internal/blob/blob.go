// Package blob is a content-addressed blob store on local disk. Blobs are
// keyed by their SHA-256 alone, so the store is inherently shared across
// tenants: identical content is one file regardless of who wrote it. Tenant
// isolation lives above this layer, in package tenant and the action cache.
package blob

import (
	"crypto/sha256"
	"encoding/hex"
	"errors"
	"fmt"
	"io"
	"io/fs"
	"os"
	"path/filepath"
	"slices"
	"strings"
	"sync"
	"sync/atomic"
	"time"

	repb "github.com/bazelbuild/remote-apis/build/bazel/remote/execution/v2"

	"github.com/imjasonh/playground/ci-substrate/internal/digest"
)

// ErrNotFound is returned by Get and Open for a digest the store does not hold.
var ErrNotFound = errors.New("blob not found")

// Store holds blobs under a root directory. When maxBytes is positive, Store
// evicts the least-recently-used blobs whenever stored bytes exceed the limit.
type Store struct {
	root     string
	maxBytes int64

	usage     atomic.Int64
	evictions atomic.Int64
	evictMu   sync.Mutex
}

// NewStore creates the root directory if needed and returns an unbounded store
// rooted there.
func NewStore(root string) (*Store, error) {
	return NewStoreWithLimit(root, 0)
}

// NewStoreWithLimit creates the root directory if needed and returns a store
// that evicts least-recently-used blobs once stored bytes exceed maxBytes. A
// non-positive maxBytes disables eviction.
func NewStoreWithLimit(root string, maxBytes int64) (*Store, error) {
	if err := os.MkdirAll(root, 0o755); err != nil {
		return nil, err
	}
	s := &Store{root: root, maxBytes: maxBytes}
	if maxBytes > 0 {
		s.scanUsage()
	}
	return s, nil
}

func (s *Store) scanUsage() {
	var total int64
	_ = filepath.WalkDir(s.root, func(path string, de fs.DirEntry, err error) error {
		if err != nil || de.IsDir() || strings.HasPrefix(de.Name(), ".") {
			return nil
		}
		if fi, err := de.Info(); err == nil {
			total += fi.Size()
		}
		return nil
	})
	s.usage.Store(total)
}

// Usage returns the store's tracked byte usage when a size limit is enabled.
func (s *Store) Usage() int64 { return s.usage.Load() }

// Evictions returns how many blobs the store has evicted to stay within its
// size limit.
func (s *Store) Evictions() int64 { return s.evictions.Load() }

// path maps a validated digest to its file. The hash comes from the client, so
// it is validated as hex first: anything else could name a path outside root.
func (s *Store) path(d *repb.Digest) (string, error) {
	if err := digest.Validate(d); err != nil {
		return "", err
	}
	h := d.GetHash()
	return filepath.Join(s.root, h[:2], h[2:4], h), nil
}

func (s *Store) touch(p string) {
	if s.maxBytes <= 0 {
		return
	}
	now := time.Now()
	_ = os.Chtimes(p, now, now)
}

// Has reports whether the store holds d with d's size. A malformed digest is
// never held.
func (s *Store) Has(d *repb.Digest) bool {
	p, err := s.path(d)
	if err != nil {
		return false
	}
	fi, err := os.Stat(p)
	if err != nil || fi.Size() != d.GetSizeBytes() {
		return false
	}
	s.touch(p)
	return true
}

// Put verifies b against d and writes it. The write is atomic: a reader never
// sees a half-written blob, and a verified blob on disk always matches its
// name.
func (s *Store) Put(d *repb.Digest, b []byte) error {
	p, err := s.path(d)
	if err != nil {
		return err
	}
	if err := digest.Verify(d, b); err != nil {
		return err
	}
	if err := os.MkdirAll(filepath.Dir(p), 0o755); err != nil {
		return err
	}
	existed := s.fileExists(p)
	tmp, err := os.CreateTemp(filepath.Dir(p), ".tmp-*")
	if err != nil {
		return err
	}
	tmpName := tmp.Name()
	defer os.Remove(tmpName)
	if _, err := tmp.Write(b); err != nil {
		tmp.Close()
		return err
	}
	if err := tmp.Close(); err != nil {
		return err
	}
	if err := os.Rename(tmpName, p); err != nil {
		return err
	}
	if !existed && s.maxBytes > 0 {
		s.noteAdded(int64(len(b)))
	}
	return nil
}

// PutReader streams r to disk while computing its SHA-256 digest and commits
// the blob atomically only if both size and hash match d. It never buffers the
// entire blob in memory.
func (s *Store) PutReader(d *repb.Digest, r io.Reader) error {
	p, err := s.path(d)
	if err != nil {
		return err
	}
	if err := os.MkdirAll(filepath.Dir(p), 0o755); err != nil {
		return err
	}
	existed := s.fileExists(p)
	tmp, err := os.CreateTemp(filepath.Dir(p), ".tmp-*")
	if err != nil {
		return err
	}
	tmpName := tmp.Name()
	defer os.Remove(tmpName)

	h := sha256.New()
	limited := io.LimitReader(r, d.GetSizeBytes()+1)
	n, err := io.Copy(io.MultiWriter(tmp, h), limited)
	if err != nil {
		tmp.Close()
		return err
	}
	if err := tmp.Close(); err != nil {
		return err
	}
	if n != d.GetSizeBytes() {
		return fmt.Errorf("size mismatch for %s: have %d bytes, want %d", d.GetHash(), n, d.GetSizeBytes())
	}
	if got := hex.EncodeToString(h.Sum(nil)); got != d.GetHash() {
		return fmt.Errorf("hash mismatch: want %s, have %s", d.GetHash(), got)
	}
	if err := os.Rename(tmpName, p); err != nil {
		return err
	}
	if !existed && s.maxBytes > 0 {
		s.noteAdded(n)
	}
	return nil
}

func (s *Store) fileExists(p string) bool {
	_, err := os.Stat(p)
	return err == nil
}

func (s *Store) noteAdded(n int64) {
	if s.usage.Add(n) > s.maxBytes {
		_, _, _ = s.Evict()
	}
}

// Open returns an open file handle and byte size for d, or ErrNotFound. Callers
// must close the returned file. Open does not verify the contents; callers that
// require verification must hash while reading.
func (s *Store) Open(d *repb.Digest) (*os.File, int64, error) {
	p, err := s.path(d)
	if err != nil {
		return nil, 0, err
	}
	f, err := os.Open(p)
	if errors.Is(err, fs.ErrNotExist) {
		return nil, 0, ErrNotFound
	}
	if err != nil {
		return nil, 0, err
	}
	fi, err := f.Stat()
	if err != nil {
		f.Close()
		return nil, 0, err
	}
	s.touch(p)
	return f, fi.Size(), nil
}

// Get returns the bytes for d, or ErrNotFound. Get does not verify; callers
// that did not write the blob themselves must verify what they read, because a
// file on disk can still be corrupted or tampered with after it was stored.
func (s *Store) Get(d *repb.Digest) ([]byte, error) {
	p, err := s.path(d)
	if err != nil {
		return nil, err
	}
	b, err := os.ReadFile(p)
	if errors.Is(err, fs.ErrNotExist) {
		return nil, ErrNotFound
	}
	if err == nil {
		s.touch(p)
	}
	return b, err
}

// Delete removes d from the store if present.
func (s *Store) Delete(d *repb.Digest) error {
	p, err := s.path(d)
	if err != nil {
		return err
	}
	var size int64
	if s.maxBytes > 0 {
		if fi, err := os.Stat(p); err == nil {
			size = fi.Size()
		}
	}
	err = os.Remove(p)
	if errors.Is(err, fs.ErrNotExist) {
		return nil
	}
	if err == nil && size > 0 {
		s.usage.Add(-size)
	}
	return err
}

// Evict removes the least-recently-used blobs until total disk usage is at or
// below 85% of the configured limit. It is a no-op when no limit is set or
// usage is within the limit.
func (s *Store) Evict() (int, int64, error) {
	if s.maxBytes <= 0 {
		return 0, 0, nil
	}
	s.evictMu.Lock()
	defer s.evictMu.Unlock()

	type entry struct {
		path    string
		size    int64
		modTime time.Time
	}
	var entries []entry
	var total int64
	err := filepath.WalkDir(s.root, func(path string, de fs.DirEntry, err error) error {
		if err != nil || de.IsDir() || strings.HasPrefix(de.Name(), ".") {
			return nil
		}
		fi, err := de.Info()
		if err != nil {
			return nil
		}
		total += fi.Size()
		entries = append(entries, entry{path: path, size: fi.Size(), modTime: fi.ModTime()})
		return nil
	})
	if err != nil {
		return 0, 0, err
	}
	s.usage.Store(total)
	if total <= s.maxBytes {
		return 0, 0, nil
	}
	target := (s.maxBytes * 85) / 100
	slices.SortFunc(entries, func(a, b entry) int {
		return a.modTime.Compare(b.modTime)
	})
	var evicted int
	var freed int64
	for _, e := range entries {
		if total <= target {
			break
		}
		if err := os.Remove(e.path); err != nil && !errors.Is(err, fs.ErrNotExist) {
			continue
		}
		total -= e.size
		freed += e.size
		evicted++
	}
	s.usage.Store(total)
	s.evictions.Add(int64(evicted))
	return evicted, freed, nil
}
