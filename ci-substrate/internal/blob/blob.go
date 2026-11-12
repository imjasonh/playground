// Package blob is a content-addressed blob store on local disk. Blobs are
// keyed by their SHA-256 alone, so the store is inherently shared across
// tenants: identical content is one file regardless of who wrote it. Tenant
// isolation lives above this layer, in package tenant and the action cache.
package blob

import (
	"errors"
	"io/fs"
	"os"
	"path/filepath"

	repb "github.com/bazelbuild/remote-apis/build/bazel/remote/execution/v2"

	"github.com/imjasonh/playground/ci-substrate/internal/digest"
)

// ErrNotFound is returned by Get for a digest the store does not hold.
var ErrNotFound = errors.New("blob not found")

// Store holds blobs under a root directory.
type Store struct {
	root string
}

// NewStore creates the root directory if needed and returns a store rooted
// there.
func NewStore(root string) (*Store, error) {
	if err := os.MkdirAll(root, 0o755); err != nil {
		return nil, err
	}
	return &Store{root: root}, nil
}

func (s *Store) path(hash string) string {
	if len(hash) >= 4 {
		return filepath.Join(s.root, hash[:2], hash[2:4], hash)
	}
	return filepath.Join(s.root, hash)
}

// Has reports whether the store holds d, by hash.
func (s *Store) Has(d *repb.Digest) bool {
	_, err := os.Stat(s.path(d.GetHash()))
	return err == nil
}

// Put verifies b against d and writes it. The write is atomic: a reader never
// sees a half-written blob, and a verified blob on disk always matches its
// name. Putting a blob the store already holds is a no-op.
func (s *Store) Put(d *repb.Digest, b []byte) error {
	if err := digest.Verify(d, b); err != nil {
		return err
	}
	p := s.path(d.GetHash())
	if err := os.MkdirAll(filepath.Dir(p), 0o755); err != nil {
		return err
	}
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
	return os.Rename(tmpName, p)
}

// Get returns the bytes for d, or ErrNotFound. Get does not verify; callers
// that did not write the blob themselves must verify what they read, because a
// file on disk can still be corrupted or tampered with after it was stored.
func (s *Store) Get(d *repb.Digest) ([]byte, error) {
	b, err := os.ReadFile(s.path(d.GetHash()))
	if errors.Is(err, fs.ErrNotExist) {
		return nil, ErrNotFound
	}
	return b, err
}

// Delete removes d from the store if present.
func (s *Store) Delete(d *repb.Digest) error {
	err := os.Remove(s.path(d.GetHash()))
	if errors.Is(err, fs.ErrNotExist) {
		return nil
	}
	return err
}
