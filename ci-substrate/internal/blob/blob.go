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

// path maps a validated digest to its file. The hash comes from the client, so
// it is validated as hex first: anything else could name a path outside root.
func (s *Store) path(d *repb.Digest) (string, error) {
	if err := digest.Validate(d); err != nil {
		return "", err
	}
	h := d.GetHash()
	return filepath.Join(s.root, h[:2], h[2:4], h), nil
}

// Has reports whether the store holds d with d's size. A malformed digest is
// never held.
func (s *Store) Has(d *repb.Digest) bool {
	p, err := s.path(d)
	if err != nil {
		return false
	}
	fi, err := os.Stat(p)
	return err == nil && fi.Size() == d.GetSizeBytes()
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
	p, err := s.path(d)
	if err != nil {
		return nil, err
	}
	b, err := os.ReadFile(p)
	if errors.Is(err, fs.ErrNotExist) {
		return nil, ErrNotFound
	}
	return b, err
}

// Delete removes d from the store if present.
func (s *Store) Delete(d *repb.Digest) error {
	p, err := s.path(d)
	if err != nil {
		return err
	}
	err = os.Remove(p)
	if errors.Is(err, fs.ErrNotExist) {
		return nil
	}
	return err
}
