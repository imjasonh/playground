// Package actioncache is the durable action cache. An entry maps an action
// digest, within one Remote Execution instance, to the ActionResult that ran
// it. Entries live on disk next to the blob store, so a cas restart keeps
// every tenant's results. The instance name is part of the key: the same
// action digest cached by two tenants is two entries, which is the isolation
// the tenant layer enforces when it authorizes an instance.
package actioncache

import (
	"encoding/hex"
	"errors"
	"io/fs"
	"os"
	"path/filepath"

	repb "github.com/bazelbuild/remote-apis/build/bazel/remote/execution/v2"
	"google.golang.org/protobuf/proto"

	"github.com/imjasonh/playground/ci-substrate/internal/digest"
)

// ErrNotFound is returned by Get for an action the cache does not hold.
var ErrNotFound = errors.New("action result not found")

// Store holds action results under a root directory.
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

// path maps an instance and a validated action digest to a file. Instance
// names come from clients and may hold any character, so they are hex
// encoded; the hash is validated hex, so it is safe as a file name.
func (s *Store) path(instance string, action *repb.Digest) (string, error) {
	if err := digest.Validate(action); err != nil {
		return "", err
	}
	return filepath.Join(s.root, hex.EncodeToString([]byte(instance)), action.GetHash()), nil
}

// Get returns the result cached for action in instance, or ErrNotFound.
func (s *Store) Get(instance string, action *repb.Digest) (*repb.ActionResult, error) {
	p, err := s.path(instance, action)
	if err != nil {
		return nil, err
	}
	b, err := os.ReadFile(p)
	if errors.Is(err, fs.ErrNotExist) {
		return nil, ErrNotFound
	}
	if err != nil {
		return nil, err
	}
	ar := &repb.ActionResult{}
	if err := proto.Unmarshal(b, ar); err != nil {
		return nil, err
	}
	return ar, nil
}

// Put records ar as the result of action in instance. The write is atomic, so
// a reader never sees a partial entry.
func (s *Store) Put(instance string, action *repb.Digest, ar *repb.ActionResult) error {
	p, err := s.path(instance, action)
	if err != nil {
		return err
	}
	b, err := proto.Marshal(ar)
	if err != nil {
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
