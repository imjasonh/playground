// Package session defines how Wish apps dump and restore in-memory state.
//
// Kubernetes sends SIGTERM on pod shutdown, then SIGKILL after
// terminationGracePeriodSeconds. Only SIGTERM is catchable. Snapshot on
// SIGTERM (and periodically). Treat SIGKILL as a hard failure mode you
// shrink by keeping grace periods long enough for the dump to finish.
package session

import (
	"context"
	"errors"
)

// ErrNotFound means no snapshot exists for the key.
var ErrNotFound = errors.New("session: not found")

// Store persists opaque session blobs. GCS is the intended production Store.
type Store interface {
	Put(ctx context.Context, key string, value []byte) error
	Get(ctx context.Context, key string) ([]byte, error)
	Delete(ctx context.Context, key string) error
}

// Snapshotter is implemented by apps that can freeze in-memory state.
type Snapshotter interface {
	Snapshot(ctx context.Context) (key string, blob []byte, err error)
	Restore(ctx context.Context, blob []byte) error
}

// MemoryStore is an in-process Store for tests.
type MemoryStore struct {
	m map[string][]byte
}

// NewMemoryStore returns an empty MemoryStore.
func NewMemoryStore() *MemoryStore {
	return &MemoryStore{m: make(map[string][]byte)}
}

// Put implements Store.
func (s *MemoryStore) Put(ctx context.Context, key string, value []byte) error {
	cp := make([]byte, len(value))
	copy(cp, value)
	s.m[key] = cp
	return nil
}

// Get implements Store.
func (s *MemoryStore) Get(ctx context.Context, key string) ([]byte, error) {
	v, ok := s.m[key]
	if !ok {
		return nil, ErrNotFound
	}
	cp := make([]byte, len(v))
	copy(cp, v)
	return cp, nil
}

// Delete implements Store.
func (s *MemoryStore) Delete(ctx context.Context, key string) error {
	delete(s.m, key)
	return nil
}
