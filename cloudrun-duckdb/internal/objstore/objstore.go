// Package objstore reads and writes the replica's objects in Cloud Storage
// or a local directory. It needs four operations: get, conditional create,
// list, and delete. A conditional create is what lets two instances race to
// publish the same transaction and have exactly one of them win.
package objstore

import (
	"context"
	"errors"
	"fmt"
	"io"
	"net/url"
	"strings"
	"time"
)

// ErrNotFound is returned by Get when no object has the key.
var ErrNotFound = errors.New("object not found")

// ErrExists is returned by Create when an object already has the key.
var ErrExists = errors.New("object already exists")

// Object describes one object in a listing.
type Object struct {
	Key     string
	Size    int64
	Created time.Time
}

// Bucket is a flat namespace of immutable objects. Keys are relative to the
// replica URL's path.
type Bucket interface {
	// Get returns the object's contents.
	Get(ctx context.Context, key string) (io.ReadCloser, error)
	// Create stores size bytes from r under key only if no object has that
	// key, and returns ErrExists otherwise.
	Create(ctx context.Context, key string, r io.Reader, size int64) error
	// List returns the objects whose keys start with prefix and sort after
	// startAfter, in key order.
	List(ctx context.Context, prefix, startAfter string) ([]Object, error)
	// Delete removes the object. Deleting a missing object is not an error.
	Delete(ctx context.Context, key string) error
}

// Open returns the bucket for a replica URL: file:///dir or
// gs://bucket/prefix. A gs:// URL may set ?endpoint=http://host:port to use
// an emulator such as cmd/fakegcs; STORAGE_EMULATOR_HOST does the same.
func Open(ctx context.Context, rawURL string) (Bucket, error) {
	u, err := url.Parse(rawURL)
	if err != nil {
		return nil, fmt.Errorf("parse replica URL: %w", err)
	}
	switch u.Scheme {
	case "file":
		return NewFile(u.Path)
	case "gs":
		if u.Host == "" {
			return nil, fmt.Errorf("replica URL %q has no bucket", rawURL)
		}
		return NewGCS(ctx, u.Host, strings.Trim(u.Path, "/"), u.Query().Get("endpoint"))
	default:
		return nil, fmt.Errorf("replica URL %q: scheme must be file or gs", rawURL)
	}
}

// ReadAll gets an object and reads all of it.
func ReadAll(ctx context.Context, b Bucket, key string) ([]byte, error) {
	rc, err := b.Get(ctx, key)
	if err != nil {
		return nil, err
	}
	defer rc.Close()
	return io.ReadAll(rc)
}
