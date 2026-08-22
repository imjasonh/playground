package session

import (
	"context"
	"errors"
	"fmt"
	"io"
	"os"
	"strings"

	"cloud.google.com/go/storage"
)

// GCSStore stores snapshots in a GCS bucket under prefix/.
type GCSStore struct {
	bucket *storage.BucketHandle
	prefix string
}

// NewGCSStore opens a Store for bucket/prefix. prefix may be empty.
func NewGCSStore(ctx context.Context, bucket, prefix string) (*GCSStore, error) {
	if bucket == "" {
		return nil, fmt.Errorf("session: GCS bucket is required")
	}
	client, err := storage.NewClient(ctx)
	if err != nil {
		return nil, err
	}
	p := strings.Trim(prefix, "/")
	if p != "" {
		p += "/"
	}
	return &GCSStore{bucket: client.Bucket(bucket), prefix: p}, nil
}

// NewGCSStoreFromEnv builds a GCSStore from SSHAPP_SESSION_BUCKET and
// optional SSHAPP_SESSION_PREFIX. Returns (nil, nil) when the bucket env is unset.
func NewGCSStoreFromEnv(ctx context.Context) (*GCSStore, error) {
	bucket := os.Getenv("SSHAPP_SESSION_BUCKET")
	if bucket == "" {
		return nil, nil
	}
	return NewGCSStore(ctx, bucket, os.Getenv("SSHAPP_SESSION_PREFIX"))
}

// Put implements Store.
func (s *GCSStore) Put(ctx context.Context, key string, value []byte) error {
	w := s.bucket.Object(s.prefix + key).NewWriter(ctx)
	if _, err := w.Write(value); err != nil {
		_ = w.Close()
		return err
	}
	return w.Close()
}

// Get implements Store.
func (s *GCSStore) Get(ctx context.Context, key string) ([]byte, error) {
	r, err := s.bucket.Object(s.prefix + key).NewReader(ctx)
	if err != nil {
		if errors.Is(err, storage.ErrObjectNotExist) {
			return nil, ErrNotFound
		}
		return nil, err
	}
	defer r.Close()
	return io.ReadAll(r)
}

// Delete implements Store.
func (s *GCSStore) Delete(ctx context.Context, key string) error {
	err := s.bucket.Object(s.prefix + key).Delete(ctx)
	if errors.Is(err, storage.ErrObjectNotExist) {
		return nil
	}
	return err
}
