package snapshot

import (
	"context"
	"fmt"
	"io"
	"os"
	"path"
	"path/filepath"

	"cloud.google.com/go/storage"
)

// GCSStore persists snapshot packages in a GCS bucket.
type GCSStore struct {
	Bucket string
	Prefix string // optional key prefix, e.g. "sshcloud/snaps"
	client *storage.Client
}

// NewGCSStore creates a GCS-backed store. prefix may be empty.
func NewGCSStore(ctx context.Context, bucket, prefix string) (*GCSStore, error) {
	if bucket == "" {
		return nil, fmt.Errorf("bucket required")
	}
	client, err := storage.NewClient(ctx)
	if err != nil {
		return nil, err
	}
	return &GCSStore{Bucket: bucket, Prefix: prefix, client: client}, nil
}

func (s *GCSStore) objectKey(key, name string) string {
	return path.Join(s.Prefix, key, name)
}

func (s *GCSStore) Put(ctx context.Context, key string, pkg Package) error {
	bkt := s.client.Bucket(s.Bucket)
	for _, name := range objectNames() {
		src := filepath.Join(pkg.Dir, name)
		f, err := os.Open(src)
		if err != nil {
			return err
		}
		w := bkt.Object(s.objectKey(key, name)).NewWriter(ctx)
		_, copyErr := io.Copy(w, f)
		closeErr := w.Close()
		_ = f.Close()
		if copyErr != nil {
			return copyErr
		}
		if closeErr != nil {
			return closeErr
		}
	}
	return nil
}

func (s *GCSStore) Get(ctx context.Context, key, destDir string) (Package, error) {
	pkg := NewPackageDir(destDir)
	if err := os.MkdirAll(destDir, 0o755); err != nil {
		return pkg, err
	}
	bkt := s.client.Bucket(s.Bucket)
	for _, name := range objectNames() {
		r, err := bkt.Object(s.objectKey(key, name)).NewReader(ctx)
		if err != nil {
			return pkg, fmt.Errorf("get %s: %w", name, err)
		}
		dst := filepath.Join(destDir, name)
		f, err := os.Create(dst)
		if err != nil {
			_ = r.Close()
			return pkg, err
		}
		_, copyErr := io.Copy(f, r)
		closeR := r.Close()
		closeF := f.Close()
		if copyErr != nil {
			return pkg, copyErr
		}
		if closeR != nil {
			return pkg, closeR
		}
		if closeF != nil {
			return pkg, closeF
		}
	}
	meta, err := pkg.ReadMeta()
	if err != nil {
		return pkg, err
	}
	pkg.Meta = meta
	return pkg, nil
}

func (s *GCSStore) Delete(ctx context.Context, key string) error {
	bkt := s.client.Bucket(s.Bucket)
	var first error
	for _, name := range objectNames() {
		if err := bkt.Object(s.objectKey(key, name)).Delete(ctx); err != nil && first == nil {
			first = err
		}
	}
	return first
}

// Close closes the underlying GCS client.
func (s *GCSStore) Close() error {
	if s.client != nil {
		return s.client.Close()
	}
	return nil
}
