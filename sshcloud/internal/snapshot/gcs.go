package snapshot

import (
	"context"
	"crypto/rand"
	"encoding/hex"
	"encoding/json"
	"errors"
	"fmt"
	"io"
	"os"
	"path"
	"path/filepath"
	"strings"

	"cloud.google.com/go/storage"
	"google.golang.org/api/iterator"
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
	if err := validateKey(key); err != nil {
		return err
	}
	bkt := s.client.Bucket(s.Bucket)
	var random [16]byte
	if _, err := rand.Read(random[:]); err != nil {
		return fmt.Errorf("snapshot version: %w", err)
	}
	version := hex.EncodeToString(random[:])
	for _, name := range objectNames() {
		src := filepath.Join(pkg.Dir, name)
		f, err := os.Open(src)
		if err != nil {
			return err
		}
		w := bkt.Object(s.objectKey(key, path.Join("versions", version, name))).NewWriter(ctx)
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
	// Publish one small pointer only after every immutable version object is
	// durable, so readers never observe a mixed/partial four-file package.
	manifest, err := json.Marshal(map[string]string{"version": version})
	if err != nil {
		return err
	}
	writeCtx, cancelWrite := context.WithCancel(ctx)
	w := bkt.Object(s.objectKey(key, "current.json")).NewWriter(writeCtx)
	if _, err := w.Write(append(manifest, '\n')); err != nil {
		cancelWrite()
		_ = w.Close()
		return err
	}
	if err := w.Close(); err != nil {
		cancelWrite()
		return err
	}
	cancelWrite()
	return nil
}

func (s *GCSStore) Get(ctx context.Context, key, destDir string) (Package, error) {
	pkg := NewPackageDir(destDir)
	if err := validateKey(key); err != nil {
		return pkg, err
	}
	if err := os.MkdirAll(destDir, 0o755); err != nil {
		return pkg, err
	}
	bkt := s.client.Bucket(s.Bucket)
	r, err := bkt.Object(s.objectKey(key, "current.json")).NewReader(ctx)
	if err != nil {
		return pkg, fmt.Errorf("get snapshot manifest: %w", err)
	}
	var manifest struct {
		Version string `json:"version"`
	}
	decodeErr := json.NewDecoder(io.LimitReader(r, 4<<10)).Decode(&manifest)
	closeErr := r.Close()
	if decodeErr != nil {
		return pkg, fmt.Errorf("decode snapshot manifest: %w", decodeErr)
	}
	if closeErr != nil {
		return pkg, closeErr
	}
	if len(manifest.Version) != 32 || strings.Trim(manifest.Version, "0123456789abcdef") != "" {
		return pkg, fmt.Errorf("invalid snapshot version %q", manifest.Version)
	}
	for _, name := range objectNames() {
		r, err := bkt.Object(s.objectKey(key, path.Join("versions", manifest.Version, name))).NewReader(ctx)
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

// Has checks the atomic current-version manifest.
func (s *GCSStore) Has(ctx context.Context, key string) (bool, error) {
	if err := validateKey(key); err != nil {
		return false, err
	}
	_, err := s.client.Bucket(s.Bucket).Object(s.objectKey(key, "current.json")).Attrs(ctx)
	if errors.Is(err, storage.ErrObjectNotExist) {
		return false, nil
	}
	return err == nil, err
}

func (s *GCSStore) Meta(ctx context.Context, key string) (Meta, error) {
	if err := validateKey(key); err != nil {
		return Meta{}, err
	}
	bkt := s.client.Bucket(s.Bucket)
	r, err := bkt.Object(s.objectKey(key, "current.json")).NewReader(ctx)
	if err != nil {
		return Meta{}, err
	}
	var manifest struct {
		Version string `json:"version"`
	}
	decodeErr := json.NewDecoder(io.LimitReader(r, 4<<10)).Decode(&manifest)
	closeErr := r.Close()
	if decodeErr != nil {
		return Meta{}, decodeErr
	}
	if closeErr != nil {
		return Meta{}, closeErr
	}
	if len(manifest.Version) != 32 || strings.Trim(manifest.Version, "0123456789abcdef") != "" {
		return Meta{}, fmt.Errorf("invalid snapshot version %q", manifest.Version)
	}
	metaReader, err := bkt.Object(s.objectKey(key, path.Join("versions", manifest.Version, "meta.json"))).NewReader(ctx)
	if err != nil {
		return Meta{}, err
	}
	var meta Meta
	decodeErr = json.NewDecoder(io.LimitReader(metaReader, 64<<10)).Decode(&meta)
	closeErr = metaReader.Close()
	if decodeErr != nil {
		return Meta{}, decodeErr
	}
	return meta, closeErr
}

func (s *GCSStore) Delete(ctx context.Context, key string) error {
	if err := validateKey(key); err != nil {
		return err
	}
	bkt := s.client.Bucket(s.Bucket)
	var first error
	prefix := s.objectKey(key, "") + "/"
	it := bkt.Objects(ctx, &storage.Query{Prefix: prefix})
	for {
		attrs, err := it.Next()
		if err == iterator.Done {
			break
		}
		if err != nil {
			if first == nil {
				first = err
			}
			break
		}
		if err := bkt.Object(attrs.Name).Delete(ctx); err != nil && !errors.Is(err, storage.ErrObjectNotExist) && first == nil {
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
