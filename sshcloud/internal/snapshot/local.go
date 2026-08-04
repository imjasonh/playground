package snapshot

import (
	"context"
	"fmt"
	"os"
	"path/filepath"
)

// LocalStore keeps snapshot packages under a directory tree (GCS stand-in / cache).
type LocalStore struct {
	Root string
}

// NewLocalStore creates a filesystem blob store rooted at root.
func NewLocalStore(root string) (*LocalStore, error) {
	if root == "" {
		return nil, fmt.Errorf("root required")
	}
	if err := os.MkdirAll(root, 0o755); err != nil {
		return nil, err
	}
	return &LocalStore{Root: root}, nil
}

func (s *LocalStore) keyDir(key string) string {
	return filepath.Join(s.Root, filepath.FromSlash(key))
}

func (s *LocalStore) Put(ctx context.Context, key string, pkg Package) error {
	_ = ctx
	dst := s.keyDir(key)
	if err := os.MkdirAll(dst, 0o755); err != nil {
		return err
	}
	for _, name := range objectNames() {
		src := filepath.Join(pkg.Dir, name)
		if err := copyFile(src, filepath.Join(dst, name)); err != nil {
			return fmt.Errorf("put %s: %w", name, err)
		}
	}
	return nil
}

func (s *LocalStore) Get(ctx context.Context, key, destDir string) (Package, error) {
	_ = ctx
	src := s.keyDir(key)
	pkg := NewPackageDir(destDir)
	if err := os.MkdirAll(destDir, 0o755); err != nil {
		return pkg, err
	}
	for _, name := range objectNames() {
		if err := copyFile(filepath.Join(src, name), filepath.Join(destDir, name)); err != nil {
			return pkg, fmt.Errorf("get %s: %w", name, err)
		}
	}
	meta, err := pkg.ReadMeta()
	if err != nil {
		return pkg, err
	}
	pkg.Meta = meta
	return pkg, nil
}

func (s *LocalStore) Delete(ctx context.Context, key string) error {
	_ = ctx
	return os.RemoveAll(s.keyDir(key))
}

// Exists reports whether a package is present.
func (s *LocalStore) Exists(key string) bool {
	_, err := os.Stat(filepath.Join(s.keyDir(key), "meta.json"))
	return err == nil
}
