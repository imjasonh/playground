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
	if err := os.MkdirAll(root, 0o700); err != nil {
		return nil, err
	}
	if err := os.Chmod(root, 0o700); err != nil {
		return nil, err
	}
	return &LocalStore{Root: root}, nil
}

func (s *LocalStore) keyDir(ref Ref) (string, error) {
	if err := ref.Validate(); err != nil {
		return "", err
	}
	return filepath.Join(s.Root, filepath.FromSlash(ref.Key())), nil
}

func (s *LocalStore) Put(ctx context.Context, ref Ref, pkg Package) error {
	meta, err := pkg.ReadMeta()
	if err != nil {
		return err
	}
	if err := ValidateMeta(ref, meta, ""); err != nil {
		return err
	}
	dst, err := s.keyDir(ref)
	if err != nil {
		return err
	}
	if err := os.MkdirAll(filepath.Dir(dst), 0o700); err != nil {
		return err
	}
	tmp, err := os.MkdirTemp(filepath.Dir(dst), "."+filepath.Base(dst)+".tmp-")
	if err != nil {
		return err
	}
	defer os.RemoveAll(tmp)
	for _, name := range objectNames() {
		if err := ctx.Err(); err != nil {
			return err
		}
		src := filepath.Join(pkg.Dir, name)
		if err := copyFile(src, filepath.Join(tmp, name)); err != nil {
			return fmt.Errorf("put %s: %w", name, err)
		}
	}
	backup := dst + ".old"
	_ = os.RemoveAll(backup)
	hadOld := false
	if err := os.Rename(dst, backup); err == nil {
		hadOld = true
	} else if !os.IsNotExist(err) {
		return err
	}
	if err := os.Rename(tmp, dst); err != nil {
		if hadOld {
			_ = os.Rename(backup, dst)
		}
		return err
	}
	_ = os.RemoveAll(backup)
	return nil
}

func (s *LocalStore) Get(ctx context.Context, ref Ref, destDir string) (Package, error) {
	pkg := NewPackageDir(destDir)
	src, err := s.keyDir(ref)
	if err != nil {
		return pkg, err
	}
	if err := os.MkdirAll(destDir, 0o700); err != nil {
		return pkg, err
	}
	for _, name := range objectNames() {
		if err := ctx.Err(); err != nil {
			return pkg, err
		}
		if err := copyFile(filepath.Join(src, name), filepath.Join(destDir, name)); err != nil {
			return pkg, fmt.Errorf("get %s: %w", name, err)
		}
	}
	meta, err := pkg.ReadMeta()
	if err != nil {
		return pkg, err
	}
	if err := ValidateMeta(ref, meta, ""); err != nil {
		return pkg, err
	}
	pkg.Meta = meta
	return pkg, nil
}

func (s *LocalStore) Delete(ctx context.Context, ref Ref) error {
	if err := ctx.Err(); err != nil {
		return err
	}
	dir, err := s.keyDir(ref)
	if err != nil {
		return err
	}
	return os.RemoveAll(dir)
}

// Has reports whether every file in a complete local package exists.
func (s *LocalStore) Has(ctx context.Context, ref Ref) (bool, error) {
	if err := ctx.Err(); err != nil {
		return false, err
	}
	dir, err := s.keyDir(ref)
	if err != nil {
		return false, err
	}
	for _, name := range objectNames() {
		info, statErr := os.Stat(filepath.Join(dir, name))
		if os.IsNotExist(statErr) {
			return false, nil
		}
		if statErr != nil {
			return false, statErr
		}
		if !info.Mode().IsRegular() || info.Size() == 0 {
			return false, nil
		}
	}
	meta, err := NewPackageDir(dir).ReadMeta()
	if err != nil {
		return false, err
	}
	if err := ValidateMeta(ref, meta, ""); err != nil {
		return false, err
	}
	return true, nil
}

func (s *LocalStore) Meta(ctx context.Context, ref Ref) (Meta, error) {
	ok, err := s.Has(ctx, ref)
	if err != nil {
		return Meta{}, err
	}
	if !ok {
		return Meta{}, os.ErrNotExist
	}
	dir, err := s.keyDir(ref)
	if err != nil {
		return Meta{}, err
	}
	return NewPackageDir(dir).ReadMeta()
}

// Exists reports whether a package is present.
func (s *LocalStore) Exists(ref Ref) bool {
	ok, _ := s.Has(context.Background(), ref)
	return ok
}

func (s *LocalStore) Health(ctx context.Context) error {
	if err := ctx.Err(); err != nil {
		return err
	}
	_, err := os.Stat(s.Root)
	return err
}
