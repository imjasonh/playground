package snapshot

import (
	"context"
	"errors"
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

func (s *LocalStore) Put(ctx context.Context, ref Ref, pkg Package) (retErr error) {
	dst, err := s.keyDir(ref)
	if err != nil {
		return err
	}
	if err := os.MkdirAll(filepath.Dir(dst), 0o700); err != nil {
		return err
	}
	tmp, err := unusedTempPath(filepath.Dir(dst), "."+filepath.Base(dst)+".put-")
	if err != nil {
		return err
	}
	defer func() {
		if err := os.RemoveAll(tmp); err != nil {
			retErr = errors.Join(retErr, fmt.Errorf("clean local snapshot staging: %w", err))
		}
	}()
	if _, err := ClonePackage(ctx, ref, pkg, tmp, ""); err != nil {
		return err
	}
	backup, err := unusedTempPath(filepath.Dir(dst), "."+filepath.Base(dst)+".previous-")
	if err != nil {
		return err
	}
	hadOld := false
	if err := os.Rename(dst, backup); err == nil {
		hadOld = true
	} else if !os.IsNotExist(err) {
		return err
	}
	if err := os.Rename(tmp, dst); err != nil {
		if hadOld {
			if rollbackErr := os.Rename(backup, dst); rollbackErr != nil {
				return fmt.Errorf("publish local snapshot: %w (rollback: %v)", err, rollbackErr)
			}
		}
		return err
	}
	if hadOld {
		if err := os.RemoveAll(backup); err != nil {
			return fmt.Errorf("clean previous local snapshot: %w", err)
		}
	}
	return nil
}

func (s *LocalStore) Get(ctx context.Context, ref Ref, destDir string) (Package, error) {
	pkg := NewPackageDir(destDir)
	src, err := s.keyDir(ref)
	if err != nil {
		return pkg, err
	}
	return ClonePackage(ctx, ref, NewPackageDir(src), destDir, "")
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
	if _, err := os.Stat(dir); os.IsNotExist(err) {
		return false, nil
	} else if err != nil {
		return false, err
	}
	if _, err := ValidatePackage(ref, NewPackageDir(dir), ""); err != nil {
		return false, err
	}
	return true, nil
}

func (s *LocalStore) Meta(ctx context.Context, ref Ref) (Meta, error) {
	dir, err := s.keyDir(ref)
	if err != nil {
		return Meta{}, err
	}
	if err := ctx.Err(); err != nil {
		return Meta{}, err
	}
	meta, err := ValidatePackage(ref, NewPackageDir(dir), "")
	if os.IsNotExist(err) {
		return Meta{}, os.ErrNotExist
	}
	return meta, err
}

func (s *LocalStore) Health(ctx context.Context) error {
	if err := ctx.Err(); err != nil {
		return err
	}
	_, err := os.Stat(s.Root)
	return err
}

func unusedTempPath(parent, pattern string) (string, error) {
	path, err := os.MkdirTemp(parent, pattern)
	if err != nil {
		return "", err
	}
	if err := os.Remove(path); err != nil {
		return "", err
	}
	return path, nil
}
