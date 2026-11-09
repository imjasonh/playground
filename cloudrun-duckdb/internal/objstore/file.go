package objstore

import (
	"context"
	"errors"
	"io"
	"io/fs"
	"os"
	"path/filepath"
	"slices"
	"strings"
)

// File is a bucket in a local directory. Create writes a temporary file and
// links it into place, which fails if the name exists, so it is as atomic
// as a conditional create in Cloud Storage.
type File struct {
	root string
}

// NewFile returns a bucket rooted at dir.
func NewFile(dir string) (*File, error) {
	if dir == "" {
		return nil, errors.New("file replica URL has no path")
	}
	if err := os.MkdirAll(dir, 0o755); err != nil {
		return nil, err
	}
	return &File{root: dir}, nil
}

func (f *File) path(key string) string {
	return filepath.Join(f.root, filepath.FromSlash(key))
}

// Get implements Bucket.
func (f *File) Get(ctx context.Context, key string) (io.ReadCloser, error) {
	file, err := os.Open(f.path(key))
	if errors.Is(err, fs.ErrNotExist) {
		return nil, ErrNotFound
	}
	return file, err
}

// Create implements Bucket.
func (f *File) Create(ctx context.Context, key string, r io.Reader, size int64) error {
	dst := f.path(key)
	if err := os.MkdirAll(filepath.Dir(dst), 0o755); err != nil {
		return err
	}
	tmp, err := os.CreateTemp(filepath.Dir(dst), ".tmp-*")
	if err != nil {
		return err
	}
	defer os.Remove(tmp.Name())
	if _, err := io.Copy(tmp, r); err != nil {
		tmp.Close()
		return err
	}
	if err := tmp.Close(); err != nil {
		return err
	}
	if err := os.Link(tmp.Name(), dst); err != nil {
		if errors.Is(err, fs.ErrExist) {
			return ErrExists
		}
		return err
	}
	return nil
}

// List implements Bucket. Keys don't nest: the part of prefix after its
// last slash matches the start of a file name in that directory.
func (f *File) List(ctx context.Context, prefix, startAfter string) ([]Object, error) {
	dir, namePrefix := "", prefix
	if i := strings.LastIndex(prefix, "/"); i >= 0 {
		dir, namePrefix = prefix[:i+1], prefix[i+1:]
	}
	entries, err := os.ReadDir(f.path(dir))
	if errors.Is(err, fs.ErrNotExist) {
		return nil, nil
	}
	if err != nil {
		return nil, err
	}
	var out []Object
	for _, e := range entries {
		name := e.Name()
		key := dir + name
		if e.IsDir() || strings.HasPrefix(name, ".tmp-") || !strings.HasPrefix(name, namePrefix) || key <= startAfter {
			continue
		}
		info, err := e.Info()
		if errors.Is(err, fs.ErrNotExist) {
			continue
		}
		if err != nil {
			return nil, err
		}
		out = append(out, Object{Key: key, Size: info.Size(), Created: info.ModTime()})
	}
	slices.SortFunc(out, func(a, b Object) int { return strings.Compare(a.Key, b.Key) })
	return out, nil
}

// Delete implements Bucket.
func (f *File) Delete(ctx context.Context, key string) error {
	err := os.Remove(f.path(key))
	if errors.Is(err, fs.ErrNotExist) {
		return nil
	}
	return err
}
