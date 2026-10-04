package main

import (
	"errors"
	"io"
	"io/fs"
	"log/slog"
	"os"
	"path/filepath"
	"slices"
	"sync"
	"sync/atomic"
	"time"
)

// store keeps files in a directory, by key, and removes the least recently
// used ones when their total size passes max. A file is written to a
// temporary file and then linked into place, so readers never see part of
// one, and the first of two writers of a key wins.
type store struct {
	dir     string
	max     int64
	metrics *metrics
	log     *slog.Logger

	mu       sync.Mutex
	size     int64
	evicting atomic.Bool
}

// touchAfter is how old a file's modification time, which eviction goes
// by, gets before a read updates it.
const touchAfter = time.Hour

func openStore(dir string, max int64, m *metrics, log *slog.Logger) (*store, error) {
	s := &store{dir: dir, max: max, metrics: m, log: log}
	tmp := filepath.Join(dir, "tmp")
	if err := os.RemoveAll(tmp); err != nil {
		return nil, err
	}
	if err := os.MkdirAll(tmp, 0o755); err != nil {
		return nil, err
	}
	files, err := s.files()
	if err != nil {
		return nil, err
	}
	for _, f := range files {
		s.size += f.size
	}
	m.stored.Store(s.size)
	return s, nil
}

type file struct {
	path  string
	size  int64
	mtime time.Time
}

func (s *store) files() ([]file, error) {
	var out []file
	err := filepath.WalkDir(s.dir, func(path string, d fs.DirEntry, err error) error {
		if errors.Is(err, fs.ErrNotExist) {
			return nil
		} else if err != nil {
			return err
		}
		if d.IsDir() {
			if path == filepath.Join(s.dir, "tmp") {
				return filepath.SkipDir
			}
			return nil
		}
		fi, err := d.Info()
		if errors.Is(err, fs.ErrNotExist) {
			return nil
		} else if err != nil {
			return err
		}
		out = append(out, file{path, fi.Size(), fi.ModTime()})
		return nil
	})
	return out, err
}

func (s *store) path(key string) string {
	return filepath.Join(s.dir, filepath.FromSlash(key))
}

// open opens the file for key and marks it as recently used.
func (s *store) open(key string) (*os.File, error) {
	path := s.path(key)
	f, err := os.Open(path)
	if err != nil {
		return nil, err
	}
	if fi, err := f.Stat(); err == nil && time.Since(fi.ModTime()) > touchAfter {
		now := time.Now()
		if err := os.Chtimes(path, now, now); err != nil {
			s.log.Warn("marking a file as used", "err", err)
		}
	}
	return f, nil
}

// put writes the file for key with write. It reports false if key
// already existed, and leaves that file alone.
func (s *store) put(key string, write func(io.Writer) error) (bool, error) {
	f, err := os.CreateTemp(filepath.Join(s.dir, "tmp"), "put-")
	if err != nil {
		return false, err
	}
	defer os.Remove(f.Name())
	err = write(f)
	if cerr := f.Close(); err == nil {
		err = cerr
	}
	if err != nil {
		return false, err
	}
	fi, err := os.Stat(f.Name())
	if err != nil {
		return false, err
	}
	path := s.path(key)
	if err := os.MkdirAll(filepath.Dir(path), 0o755); err != nil {
		return false, err
	}
	if err := os.Link(f.Name(), path); errors.Is(err, fs.ErrExist) {
		return false, nil
	} else if err != nil {
		return false, err
	}
	s.mu.Lock()
	s.size += fi.Size()
	over := s.size > s.max
	s.metrics.stored.Store(s.size)
	s.mu.Unlock()
	if over {
		s.evict()
	}
	return true, nil
}

// evict removes the least recently used files until the store holds at
// most 90% of max.
func (s *store) evict() {
	if !s.evicting.CompareAndSwap(false, true) {
		return
	}
	defer s.evicting.Store(false)
	files, err := s.files()
	if err != nil {
		s.log.Error("listing files to evict", "err", err)
		return
	}
	slices.SortFunc(files, func(a, b file) int { return a.mtime.Compare(b.mtime) })
	target := s.max / 10 * 9
	for _, f := range files {
		s.mu.Lock()
		done := s.size <= target
		s.mu.Unlock()
		if done {
			return
		}
		if err := os.Remove(f.path); err != nil {
			if !errors.Is(err, fs.ErrNotExist) {
				s.log.Error("evicting", "err", err)
			}
			continue
		}
		s.mu.Lock()
		s.size -= f.size
		s.metrics.stored.Store(s.size)
		s.mu.Unlock()
		s.metrics.evicted.Add(f.size)
	}
}
