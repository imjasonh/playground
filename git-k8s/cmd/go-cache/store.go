package main

import (
	"context"
	"errors"
	"io"
	"io/fs"
	"log/slog"
	"os"
	"path/filepath"
	"slices"
	"sync"
	"time"
)

// store keeps files in a directory, by key, and keeps their total size,
// with the writes in progress, under max. A write reserves room for its
// bytes before it writes them, and the store removes the least recently
// used files to make room. A file is written to a temporary file and then
// linked into place, so readers never see part of one, and the first of
// two writers of a key wins.
type store struct {
	dir     string
	max     int64
	metrics *metrics
	log     *slog.Logger
	// writes holds a value for each write in progress, up to its capacity.
	writes chan struct{}
	// writeWait is how long a write waits for another to finish.
	writeWait time.Duration

	mu       sync.Mutex
	size     int64 // bytes in files
	reserved int64 // bytes that writes in progress can still add

	evicting sync.Mutex
}

const (
	// touchAfter is how old a file's modification time, which eviction goes
	// by, gets before a read updates it.
	touchAfter = time.Hour
	// maxWrites is how many writes a store runs at once.
	maxWrites = 16
)

var (
	errFull = errors.New("there's no room for the write under -max-size")
	errBusy = errors.New("too many writes are in progress")
)

func openStore(dir string, max int64, m *metrics, log *slog.Logger) (*store, error) {
	s := &store{dir: dir, max: max, metrics: m, log: log, writes: make(chan struct{}, maxWrites), writeWait: 30 * time.Second}
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

// put writes the file for key with write, which must write at most size
// bytes, or any number if size is negative. It reports false if key
// already existed, and leaves that file alone. put fails with errBusy if
// other writes keep it waiting for longer than writeWait, and with errFull
// if it can't reserve room for what write writes.
func (s *store) put(ctx context.Context, key string, size int64, write func(io.Writer) error) (bool, error) {
	return s.putWithin(ctx, s.writeWait, key, size, write)
}

// tryPut is put, but fails with errBusy at once if other writes are using
// every slot.
func (s *store) tryPut(ctx context.Context, key string, size int64, write func(io.Writer) error) (bool, error) {
	return s.putWithin(ctx, 0, key, size, write)
}

func (s *store) putWithin(ctx context.Context, wait time.Duration, key string, size int64, write func(io.Writer) error) (bool, error) {
	path := s.path(key)
	if _, err := os.Stat(path); err == nil {
		return false, nil
	}
	if err := s.takeSlot(ctx, wait); err != nil {
		return false, err
	}
	defer func() { <-s.writes }()
	w := &reservedWriter{s: s, fixed: size >= 0}
	defer func() { s.release(w.reserved) }()
	if size >= 0 {
		if err := s.reserve(size); err != nil {
			return false, err
		}
		w.reserved = size
	}
	f, err := os.CreateTemp(filepath.Join(s.dir, "tmp"), "put-")
	if err != nil {
		return false, err
	}
	defer os.Remove(f.Name())
	w.f = f
	err = write(w)
	if cerr := f.Close(); err == nil {
		err = cerr
	}
	if err != nil {
		return false, err
	}
	if err := os.MkdirAll(filepath.Dir(path), 0o755); err != nil {
		return false, err
	}
	if err := os.Link(f.Name(), path); errors.Is(err, fs.ErrExist) {
		return false, nil
	} else if err != nil {
		return false, err
	}
	s.mu.Lock()
	s.size += w.written
	s.reserved -= w.reserved
	w.reserved = 0
	s.metrics.stored.Store(s.size)
	s.mu.Unlock()
	return true, nil
}

// takeSlot takes a slot for a write, waiting up to wait for one.
func (s *store) takeSlot(ctx context.Context, wait time.Duration) error {
	select {
	case s.writes <- struct{}{}:
		return nil
	default:
	}
	if wait <= 0 {
		return errBusy
	}
	timer := time.NewTimer(wait)
	defer timer.Stop()
	select {
	case s.writes <- struct{}{}:
		return nil
	case <-timer.C:
		return errBusy
	case <-ctx.Done():
		return ctx.Err()
	}
}

// reservedWriter writes a store's temporary file, and reserves room for
// each byte before it writes it.
type reservedWriter struct {
	s *store
	f *os.File
	// fixed is whether the write reserved its size before it started, so
	// it can't grow.
	fixed    bool
	reserved int64
	written  int64
}

var errOverSize = errors.New("the write is larger than its size")

func (w *reservedWriter) Write(p []byte) (int, error) {
	if need := w.written + int64(len(p)) - w.reserved; need > 0 {
		if w.fixed {
			return 0, errOverSize
		}
		if err := w.s.reserve(need); err != nil {
			return 0, err
		}
		w.reserved += need
	}
	n, err := w.f.Write(p)
	w.written += int64(n)
	return n, err
}

// reserve counts n more bytes toward max for a write in progress. If they
// don't fit, it removes the least recently used files, and fails with
// errFull if they still don't.
func (s *store) reserve(n int64) error {
	if s.tryReserve(n) {
		return nil
	}
	s.evicting.Lock()
	defer s.evicting.Unlock()
	if !s.tryReserve(n) {
		s.evict(n)
		if !s.tryReserve(n) {
			return errFull
		}
	}
	return nil
}

func (s *store) tryReserve(n int64) bool {
	s.mu.Lock()
	defer s.mu.Unlock()
	if s.size+s.reserved+n > s.max {
		return false
	}
	s.reserved += n
	return true
}

func (s *store) release(n int64) {
	s.mu.Lock()
	defer s.mu.Unlock()
	s.reserved -= n
}

// evict removes the least recently used files until n more bytes would
// leave the store at most 90% full, or would fit, if writes in progress
// hold more than that. It removes nothing if writes in progress hold too
// much room for n more bytes to fit at all.
func (s *store) evict(n int64) {
	s.mu.Lock()
	target := s.max / 10 * 9
	if s.reserved+n > target {
		target = s.max
	}
	hopeless := s.reserved+n > s.max
	s.mu.Unlock()
	if hopeless {
		return
	}
	files, err := s.files()
	if err != nil {
		s.log.Error("listing files to evict", "err", err)
		return
	}
	slices.SortFunc(files, func(a, b file) int { return a.mtime.Compare(b.mtime) })
	for _, f := range files {
		s.mu.Lock()
		done := s.size+s.reserved+n <= target
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
