package cache

import (
	"context"
	"errors"
	"os"
	"path/filepath"
	"sync"
	"testing"

	repb "github.com/bazelbuild/remote-apis/build/bazel/remote/execution/v2"

	"github.com/imjasonh/playground/ci-substrate/internal/blob"
	"github.com/imjasonh/playground/ci-substrate/internal/digest"
)

// fakeOrigin is an in-memory authoritative CAS that counts fetches.
type fakeOrigin struct {
	mu     sync.Mutex
	blobs  map[string][]byte
	fetchN int
	block  chan struct{} // when non-nil, Fetch waits on it before returning
}

func newFakeOrigin() *fakeOrigin { return &fakeOrigin{blobs: map[string][]byte{}} }

func (f *fakeOrigin) put(b []byte) *repb.Digest {
	d := digest.FromBytes(b)
	f.mu.Lock()
	f.blobs[digest.Key(d)] = b
	f.mu.Unlock()
	return d
}

func (f *fakeOrigin) Fetch(ctx context.Context, instanceName string, d *repb.Digest) ([]byte, error) {
	if f.block != nil {
		<-f.block
	}
	f.mu.Lock()
	defer f.mu.Unlock()
	f.fetchN++
	b, ok := f.blobs[digest.Key(d)]
	if !ok {
		return nil, errors.New("not found at origin")
	}
	return b, nil
}

func newCache(t *testing.T, origin Origin) *Cache {
	t.Helper()
	store, err := blob.NewStore(t.TempDir())
	if err != nil {
		t.Fatal(err)
	}
	return New(store, origin)
}

func TestColdThenWarm(t *testing.T) {
	origin := newFakeOrigin()
	d := origin.put([]byte("build output"))
	c := newCache(t, origin)

	for i := 0; i < 3; i++ {
		got, _, err := c.Get(t.Context(), "shared", d)
		if err != nil {
			t.Fatalf("Get #%d: %v", i, err)
		}
		if string(got) != "build output" {
			t.Fatalf("Get #%d = %q", i, got)
		}
	}
	if origin.fetchN != 1 {
		t.Errorf("origin fetched %d times, want 1 (cache should serve the rest)", origin.fetchN)
	}
	if s := c.Stats(); s.OriginFetches != 1 || s.Hits != 2 {
		t.Errorf("stats = %+v, want 1 fetch and 2 hits", s)
	}
}

func TestCrossTenantReuse(t *testing.T) {
	origin := newFakeOrigin()
	d := origin.put([]byte("shared base layer"))
	c := newCache(t, origin)

	if _, _, err := c.Get(t.Context(), "shared", d); err != nil {
		t.Fatalf("tenant A warm: %v", err)
	}
	if _, _, err := c.Get(t.Context(), "shared", d); err != nil {
		t.Fatalf("tenant B read: %v", err)
	}
	if origin.fetchN != 1 {
		t.Errorf("origin fetched %d times across two tenants, want 1", origin.fetchN)
	}
}

func TestPoisonedEntryFallsBack(t *testing.T) {
	origin := newFakeOrigin()
	content := []byte("trusted compiler binary")
	d := origin.put(content)

	root := t.TempDir()
	store, err := blob.NewStore(root)
	if err != nil {
		t.Fatal(err)
	}
	c := New(store, origin)

	// Warm the cache, then tamper with the stored copy out of band, keeping the
	// same length so only a hash check can catch it.
	if _, _, err := c.Get(t.Context(), "shared", d); err != nil {
		t.Fatal(err)
	}
	poisoned := append([]byte(nil), content...)
	poisoned[0] ^= 0xff
	// Overwrite the one stored file in place, simulating on-disk corruption or
	// a cache-poisoning write that bypasses the store's own verification.
	overwriteStoredFile(t, root, poisoned)

	got, _, err := c.Get(t.Context(), "shared", d)
	if err != nil {
		t.Fatalf("Get after poisoning: %v", err)
	}
	if string(got) != string(content) {
		t.Errorf("Get returned poisoned bytes %q, want %q", got, content)
	}
	if s := c.Stats(); s.PoisonRejected != 1 {
		t.Errorf("PoisonRejected = %d, want 1", s.PoisonRejected)
	}
	if origin.fetchN != 2 {
		t.Errorf("origin fetched %d times, want 2 (warm + refetch after poison)", origin.fetchN)
	}
}

func TestOriginBytesNotCachedWhenCorrupt(t *testing.T) {
	origin := newFakeOrigin()
	d := digest.FromBytes([]byte("honest"))
	// The origin lies: it stores bytes under a digest they do not match.
	origin.mu.Lock()
	origin.blobs[digest.Key(d)] = []byte("forged")
	origin.mu.Unlock()

	c := newCache(t, origin)
	if _, _, err := c.Get(t.Context(), "shared", d); err == nil {
		t.Error("Get accepted corrupt bytes from the origin")
	}
}

func TestSingleflightCollapsesFetches(t *testing.T) {
	origin := newFakeOrigin()
	origin.block = make(chan struct{})
	d := origin.put([]byte("hot cold blob"))
	c := newCache(t, origin)

	const n = 16
	var wg sync.WaitGroup
	errs := make([]error, n)
	for i := 0; i < n; i++ {
		wg.Add(1)
		go func(i int) {
			defer wg.Done()
			_, _, errs[i] = c.Get(t.Context(), "shared", d)
		}(i)
	}
	close(origin.block) // release all waiters at once
	wg.Wait()

	for i, err := range errs {
		if err != nil {
			t.Fatalf("Get %d: %v", i, err)
		}
	}
	if origin.fetchN > 2 {
		t.Errorf("origin fetched %d times for %d concurrent cold reads; singleflight should collapse them", origin.fetchN, n)
	}
}

// overwriteStoredFile replaces the single blob file under root with b.
func overwriteStoredFile(t *testing.T, root string, b []byte) {
	t.Helper()
	var target string
	err := filepath.WalkDir(root, func(path string, de os.DirEntry, err error) error {
		if err != nil {
			return err
		}
		if !de.IsDir() {
			target = path
		}
		return nil
	})
	if err != nil {
		t.Fatal(err)
	}
	if target == "" {
		t.Fatal("no stored blob file found to poison")
	}
	if err := os.WriteFile(target, b, 0o644); err != nil {
		t.Fatal(err)
	}
}
