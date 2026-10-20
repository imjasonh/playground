//go:build vfs

package litestream

import (
	"context"
	"errors"
	"fmt"
	"io"
	"sync/atomic"
	"testing"
	"time"

	"github.com/psanford/sqlite3vfs"
	"github.com/superfly/ltx"
)

// fencedMemClient fails an L0 upload whose file already exists, as a replica
// client with conditional creates does, and counts L0 listings.
type fencedMemClient struct {
	*memClient
	l0Lists atomic.Int32
}

func (c *fencedMemClient) LTXFiles(ctx context.Context, level int, seek ltx.TXID, useMetadata bool) (ltx.FileIterator, error) {
	if level == 0 {
		c.l0Lists.Add(1)
	}
	return c.memClient.LTXFiles(ctx, level, seek, useMetadata)
}

func (c *fencedMemClient) WriteLTXFile(ctx context.Context, level int, minTXID, maxTXID ltx.TXID, r io.Reader) (*ltx.FileInfo, error) {
	if level == 0 {
		c.mu.Lock()
		_, exists := c.data[memKey{level, minTXID, maxTXID}]
		c.mu.Unlock()
		if exists {
			return nil, fmt.Errorf("%w: L0 %s exists", ErrConflict, ltx.FormatFilename(minTXID, maxTXID))
		}
	}
	return c.memClient.WriteLTXFile(ctx, level, minTXID, maxTXID, r)
}

// commitPage writes one version of a page in a write transaction and syncs it.
func commitPage(f *VFSFile, pgno uint32, version uint64) error {
	for _, l := range []sqlite3vfs.LockType{sqlite3vfs.LockShared, sqlite3vfs.LockReserved, sqlite3vfs.LockExclusive} {
		if err := f.Lock(l); err != nil {
			return err
		}
	}
	if _, err := f.WriteAt(pageData(pgno, version), int64(pgno-1)*ilPageSize); err != nil {
		return err
	}
	if err := f.Unlock(sqlite3vfs.LockShared); err != nil {
		return err
	}
	if err := f.Unlock(sqlite3vfs.LockNone); err != nil {
		return err
	}
	return f.Sync(sqlite3vfs.SyncNormal)
}

func TestVFSFile_ConflictCheckInterval(t *testing.T) {
	newWriter := func(t *testing.T, client ReplicaClient, interval time.Duration) *VFSFile {
		t.Helper()
		f, err := openTestFile(t.TempDir(), client, true)
		if err != nil {
			t.Fatal(err)
		}
		t.Cleanup(func() { _ = f.Close() })
		f.conflictCheckInterval = interval
		return f
	}
	// lists returns how many times fn listed L0.
	lists := func(t *testing.T, client *fencedMemClient, fn func() error) (int32, error) {
		t.Helper()
		before := client.l0Lists.Load()
		err := fn()
		return client.l0Lists.Load() - before, err
	}

	t.Run("zero lists before every upload", func(t *testing.T) {
		client := &fencedMemClient{memClient: newMemClient()}
		f := newWriter(t, client, 0)
		for v := uint64(1); v <= 3; v++ {
			n, err := lists(t, client, func() error { return commitPage(f, 1, v) })
			if err != nil {
				t.Fatal(err)
			}
			if n != 1 {
				t.Fatalf("sync %d listed L0 %d times, want 1", v, n)
			}
		}
	})

	t.Run("skips the listing while the position is fresh", func(t *testing.T) {
		client := &fencedMemClient{memClient: newMemClient()}
		f := newWriter(t, client, time.Hour)
		// The first sync has no earlier listing or upload to rely on.
		for i, want := range []int32{1, 0, 0} {
			n, err := lists(t, client, func() error { return commitPage(f, 1, uint64(i+1)) })
			if err != nil {
				t.Fatal(err)
			}
			if n != want {
				t.Fatalf("sync %d listed L0 %d times, want %d", i+1, n, want)
			}
		}

		f.mu.Lock()
		f.positionConfirmedAt = time.Now().Add(-2 * time.Hour)
		f.mu.Unlock()
		n, err := lists(t, client, func() error { return commitPage(f, 1, 4) })
		if err != nil {
			t.Fatal(err)
		}
		if n != 1 {
			t.Fatalf("sync after the interval listed L0 %d times, want 1", n)
		}
	})

	t.Run("a conditional upload stops a writer that skipped the listing", func(t *testing.T) {
		client := &fencedMemClient{memClient: newMemClient()}
		f := newWriter(t, client, time.Hour)
		if err := commitPage(f, 1, 1); err != nil {
			t.Fatal(err)
		}
		other := newWriter(t, client, 0)
		if err := commitPage(other, 1, 2); err != nil {
			t.Fatal(err)
		}

		n, err := lists(t, client, func() error { return commitPage(f, 1, 3) })
		if !errors.Is(err, ErrConflict) {
			t.Fatalf("sync = %v, want ErrConflict", err)
		}
		if n != 0 {
			t.Fatalf("listed L0 %d times, want 0", n)
		}
	})

	t.Run("lists when a poll has seen another writer", func(t *testing.T) {
		client := &fencedMemClient{memClient: newMemClient()}
		f := newWriter(t, client, time.Hour)
		if err := commitPage(f, 1, 1); err != nil {
			t.Fatal(err)
		}
		other := newWriter(t, client, 0)
		if err := commitPage(other, 1, 2); err != nil {
			t.Fatal(err)
		}
		if err := f.pollReplicaClient(context.Background()); err != nil {
			t.Fatal(err)
		}

		n, err := lists(t, client, func() error { return commitPage(f, 1, 3) })
		if !errors.Is(err, ErrConflict) {
			t.Fatalf("sync = %v, want ErrConflict", err)
		}
		if n != 1 {
			t.Fatalf("listed L0 %d times, want 1", n)
		}
	})
}
