package litestream_test

import (
	"context"
	"io"
	"log/slog"
	"reflect"
	"sync/atomic"
	"testing"
	"time"

	"github.com/benbjohnson/litestream"
	"github.com/benbjohnson/litestream/file"
	"github.com/superfly/ltx"
)

type prefetchCountingClient struct {
	litestream.ReplicaClient
	lists, opens atomic.Int64
}

func (c *prefetchCountingClient) LTXFiles(ctx context.Context, level int, seek ltx.TXID, useMetadata bool) (ltx.FileIterator, error) {
	c.lists.Add(1)
	return c.ReplicaClient.LTXFiles(ctx, level, seek, useMetadata)
}

func (c *prefetchCountingClient) OpenLTXFile(ctx context.Context, level int, minTXID, maxTXID ltx.TXID, offset, size int64) (io.ReadCloser, error) {
	c.opens.Add(1)
	return c.ReplicaClient.OpenLTXFile(ctx, level, minTXID, maxTXID, offset, size)
}

func TestOpenPrefetchReplicaClient_CachesListings(t *testing.T) {
	replica := t.TempDir()
	inner := file.NewReplicaClient(replica)
	createTestLTXFile(t, inner, 0, 1, 1)
	counting := &prefetchCountingClient{ReplicaClient: inner}
	pf := litestream.NewOpenPrefetchReplicaClient(counting)

	pf.PrefetchOpen(t.Context(), nil)
	afterPrefetch := counting.lists.Load()
	if afterPrefetch < litestream.SnapshotLevel+1 {
		t.Fatalf("prefetch listed %d times, want at least %d level listings", afterPrefetch, litestream.SnapshotLevel+1)
	}

	if _, err := pf.LTXFiles(t.Context(), 0, 0, false); err != nil {
		t.Fatal(err)
	}
	if counting.lists.Load() != afterPrefetch {
		t.Fatalf("listing through cache issued another list (%d -> %d)", afterPrefetch, counting.lists.Load())
	}

	pf.EndOpenPrefetch()
	if _, err := pf.LTXFiles(t.Context(), 0, 0, false); err != nil {
		t.Fatal(err)
	}
	if counting.lists.Load() <= afterPrefetch {
		t.Fatal("listing after EndOpenPrefetch did not reach the replica")
	}
}

// A read-only open of a replica with no files waits by listing again, so a
// prefetch that finds no database must not cache the empty listing.
func TestOpenPrefetchReplicaClient_EmptyReplicaListsFresh(t *testing.T) {
	replica := t.TempDir()
	direct := file.NewReplicaClient(replica)
	pf := litestream.NewOpenPrefetchReplicaClient(direct)

	pf.PrefetchOpen(t.Context(), nil)
	createTestLTXFile(t, direct, 0, 1, 1)

	plan, err := litestream.CalcRestorePlan(t.Context(), pf, 0, time.Time{}, slog.New(slog.DiscardHandler))
	if err != nil {
		t.Fatalf("plan after the first file landed: %v", err)
	}
	if len(plan) != 1 || plan[0].MaxTXID != 1 {
		t.Fatalf("plan = %+v, want the one file at TXID 1", plan)
	}
}

func TestOpenPrefetchReplicaClient_ServesIdenticalData(t *testing.T) {
	replica := t.TempDir()
	direct := file.NewReplicaClient(replica)
	createTestLTXFile(t, direct, litestream.SnapshotLevel, 1, 10)
	for txid := ltx.TXID(11); txid <= 30; txid++ {
		createTestLTXFile(t, direct, 0, txid, txid)
	}

	logger := slog.New(slog.DiscardHandler)
	want, err := litestream.CalcRestorePlan(t.Context(), direct, 0, time.Time{}, logger)
	if err != nil {
		t.Fatal(err)
	}

	counting := &prefetchCountingClient{ReplicaClient: file.NewReplicaClient(replica)}
	fc := litestream.NewOpenPrefetchReplicaClient(counting)
	fc.PrefetchOpen(t.Context(), nil)
	lists, opens := counting.lists.Load(), counting.opens.Load()

	got, err := litestream.CalcRestorePlan(t.Context(), fc, 0, time.Time{}, logger)
	if err != nil {
		t.Fatal(err)
	}
	if len(got) != len(want) {
		t.Fatalf("plan through cache has %d files, want %d", len(got), len(want))
	}
	for i := range want {
		if got[i].Level != want[i].Level || got[i].MinTXID != want[i].MinTXID || got[i].MaxTXID != want[i].MaxTXID || got[i].Size != want[i].Size {
			t.Fatalf("plan[%d] = %+v, want %+v", i, got[i], want[i])
		}
		gotIdx, err := litestream.FetchPageIndex(t.Context(), fc, got[i])
		if err != nil {
			t.Fatal(err)
		}
		wantIdx, err := litestream.FetchPageIndex(t.Context(), direct, want[i])
		if err != nil {
			t.Fatal(err)
		}
		if !reflect.DeepEqual(gotIdx, wantIdx) {
			t.Fatalf("page index of %s differs through cache", ltx.FormatFilename(want[i].MinTXID, want[i].MaxTXID))
		}
		gotHdr, err := litestream.FetchLTXHeader(t.Context(), fc, got[i])
		if err != nil {
			t.Fatal(err)
		}
		wantHdr, err := litestream.FetchLTXHeader(t.Context(), direct, want[i])
		if err != nil {
			t.Fatal(err)
		}
		if gotHdr != wantHdr {
			t.Fatalf("header differs through cache: %+v vs %+v", gotHdr, wantHdr)
		}
	}
	if counting.lists.Load() != lists || counting.opens.Load() != opens {
		t.Errorf("reading the plan through the cache made %d listings and %d reads; want none",
			counting.lists.Load()-lists, counting.opens.Load()-opens)
	}

	fc.EndOpenPrefetch()
	if _, err := fc.LTXFiles(t.Context(), 0, 0, false); err != nil {
		t.Fatal(err)
	}
	if counting.lists.Load() == lists {
		t.Error("listing after EndOpenPrefetch was served from the cache")
	}
}
