package store

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

type countingClient struct {
	litestream.ReplicaClient
	lists, opens atomic.Int64
}

func (c *countingClient) LTXFiles(ctx context.Context, level int, seek ltx.TXID, useMetadata bool) (ltx.FileIterator, error) {
	c.lists.Add(1)
	return c.ReplicaClient.LTXFiles(ctx, level, seek, useMetadata)
}

func (c *countingClient) OpenLTXFile(ctx context.Context, level int, minTXID, maxTXID ltx.TXID, offset, size int64) (io.ReadCloser, error) {
	c.opens.Add(1)
	return c.ReplicaClient.OpenLTXFile(ctx, level, minTXID, maxTXID, offset, size)
}

// The warm cache must hand the VFS exactly what the replica would.
func TestWarmUpServesIdenticalData(t *testing.T) {
	replica := t.TempDir()
	s := mustOpen(t, testConfig(t, replica))
	mustWrite(t, s, "CREATE TABLE t (id INTEGER PRIMARY KEY, v BLOB)")
	for range 20 {
		mustWrite(t, s, "INSERT INTO t (v) VALUES (randomblob(20000))")
	}
	if err := s.Close(); err != nil {
		t.Fatal(err)
	}

	logger := slog.New(slog.DiscardHandler)
	direct := file.NewReplicaClient(replica)
	want, err := litestream.CalcRestorePlan(t.Context(), direct, 0, time.Time{}, logger)
	if err != nil {
		t.Fatal(err)
	}

	counting := &countingClient{ReplicaClient: file.NewReplicaClient(replica)}
	fc := &fencedClient{ReplicaClient: counting}
	if err := fc.warmUp(t.Context()); err != nil {
		t.Fatal(err)
	}
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

	fc.coolDown()
	if _, err := fc.LTXFiles(t.Context(), 0, 0, false); err != nil {
		t.Fatal(err)
	}
	if counting.lists.Load() == lists {
		t.Error("listing after coolDown was served from the cache")
	}
}
