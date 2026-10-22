package litestream_test

import (
	"context"
	"io"
	"sync/atomic"
	"testing"

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
