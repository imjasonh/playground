package store

import (
	"context"
	"io"
	"sync"
	"sync/atomic"
	"time"

	"github.com/benbjohnson/litestream"
	"github.com/superfly/ltx"

	"github.com/imjasonh/playground/cloudrun-sqlite/internal/observe"
)

// monitoredClient wraps a Litestream replica client with open prefetch and
// replica operation timing for /stats.
type monitoredClient struct {
	litestream.ReplicaClient
	warm  atomic.Pointer[warmCache]
	gets  latencies
	lists latencies
	puts  latencies
}

var _ litestream.L0CreateOnlyReplicaClient = (*monitoredClient)(nil)

func (c *monitoredClient) SetL0CreateOnly(enabled bool) {
	_ = litestream.SetReplicaL0CreateOnly(c.ReplicaClient, enabled)
}

func (c *monitoredClient) L0CreateOnly() bool {
	cc, ok := c.ReplicaClient.(litestream.L0CreateOnlyReplicaClient)
	return ok && cc.L0CreateOnly()
}

func (c *monitoredClient) L0ConflictCount() int64 {
	return litestream.ReplicaL0ConflictCount(c.ReplicaClient)
}

func (c *monitoredClient) WriteLTXFile(ctx context.Context, level int, minTXID, maxTXID ltx.TXID, r io.Reader) (*ltx.FileInfo, error) {
	ctx, end := observe.Span(ctx, "replica.put")
	start := time.Now()
	info, err := c.ReplicaClient.WriteLTXFile(ctx, level, minTXID, maxTXID, r)
	d := time.Since(start)
	c.puts.add(d)
	observe.Measure(ctx, observe.ReplicaOperation, d, "op", "put")
	end(err)
	return info, err
}

func (c *monitoredClient) remoteOpen(ctx context.Context, level int, minTXID, maxTXID ltx.TXID, offset, size int64) (io.ReadCloser, error) {
	ctx, end := observe.Span(ctx, "replica.get")
	start := time.Now()
	rc, err := c.ReplicaClient.OpenLTXFile(ctx, level, minTXID, maxTXID, offset, size)
	d := time.Since(start)
	c.gets.add(d)
	observe.Measure(ctx, observe.ReplicaOperation, d, "op", "get")
	end(err)
	return rc, err
}

func (c *monitoredClient) remoteList(ctx context.Context, level int, seek ltx.TXID, useMetadata bool) (ltx.FileIterator, error) {
	ctx, end := observe.Span(ctx, "replica.list")
	start := time.Now()
	itr, err := c.ReplicaClient.LTXFiles(ctx, level, seek, useMetadata)
	if err != nil {
		d := time.Since(start)
		c.lists.add(d)
		observe.Measure(ctx, observe.ReplicaOperation, d, "op", "list")
		end(err)
		return nil, err
	}
	return &recordingIter{FileIterator: itr, start: start, done: func(d time.Duration, err error) {
		c.lists.add(d)
		observe.Measure(ctx, observe.ReplicaOperation, d, "op", "list")
		end(err)
	}}, nil
}

// recordingIter times a listing through Close, which is when the pages of
// results have been read.
type recordingIter struct {
	ltx.FileIterator
	start time.Time
	once  sync.Once
	done  func(time.Duration, error)
}

func (r *recordingIter) Close() error {
	err := r.FileIterator.Close()
	r.once.Do(func() {
		spanErr := err
		if spanErr == nil {
			spanErr = r.FileIterator.Err()
		}
		r.done(time.Since(r.start), spanErr)
	})
	return err
}
