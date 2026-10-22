package litestream

import (
	"bytes"
	"cmp"
	"context"
	"encoding/binary"
	"io"
	"log/slog"
	"slices"
	"sync"
	"sync/atomic"
	"time"

	"github.com/superfly/ltx"
	"golang.org/x/sync/errgroup"
)

// OpenPrefetchReplicaClient wraps a ReplicaClient and, while open prefetch is
// active, serves the level listings and byte ranges the VFS reads during a cold
// open from memory. PrefetchOpen lists every level concurrently, computes the
// restore plan, then fetches each file's header and page-index tail in parallel
// (the same requests FetchLTXHeader and FetchPageIndex make). EndOpenPrefetch
// clears the cache so polling and compaction see fresh listings.
type OpenPrefetchReplicaClient struct {
	Base ReplicaClient

	cache atomic.Pointer[openPrefetchCache]
}

var _ L0CreateOnlyReplicaClient = (*OpenPrefetchReplicaClient)(nil)

// NewOpenPrefetchReplicaClient returns a client that delegates to base.
func NewOpenPrefetchReplicaClient(base ReplicaClient) *OpenPrefetchReplicaClient {
	return &OpenPrefetchReplicaClient{Base: base}
}

type openPrefetchCache struct {
	levels map[int][]*ltx.FileInfo
	ranges map[openPrefetchRange][]byte
}

type openPrefetchRange struct {
	level            int
	minTXID, maxTXID ltx.TXID
	offset, size     int64
}

func (c *OpenPrefetchReplicaClient) Type() string { return c.Base.Type() }

func (c *OpenPrefetchReplicaClient) Init(ctx context.Context) error { return c.Base.Init(ctx) }

func (c *OpenPrefetchReplicaClient) SetLogger(logger *slog.Logger) { c.Base.SetLogger(logger) }

func (c *OpenPrefetchReplicaClient) SetL0CreateOnly(enabled bool) {
	_ = SetReplicaL0CreateOnly(c.Base, enabled)
}

func (c *OpenPrefetchReplicaClient) L0CreateOnly() bool {
	cc, ok := c.Base.(L0CreateOnlyReplicaClient)
	return ok && cc.L0CreateOnly()
}

func (c *OpenPrefetchReplicaClient) L0ConflictCount() int64 {
	return ReplicaL0ConflictCount(c.Base)
}

func (c *OpenPrefetchReplicaClient) LTXFiles(ctx context.Context, level int, seek ltx.TXID, useMetadata bool) (ltx.FileIterator, error) {
	if w := c.cache.Load(); w != nil && !useMetadata {
		if infos, ok := w.levels[level]; ok {
			var out []*ltx.FileInfo
			for _, info := range infos {
				if info.MinTXID >= seek {
					cp := *info
					out = append(out, &cp)
				}
			}
			return ltx.NewFileInfoSliceIterator(out), nil
		}
	}
	return c.Base.LTXFiles(ctx, level, seek, useMetadata)
}

func (c *OpenPrefetchReplicaClient) OpenLTXFile(ctx context.Context, level int, minTXID, maxTXID ltx.TXID, offset, size int64) (io.ReadCloser, error) {
	if w := c.cache.Load(); w != nil {
		if b, ok := w.ranges[openPrefetchRange{level, minTXID, maxTXID, offset, size}]; ok {
			return io.NopCloser(bytes.NewReader(b)), nil
		}
	}
	return c.Base.OpenLTXFile(ctx, level, minTXID, maxTXID, offset, size)
}

func (c *OpenPrefetchReplicaClient) WriteLTXFile(ctx context.Context, level int, minTXID, maxTXID ltx.TXID, r io.Reader) (*ltx.FileInfo, error) {
	return c.Base.WriteLTXFile(ctx, level, minTXID, maxTXID, r)
}

func (c *OpenPrefetchReplicaClient) DeleteLTXFiles(ctx context.Context, files []*ltx.FileInfo) error {
	return c.Base.DeleteLTXFiles(ctx, files)
}

func (c *OpenPrefetchReplicaClient) DeleteAll(ctx context.Context) error {
	return c.Base.DeleteAll(ctx)
}

// PrefetchOpen fills the open cache. Failures are logged when logger is non-nil
// but do not fail the open: the VFS falls back to the replica.
func (c *OpenPrefetchReplicaClient) PrefetchOpen(ctx context.Context, logger *slog.Logger) {
	if err := c.prefetch(ctx); err != nil && logger != nil {
		logger.Warn("open prefetch failed", "error", err)
	}
}

// EndOpenPrefetch clears the open cache.
func (c *OpenPrefetchReplicaClient) EndOpenPrefetch() { c.cache.Store(nil) }

func (c *OpenPrefetchReplicaClient) prefetch(ctx context.Context) error {
	w := &openPrefetchCache{levels: map[int][]*ltx.FileInfo{}, ranges: map[openPrefetchRange][]byte{}}
	var mu sync.Mutex

	g, gctx := errgroup.WithContext(ctx)
	for level := 0; level <= SnapshotLevel; level++ {
		g.Go(func() error {
			itr, err := c.Base.LTXFiles(gctx, level, 0, false)
			if err != nil {
				return err
			}
			defer itr.Close()
			var infos []*ltx.FileInfo
			for itr.Next() {
				info := *itr.Item()
				infos = append(infos, &info)
			}
			if err := itr.Close(); err != nil {
				return err
			}
			slices.SortFunc(infos, func(a, b *ltx.FileInfo) int { return cmp.Compare(a.MinTXID, b.MinTXID) })
			mu.Lock()
			w.levels[level] = infos
			mu.Unlock()
			return nil
		})
	}
	if err := g.Wait(); err != nil {
		return err
	}
	c.cache.Store(w)

	plan, err := CalcRestorePlan(ctx, c, 0, time.Time{}, slog.New(slog.DiscardHandler))
	if err != nil {
		return nil
	}
	if len(plan) == 0 {
		return nil
	}

	fetch := func(ctx context.Context, info *ltx.FileInfo, offset, size int64) []byte {
		rc, err := c.Base.OpenLTXFile(ctx, info.Level, info.MinTXID, info.MaxTXID, offset, size)
		if err != nil {
			return nil
		}
		defer rc.Close()
		b, err := io.ReadAll(rc)
		if err != nil {
			return nil
		}
		mu.Lock()
		w.ranges[openPrefetchRange{info.Level, info.MinTXID, info.MaxTXID, offset, size}] = b
		mu.Unlock()
		return b
	}
	var fg errgroup.Group
	fg.SetLimit(32)
	for _, info := range plan {
		fg.Go(func() error {
			fetch(ctx, info, 0, ltx.HeaderSize)
			return nil
		})
		fg.Go(func() error {
			tail := fetch(ctx, info, max(0, info.Size-DefaultEstimatedPageIndexSize), 0)
			if len(tail) < ltx.TrailerSize+8 {
				return nil
			}
			n := binary.BigEndian.Uint64(tail[len(tail)-ltx.TrailerSize-8:])
			if len(tail)-int(n)-ltx.TrailerSize-8 <= 0 {
				fetch(ctx, info, info.Size-ltx.TrailerSize-8-int64(n), 0)
			}
			return nil
		})
	}
	fg.Wait()
	return nil
}
