package store

import (
	"bytes"
	"cmp"
	"context"
	"encoding/binary"
	"io"
	"log/slog"
	"slices"
	"sync"
	"time"

	"github.com/benbjohnson/litestream"
	"github.com/superfly/ltx"
	"golang.org/x/sync/errgroup"
)

// warmCache holds the listings and byte ranges the VFS reads while it opens
// the database. The VFS reads them one request at a time: ten level
// listings, then a header and page index per file in the restore plan.
// warmUp fetches the same requests concurrently first, which cuts a cold
// open from about 4+3n round trips to about three.
type warmCache struct {
	levels map[int][]*ltx.FileInfo
	ranges map[rangeKey][]byte
}

type rangeKey struct {
	level            int
	minTXID, maxTXID ltx.TXID
	offset, size     int64
}

func (c *fencedClient) LTXFiles(ctx context.Context, level int, seek ltx.TXID, useMetadata bool) (ltx.FileIterator, error) {
	if w := c.warm.Load(); w != nil && !useMetadata {
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
	return c.remoteList(ctx, level, seek, useMetadata)
}

func (c *fencedClient) OpenLTXFile(ctx context.Context, level int, minTXID, maxTXID ltx.TXID, offset, size int64) (io.ReadCloser, error) {
	if w := c.warm.Load(); w != nil {
		if b, ok := w.ranges[rangeKey{level, minTXID, maxTXID, offset, size}]; ok {
			return io.NopCloser(bytes.NewReader(b)), nil
		}
	}
	return c.remoteOpen(ctx, level, minTXID, maxTXID, offset, size)
}

// warmUp fills the cache. Requests it doesn't anticipate, or that fail
// here, go to the replica as usual. Call coolDown once the database is
// open so polling sees fresh listings.
func (c *fencedClient) warmUp(ctx context.Context) error {
	w := &warmCache{levels: map[int][]*ltx.FileInfo{}, ranges: map[rangeKey][]byte{}}
	var mu sync.Mutex

	g, gctx := errgroup.WithContext(ctx)
	for level := 0; level <= litestream.SnapshotLevel; level++ {
		g.Go(func() error {
			itr, err := c.remoteList(gctx, level, 0, false)
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
	c.warm.Store(w)

	plan, err := litestream.CalcRestorePlan(ctx, c, 0, time.Time{}, slog.New(slog.DiscardHandler))
	if err != nil {
		return nil // empty replica: nothing else to fetch
	}

	fetch := func(ctx context.Context, info *ltx.FileInfo, offset, size int64) []byte {
		rc, err := c.remoteOpen(ctx, info.Level, info.MinTXID, info.MaxTXID, offset, size)
		if err != nil {
			return nil
		}
		defer rc.Close()
		b, err := io.ReadAll(rc)
		if err != nil {
			return nil
		}
		mu.Lock()
		w.ranges[rangeKey{info.Level, info.MinTXID, info.MaxTXID, offset, size}] = b
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
		// The same ranges litestream.FetchPageIndex asks for: the end of the
		// file, then the whole index if it didn't fit.
		fg.Go(func() error {
			tail := fetch(ctx, info, max(0, info.Size-litestream.DefaultEstimatedPageIndexSize), 0)
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

func (c *fencedClient) coolDown() { c.warm.Store(nil) }
