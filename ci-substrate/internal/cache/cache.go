// Package cache is a node-local, content-addressed, verified read-through
// cache in front of an authoritative CAS origin.
//
// It is the "optimized caching" layer: a blob fetched once from the origin is
// served to every later reader from local disk, including a reader on behalf
// of a different tenant, because a content-addressed blob is identified by its
// bytes and is safe to share. Each served blob is verified against its digest
// in flight, so a locally corrupted or tampered entry can never be handed out:
// on a hash mismatch the cache drops the poisoned entry and circuit-breaks to
// the origin, which is the cryptographic root of trust.
package cache

import (
	"context"
	"log/slog"
	"sync/atomic"

	repb "github.com/bazelbuild/remote-apis/build/bazel/remote/execution/v2"
	"golang.org/x/sync/singleflight"

	"github.com/imjasonh/playground/ci-substrate/internal/blob"
	"github.com/imjasonh/playground/ci-substrate/internal/digest"
)

// Origin fetches authoritative blob bytes. The implementation that the
// cascache binary uses is a gRPC client to the central CAS; tests use an
// in-memory fake.
type Origin interface {
	Fetch(ctx context.Context, instanceName string, d *repb.Digest) ([]byte, error)
}

// Stats is a snapshot of cache counters.
type Stats struct {
	Hits           int64
	OriginFetches  int64
	PoisonRejected int64
}

// Cache serves blobs from a local store, falling back to an origin.
type Cache struct {
	local  *blob.Store
	origin Origin
	group  singleflight.Group

	hits    atomic.Int64
	fetches atomic.Int64
	poison  atomic.Int64
}

// New returns a cache backed by local and origin.
func New(local *blob.Store, origin Origin) *Cache {
	return &Cache{local: local, origin: origin}
}

// Get returns the bytes for d, serving from the local store when possible and
// otherwise fetching from the origin. instanceName is forwarded to the origin
// on a miss so the origin can enforce tenant authorization; a local hit is
// keyed by content alone, which is what lets one cached copy serve every
// tenant that holds the same bytes.
//
// Concurrent Gets for the same digest collapse into a single origin fetch, so
// a cold blob requested by many actors at once crosses the network once.
func (c *Cache) Get(ctx context.Context, instanceName string, d *repb.Digest) ([]byte, error) {
	if b, ok := c.localHit(d); ok {
		c.hits.Add(1)
		return b, nil
	}
	v, err, _ := c.group.Do(digest.Key(d), func() (any, error) {
		// Re-check under the singleflight: a sibling call may have filled it.
		if b, ok := c.localHit(d); ok {
			c.hits.Add(1)
			return b, nil
		}
		b, err := c.origin.Fetch(ctx, instanceName, d)
		if err != nil {
			return nil, err
		}
		if err := digest.Verify(d, b); err != nil {
			// The origin itself returned bad bytes; do not cache them.
			return nil, err
		}
		c.fetches.Add(1)
		if err := c.local.Put(d, b); err != nil {
			// Still serve the verified bytes; the next reader will refetch.
			slog.Warn("caching blob locally", "digest", digest.Key(d), "err", err)
		}
		return b, nil
	})
	if err != nil {
		return nil, err
	}
	return v.([]byte), nil
}

// localHit returns verified local bytes. A present-but-corrupt entry is
// dropped and reported as a miss, so the caller falls back to the origin.
func (c *Cache) localHit(d *repb.Digest) ([]byte, bool) {
	b, err := c.local.Get(d)
	if err != nil {
		return nil, false
	}
	if err := digest.Verify(d, b); err != nil {
		c.poison.Add(1)
		_ = c.local.Delete(d)
		return nil, false
	}
	return b, true
}

// Stats returns a snapshot of the counters.
func (c *Cache) Stats() Stats {
	return Stats{
		Hits:           c.hits.Load(),
		OriginFetches:  c.fetches.Load(),
		PoisonRejected: c.poison.Load(),
	}
}
