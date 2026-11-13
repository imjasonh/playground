// Package cache is a node-local, verified read-through cache in front of the
// CAS origin. A blob fetched once is served from local disk to every later
// reader, including one for another tenant: a content-addressed blob is
// identified by its bytes. Every served blob is checked against its digest,
// and a local entry that fails is dropped and fetched from the origin again.
package cache

import (
	"context"
	"log/slog"
	"sync/atomic"
	"time"

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

// fetchTimeout bounds one origin fetch. A fetch is shared by every caller
// waiting on the same blob, so it runs detached from the first caller's
// cancellation and needs its own deadline.
const fetchTimeout = 5 * time.Minute

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
// Concurrent Gets for the same instance and digest collapse into a single
// origin fetch, so a cold blob requested by many actors at once crosses the
// network once. The instance is part of that key so a caller never receives
// bytes from a fetch the origin authorized for a different instance; once the
// blob is local, every instance shares it.
func (c *Cache) Get(ctx context.Context, instanceName string, d *repb.Digest) ([]byte, error) {
	if b, ok := c.localHit(d); ok {
		c.hits.Add(1)
		return b, nil
	}
	v, err, _ := c.group.Do(instanceName+"\x00"+digest.Key(d), func() (any, error) {
		if b, ok := c.localHit(d); ok {
			c.hits.Add(1)
			return b, nil
		}
		fctx, cancel := context.WithTimeout(context.WithoutCancel(ctx), fetchTimeout)
		defer cancel()
		b, err := c.origin.Fetch(fctx, instanceName, d)
		if err != nil {
			return nil, err
		}
		if err := digest.Verify(d, b); err != nil {
			return nil, err
		}
		c.fetches.Add(1)
		if err := c.local.Put(d, b); err != nil {
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
