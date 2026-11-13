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
	"go.opentelemetry.io/otel/attribute"
	"go.opentelemetry.io/otel/codes"
	"go.opentelemetry.io/otel/metric"
	"go.opentelemetry.io/otel/trace"
	"golang.org/x/sync/singleflight"

	"github.com/imjasonh/playground/ci-substrate/internal/blob"
	"github.com/imjasonh/playground/ci-substrate/internal/digest"
	"github.com/imjasonh/playground/ci-substrate/internal/telemetry"
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

	requests      metric.Int64Counter
	bytes         metric.Int64Counter
	fetchDuration metric.Float64Histogram
	poisoned      metric.Int64Counter
}

// New returns a cache backed by local and origin.
func New(local *blob.Store, origin Origin) *Cache {
	m := telemetry.Meter()
	return &Cache{
		local:  local,
		origin: origin,
		requests: telemetry.Handle(m.Int64Counter("cascache.requests",
			metric.WithDescription("Blob reads, by result: hit (local disk), miss (fetched from cas), merged (waited on another reader's fetch), or error."))),
		bytes: telemetry.Handle(m.Int64Counter("cascache.bytes", metric.WithUnit("By"),
			metric.WithDescription("Blob bytes served, by source: local or origin."))),
		fetchDuration: telemetry.Handle(m.Float64Histogram("cascache.origin.fetch.duration", metric.WithUnit("s"),
			metric.WithDescription("Time to fetch and verify one blob from cas on a miss."),
			metric.WithExplicitBucketBoundaries(.001, .0025, .005, .01, .025, .05, .1, .25, .5, 1, 2.5, 5, 10, 30))),
		poisoned: telemetry.Handle(m.Int64Counter("cascache.poisoned",
			metric.WithDescription("Local entries that failed verification and were dropped."))),
	}
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
//
// Get reports whether the bytes came from local disk.
func (c *Cache) Get(ctx context.Context, instanceName string, d *repb.Digest) ([]byte, bool, error) {
	if b, ok := c.localHit(ctx, d); ok {
		c.served(ctx, instanceName, "hit", len(b))
		return b, true, nil
	}
	var local bool
	v, err, shared := c.group.Do(instanceName+"\x00"+digest.Key(d), func() (any, error) {
		if b, ok := c.localHit(ctx, d); ok {
			local = true
			return b, nil
		}
		return c.fetch(ctx, instanceName, d)
	})
	switch {
	case err != nil:
		c.served(ctx, instanceName, "error", 0)
		return nil, false, err
	case local:
		c.served(ctx, instanceName, "hit", len(v.([]byte)))
	case shared:
		c.served(ctx, instanceName, "merged", len(v.([]byte)))
	default:
		c.served(ctx, instanceName, "miss", len(v.([]byte)))
	}
	return v.([]byte), local, nil
}

// fetch reads d from the origin, verifies it, and stores it locally.
func (c *Cache) fetch(ctx context.Context, instanceName string, d *repb.Digest) ([]byte, error) {
	fctx, cancel := context.WithTimeout(context.WithoutCancel(ctx), fetchTimeout)
	defer cancel()
	fctx, span := telemetry.Tracer().Start(fctx, "cascache.origin_fetch", trace.WithAttributes(
		attribute.String("ci_substrate.digest", digest.Key(d)),
		attribute.Int64("ci_substrate.bytes", d.GetSizeBytes()),
	))
	defer span.End()
	start := time.Now()
	b, err := c.origin.Fetch(fctx, instanceName, d)
	if err == nil {
		err = digest.Verify(d, b)
	}
	if err != nil {
		span.RecordError(err)
		span.SetStatus(codes.Error, err.Error())
		return nil, err
	}
	c.fetchDuration.Record(ctx, time.Since(start).Seconds(), metric.WithAttributes(telemetry.AttrInstance.String(instanceName)))
	c.fetches.Add(1)
	if err := c.local.Put(d, b); err != nil {
		slog.WarnContext(fctx, "caching blob locally", "digest", digest.Key(d), "err", err)
	}
	return b, nil
}

func (c *Cache) served(ctx context.Context, instanceName, result string, n int) {
	if result == "hit" {
		c.hits.Add(1)
	}
	c.requests.Add(ctx, 1, metric.WithAttributes(telemetry.AttrInstance.String(instanceName), telemetry.AttrResult.String(result)))
	if n == 0 {
		return
	}
	source := "origin"
	if result == "hit" {
		source = "local"
	}
	c.bytes.Add(ctx, int64(n), metric.WithAttributes(telemetry.AttrInstance.String(instanceName), attribute.String("source", source)))
}

// localHit returns verified local bytes. A present-but-corrupt entry is
// dropped and reported as a miss, so the caller falls back to the origin.
func (c *Cache) localHit(ctx context.Context, d *repb.Digest) ([]byte, bool) {
	b, err := c.local.Get(d)
	if err != nil {
		return nil, false
	}
	if err := digest.Verify(d, b); err != nil {
		c.poison.Add(1)
		c.poisoned.Add(ctx, 1)
		slog.WarnContext(ctx, "dropping corrupt cache entry", "digest", digest.Key(d), "err", err)
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
