package remote

import (
	"context"

	"go.opentelemetry.io/otel/attribute"
	"go.opentelemetry.io/otel/metric"
	"go.opentelemetry.io/otel/trace"

	"github.com/imjasonh/playground/ci-substrate/internal/invocation"
	"github.com/imjasonh/playground/ci-substrate/internal/telemetry"
)

var blobSizeBuckets = metric.WithExplicitBucketBoundaries(0, 256, 1<<10, 4<<10, 16<<10, 64<<10, 256<<10, 1<<20, 4<<20, 16<<20, 64<<20, 256<<20, 1<<30)

type originMetrics struct {
	bytes       metric.Int64Counter
	blobs       metric.Int64Counter
	blobSize    metric.Int64Histogram
	findMissing metric.Int64Counter
	actionCache metric.Int64Counter
}

func newOriginMetrics() originMetrics {
	m := telemetry.Meter()
	return originMetrics{
		bytes: telemetry.Handle(m.Int64Counter("cas.blob.bytes", metric.WithUnit("By"),
			metric.WithDescription("Blob bytes cas served (read) or stored (write), by api and by the peer that asked."))),
		blobs: telemetry.Handle(m.Int64Counter("cas.blob.count",
			metric.WithDescription("Blobs cas served (read) or stored (write), by api and peer."))),
		blobSize: telemetry.Handle(m.Int64Histogram("cas.blob.size", metric.WithUnit("By"),
			metric.WithDescription("Size of each blob cas served or stored."), blobSizeBuckets)),
		findMissing: telemetry.Handle(m.Int64Counter("cas.find_missing.digests",
			metric.WithDescription("Digests checked by FindMissingBlobs, by result: present or missing."))),
		actionCache: telemetry.Handle(m.Int64Counter("cas.action_cache.requests",
			metric.WithDescription("Action cache calls, by op (get or update) and result (hit, miss, or ok)."))),
	}
}

// moved records blobs that cas read or wrote for the call ctx belongs to,
// on the metrics, the call's span, and its invocation.
func (o *Origin) moved(ctx context.Context, instance, direction, api string, sizes ...int64) {
	if len(sizes) == 0 {
		return
	}
	md := telemetry.RequestMetadata(ctx)
	peer := telemetry.Peer(md)
	attrs := metric.WithAttributes(
		telemetry.AttrInstance.String(instance),
		telemetry.AttrDirection.String(direction),
		telemetry.AttrAPI.String(api),
		telemetry.AttrPeer.String(peer),
	)
	var total int64
	for _, n := range sizes {
		total += n
		o.metrics.blobSize.Record(ctx, n, metric.WithAttributes(telemetry.AttrDirection.String(direction)))
	}
	o.metrics.bytes.Add(ctx, total, attrs)
	o.metrics.blobs.Add(ctx, int64(len(sizes)), attrs)
	trace.SpanFromContext(ctx).SetAttributes(
		attribute.Int("ci_substrate.blobs", len(sizes)),
		attribute.Int64("ci_substrate.bytes", total),
	)

	var c invocation.Counts
	switch {
	case peer == "bazel" && direction == "write":
		c.BlobsUploaded, c.BytesUploaded = int64(len(sizes)), total
	case peer == "bazel":
		c.BlobsDownloaded, c.BytesDownloaded = int64(len(sizes)), total
	case peer == "runner" && direction == "write":
		c.RunnerBytesUploaded = total
	case peer == "cascache":
		c.CacheFillBytes = total
	default:
		return
	}
	o.invocations.AddFor(md, instance, c)
}
