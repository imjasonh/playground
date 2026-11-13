// Package invocation keeps a running account of each Bazel invocation cas
// serves: cache hits and misses, actions run, bytes moved, and time spent
// queued and running. Bazel never says when a build ends, so an invocation
// is over once it has been idle for a while. Then the Tracker records the
// invocation's root span, which every call of the build is already
// parented on (see telemetry.InvocationSpanContext), logs a summary, and
// records the per-build metrics.
package invocation

import (
	"context"
	"log/slog"
	"sync"
	"time"

	repb "github.com/bazelbuild/remote-apis/build/bazel/remote/execution/v2"
	"go.opentelemetry.io/otel/attribute"
	"go.opentelemetry.io/otel/metric"
	"go.opentelemetry.io/otel/trace"

	"github.com/imjasonh/playground/ci-substrate/internal/telemetry"
)

// Counts is what one call adds to its invocation's account.
type Counts struct {
	// ActionCacheHits and ActionCacheMisses count GetActionResult lookups.
	ActionCacheHits, ActionCacheMisses int64
	// ActionCacheWrites counts UpdateActionResult calls.
	ActionCacheWrites int64

	// ExecuteRequests counts Execute calls. Each ends cached (the action
	// cache had a result), merged (it joined an identical queued or running
	// action), or queued; queued actions end in ActionsRun or ActionsFailed.
	ExecuteRequests, ExecuteCached, ExecuteMerged int64
	// ActionsRun counts executions that produced a result; ActionsFailed
	// counts those that ended in an error, including a nonzero exit code.
	ActionsRun, ActionsFailed int64
	// QueueTime and ExecutionTime add up the time executed actions spent
	// waiting for a runner and running.
	QueueTime, ExecutionTime time.Duration

	// DigestsChecked counts digests in FindMissingBlobs calls;
	// DigestsMissing counts those the CAS lacked.
	DigestsChecked, DigestsMissing int64

	// BytesUploaded and BytesDownloaded count blob bytes the build client
	// wrote to and read from cas; BlobsUploaded and BlobsDownloaded count
	// the blobs.
	BlobsUploaded, BytesUploaded, BlobsDownloaded, BytesDownloaded int64
	// RunnerBytesUploaded counts output bytes runners wrote to cas.
	RunnerBytesUploaded int64
	// CacheFillBytes counts bytes cascache read from cas to fill a miss.
	CacheFillBytes int64
}

func (c *Counts) add(o Counts) {
	c.ActionCacheHits += o.ActionCacheHits
	c.ActionCacheMisses += o.ActionCacheMisses
	c.ActionCacheWrites += o.ActionCacheWrites
	c.ExecuteRequests += o.ExecuteRequests
	c.ExecuteCached += o.ExecuteCached
	c.ExecuteMerged += o.ExecuteMerged
	c.ActionsRun += o.ActionsRun
	c.ActionsFailed += o.ActionsFailed
	c.QueueTime += o.QueueTime
	c.ExecutionTime += o.ExecutionTime
	c.DigestsChecked += o.DigestsChecked
	c.DigestsMissing += o.DigestsMissing
	c.BlobsUploaded += o.BlobsUploaded
	c.BytesUploaded += o.BytesUploaded
	c.BlobsDownloaded += o.BlobsDownloaded
	c.BytesDownloaded += o.BytesDownloaded
	c.RunnerBytesUploaded += o.RunnerBytesUploaded
	c.CacheFillBytes += o.CacheFillBytes
}

// HitRatio is the fraction of action results the build got without running
// anything: action cache hits and cached or merged Execute calls, over all
// lookups that could have been. It is -1 when the build looked up nothing.
func (c Counts) HitRatio() float64 {
	hits := c.ActionCacheHits + c.ExecuteCached + c.ExecuteMerged
	// Bazel calls Execute after an action cache miss, so a miss and its
	// Execute are one lookup; a client that skips GetActionResult sends
	// only the Execute.
	total := c.ActionCacheHits + max(c.ActionCacheMisses, c.ExecuteRequests)
	if total == 0 {
		return -1
	}
	return float64(hits) / float64(total)
}

// Summary is a finished invocation.
type Summary struct {
	ID, CorrelatedID, Tool, ToolVersion string
	Instances                           []string
	Start, End                          time.Time
	Counts
}

type record struct {
	Summary
	instances map[string]bool
}

// Tracker accounts invocations. A nil *Tracker accounts nothing.
type Tracker struct {
	idle time.Duration
	now  func() time.Time

	mu   sync.Mutex
	open map[string]*record

	invocations metric.Int64Counter
	duration    metric.Float64Histogram
	hitRatio    metric.Float64Histogram
	bytes       metric.Int64Histogram
	actions     metric.Int64Histogram
}

// New returns a Tracker that ends an invocation after idle with no calls.
func New(idle time.Duration) *Tracker {
	t := &Tracker{idle: idle, now: time.Now, open: map[string]*record{}}
	m := telemetry.Meter()
	t.invocations = telemetry.Handle(m.Int64Counter("bazel.invocations",
		metric.WithDescription("Finished Bazel invocations.")))
	t.duration = telemetry.Handle(m.Float64Histogram("bazel.invocation.duration", metric.WithUnit("s"),
		metric.WithDescription("Time from an invocation's first call to its last."),
		metric.WithExplicitBucketBoundaries(1, 5, 15, 30, 60, 120, 300, 600, 1200, 1800, 3600)))
	t.hitRatio = telemetry.Handle(m.Float64Histogram("bazel.invocation.cache_hit_ratio",
		metric.WithDescription("Fraction of an invocation's actions served without running; see Counts.HitRatio."),
		metric.WithExplicitBucketBoundaries(0, .1, .2, .3, .4, .5, .6, .7, .8, .9, .95, .99, 1)))
	t.bytes = telemetry.Handle(m.Int64Histogram("bazel.invocation.bytes", metric.WithUnit("By"),
		metric.WithDescription("Blob bytes one invocation moved, by direction from cas's side."),
		metric.WithExplicitBucketBoundaries(0, 1<<20, 10<<20, 100<<20, 1<<30, 10<<30, 100<<30)))
	t.actions = telemetry.Handle(m.Int64Histogram("bazel.invocation.actions",
		metric.WithDescription("Actions one invocation ran remotely."),
		metric.WithExplicitBucketBoundaries(0, 1, 10, 100, 1000, 10000, 100000)))
	active := telemetry.Handle(m.Int64ObservableGauge("bazel.invocations.active",
		metric.WithDescription("Invocations that made a call within the idle timeout.")))
	telemetry.Handle(m.RegisterCallback(func(_ context.Context, o metric.Observer) error {
		t.mu.Lock()
		n := len(t.open)
		t.mu.Unlock()
		o.ObserveInt64(active, int64(n))
		return nil
	}, active))
	return t
}

// Add adds c to the invocation of the call ctx belongs to, if any.
func (t *Tracker) Add(ctx context.Context, instance string, c Counts) {
	t.AddFor(telemetry.RequestMetadata(ctx), instance, c)
}

// AddFor adds c to the invocation md names, if any.
func (t *Tracker) AddFor(md *repb.RequestMetadata, instance string, c Counts) {
	if t == nil || md.GetToolInvocationId() == "" {
		return
	}
	now := t.now()
	t.mu.Lock()
	defer t.mu.Unlock()
	r, ok := t.open[md.GetToolInvocationId()]
	if !ok {
		r = &record{
			Summary:   Summary{ID: md.GetToolInvocationId(), CorrelatedID: md.GetCorrelatedInvocationsId(), Start: now},
			instances: map[string]bool{},
		}
		t.open[r.ID] = r
	}
	if r.Tool == "" && telemetry.Peer(md) == "bazel" {
		r.Tool = md.GetToolDetails().GetToolName()
		r.ToolVersion = md.GetToolDetails().GetToolVersion()
	}
	if instance != "" && !r.instances[instance] {
		r.instances[instance] = true
		r.Instances = append(r.Instances, instance)
	}
	r.End = now
	r.add(c)
}

// Run ends idle invocations until ctx is done, then ends the rest.
func (t *Tracker) Run(ctx context.Context) {
	tick := time.NewTicker(t.idle / 4)
	defer tick.Stop()
	for {
		select {
		case <-ctx.Done():
			t.Flush(context.WithoutCancel(ctx), time.Time{})
			return
		case <-tick.C:
			t.Flush(ctx, t.now().Add(-t.idle))
		}
	}
}

// Flush ends the invocations whose last call was before cutoff, or all of
// them when cutoff is zero, and returns their summaries.
func (t *Tracker) Flush(ctx context.Context, cutoff time.Time) []Summary {
	t.mu.Lock()
	var done []Summary
	for id, r := range t.open {
		if cutoff.IsZero() || r.End.Before(cutoff) {
			done = append(done, r.Summary)
			delete(t.open, id)
		}
	}
	t.mu.Unlock()
	for _, s := range done {
		t.record(ctx, s)
	}
	return done
}

func (t *Tracker) record(ctx context.Context, s Summary) {
	sc := telemetry.InvocationSpanContext(s.ID)
	attrs := []attribute.KeyValue{
		attribute.String("bazel.invocation_id", s.ID),
		attribute.String("bazel.correlated_invocations_id", s.CorrelatedID),
		attribute.String("bazel.tool", s.Tool),
		attribute.String("bazel.tool_version", s.ToolVersion),
		attribute.StringSlice("ci_substrate.instances", s.Instances),
		attribute.Int64("bazel.action_cache.hits", s.ActionCacheHits),
		attribute.Int64("bazel.action_cache.misses", s.ActionCacheMisses),
		attribute.Int64("bazel.action_cache.writes", s.ActionCacheWrites),
		attribute.Int64("bazel.execute.requests", s.ExecuteRequests),
		attribute.Int64("bazel.execute.cached", s.ExecuteCached),
		attribute.Int64("bazel.execute.merged", s.ExecuteMerged),
		attribute.Int64("bazel.actions.run", s.ActionsRun),
		attribute.Int64("bazel.actions.failed", s.ActionsFailed),
		attribute.Float64("bazel.queue_time_s", s.QueueTime.Seconds()),
		attribute.Float64("bazel.execution_time_s", s.ExecutionTime.Seconds()),
		attribute.Int64("bazel.digests.checked", s.DigestsChecked),
		attribute.Int64("bazel.digests.missing", s.DigestsMissing),
		attribute.Int64("bazel.blobs.uploaded", s.BlobsUploaded),
		attribute.Int64("bazel.bytes.uploaded", s.BytesUploaded),
		attribute.Int64("bazel.blobs.downloaded", s.BlobsDownloaded),
		attribute.Int64("bazel.bytes.downloaded", s.BytesDownloaded),
		attribute.Int64("ci_substrate.runner_bytes_uploaded", s.RunnerBytesUploaded),
		attribute.Int64("ci_substrate.cache_fill_bytes", s.CacheFillBytes),
		attribute.Float64("bazel.cache_hit_ratio", s.HitRatio()),
	}
	_, span := telemetry.Tracer().Start(telemetry.WithIDs(context.Background(), sc), "bazel invocation",
		trace.WithNewRoot(), trace.WithSpanKind(trace.SpanKindServer),
		trace.WithTimestamp(s.Start), trace.WithAttributes(attrs...))
	span.End(trace.WithTimestamp(s.End))

	tool := metric.WithAttributes(attribute.String("tool", s.Tool))
	t.invocations.Add(ctx, 1, tool)
	t.duration.Record(ctx, s.End.Sub(s.Start).Seconds(), tool)
	if r := s.HitRatio(); r >= 0 {
		t.hitRatio.Record(ctx, r, tool)
	}
	t.bytes.Record(ctx, s.BytesUploaded, metric.WithAttributes(telemetry.AttrDirection.String("write")))
	t.bytes.Record(ctx, s.BytesDownloaded, metric.WithAttributes(telemetry.AttrDirection.String("read")))
	t.actions.Record(ctx, s.ActionsRun+s.ActionsFailed, tool)

	slog.InfoContext(trace.ContextWithSpanContext(ctx, sc), "invocation finished",
		"invocation", s.ID, "tool", s.Tool, "instances", s.Instances,
		"duration", s.End.Sub(s.Start), "cache_hit_ratio", s.HitRatio(),
		"actions_run", s.ActionsRun, "actions_failed", s.ActionsFailed,
		"execute_cached", s.ExecuteCached, "execute_merged", s.ExecuteMerged,
		"ac_hits", s.ActionCacheHits, "ac_misses", s.ActionCacheMisses,
		"bytes_uploaded", s.BytesUploaded, "bytes_downloaded", s.BytesDownloaded,
		"queue_time", s.QueueTime, "execution_time", s.ExecutionTime)
}
