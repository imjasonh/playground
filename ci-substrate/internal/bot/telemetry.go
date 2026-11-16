package bot

import (
	"context"
	"sync/atomic"
	"time"

	repb "github.com/bazelbuild/remote-apis/build/bazel/remote/execution/v2"
	"go.opentelemetry.io/otel/attribute"
	otelcodes "go.opentelemetry.io/otel/codes"
	"go.opentelemetry.io/otel/metric"
	"go.opentelemetry.io/otel/trace"
	"google.golang.org/grpc/metadata"

	"github.com/imjasonh/playground/ci-substrate/internal/digest"
	"github.com/imjasonh/playground/ci-substrate/internal/telemetry"
	"github.com/imjasonh/playground/ci-substrate/internal/tree"
)

var durationBuckets = metric.WithExplicitBucketBoundaries(.005, .01, .025, .05, .1, .25, .5, 1, 2.5, 5, 10, 30, 60, 120, 300, 600, 1800)

type metrics struct {
	actions     metric.Int64Counter
	duration    metric.Float64Histogram
	stage       metric.Float64Histogram
	busy        metric.Float64Counter
	inputBytes  metric.Int64Counter
	uploadBytes metric.Int64Counter
	read        metric.Float64Histogram
}

func newMetrics() metrics {
	m := telemetry.Meter()
	return metrics{
		actions: telemetry.Handle(m.Int64Counter("runner.actions",
			metric.WithDescription("Actions this runner ran, by outcome: ok, exit_nonzero, or error."))),
		duration: telemetry.Handle(m.Float64Histogram("runner.action.duration", metric.WithUnit("s"),
			metric.WithDescription("Time from lease to Complete for one action."), durationBuckets)),
		stage: telemetry.Handle(m.Float64Histogram("runner.stage.duration", metric.WithUnit("s"),
			metric.WithDescription("Time one action spent in each stage: fetch_action, prepare_inputs, run, upload_outputs, complete."), durationBuckets)),
		busy: telemetry.Handle(m.Float64Counter("runner.busy.time", metric.WithUnit("s"),
			metric.WithDescription("Time this runner spent on actions. Its rate over the runner count is utilization."))),
		inputBytes: telemetry.Handle(m.Int64Counter("runner.input.bytes", metric.WithUnit("By"),
			metric.WithDescription("Input bytes this runner read from the cache for its actions. Volume mode reads on the host instead."))),
		uploadBytes: telemetry.Handle(m.Int64Counter("runner.upload.bytes", metric.WithUnit("By"),
			metric.WithDescription("Output bytes, by result: sent to cas, or deduplicated because cas held them."))),
		read: telemetry.Handle(m.Float64Histogram("runner.blob.read.duration", metric.WithUnit("s"),
			metric.WithDescription("Time for one call that reads from the cache, by phase: prepare, before the command starts, or lazy, through FUSE while it runs. A call reads one blob, or a batch, such as one level of the input tree."),
			metric.WithExplicitBucketBoundaries(.0005, .001, .0025, .005, .01, .025, .05, .1, .25, .5, 1, 2.5, 5, 10, 30))),
	}
}

// stage starts the span of one step of an action, and returns the function
// that ends it and records its duration.
func (b *Bot) stage(ctx context.Context, name string) (context.Context, func(error)) {
	start := time.Now()
	ctx, span := telemetry.Tracer().Start(ctx, "runner."+name)
	return ctx, func(err error) {
		if err != nil {
			span.RecordError(err)
			span.SetStatus(otelcodes.Error, err.Error())
		}
		span.End()
		b.metrics.stage.Record(ctx, time.Since(start).Seconds(), metric.WithAttributes(
			telemetry.AttrStage.String(name),
			telemetry.AttrInputMode.String(string(b.cfg.InputMode)),
			telemetry.AttrMnemonic.String(telemetry.RequestMetadata(ctx).GetActionMnemonic()),
		))
	}
}

const (
	phasePrepare = "prepare"
	phaseLazy    = "lazy"
)

// readStats sums one job's blob reads in one phase. A call reads one blob,
// or many with FetchBatch.
type readStats struct {
	calls, blobs, bytes, errors atomic.Int64
	// total and slowest are call durations in nanoseconds. Reads through a
	// FUSE mount can overlap, so total can exceed the phase's wall time.
	total, slowest atomic.Int64
}

func (s *readStats) add(blobs int, n int64, took time.Duration, err error) {
	s.calls.Add(1)
	s.blobs.Add(int64(blobs))
	s.bytes.Add(n)
	s.total.Add(int64(took))
	if err != nil {
		s.errors.Add(1)
	}
	for {
		old := s.slowest.Load()
		if int64(took) <= old || s.slowest.CompareAndSwap(old, int64(took)) {
			return
		}
	}
}

func (s *readStats) attributes(phase string) []attribute.KeyValue {
	p := "ci_substrate.reads." + phase + "."
	return []attribute.KeyValue{
		attribute.Int64(p+"calls", s.calls.Load()),
		attribute.Int64(p+"blobs", s.blobs.Load()),
		attribute.Int64(p+"bytes", s.bytes.Load()),
		attribute.Int64(p+"errors", s.errors.Load()),
		attribute.Float64(p+"seconds", time.Duration(s.total.Load()).Seconds()),
		attribute.Float64(p+"slowest_seconds", time.Duration(s.slowest.Load()).Seconds()),
	}
}

// jobFetcher reads for one job, measures every read, and sums them by
// phase for the job's span. A FUSE mount reads with the context of the
// file operation, which carries neither the job's span nor its
// RequestMetadata, so a read without a span is a lazy read and gets the
// job's span and outgoing metadata.
type jobFetcher struct {
	inner    tree.Fetcher
	span     trace.SpanContext
	outgoing metadata.MD
	read     metric.Float64Histogram
	instance string
	mode     string
	prepare  readStats
	lazy     readStats
}

func (b *Bot) newJobFetcher(ctx context.Context, instance string) *jobFetcher {
	md, _ := metadata.FromOutgoingContext(ctx)
	return &jobFetcher{
		inner:    b.cache,
		span:     trace.SpanContextFromContext(ctx),
		outgoing: md,
		read:     b.metrics.read,
		instance: instance,
		mode:     string(b.cfg.InputMode),
	}
}

func (f *jobFetcher) Fetch(ctx context.Context, instance string, d *repb.Digest) ([]byte, error) {
	ctx, phase, stats := f.phase(ctx)
	start := time.Now()
	b, err := f.inner.Fetch(ctx, instance, d)
	f.record(ctx, phase, stats, start, 1, int64(len(b)), err,
		attribute.String("ci_substrate.digest", digest.Key(d)),
		attribute.Int64("ci_substrate.bytes", d.GetSizeBytes()),
	)
	return b, err
}

func (f *jobFetcher) FetchBatch(ctx context.Context, instance string, ds []*repb.Digest) ([][]byte, error) {
	ctx, phase, stats := f.phase(ctx)
	start := time.Now()
	blobs, err := tree.FetchAll(ctx, f.inner, instance, ds)
	var n, size int64
	for i, b := range blobs {
		n += int64(len(b))
		size += ds[i].GetSizeBytes()
	}
	f.record(ctx, phase, stats, start, len(ds), n, err,
		attribute.Int("ci_substrate.blobs", len(ds)),
		attribute.Int64("ci_substrate.bytes", size),
	)
	return blobs, err
}

// phase returns the phase of a read with ctx, its stats, and the context
// to read with.
func (f *jobFetcher) phase(ctx context.Context) (context.Context, string, *readStats) {
	if trace.SpanContextFromContext(ctx).IsValid() {
		return ctx, phasePrepare, &f.prepare
	}
	return metadata.NewOutgoingContext(trace.ContextWithSpanContext(ctx, f.span), f.outgoing), phaseLazy, &f.lazy
}

// record adds one read call to stats and to the runner.blob.read.duration
// histogram with the job's span, so a slow bucket's exemplar links to the
// action, and gives a slow or failed call a runner.blob_read span.
func (f *jobFetcher) record(ctx context.Context, phase string, stats *readStats, start time.Time, blobs int, n int64, err error, attrs ...attribute.KeyValue) {
	took := time.Since(start)
	stats.add(blobs, n, took, err)
	outcome := "ok"
	if err != nil {
		outcome = "error"
	}
	f.read.Record(ctx, took.Seconds(), metric.WithAttributes(
		telemetry.AttrInstance.String(f.instance),
		telemetry.AttrInputMode.String(f.mode),
		telemetry.AttrPhase.String(phase),
		telemetry.AttrOutcome.String(outcome),
	))
	telemetry.RecordRead(ctx, "runner.blob_read", start, err, append(attrs, attribute.String("ci_substrate.phase", phase))...)
}

// inputBytes is how many bytes the job has read.
func (f *jobFetcher) inputBytes() int64 { return f.prepare.bytes.Load() + f.lazy.bytes.Load() }

// attributes describes the job's reads on its span.
func (f *jobFetcher) attributes() []attribute.KeyValue {
	return append(f.prepare.attributes(phasePrepare), f.lazy.attributes(phaseLazy)...)
}
