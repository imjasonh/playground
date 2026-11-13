package bot

import (
	"context"
	"sync/atomic"
	"time"

	repb "github.com/bazelbuild/remote-apis/build/bazel/remote/execution/v2"
	otelcodes "go.opentelemetry.io/otel/codes"
	"go.opentelemetry.io/otel/metric"
	"go.opentelemetry.io/otel/trace"
	"google.golang.org/grpc/metadata"

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

// jobFetcher reads for one job and counts the bytes. A FUSE mount reads
// with the context of the file operation, which carries neither the job's
// span nor its RequestMetadata, so a read without a span gets the job's
// span and outgoing metadata.
type jobFetcher struct {
	inner    tree.Fetcher
	span     trace.SpanContext
	outgoing metadata.MD
	bytes    atomic.Int64
}

func newJobFetcher(ctx context.Context, inner tree.Fetcher) *jobFetcher {
	md, _ := metadata.FromOutgoingContext(ctx)
	return &jobFetcher{inner: inner, span: trace.SpanContextFromContext(ctx), outgoing: md}
}

func (f *jobFetcher) Fetch(ctx context.Context, instance string, d *repb.Digest) ([]byte, error) {
	if !trace.SpanContextFromContext(ctx).IsValid() {
		ctx = metadata.NewOutgoingContext(trace.ContextWithSpanContext(ctx, f.span), f.outgoing)
	}
	b, err := f.inner.Fetch(ctx, instance, d)
	f.bytes.Add(int64(len(b)))
	return b, err
}
