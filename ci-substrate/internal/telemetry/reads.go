package telemetry

import (
	"context"
	"time"

	"go.opentelemetry.io/otel/attribute"
	"go.opentelemetry.io/otel/codes"
	sdktrace "go.opentelemetry.io/otel/sdk/trace"
	"go.opentelemetry.io/otel/trace"
)

// SlowRead is how long a blob read takes before RecordRead gives it a span.
const SlowRead = 100 * time.Millisecond

// blobReadSpans are the RPCs that read one blob each. A build reads every
// input of every action through them, hundreds of thousands of calls, so
// they get metrics but no spans: the runner sums them on the action's span
// instead, and RecordRead keeps the slow and failed ones.
var blobReadSpans = map[string]bool{
	"build.bazel.remote.execution.v2.ContentAddressableStorage/BatchReadBlobs": true,
	"google.bytestream.ByteStream/Read":                                        true,
}

// Sampler returns the sampler Setup installs: every span whose parent is
// sampled, and every root, except blob reads. A dropped read's trace
// context goes out unsampled, so the server it calls, and the server's own
// calls, drop their spans too.
func Sampler() sdktrace.Sampler {
	return blobReadSampler{sdktrace.ParentBased(sdktrace.AlwaysSample())}
}

type blobReadSampler struct{ inner sdktrace.Sampler }

func (s blobReadSampler) ShouldSample(p sdktrace.SamplingParameters) sdktrace.SamplingResult {
	if blobReadSpans[p.Name] {
		return sdktrace.SamplingResult{
			Decision:   sdktrace.Drop,
			Tracestate: trace.SpanContextFromContext(p.ParentContext).TraceState(),
		}
	}
	return s.inner.ShouldSample(p)
}

func (s blobReadSampler) Description() string {
	return "DropBlobReads{" + s.inner.Description() + "}"
}

// RecordRead records a span named name, from start until now, for a blob
// read that failed or took SlowRead or longer, and records nothing for any
// other read. The span's parent is ctx's span when that is sampled. A read
// inside a dropped blob-read call has an unsampled parent, so the span goes
// under the invocation span of ctx's RequestMetadata instead, with the
// RequestMetadata's attributes, and is dropped when there is neither.
func RecordRead(ctx context.Context, name string, start time.Time, err error, attrs ...attribute.KeyValue) {
	end := time.Now()
	if err == nil && end.Sub(start) < SlowRead {
		return
	}
	if !trace.SpanContextFromContext(ctx).IsSampled() {
		md := RequestMetadata(ctx)
		if md.GetToolInvocationId() == "" {
			return
		}
		ctx = trace.ContextWithRemoteSpanContext(ctx, InvocationSpanContext(md.GetToolInvocationId()))
		attrs = append(attrs, Attributes(md)...)
	}
	_, span := Tracer().Start(ctx, name, trace.WithTimestamp(start), trace.WithAttributes(attrs...))
	if err != nil {
		span.RecordError(err)
		span.SetStatus(codes.Error, err.Error())
	}
	span.End(trace.WithTimestamp(end))
}
