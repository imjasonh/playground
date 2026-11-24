package telemetry

import (
	"errors"
	"testing"
	"time"

	repb "github.com/bazelbuild/remote-apis/build/bazel/remote/execution/v2"
	"go.opentelemetry.io/otel"
	"go.opentelemetry.io/otel/codes"
	sdktrace "go.opentelemetry.io/otel/sdk/trace"
	"go.opentelemetry.io/otel/sdk/trace/tracetest"
	"go.opentelemetry.io/otel/trace"
)

func recorder(t *testing.T) *tracetest.SpanRecorder {
	t.Helper()
	rec := tracetest.NewSpanRecorder()
	tp := sdktrace.NewTracerProvider(sdktrace.WithSampler(Sampler()), sdktrace.WithSpanProcessor(rec))
	prev := otel.GetTracerProvider()
	otel.SetTracerProvider(tp)
	t.Cleanup(func() { otel.SetTracerProvider(prev) })
	return rec
}

func TestSamplerDropsBlobReads(t *testing.T) {
	rec := recorder(t)
	ctx, parent := Tracer().Start(t.Context(), "runner.prepare_inputs")
	for name := range blobReadSpans {
		rctx, span := Tracer().Start(ctx, name)
		if span.SpanContext().IsSampled() {
			t.Errorf("%s is sampled", name)
		}
		if !span.SpanContext().IsValid() {
			t.Errorf("%s has no span context, so the server it calls would sample its own spans", name)
		}
		_, child := Tracer().Start(rctx, "cascache.origin_fetch")
		if child.SpanContext().IsSampled() {
			t.Errorf("a span under %s is sampled", name)
		}
		child.End()
		span.End()
	}
	parent.End()

	var names []string
	for _, s := range rec.Ended() {
		names = append(names, s.Name())
	}
	if len(names) != 1 || names[0] != "runner.prepare_inputs" {
		t.Errorf("recorded spans = %v, want only runner.prepare_inputs", names)
	}
}

func TestRecordRead(t *testing.T) {
	md := &repb.RequestMetadata{ToolInvocationId: "inv-1", ActionMnemonic: "GoCompile"}
	invocation := InvocationSpanContext("inv-1").SpanID()
	for _, tc := range []struct {
		name       string
		md         *repb.RequestMetadata
		took       time.Duration
		err        error
		wantSpan   bool
		wantParent trace.SpanID
	}{
		{name: "fast", md: md, took: time.Millisecond},
		{name: "slow", md: md, took: SlowRead, wantSpan: true, wantParent: invocation},
		{name: "failed", md: md, err: errors.New("unavailable"), wantSpan: true, wantParent: invocation},
		{name: "no invocation", err: errors.New("unavailable")},
	} {
		t.Run(tc.name, func(t *testing.T) {
			rec := recorder(t)
			unsampled := trace.ContextWithRemoteSpanContext(WithRequestMetadata(t.Context(), tc.md), trace.NewSpanContext(trace.SpanContextConfig{
				TraceID: trace.TraceID{1},
				SpanID:  trace.SpanID{1},
			}))
			RecordRead(unsampled, "runner.blob_read", time.Now().Add(-tc.took), tc.err)
			spans := rec.Ended()
			if !tc.wantSpan {
				if len(spans) != 0 {
					t.Errorf("recorded %d spans, want none", len(spans))
				}
				return
			}
			if len(spans) != 1 {
				t.Fatalf("recorded %d spans, want 1", len(spans))
			}
			s := spans[0]
			if got := s.Parent().SpanID(); got != tc.wantParent {
				t.Errorf("parent = %v, want the invocation span %v", got, tc.wantParent)
			}
			if got := s.EndTime().Sub(s.StartTime()); got < tc.took {
				t.Errorf("span lasts %v, want at least %v", got, tc.took)
			}
			if wantErr := tc.err != nil; (s.Status().Code == codes.Error) != wantErr {
				t.Errorf("status = %v, want an error status: %v", s.Status(), wantErr)
			}
			var mnemonic bool
			for _, a := range s.Attributes() {
				mnemonic = mnemonic || a.Value.AsString() == "GoCompile"
			}
			if !mnemonic {
				t.Errorf("attributes %v lack the RequestMetadata's mnemonic", s.Attributes())
			}
		})
	}
}
