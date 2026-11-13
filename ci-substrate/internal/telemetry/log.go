package telemetry

import (
	"context"
	"log/slog"

	"go.opentelemetry.io/otel/trace"
)

// traceHandler adds the current span to each record, so a log line links to
// its trace. With project set, it uses the keys Cloud Logging reads to
// link the line in the console; otherwise trace_id and span_id.
type traceHandler struct {
	inner   slog.Handler
	project string
}

func (h traceHandler) Enabled(ctx context.Context, l slog.Level) bool {
	return h.inner.Enabled(ctx, l)
}

func (h traceHandler) Handle(ctx context.Context, r slog.Record) error {
	if sc := trace.SpanContextFromContext(ctx); sc.IsValid() {
		if h.project != "" {
			r.AddAttrs(
				slog.String("logging.googleapis.com/trace", "projects/"+h.project+"/traces/"+sc.TraceID().String()),
				slog.String("logging.googleapis.com/spanId", sc.SpanID().String()),
				slog.Bool("logging.googleapis.com/trace_sampled", sc.IsSampled()),
			)
		} else {
			r.AddAttrs(slog.String("trace_id", sc.TraceID().String()), slog.String("span_id", sc.SpanID().String()))
		}
	}
	return h.inner.Handle(ctx, r)
}

func (h traceHandler) WithAttrs(as []slog.Attr) slog.Handler {
	return traceHandler{inner: h.inner.WithAttrs(as), project: h.project}
}

func (h traceHandler) WithGroup(name string) slog.Handler {
	return traceHandler{inner: h.inner.WithGroup(name), project: h.project}
}
