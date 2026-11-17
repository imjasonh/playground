package telemetry

import (
	"bytes"
	"log/slog"
	"strings"
	"testing"

	semconv "go.opentelemetry.io/otel/semconv/v1.43.0"
	"go.opentelemetry.io/otel/trace"
)

func TestSetupWithoutCollector(t *testing.T) {
	t.Setenv("OTEL_EXPORTER_OTLP_ENDPOINT", "")
	t.Setenv("OTEL_RESOURCE_ATTRIBUTES", "k8s.pod.name=pod-1")
	old := slog.Default()
	t.Cleanup(func() { slog.SetDefault(old) })
	shutdown, err := Setup(t.Context(), "test", semconv.ServiceInstanceID("bot-1"))
	if err != nil {
		t.Fatal(err)
	}
	_, span := Tracer().Start(t.Context(), "work")
	if !span.SpanContext().IsValid() {
		t.Error("span from the installed provider has no IDs")
	}
	span.End()
	if err := shutdown(t.Context()); err != nil {
		t.Errorf("shutdown: %v", err)
	}
}

func TestLogsCarryTrace(t *testing.T) {
	sc := InvocationSpanContext("inv-1")
	ctx := trace.ContextWithSpanContext(t.Context(), sc)
	for _, tc := range []struct {
		project, want string
	}{
		{"", "trace_id=" + sc.TraceID().String()},
		{"my-project", "logging.googleapis.com/trace=projects/my-project/traces/" + sc.TraceID().String()},
	} {
		var buf bytes.Buffer
		slog.New(traceHandler{inner: slog.NewTextHandler(&buf, nil), project: tc.project}).InfoContext(ctx, "hi")
		if !strings.Contains(buf.String(), tc.want) {
			t.Errorf("project %q: log %q lacks %q", tc.project, buf.String(), tc.want)
		}
	}
}
