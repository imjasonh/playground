package bot

import (
	"os/exec"
	"strings"
	"testing"

	repb "github.com/bazelbuild/remote-apis/build/bazel/remote/execution/v2"
	"go.opentelemetry.io/otel"
	"go.opentelemetry.io/otel/propagation"
	sdktrace "go.opentelemetry.io/otel/sdk/trace"
	"go.opentelemetry.io/otel/trace"

	"github.com/imjasonh/playground/ci-substrate/internal/telemetry"
)

func TestEnvironmentCarriesTheBuildTrace(t *testing.T) {
	otel.SetTextMapPropagator(propagation.TraceContext{})
	t.Cleanup(func() {
		otel.SetTextMapPropagator(propagation.NewCompositeTextMapPropagator())
	})
	sc := telemetry.InvocationSpanContext("build-1")
	ctx := trace.ContextWithRemoteSpanContext(t.Context(), sc)
	ctx, span := sdktrace.NewTracerProvider().Tracer("runner").Start(ctx, "runner.execute")
	defer span.End()

	got := envMap(environment(ctx, &repb.Command{
		EnvironmentVariables: []*repb.Command_EnvironmentVariable{{Name: "FOO", Value: "bar"}},
	}))
	if got["FOO"] != "bar" {
		t.Errorf("FOO = %q", got["FOO"])
	}
	if got["PATH"] == "" {
		t.Error("PATH was not defaulted")
	}
	parent := got["TRACEPARENT"]
	wantTrace := sc.TraceID().String()
	wantSpan := span.SpanContext().SpanID().String()
	if !strings.Contains(parent, wantTrace) || !strings.Contains(parent, wantSpan) {
		t.Errorf("TRACEPARENT = %q, want trace %s and span %s", parent, wantTrace, wantSpan)
	}

	kept := envMap(environment(ctx, &repb.Command{
		EnvironmentVariables: []*repb.Command_EnvironmentVariable{{Name: "TRACEPARENT", Value: "set-by-action"}},
	}))
	if kept["TRACEPARENT"] != "set-by-action" {
		t.Errorf("TRACEPARENT = %q, want the command's value", kept["TRACEPARENT"])
	}
	if _, ok := kept["TRACESTATE"]; ok {
		t.Error("TRACESTATE was added beside a command-set TRACEPARENT")
	}
}

func TestActionProcessSeesTheBuildTrace(t *testing.T) {
	otel.SetTextMapPropagator(propagation.TraceContext{})
	t.Cleanup(func() {
		otel.SetTextMapPropagator(propagation.NewCompositeTextMapPropagator())
	})
	sc := telemetry.InvocationSpanContext("build-1")
	ctx := trace.ContextWithRemoteSpanContext(t.Context(), sc)
	ctx, span := sdktrace.NewTracerProvider().Tracer("runner").Start(ctx, "runner.execute")
	defer span.End()

	shell, err := exec.LookPath("bash")
	if err != nil {
		t.Skip(err)
	}
	started := &Bot{shell: shell}
	cmd, err := started.command(ctx, t.TempDir(), []string{"sh", "-c", `printf %s "$TRACEPARENT"`})
	if err != nil {
		t.Fatal(err)
	}
	cmd.Env = environment(ctx, &repb.Command{})
	out, err := cmd.Output()
	if err != nil {
		t.Fatal(err)
	}
	parent := string(out)
	if !strings.Contains(parent, sc.TraceID().String()) || !strings.Contains(parent, span.SpanContext().SpanID().String()) {
		t.Errorf("action printed %q, want trace %s and span %s", parent, sc.TraceID(), span.SpanContext().SpanID())
	}
}

func envMap(env []string) map[string]string {
	out := map[string]string{}
	for _, kv := range env {
		name, value, _ := strings.Cut(kv, "=")
		out[name] = value
	}
	return out
}
