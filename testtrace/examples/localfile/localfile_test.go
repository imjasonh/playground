// Package localfile shows wiring testtrace to write spans to a local file,
// one JSON object per line, with no collector or network call. Run it with:
//
//	go test ./testtrace/examples/localfile/ -v
package localfile

import (
	"context"
	"fmt"
	"os"
	"testing"

	"go.opentelemetry.io/otel"
	"go.opentelemetry.io/otel/exporters/stdout/stdouttrace"
	sdktrace "go.opentelemetry.io/otel/sdk/trace"

	"github.com/imjasonh/playground/testtrace"
)

var tracer = otel.Tracer("localfile-example")

// RunPipeline stands in for application code that takes a context and
// starts its own spans, the way code under test usually does.
func RunPipeline(ctx context.Context) {
	_, span := tracer.Start(ctx, "RunPipeline")
	defer span.End()
	_, step := tracer.Start(ctx, "RunPipeline.step")
	step.End()
}

func TestMain(m *testing.M) {
	f, err := os.CreateTemp("", "testtrace-example-*.jsonl")
	if err != nil {
		panic(err)
	}
	defer os.Remove(f.Name())
	defer f.Close()

	exporter, err := stdouttrace.New(stdouttrace.WithWriter(f))
	if err != nil {
		panic(err)
	}
	// WithSyncer writes each span to the file as soon as it ends. A
	// longer-lived process would use WithBatcher instead, which queues
	// spans and flushes them on a timer or on Shutdown, trading that
	// immediacy for fewer, larger writes.
	tp := sdktrace.NewTracerProvider(sdktrace.WithSyncer(exporter))
	testtrace.Install(tp)

	code := m.Run()

	if err := tp.Shutdown(context.Background()); err != nil { // pasta:ignore use_t_context — TestMain has no t
		panic(err)
	}
	data, err := os.ReadFile(f.Name())
	if err != nil {
		panic(err)
	}
	fmt.Fprintf(os.Stderr, "testtrace wrote %d bytes of span JSON to %s:\n%s", len(data), f.Name(), data)
	os.Exit(code)
}

func TestPipelineSpansGoToTheFile(t *testing.T) {
	// Hook, rather than the automatic path, so this test's own span is
	// guaranteed to be written to the file by the time TestMain reads it
	// back below: Hook ends its span from t.Cleanup, which runs before
	// m.Run() returns, where the automatic path ends its span from a
	// context.AfterFunc callback on another goroutine.
	ctx := testtrace.Hook(t)
	RunPipeline(ctx)
}
