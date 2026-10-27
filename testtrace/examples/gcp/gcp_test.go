// Package gcp shows wiring testtrace to send spans over OTLP/HTTP to an
// OpenTelemetry Collector, the way you'd land them in Google Cloud Trace.
//
// The Go side is the whole story here, and it's the same OTLP exporter and
// endpoint config no matter where the Collector forwards spans afterward.
// What makes this "GCP" is the Collector's own config, in
// collector-config.yaml next to this file, which uses the googlecloud
// exporter to forward every batch it receives to Cloud Trace. This test
// fakes that Collector with a plain HTTP server that decodes the same OTLP
// protobuf a real one would, so go test here needs no GCP project,
// credentials, or network beyond localhost.
//
// Point it at a real Collector instead, already running with
// collector-config.yaml and credentials for your project (see that file's
// header), by setting the endpoint it would otherwise fake:
//
//	OTEL_EXPORTER_OTLP_ENDPOINT=http://localhost:4318 go test ./testtrace/examples/gcp/ -v
package gcp

import (
	"context"
	"io"
	"net/http"
	"net/http/httptest"
	"os"
	"sync"
	"testing"

	"google.golang.org/protobuf/proto"

	coltracepb "go.opentelemetry.io/proto/otlp/collector/trace/v1"

	"go.opentelemetry.io/otel"
	"go.opentelemetry.io/otel/exporters/otlp/otlptrace/otlptracehttp"
	sdktrace "go.opentelemetry.io/otel/sdk/trace"

	"github.com/imjasonh/playground/testtrace"
)

var tracer = otel.Tracer("gcp-example")

// RunPipeline stands in for application code that takes a context and
// starts its own spans, the way code under test usually does.
func RunPipeline(ctx context.Context) {
	_, span := tracer.Start(ctx, "RunPipeline")
	span.End()
}

// tp is the TracerProvider TestMain installs, so a test can call
// ForceFlush: the batch span processor below otherwise sends spans to the
// collector on its own schedule, not when the test that started them ends.
var tp *sdktrace.TracerProvider

// selfContained is true when no OTEL_EXPORTER_OTLP_ENDPOINT points this
// test at a real Collector, so TestMain started the fake one below and
// tests can check what it received.
var selfContained bool

func TestMain(m *testing.M) {
	ctx := context.Background() // pasta:ignore use_t_context — TestMain has no t
	var opts []otlptracehttp.Option
	if os.Getenv("OTEL_EXPORTER_OTLP_ENDPOINT") == "" {
		selfContained = true
		srv := httptest.NewServer(http.HandlerFunc(fakeCollector))
		defer srv.Close()
		opts = append(opts, otlptracehttp.WithEndpointURL(srv.URL))
	}
	exporter, err := otlptracehttp.New(ctx, opts...)
	if err != nil {
		panic(err)
	}
	tp = sdktrace.NewTracerProvider(sdktrace.WithBatcher(exporter))
	testtrace.Install(tp)

	code := m.Run()
	if err := tp.Shutdown(ctx); err != nil {
		panic(err)
	}
	os.Exit(code)
}

var (
	mu       sync.Mutex
	received []string
)

// fakeCollector stands in for an OpenTelemetry Collector's OTLP/HTTP trace
// receiver: it decodes the same protobuf request body a real one would.
// collector-config.yaml shows what a real Collector does with it next.
func fakeCollector(w http.ResponseWriter, r *http.Request) {
	body, err := io.ReadAll(r.Body)
	if err != nil {
		http.Error(w, err.Error(), http.StatusBadRequest)
		return
	}
	var req coltracepb.ExportTraceServiceRequest
	if err := proto.Unmarshal(body, &req); err != nil {
		http.Error(w, err.Error(), http.StatusBadRequest)
		return
	}
	mu.Lock()
	for _, rs := range req.ResourceSpans {
		for _, ss := range rs.ScopeSpans {
			for _, s := range ss.Spans {
				received = append(received, s.Name)
			}
		}
	}
	mu.Unlock()

	resp, err := proto.Marshal(&coltracepb.ExportTraceServiceResponse{})
	if err != nil {
		http.Error(w, err.Error(), http.StatusInternalServerError)
		return
	}
	w.Header().Set("Content-Type", "application/x-protobuf")
	_, _ = w.Write(resp) // the client already got the spans; nothing left to do with a write error here
}

func TestPipelineSpansReachTheCollector(t *testing.T) {
	// Registered before Hook's own t.Cleanup call, so it runs after Hook's:
	// cleanups run in last-registered-first-run order, and the test's span
	// isn't ended, let alone queued for export, until Hook's cleanup runs.
	// By then t.Context() is already canceled, so this flush needs its own
	// context.
	t.Cleanup(func() {
		if err := tp.ForceFlush(context.Background()); err != nil { // pasta:ignore use_t_context — t.Context() is already canceled inside Cleanup
			t.Fatal(err)
		}
		if !selfContained {
			t.Skip("OTEL_EXPORTER_OTLP_ENDPOINT points at a real collector; this test has nothing of its own to check")
		}
		mu.Lock()
		got := append([]string(nil), received...)
		mu.Unlock()
		for _, want := range []string{t.Name(), "RunPipeline"} {
			if !contains(got, want) {
				t.Errorf("collector never received a span named %q; got %v", want, got)
			}
		}
	})
	ctx := testtrace.Hook(t)
	RunPipeline(ctx)
}

func contains(ss []string, s string) bool {
	for _, v := range ss {
		if v == s {
			return true
		}
	}
	return false
}
