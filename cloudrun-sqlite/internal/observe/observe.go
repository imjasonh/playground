// Package observe records how long the server spends in HTTP, SQLite, and
// replica storage. /metrics serves the histograms in the Prometheus text
// format. On Cloud Run the same histograms also go to Cloud Monitoring, and
// spans go to Cloud Trace; elsewhere the spans are dropped.
package observe

import (
	"context"
	"encoding/binary"
	"errors"
	"log/slog"
	"net/http"
	"os"
	"strconv"
	"strings"
	"sync"
	"sync/atomic"
	"time"

	"cloud.google.com/go/compute/metadata"
	mexporter "github.com/GoogleCloudPlatform/opentelemetry-operations-go/exporter/metric"
	texporter "github.com/GoogleCloudPlatform/opentelemetry-operations-go/exporter/trace"
	"github.com/prometheus/client_golang/prometheus"
	"github.com/prometheus/client_golang/prometheus/promhttp"
	"go.opentelemetry.io/contrib/detectors/gcp"
	"go.opentelemetry.io/otel"
	"go.opentelemetry.io/otel/attribute"
	"go.opentelemetry.io/otel/codes"
	otelprom "go.opentelemetry.io/otel/exporters/prometheus"
	"go.opentelemetry.io/otel/metric"
	"go.opentelemetry.io/otel/propagation"
	sdkmetric "go.opentelemetry.io/otel/sdk/metric"
	"go.opentelemetry.io/otel/sdk/resource"
	sdktrace "go.opentelemetry.io/otel/sdk/trace"
	"go.opentelemetry.io/otel/trace"
)

const scope = "github.com/imjasonh/playground/cloudrun-sqlite"

// Histogram names. Cloud Monitoring calls each one
// workload.googleapis.com/NAME, and /metrics calls it NAME with dots
// replaced by underscores, plus _seconds.
const (
	// HTTPServer is a request's time in the server, labeled with its route.
	HTTPServer = "http.server"
	// StorePhase is one part of a read or write, labeled with its phase.
	StorePhase = "store.phase"
	// StoreWrite is a write from the call to its acknowledgement, labeled
	// with durable and result.
	StoreWrite = "store.write"
	// VFSPageRead is one SQLite page read through the VFS, labeled with
	// source: paged_in or cold.
	VFSPageRead = "vfs.page_read"
	// ReplicaOperation is one object-storage call, labeled with op.
	ReplicaOperation = "replica.operation"
)

var descriptions = map[string]string{
	HTTPServer:       "Time a request spent in the server, by route.",
	StorePhase:       "Time in one part of a read or write: read_wait, read_query, write_queue, tx, or flush.",
	StoreWrite:       "Time from a write's call to its acknowledgement. A durable write includes its upload.",
	VFSPageRead:      "Time for one SQLite page read through the VFS: paged_in from memory or the hydrated copy, or cold from the replica.",
	ReplicaOperation: "Time for one object-storage call: get, list, or put.",
}

// Buckets run from 1 µs, where a page read from memory lands, to 10 s, a
// stalled upload, with extra steps from 10 to 100 ms, where object-storage
// calls land. They are in seconds.
var buckets = []float64{
	0.000001, 0.0000025, 0.000005,
	0.00001, 0.000025, 0.00005,
	0.0001, 0.00025, 0.0005,
	0.001, 0.0025, 0.005,
	0.01, 0.015, 0.02, 0.03, 0.04, 0.05, 0.075,
	0.1, 0.15, 0.2, 0.3, 0.5, 0.75,
	1, 2, 5, 10,
}

var (
	histMu  sync.Mutex
	hists   = map[string]metric.Float64Histogram{}
	proj    string
	metrics atomic.Pointer[http.Handler]
)

// Start sets up the meter provider behind /metrics. On a Cloud Run service
// it also exports traces to Cloud Trace and metrics to Cloud Monitoring.
// The returned function flushes them. A setup failure disables that export
// and leaves the server running.
func Start(ctx context.Context, log *slog.Logger) func(context.Context) error {
	if log == nil {
		log = slog.New(slog.DiscardHandler)
	}
	res := resource.NewSchemaless(attribute.String("service.name", "cloudrun-sqlite"))
	var opts []sdkmetric.Option
	var shutdowns []func(context.Context) error

	reg := prometheus.NewRegistry()
	if exp, err := otelprom.New(otelprom.WithRegisterer(reg), otelprom.WithoutScopeInfo()); err != nil {
		log.Warn("prometheus exporter", "error", err)
	} else {
		opts = append(opts, sdkmetric.WithReader(exp))
		h := promhttp.HandlerFor(reg, promhttp.HandlerOpts{})
		metrics.Store(&h)
	}

	if os.Getenv("K_SERVICE") != "" {
		if projectID, err := projectID(ctx); err != nil {
			log.Warn("Cloud Monitoring and Cloud Trace disabled", "error", err)
		} else {
			proj = projectID
			if detected, err := resource.New(ctx,
				resource.WithDetectors(gcp.NewDetector()),
				resource.WithAttributes(attribute.String("service.name", "cloudrun-sqlite")),
			); err != nil {
				log.Warn("telemetry resource", "error", err)
			} else {
				res = detected
			}
			if exp, err := texporter.New(texporter.WithProjectID(projectID)); err != nil {
				log.Warn("trace exporter", "error", err)
			} else {
				tp := sdktrace.NewTracerProvider(
					sdktrace.WithBatcher(exp),
					sdktrace.WithResource(res),
					sdktrace.WithSampler(sdktrace.AlwaysSample()),
				)
				otel.SetTracerProvider(tp)
				otel.SetTextMapPropagator(cloudTracePropagator{})
				shutdowns = append(shutdowns, tp.Shutdown)
			}
			if exp, err := mexporter.New(mexporter.WithProjectID(projectID)); err != nil {
				log.Warn("metric exporter", "error", err)
			} else {
				opts = append(opts, sdkmetric.WithReader(sdkmetric.NewPeriodicReader(exp, sdkmetric.WithInterval(30*time.Second))))
			}
			log.Info("telemetry enabled", "project", projectID)
		}
	}

	mp := sdkmetric.NewMeterProvider(append(opts, sdkmetric.WithResource(res))...)
	otel.SetMeterProvider(mp)
	// Histograms made from an earlier provider would keep recording there.
	histMu.Lock()
	clear(hists)
	histMu.Unlock()
	shutdowns = append(shutdowns, mp.Shutdown)
	return func(ctx context.Context) error {
		var err error
		for _, fn := range shutdowns {
			err = errors.Join(err, fn(ctx))
		}
		return err
	}
}

func projectID(ctx context.Context) (string, error) {
	ctx, cancel := context.WithTimeout(ctx, 2*time.Second)
	defer cancel()
	return metadata.ProjectIDWithContext(ctx)
}

// Metrics serves the histograms in the Prometheus text format. Before
// Start, it serves nothing.
func Metrics() http.Handler {
	return http.HandlerFunc(func(w http.ResponseWriter, r *http.Request) {
		h := metrics.Load()
		if h == nil {
			http.Error(w, "metrics are not set up", http.StatusServiceUnavailable)
			return
		}
		(*h).ServeHTTP(w, r)
	})
}

// Span starts a span and returns a function that ends it. err == nil marks
// the span successful.
func Span(ctx context.Context, name string) (context.Context, func(error)) {
	ctx, sp := otel.Tracer(scope).Start(ctx, name)
	return ctx, func(err error) {
		if err != nil {
			sp.RecordError(err)
			sp.SetStatus(codes.Error, err.Error())
		}
		sp.End()
	}
}

// Measure records d on the histogram name. labels alternate keys and
// values.
func Measure(ctx context.Context, name string, d time.Duration, labels ...string) {
	h := histogram(name)
	if h == nil {
		return
	}
	attrs := make([]attribute.KeyValue, 0, len(labels)/2)
	for i := 0; i+1 < len(labels); i += 2 {
		attrs = append(attrs, attribute.String(labels[i], labels[i+1]))
	}
	h.Record(ctx, d.Seconds(), metric.WithAttributes(attrs...))
}

func histogram(name string) metric.Float64Histogram {
	histMu.Lock()
	defer histMu.Unlock()
	if h, ok := hists[name]; ok {
		return h
	}
	h, err := otel.Meter(scope).Float64Histogram(name,
		metric.WithDescription(descriptions[name]),
		metric.WithUnit("s"),
		metric.WithExplicitBucketBoundaries(buckets...),
	)
	if err != nil {
		return nil
	}
	hists[name] = h
	return h
}

// HTTP records one span and one histogram per request. Routes come from
// the ServeMux pattern, so /items/1 and /items/2 share a series.
func HTTP(next http.Handler) http.Handler {
	return http.HandlerFunc(func(w http.ResponseWriter, r *http.Request) {
		ctx := otel.GetTextMapPropagator().Extract(r.Context(), propagation.HeaderCarrier(r.Header))
		ctx, sp := otel.Tracer(scope).Start(ctx, "http.request")
		sw := &statusWriter{ResponseWriter: w, code: http.StatusOK}
		var route string
		start := time.Now()
		defer func() {
			if route == "" {
				route = "unmatched"
			}
			d := time.Since(start)
			sp.SetName(route)
			sp.SetAttributes(
				attribute.String("http.route", route),
				attribute.Int("http.status_code", sw.code),
			)
			if sw.code >= 500 {
				sp.SetStatus(codes.Error, http.StatusText(sw.code))
			}
			sp.End()
			Measure(ctx, HTTPServer, d, "route", route)
			if d < 200*time.Millisecond && sw.code < 500 {
				return
			}
			attrs := []any{"route", route, "status", sw.code, "duration_ms", float64(d.Microseconds()) / 1000}
			if sc := sp.SpanContext(); proj != "" && sc.IsValid() {
				attrs = append(attrs,
					"logging.googleapis.com/trace", "projects/"+proj+"/traces/"+sc.TraceID().String(),
					"logging.googleapis.com/spanId", sc.SpanID().String(),
				)
			}
			slog.Info("slow request", attrs...)
		}()
		next.ServeHTTP(sw, r.WithContext(ctx))
		route = r.Pattern
	})
}

type statusWriter struct {
	http.ResponseWriter
	code int
}

func (w *statusWriter) WriteHeader(code int) {
	w.code = code
	w.ResponseWriter.WriteHeader(code)
}

func (w *statusWriter) Unwrap() http.ResponseWriter { return w.ResponseWriter }

// cloudTracePropagator reads the X-Cloud-Trace-Context header Cloud Run
// sends: TRACE_ID/SPAN_ID;o=1. SPAN_ID is a decimal integer.
type cloudTracePropagator struct{}

func (cloudTracePropagator) Fields() []string { return []string{"X-Cloud-Trace-Context"} }

func (cloudTracePropagator) Inject(context.Context, propagation.TextMapCarrier) {}

func (cloudTracePropagator) Extract(ctx context.Context, carrier propagation.TextMapCarrier) context.Context {
	traceID, spanID, sampled, ok := parseCloudTrace(carrier.Get("X-Cloud-Trace-Context"))
	if !ok {
		return ctx
	}
	flags := trace.TraceFlags(0)
	if sampled {
		flags = trace.FlagsSampled
	}
	return trace.ContextWithRemoteSpanContext(ctx, trace.NewSpanContext(trace.SpanContextConfig{
		TraceID:    traceID,
		SpanID:     spanID,
		TraceFlags: flags,
		Remote:     true,
	}))
}

func parseCloudTrace(header string) (trace.TraceID, trace.SpanID, bool, bool) {
	var zeroID trace.TraceID
	var zeroSpan trace.SpanID
	idPart, rest, _ := strings.Cut(header, ";")
	traceHex, spanDec, ok := strings.Cut(idPart, "/")
	if !ok {
		return zeroID, zeroSpan, false, false
	}
	traceID, err := trace.TraceIDFromHex(traceHex)
	if err != nil {
		return zeroID, zeroSpan, false, false
	}
	n, err := strconv.ParseUint(spanDec, 10, 64)
	if err != nil {
		return zeroID, zeroSpan, false, false
	}
	var spanID trace.SpanID
	binary.BigEndian.PutUint64(spanID[:], n)
	sampled := false
	for _, field := range strings.Split(rest, ";") {
		if strings.TrimSpace(field) == "o=1" {
			sampled = true
		}
	}
	return traceID, spanID, sampled, true
}
