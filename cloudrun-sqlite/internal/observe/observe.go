// Package observe records how long the server spends in HTTP, SQLite, and
// replica storage. On Cloud Run it also exports spans to Cloud Trace and
// histograms to Cloud Monitoring. Elsewhere the spans are dropped and the
// in-process /stats histograms are the record.
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
	"time"

	"cloud.google.com/go/compute/metadata"
	mexporter "github.com/GoogleCloudPlatform/opentelemetry-operations-go/exporter/metric"
	texporter "github.com/GoogleCloudPlatform/opentelemetry-operations-go/exporter/trace"
	"go.opentelemetry.io/contrib/detectors/gcp"
	"go.opentelemetry.io/otel"
	"go.opentelemetry.io/otel/attribute"
	"go.opentelemetry.io/otel/codes"
	"go.opentelemetry.io/otel/metric"
	"go.opentelemetry.io/otel/propagation"
	sdkmetric "go.opentelemetry.io/otel/sdk/metric"
	"go.opentelemetry.io/otel/sdk/resource"
	sdktrace "go.opentelemetry.io/otel/sdk/trace"
	"go.opentelemetry.io/otel/trace"
)

const scope = "github.com/imjasonh/playground/cloudrun-sqlite"

// Buckets cover the 5 ms to 5 s range the replica calls and HTTP handlers
// actually land in, so Cloud Monitoring can show a median near 20 ms.
var buckets = []float64{0.005, 0.01, 0.02, 0.05, 0.1, 0.2, 0.5, 1, 2, 5}

var (
	histMu sync.Mutex
	hists  = map[string]metric.Float64Histogram{}
	proj   string
)

// Start exports traces and metrics when this process is a Cloud Run
// service. The returned function flushes them. A setup failure disables
// export and leaves the server running.
func Start(ctx context.Context, log *slog.Logger) func(context.Context) error {
	noop := func(context.Context) error { return nil }
	if os.Getenv("K_SERVICE") == "" || log == nil {
		return noop
	}
	mctx, cancel := context.WithTimeout(ctx, 2*time.Second)
	defer cancel()
	projectID, err := metadata.ProjectIDWithContext(mctx)
	if err != nil {
		log.Warn("telemetry disabled", "error", err)
		return noop
	}
	proj = projectID

	res, err := resource.New(ctx,
		resource.WithDetectors(gcp.NewDetector()),
		resource.WithAttributes(attribute.String("service.name", "cloudrun-sqlite")),
	)
	if err != nil {
		log.Warn("telemetry resource", "error", err)
		res = resource.Default()
	}

	var shutdowns []func(context.Context) error
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
		reader := sdkmetric.NewPeriodicReader(exp, sdkmetric.WithInterval(30*time.Second))
		mp := sdkmetric.NewMeterProvider(sdkmetric.WithReader(reader), sdkmetric.WithResource(res))
		otel.SetMeterProvider(mp)
		shutdowns = append(shutdowns, mp.Shutdown)
	}
	log.Info("telemetry enabled", "project", projectID)
	return func(ctx context.Context) error {
		var err error
		for _, fn := range shutdowns {
			err = errors.Join(err, fn(ctx))
		}
		return err
	}
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

// Measure records d on the histogram name, labeled with key=val.
func Measure(ctx context.Context, name, key, val string, d time.Duration) {
	h := histogram(name)
	if h == nil {
		return
	}
	h.Record(ctx, d.Seconds(), metric.WithAttributes(attribute.String(key, val)))
}

func histogram(name string) metric.Float64Histogram {
	histMu.Lock()
	defer histMu.Unlock()
	if h, ok := hists[name]; ok {
		return h
	}
	h, err := otel.Meter(scope).Float64Histogram(name,
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
			Measure(ctx, "http.server", "route", route, d)
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
