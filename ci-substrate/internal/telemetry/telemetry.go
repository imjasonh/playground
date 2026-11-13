// Package telemetry wires the ci-substrate binaries to OpenTelemetry. Setup
// installs the global tracer and meter providers, exporting over OTLP to a
// collector, which forwards to Jaeger and Prometheus on kind and to Cloud
// Trace and Cloud Monitoring on GKE. ServerOptions and DialOptions trace
// and measure every gRPC call, and tie every call of one Bazel invocation
// into one trace (see InvocationSpanContext).
package telemetry

import (
	"context"
	"errors"
	"fmt"
	"log/slog"
	"os"

	"go.opentelemetry.io/contrib/instrumentation/runtime"
	"go.opentelemetry.io/otel"
	"go.opentelemetry.io/otel/exporters/otlp/otlpmetric/otlpmetricgrpc"
	"go.opentelemetry.io/otel/exporters/otlp/otlptrace/otlptracegrpc"
	"go.opentelemetry.io/otel/metric"
	"go.opentelemetry.io/otel/propagation"
	sdkmetric "go.opentelemetry.io/otel/sdk/metric"
	"go.opentelemetry.io/otel/sdk/resource"
	sdktrace "go.opentelemetry.io/otel/sdk/trace"
	semconv "go.opentelemetry.io/otel/semconv/v1.43.0"
	"go.opentelemetry.io/otel/trace"
)

// ScopeName is the instrumentation scope of every tracer and meter in this
// module, so a backend can select ci-substrate's own telemetry.
const ScopeName = "github.com/imjasonh/playground/ci-substrate"

// Tracer returns the module's tracer from the global provider.
func Tracer() trace.Tracer { return otel.Tracer(ScopeName) }

// Meter returns the module's meter from the global provider. Instruments
// made before Setup report through the provider Setup installs.
func Meter() metric.Meter { return otel.Meter(ScopeName) }

// Handle returns an instrument, sending err to the OpenTelemetry error
// handler. A meter that fails to make an instrument still returns a no-op
// one, so a bad instrument costs its data, not the program.
func Handle[T any](instrument T, err error) T {
	if err != nil {
		otel.Handle(err)
	}
	return instrument
}

// Setup installs global providers for service and returns the function that
// flushes and stops them.
//
// Each signal exports over OTLP/gRPC when OTEL_EXPORTER_OTLP_ENDPOINT, or
// that signal's OTEL_EXPORTER_OTLP_TRACES_ENDPOINT or
// OTEL_EXPORTER_OTLP_METRICS_ENDPOINT, is set, and is dropped otherwise.
// The exporters, the sampler, the metric interval, and the resource read
// the rest of the standard OTEL_* variables, so the collector address and
// the pod's identity (OTEL_RESOURCE_ATTRIBUTES) come from the manifest.
func Setup(ctx context.Context, service string) (func(context.Context) error, error) {
	res, err := resource.New(ctx,
		resource.WithAttributes(semconv.ServiceName(service)),
		resource.WithTelemetrySDK(),
		resource.WithFromEnv(),
	)
	if err != nil {
		return nil, fmt.Errorf("telemetry resource: %w", err)
	}
	otel.SetTextMapPropagator(propagation.NewCompositeTextMapPropagator(propagation.TraceContext{}, propagation.Baggage{}))

	var shutdowns []func(context.Context) error
	shutdown := func(ctx context.Context) error {
		var errs []error
		for _, f := range shutdowns {
			errs = append(errs, f(ctx))
		}
		return errors.Join(errs...)
	}

	topts := []sdktrace.TracerProviderOption{sdktrace.WithResource(res), sdktrace.WithIDGenerator(IDGenerator())}
	if exporting("TRACES") {
		exp, err := otlptracegrpc.New(ctx)
		if err != nil {
			return nil, fmt.Errorf("trace exporter: %w", err)
		}
		topts = append(topts, sdktrace.WithBatcher(exp))
	}
	tp := sdktrace.NewTracerProvider(topts...)
	otel.SetTracerProvider(tp)
	shutdowns = append(shutdowns, tp.Shutdown)

	mopts := []sdkmetric.Option{sdkmetric.WithResource(res)}
	if exporting("METRICS") {
		exp, err := otlpmetricgrpc.New(ctx)
		if err != nil {
			return nil, errors.Join(fmt.Errorf("metric exporter: %w", err), shutdown(ctx))
		}
		mopts = append(mopts, sdkmetric.WithReader(sdkmetric.NewPeriodicReader(exp)))
	}
	mp := sdkmetric.NewMeterProvider(mopts...)
	otel.SetMeterProvider(mp)
	shutdowns = append(shutdowns, mp.Shutdown)
	if err := runtime.Start(runtime.WithMeterProvider(mp)); err != nil {
		return nil, errors.Join(fmt.Errorf("runtime metrics: %w", err), shutdown(ctx))
	}

	inner := slog.Default().Handler()
	// slog's built-in handler writes through the log package, which
	// SetDefault points back at the new handler, so wrapping it recurses.
	if fmt.Sprintf("%T", inner) == "*slog.defaultHandler" {
		inner = slog.NewTextHandler(os.Stderr, nil)
	}
	slog.SetDefault(slog.New(traceHandler{inner: inner, project: os.Getenv("GOOGLE_CLOUD_PROJECT")}))
	return shutdown, nil
}

func exporting(signal string) bool {
	return os.Getenv("OTEL_EXPORTER_OTLP_ENDPOINT") != "" || os.Getenv("OTEL_EXPORTER_OTLP_"+signal+"_ENDPOINT") != ""
}
