// Package testtrace parents OpenTelemetry spans that code under test starts
// with a detached context, such as context.Background(), on the span of the
// test that runs that code.
//
// Install wraps a TracerProvider once, in TestMain. Hook starts a span for a
// test and binds it to the test's goroutine. The binding uses the goroutine's
// profiler labels, which the runtime copies into every goroutine that the
// test's goroutine starts. Spans that background goroutines start therefore
// link to the test too, and parallel tests don't share a parent.
//
// A span keeps its parent when its context already carries a valid span
// context. The binding is lost when code under test replaces the goroutine's
// profiler labels (pprof.Do or pprof.SetGoroutineLabels) with a context that
// doesn't come from the test, and in goroutines that the runtime starts for
// time.AfterFunc.
package testtrace

import (
	"context"
	"runtime/pprof"
	"sync"
	"testing"

	"go.opentelemetry.io/otel"
	"go.opentelemetry.io/otel/attribute"
	"go.opentelemetry.io/otel/codes"
	"go.opentelemetry.io/otel/trace"
	"go.opentelemetry.io/otel/trace/embedded"
)

// LabelKey is the profiler label that Hook sets to the test name. It also
// shows up in CPU profiles that the test binary writes.
const LabelKey = "otel.test"

const instrumentationName = "github.com/imjasonh/playground/testtrace"

// bindings maps a profiler label pointer to the context that holds the test
// span. The map holds the context, and the context holds the labels, so a
// pointer can't be reused while its entry exists.
var bindings sync.Map // map[unsafe.Pointer]context.Context

// boundContext returns the test context bound to the calling goroutine.
func boundContext() (context.Context, bool) {
	p := getProfLabel()
	if p == nil {
		return nil, false
	}
	v, ok := bindings.Load(p)
	if !ok {
		return nil, false
	}
	return v.(context.Context), true
}

// WrapTracerProvider returns a TracerProvider whose tracers parent detached
// spans on the span of the bound test. Pass the result to code that takes a
// TracerProvider. To wrap the global provider, call Install instead.
//
// WrapTracerProvider panics outside a test binary, so production code can't
// pay for the lookup.
func WrapTracerProvider(tp trace.TracerProvider) trace.TracerProvider {
	if !testing.Testing() {
		panic("testtrace: WrapTracerProvider called outside a test binary")
	}
	if p, ok := tp.(*tracerProvider); ok {
		return p
	}
	return &tracerProvider{wrapped: tp}
}

// Install wraps tp with WrapTracerProvider, sets the result as the global
// TracerProvider, and returns it. Call Install in TestMain before any test
// runs and before any other call to otel.SetTracerProvider. Tracers that
// packages got from otel.Tracer before that first call forward to the
// provider it sets, and to no later one.
func Install(tp trace.TracerProvider) trace.TracerProvider {
	w := WrapTracerProvider(tp)
	otel.SetTracerProvider(w)
	return w
}

// Hook starts a span named after t, binds it to the calling goroutine and to
// the goroutines that the calling goroutine starts later, and returns
// t.Context() with the span. When t finishes, Hook ends the span, sets an
// error status if t failed, and removes the binding.
//
// Call Hook from the goroutine that runs the test, after t.Parallel. If the
// test is a subtest of a hooked test, its span is a child of the parent
// test's span. Hook fails t if Install hasn't wrapped the global
// TracerProvider.
func Hook(t testing.TB) context.Context {
	t.Helper()
	if _, ok := otel.GetTracerProvider().(*tracerProvider); !ok {
		t.Fatal("testtrace: Hook needs testtrace.Install(tp) in TestMain")
	}
	ctx, span := otel.Tracer(instrumentationName).Start(t.Context(), t.Name(),
		trace.WithAttributes(attribute.String("test.name", t.Name())))
	// Label the context that holds the span, so that the binding's context
	// keeps the label pointer alive.
	ctx = pprof.WithLabels(ctx, pprof.Labels(LabelKey, t.Name()))
	pprof.SetGoroutineLabels(ctx)
	key := getProfLabel()
	bindings.Store(key, ctx)

	t.Cleanup(func() {
		bindings.Delete(key)
		switch {
		case t.Failed():
			span.SetStatus(codes.Error, "test failed")
		case t.Skipped():
			span.SetAttributes(attribute.Bool("test.skipped", true))
		}
		span.End()
	})
	return ctx
}

type tracerProvider struct {
	embedded.TracerProvider
	wrapped trace.TracerProvider
}

func (p *tracerProvider) Tracer(name string, opts ...trace.TracerOption) trace.Tracer {
	return &tracer{wrapped: p.wrapped.Tracer(name, opts...)}
}

type tracer struct {
	embedded.Tracer
	wrapped trace.Tracer
}

func (t *tracer) Start(ctx context.Context, name string, opts ...trace.SpanStartOption) (context.Context, trace.Span) {
	if !trace.SpanContextFromContext(ctx).IsValid() {
		if testCtx, ok := boundContext(); ok {
			ctx = trace.ContextWithSpan(ctx, trace.SpanFromContext(testCtx))
		}
	}
	return t.wrapped.Start(ctx, name, opts...)
}
