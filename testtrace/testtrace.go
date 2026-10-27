// Package testtrace parents OpenTelemetry spans that code under test starts
// with a context that carries no span, such as t.Context() or
// context.Background(), on the span of the test that runs that code.
//
// Install wraps a TracerProvider once, in TestMain. From there, a test
// doesn't need to call anything: the first time the test, or code it calls,
// starts a span from t.Context() (or a context derived from it), testtrace
// starts a span for the test and parents that span on it, naming it after
// the calling function and ending it once t.Context() is done. Hook is
// still available for a test that wants the exact test name — including a
// subtest's "Parent/sub" form — a span that starts and ends synchronously,
// or linkage that doesn't depend on a context ever canceling.
//
// Both mechanisms bind the test to the calling goroutine with the
// goroutine's profiler labels, which the runtime copies into every goroutine
// that the test's goroutine starts. Spans that background goroutines start
// therefore link to the test too, and parallel tests don't share a parent.
//
// A span keeps its parent when its context already carries a valid span
// context. The binding is lost when code under test replaces the goroutine's
// profiler labels (pprof.Do or pprof.SetGoroutineLabels) with a context that
// doesn't come from the test, and in goroutines that the runtime starts for
// time.AfterFunc.
package testtrace

import (
	"context"
	"runtime"
	"runtime/pprof"
	"strings"
	"sync"
	"testing"

	"go.opentelemetry.io/otel"
	"go.opentelemetry.io/otel/attribute"
	"go.opentelemetry.io/otel/codes"
	"go.opentelemetry.io/otel/trace"
	"go.opentelemetry.io/otel/trace/embedded"
)

// LabelKey is the profiler label that a bound goroutine carries, set to the
// test name. It also shows up in CPU profiles that the test binary writes.
const LabelKey = "otel.test"

const instrumentationName = "github.com/imjasonh/playground/testtrace"

// bindings maps a bound goroutine's profiler-label pointer, and the exact
// context.Context value a lazily bound test first saw, to the context that
// holds the test's span. A binding's own context value keeps its label
// pointer alive, so the pointer can't be reused while the entry exists.
var bindings sync.Map // map[unsafe.Pointer|context.Context]context.Context

// boundContext returns the test context bound to the calling goroutine, or
// to key if key itself was bound directly (for example, a context that a
// test passed to code running on a goroutine the test didn't start).
func boundContext(key context.Context) (context.Context, bool) {
	if p := getProfLabel(); p != nil {
		if v, ok := bindings.Load(p); ok {
			return v.(context.Context), true
		}
	}
	if v, ok := bindings.Load(key); ok {
		return v.(context.Context), true
	}
	return nil, false
}

// bind starts a span named name as a child of ctx, labels the calling
// goroutine with it so that goroutines it starts inherit the binding, and
// arranges to end the span once ctx is done. Ending happens from a
// context.AfterFunc callback, so it can run slightly after ctx is actually
// canceled. It returns the context that holds the new span.
func bind(tracer trace.Tracer, ctx context.Context, name string) context.Context {
	testCtx, span := tracer.Start(ctx, name, trace.WithAttributes(attribute.String("test.name", name)))
	testCtx = pprof.WithLabels(testCtx, pprof.Labels(LabelKey, name))
	pprof.SetGoroutineLabels(testCtx)
	labelKey := getProfLabel()

	actual, loaded := bindings.LoadOrStore(ctx, testCtx)
	if loaded {
		// Another goroutine raced us to bind the same context; use its span
		// and discard ours.
		span.End()
		return actual.(context.Context)
	}
	bindings.Store(labelKey, testCtx)
	context.AfterFunc(ctx, func() {
		bindings.Delete(ctx)
		bindings.Delete(labelKey)
		span.End()
	})
	return testCtx
}

// runningTest returns the name of the test function running on the calling
// goroutine's stack, skipping over testtrace's own frames, and whether the
// stack reaches testing.tRunner. It returns ok == false in a goroutine the
// test already started (a fresh stack, with no tRunner frame) and in a
// benchmark or fuzz target, which don't run under tRunner.
func runningTest() (name string, ok bool) {
	pc := make([]uintptr, 32)
	for {
		n := runtime.Callers(2, pc)
		if n < len(pc) {
			pc = pc[:n]
			break
		}
		pc = make([]uintptr, len(pc)*2)
	}
	frames := runtime.CallersFrames(pc)
	for {
		f, more := frames.Next()
		if f.Function == "testing.tRunner" {
			return name, name != ""
		}
		if !strings.HasPrefix(f.Function, instrumentationName+".") {
			name = f.Function
		}
		if !more {
			return "", false
		}
	}
}

// WrapTracerProvider returns a TracerProvider whose tracers parent spans
// that start with no span in their context on the span of the bound test.
// Pass the result to code that takes a TracerProvider. To wrap the global
// provider, call Install instead.
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
// A test doesn't need to call Hook: the first time the test, or code it
// calls, starts a span from t.Context(), testtrace binds the test the same
// way, using the calling function's name, and ends that span from a
// context.AfterFunc callback once t.Context() is done. Call Hook instead
// when that name isn't good enough — it doesn't give a subtest's
// "Parent/sub" form — when the test wants its span to start before its
// first traced call, when the test's own context never gets canceled (so
// testtrace has nothing to end the span on), or when the test needs its
// span to be ended and exported by the time the test returns: a
// context.AfterFunc callback always runs on a new goroutine, so the
// automatic path's span can still be open for a moment after a subtest
// that triggered it returns, where Hook ends its span synchronously, from
// t.Cleanup.
//
// Call Hook from the goroutine that runs the test, after t.Parallel. If the
// test is a subtest of a hooked test, its span is a child of the parent
// test's span. Hook fails t if Install hasn't wrapped the global
// TracerProvider.
func Hook(t testing.TB) context.Context {
	t.Helper()
	p, ok := otel.GetTracerProvider().(*tracerProvider)
	if !ok {
		t.Fatal("testtrace: Hook needs testtrace.Install(tp) in TestMain")
	}
	// Apply the same parenting a plain Start call would get — in
	// particular, a subtest's own t.Context() carries no span of its own,
	// but its goroutine inherits its parent test's binding — while
	// starting from the real tracer directly, not the one otel.Tracer
	// would give back. Going through this package's own Start here would
	// also let the automatic path see t.Context() with no span yet and
	// bind to it first, making this span its child instead of a root.
	startCtx := t.Context()
	if parent, ok := boundContext(startCtx); ok {
		startCtx = trace.ContextWithSpan(startCtx, trace.SpanFromContext(parent))
	}
	ctx, span := p.wrapped.Tracer(instrumentationName).Start(startCtx, t.Name(),
		trace.WithAttributes(attribute.String("test.name", t.Name())))
	ctx = pprof.WithLabels(ctx, pprof.Labels(LabelKey, t.Name()))
	pprof.SetGoroutineLabels(ctx)
	key := getProfLabel()
	bindings.Store(key, ctx)
	bindings.Store(t.Context(), ctx)

	t.Cleanup(func() {
		bindings.Delete(key)
		bindings.Delete(t.Context())
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
	return &tracer{provider: p, wrapped: p.wrapped.Tracer(name, opts...)}
}

type tracer struct {
	embedded.Tracer
	provider *tracerProvider
	wrapped  trace.Tracer
}

func (t *tracer) Start(ctx context.Context, name string, opts ...trace.SpanStartOption) (context.Context, trace.Span) {
	if !trace.SpanContextFromContext(ctx).IsValid() {
		if testCtx, ok := boundContext(ctx); ok {
			ctx = trace.ContextWithSpan(ctx, trace.SpanFromContext(testCtx))
		} else if ctx.Done() != nil {
			if testName, ok := runningTest(); ok {
				testTracer := t.provider.wrapped.Tracer(instrumentationName)
				testCtx := bind(testTracer, ctx, testName)
				ctx = trace.ContextWithSpan(ctx, trace.SpanFromContext(testCtx))
			}
		}
	}
	return t.wrapped.Start(ctx, name, opts...)
}
