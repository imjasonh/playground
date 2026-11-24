// Package testtrace parents OpenTelemetry spans on the span of the Go test
// that starts them, when the span's context carries no span of its own.
//
// Install wraps a TracerProvider once, in TestMain. After that, a test
// doesn't need to call anything. The first time the test, or code it calls,
// starts a span from t.Context() or a context derived from it, testtrace
// starts a span for the test and parents the new span on it. testtrace names
// the test's span after the function that testing.tRunner called, and ends
// it once that context is done. A subtest gets its own span, a child of its
// parent test's span.
//
// Hook starts the test's span explicitly. Use it for the test's exact name,
// for a span that ends before the test returns, or for a test that never
// uses a cancelable context.
//
// Both paths bind the test to its goroutine with profiler labels, which the
// runtime copies into every goroutine that the goroutine starts. Spans that
// those goroutines start are children of the test's span too, and parallel
// tests don't share a parent.
//
// A span whose context already carries a valid span context keeps that
// parent. The binding doesn't reach a goroutine whose profiler labels code
// under test replaces (with pprof.Do or pprof.SetGoroutineLabels), or a
// goroutine that the runtime starts, such as a time.AfterFunc callback.
package testtrace

import (
	"context"
	"runtime"
	"runtime/pprof"
	"strings"
	"sync"
	"testing"
	"unsafe"

	"go.opentelemetry.io/otel"
	"go.opentelemetry.io/otel/attribute"
	"go.opentelemetry.io/otel/codes"
	"go.opentelemetry.io/otel/trace"
	"go.opentelemetry.io/otel/trace/embedded"
)

// LabelKey is the profiler label that a bound goroutine carries. Its value
// is the name of the test's span, and CPU profiles that the test binary
// writes include it.
const LabelKey = "otel.test"

const instrumentationName = "github.com/imjasonh/playground/testtrace"

// A binding ties a test to the context that holds the test's span.
type binding struct {
	ctx context.Context // pasta:ignore go_context_field (the binding holds the test span's context)
	// fn is the function that testing.tRunner called for the test, so a
	// subtest, which inherits its parent's goroutine labels, can tell that
	// the inherited binding isn't its own.
	fn string
}

// bindings maps two kinds of keys to a binding: the profiler-label pointer
// of a bound goroutine, and the Done channel of the context that the test
// was bound from. The binding's context holds the labels, so a label
// pointer can't be reused while its entry exists.
var bindings sync.Map // map[unsafe.Pointer | <-chan struct{}]binding

// inherits records, by goroutine label and Done channel, the contexts for
// which a bound goroutine uses its inherited binding, so that a goroutine
// that starts many spans from such a context walks its stack only once.
// The cost is that if a goroutine that a subtest started uses the
// subtest's t.Context() before the subtest itself does, the subtest's spans
// parent on its parent test's span instead of on a span of its own.
var inherits sync.Map // map[inheritKey]struct{}

type inheritKey struct {
	label unsafe.Pointer
	done  <-chan struct{}
}

// bindMu serializes automatic binding, so two goroutines that bind the same
// context don't both start a span for it.
var bindMu sync.Mutex

func load(key any) (binding, bool) {
	v, ok := bindings.Load(key)
	if !ok {
		return binding{}, false
	}
	return v.(binding), true
}

// parent returns the context holding the span that a span started from ctx
// should be a child of, binding the running test first if it isn't bound.
func (p *tracerProvider) parent(ctx context.Context) (context.Context, bool) {
	done := ctx.Done()
	if done != nil {
		if b, ok := load(done); ok {
			return b.ctx, true
		}
	}
	label := getProfLabel()
	inherited, bound := load(label)
	if done == nil {
		return inherited.ctx, bound
	}
	key := inheritKey{label, done}
	if bound {
		if _, ok := inherits.Load(key); ok {
			return inherited.ctx, true
		}
	}
	if fn, ok := runningTest(); ok && (!bound || inherited.fn != fn) {
		return p.bind(ctx, fn, inherited.ctx), true
	}
	if bound {
		if _, loaded := inherits.LoadOrStore(key, struct{}{}); !loaded {
			context.AfterFunc(ctx, func() { inherits.Delete(key) })
		}
	}
	return inherited.ctx, bound
}

// bind starts a span named fn, as a child of parentCtx's span if parentCtx
// isn't nil, labels the calling goroutine with it, and ends the span once
// ctx is done. A context.AfterFunc callback ends the span, so the span can
// end a moment after ctx is canceled. bind returns the context that holds
// the new span.
func (p *tracerProvider) bind(ctx context.Context, fn string, parentCtx context.Context) context.Context {
	bindMu.Lock()
	defer bindMu.Unlock()
	done := ctx.Done()
	if b, ok := load(done); ok {
		return b.ctx
	}
	startCtx := ctx
	if parentCtx != nil {
		startCtx = trace.ContextWithSpan(ctx, trace.SpanFromContext(parentCtx))
	}
	testCtx, span := p.wrapped.Tracer(instrumentationName).Start(startCtx, fn,
		trace.WithAttributes(attribute.String("code.function.name", fn)))
	testCtx = pprof.WithLabels(testCtx, pprof.Labels(LabelKey, fn))
	pprof.SetGoroutineLabels(testCtx)
	label := getProfLabel()
	b := binding{ctx: testCtx, fn: fn}
	bindings.Store(done, b)
	bindings.Store(label, b)
	context.AfterFunc(ctx, func() {
		bindings.CompareAndDelete(done, b)
		bindings.CompareAndDelete(label, b)
		span.End()
	})
	return testCtx
}

// runningTest returns the function that testing.tRunner called on the
// calling goroutine's stack, and false if the stack doesn't reach tRunner:
// in a goroutine that the test started, and in a benchmark. The function is
// the outermost frame below tRunner outside packages testing, reflect,
// runtime, and testtrace. That is the test or subtest function, the
// function a t.Cleanup call registered, or the function a fuzz target
// passes to F.Fuzz.
func runningTest() (string, bool) {
	pc := make([]uintptr, 32)
	for {
		n := runtime.Callers(2, pc)
		if n < len(pc) {
			pc = pc[:n]
			break
		}
		pc = make([]uintptr, len(pc)*2)
	}
	var name string
	frames := runtime.CallersFrames(pc)
	for {
		f, more := frames.Next()
		if f.Function == "testing.tRunner" {
			return name, name != ""
		}
		if !internalFrame(f.Function) {
			name = f.Function
		}
		if !more {
			return "", false
		}
	}
}

func internalFrame(fn string) bool {
	for _, prefix := range []string{"testing.", "reflect.", "runtime.", instrumentationName + "."} {
		if strings.HasPrefix(fn, prefix) {
			return true
		}
	}
	return false
}

// WrapTracerProvider returns a TracerProvider whose tracers parent spans
// that start with no span in their context on the span of the bound test.
// Pass the result to code that takes a TracerProvider. To wrap the global
// provider, call Install instead.
//
// WrapTracerProvider panics outside a test binary, because every span
// start through the result can walk the call stack.
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

// Hook starts a span named t.Name(), binds it to the calling goroutine and
// to the goroutines that goroutine starts later, and returns t.Context()
// with the span. When t finishes, a t.Cleanup function ends the span, sets
// an error status if t failed, and removes the binding.
//
// A test doesn't need Hook for its spans to get a parent. Call Hook when:
//
//   - The span needs the test's name, including a subtest's "Parent/sub"
//     form, rather than the name of a Go function.
//   - The span must be ended and exported by the time the test's cleanups
//     finish. The automatic path ends its span from a context.AfterFunc
//     callback, which runs on a new goroutine.
//   - The span needs an error status when the test fails.
//   - The test never passes a cancelable context to traced code.
//
// Call Hook from the goroutine that runs the test, after t.Parallel. If the
// test is a subtest of a bound test, its span is a child of the parent
// test's span. Hook fails t if Install hasn't wrapped the global
// TracerProvider.
func Hook(t testing.TB) context.Context {
	t.Helper()
	p, ok := otel.GetTracerProvider().(*tracerProvider)
	if !ok {
		t.Fatal("testtrace: Hook needs testtrace.Install(tp) in TestMain")
	}
	// Start from the wrapped tracer: going through tracer.Start would bind
	// t.Context() automatically and make this span a child of that one.
	startCtx := t.Context()
	if parent, ok := load(getProfLabel()); ok {
		startCtx = trace.ContextWithSpan(startCtx, trace.SpanFromContext(parent.ctx))
	}
	ctx, span := p.wrapped.Tracer(instrumentationName).Start(startCtx, t.Name(),
		trace.WithAttributes(attribute.String("test.case.name", t.Name())))
	ctx = pprof.WithLabels(ctx, pprof.Labels(LabelKey, t.Name()))
	pprof.SetGoroutineLabels(ctx)

	fn, _ := runningTest()
	b := binding{ctx: ctx, fn: fn}
	label, done := getProfLabel(), t.Context().Done()
	bindings.Store(label, b)
	bindings.Store(done, b)
	t.Cleanup(func() {
		bindings.CompareAndDelete(label, b)
		bindings.CompareAndDelete(done, b)
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
		if parent, ok := t.provider.parent(ctx); ok {
			ctx = trace.ContextWithSpan(ctx, trace.SpanFromContext(parent))
		}
	}
	return t.wrapped.Start(ctx, name, opts...)
}
