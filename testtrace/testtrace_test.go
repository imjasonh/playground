package testtrace_test

import (
	"context"
	"os"
	"runtime"
	"strconv"
	"strings"
	"sync"
	"testing"
	"time"

	"go.opentelemetry.io/otel"
	sdktrace "go.opentelemetry.io/otel/sdk/trace"
	"go.opentelemetry.io/otel/sdk/trace/tracetest"
	"go.opentelemetry.io/otel/trace"

	"github.com/imjasonh/playground/testtrace"
)

var exporter = tracetest.NewInMemoryExporter()

func TestMain(m *testing.M) {
	tp := sdktrace.NewTracerProvider(sdktrace.WithSyncer(exporter))
	testtrace.Install(tp)
	code := m.Run()
	_ = tp.Shutdown(context.Background()) // pasta:ignore use_t_context — TestMain has no t
	os.Exit(code)
}

// appTracer stands in for a package-level tracer in code under test.
var appTracer = otel.Tracer("app")

// detachedWork starts a span from context.Background(), the way code that
// doesn't take a context does.
func detachedWork(name string) {
	_, span := appTracer.Start(context.Background(), name) // pasta:ignore use_t_context — the detached context is under test
	span.End()
}

func spansNamed(name string) []tracetest.SpanStub {
	var found []tracetest.SpanStub
	for _, s := range exporter.GetSpans() {
		if s.Name == name {
			found = append(found, s)
		}
	}
	return found
}

// span returns the one exported span named name.
func span(t testing.TB, name string) tracetest.SpanStub {
	t.Helper()
	found := spansNamed(name)
	if len(found) != 1 {
		t.Fatalf("got %d spans named %q, want 1", len(found), name)
	}
	return found[0]
}

// waitForSpans polls until f returns true, or fails t after two seconds.
// The automatic binding path ends a root span from a context.AfterFunc
// callback, which the context package always runs on a new goroutine, so
// that span can be exported slightly after the subtest that triggered it
// returns. Hook, by contrast, ends its span synchronously from t.Cleanup,
// so tests that use Hook don't need this.
func waitForSpans(t testing.TB, f func() bool) {
	t.Helper()
	deadline := time.Now().Add(2 * time.Second)
	for !f() {
		if time.Now().After(deadline) {
			t.Fatal("timed out waiting for the automatic path to export a span")
		}
		time.Sleep(time.Millisecond)
	}
}

// parentOf returns the one exported span whose SpanID matches child's
// parent. Unlike looking a span up by name, this holds even when two spans
// share a name, which happens for automatically bound root spans, since
// testtrace names them after the call site rather than the test name, and
// two tests can share a call site (for example, a shared test helper).
func parentOf(t testing.TB, child tracetest.SpanStub) tracetest.SpanStub {
	t.Helper()
	if !child.Parent.IsValid() {
		t.Fatalf("%q has no parent", child.Name)
	}
	var parent tracetest.SpanStub
	waitForSpans(t, func() bool {
		for _, s := range exporter.GetSpans() {
			if s.SpanContext.SpanID() == child.Parent.SpanID() {
				parent = s
				return true
			}
		}
		return false
	})
	return parent
}

func assertChild(t testing.TB, child, parent tracetest.SpanStub) {
	t.Helper()
	if got, want := child.Parent.SpanID(), parent.SpanContext.SpanID(); got != want {
		t.Errorf("%q parent = %s, want %q (%s)", child.Name, got, parent.Name, want)
	}
	if got, want := child.SpanContext.TraceID(), parent.SpanContext.TraceID(); got != want {
		t.Errorf("%q trace = %s, want %s", child.Name, got, want)
	}
}

// hooked runs f as a subtest that calls Hook, and returns the name of the
// subtest's span once the subtest and its cleanups finish.
func hooked(t *testing.T, name string, f func(t *testing.T, ctx context.Context)) string {
	t.Helper()
	var full string
	t.Run(name, func(t *testing.T) {
		full = t.Name()
		f(t, testtrace.Hook(t))
	})
	return full
}

func TestDetachedSpanOnTestGoroutine(t *testing.T) {
	test := hooked(t, "test", func(t *testing.T, ctx context.Context) {
		detachedWork(t.Name() + "/app")
	})
	assertChild(t, span(t, test+"/app"), span(t, test))
}

func TestDetachedSpanInBackgroundGoroutines(t *testing.T) {
	test := hooked(t, "test", func(t *testing.T, ctx context.Context) {
		var wg sync.WaitGroup
		wg.Go(func() {
			// A grandchild goroutine inherits the binding too.
			var inner sync.WaitGroup
			inner.Go(func() { detachedWork(t.Name() + "/grandchild") })
			inner.Wait()
			detachedWork(t.Name() + "/child")
		})
		wg.Wait()
	})
	parent := span(t, test)
	assertChild(t, span(t, test+"/child"), parent)
	assertChild(t, span(t, test+"/grandchild"), parent)
}

func TestParallelTestsKeepTheirOwnParent(t *testing.T) {
	const n = 32
	names := make([]string, n)
	t.Run("group", func(t *testing.T) {
		for i := range n {
			t.Run(strconv.Itoa(i), func(t *testing.T) {
				t.Parallel()
				names[i] = t.Name()
				testtrace.Hook(t)
				var wg sync.WaitGroup
				wg.Go(func() {
					time.Sleep(time.Millisecond)
					detachedWork(t.Name() + "/app")
				})
				detachedWork(t.Name() + "/inline")
				wg.Wait()
			})
		}
	})
	for _, name := range names {
		parent := span(t, name)
		assertChild(t, span(t, name+"/app"), parent)
		assertChild(t, span(t, name+"/inline"), parent)
	}
}

func TestSubtestSpanIsChildOfParentTest(t *testing.T) {
	var sub string
	test := hooked(t, "parent", func(t *testing.T, ctx context.Context) {
		sub = hooked(t, "sub", func(t *testing.T, ctx context.Context) {
			detachedWork(t.Name() + "/app")
		})
	})
	assertChild(t, span(t, sub), span(t, test))
	assertChild(t, span(t, sub+"/app"), span(t, sub))
}

func TestExplicitParentWins(t *testing.T) {
	var name string
	test := hooked(t, "test", func(t *testing.T, ctx context.Context) {
		name = t.Name()
		ctx, outer := appTracer.Start(ctx, name+"/outer")
		_, inner := appTracer.Start(ctx, name+"/inner")
		inner.End()
		outer.End()

		_, root := appTracer.Start(context.Background(), name+"/root", trace.WithNewRoot()) // pasta:ignore use_t_context — the detached context is under test
		root.End()
	})
	assertChild(t, span(t, name+"/outer"), span(t, test))
	assertChild(t, span(t, name+"/inner"), span(t, name+"/outer"))
	if root := span(t, name+"/root"); root.Parent.IsValid() {
		t.Errorf("WithNewRoot span has parent %s", root.Parent.SpanID())
	}
}

func TestGoroutineOutlivingTestIsNotStitched(t *testing.T) {
	release := make(chan struct{})
	done := make(chan struct{})
	var name string
	hooked(t, "test", func(t *testing.T, ctx context.Context) {
		name = t.Name()
		go func() {
			<-release
			detachedWork(name + "/late")
			close(done)
		}()
	})
	close(release)
	<-done
	if late := span(t, name+"/late"); late.Parent.IsValid() {
		t.Errorf("span after the test ended has parent %s", late.Parent.SpanID())
	}
}

func TestUnhookedTestIsNotStitched(t *testing.T) {
	detachedWork(t.Name() + "/app")
	if s := span(t, t.Name()+"/app"); s.Parent.IsValid() {
		t.Errorf("span in an unhooked test has parent %s", s.Parent.SpanID())
	}
}

func TestHookReturnsContextWithTestSpan(t *testing.T) {
	var got trace.SpanContext
	test := hooked(t, "test", func(t *testing.T, ctx context.Context) {
		got = trace.SpanContextFromContext(ctx)
	})
	if want := span(t, test).SpanContext; !got.Equal(want) {
		t.Errorf("Hook context span = %v, want %v", got, want)
	}
}

func TestWrapTracerProviderIsIdempotent(t *testing.T) {
	w := otel.GetTracerProvider()
	if got := testtrace.WrapTracerProvider(w); got != w {
		t.Errorf("WrapTracerProvider wrapped a wrapped provider again")
	}
}

// goroutineID parses the goroutine ID from runtime.Stack, as a lookup keyed
// by goroutine ID has to.
func goroutineID() int64 {
	var buf [64]byte
	n := runtime.Stack(buf[:], false)
	id, _ := strconv.ParseInt(strings.Fields(strings.TrimPrefix(string(buf[:n]), "goroutine "))[0], 10, 64)
	return id
}

// autoRun runs f as a subtest that uses t.Context() but never calls Hook,
// and returns the subtest's own name, for spans f names itself. The
// subtest's t.Context() is canceled, and so its automatic root span is
// ended and exported, by the time autoRun returns.
func autoRun(t *testing.T, name string, f func(t *testing.T, ctx context.Context)) (subName string) {
	t.Helper()
	t.Run(name, func(t *testing.T) {
		subName = t.Name()
		f(t, t.Context())
	})
	return subName
}

// TestAutomaticBindingWithoutHook covers the zero-touch path: the test
// never calls Hook, but it passes t.Context() to traced code, which is
// enough to start and parent a span on the test.
func TestAutomaticBindingWithoutHook(t *testing.T) {
	sub := autoRun(t, "direct", func(t *testing.T, ctx context.Context) {
		detachedWorkWithContext(ctx, t.Name()+"/direct")
	})
	root := parentOf(t, span(t, sub+"/direct"))
	if root.EndTime.IsZero() {
		t.Errorf("automatic root span %q never ended", root.Name)
	}
}

// TestAutomaticBindingThroughAppCode covers passing t.Context() into a
// helper that starts the span, not the test body itself: the stack walk
// has to see through that indirection.
func TestAutomaticBindingThroughAppCode(t *testing.T) {
	sub := autoRun(t, "through-app-code", func(t *testing.T, ctx context.Context) {
		func() { // an extra call frame, standing in for application code
			detachedWorkWithContext(ctx, t.Name()+"/via-helper")
		}()
	})
	parentOf(t, span(t, sub+"/via-helper")) // only fails if there's no parent at all
}

// TestAutomaticBindingCoversBackgroundGoroutines checks that, once the
// automatic path binds the test's goroutine, a goroutine the test starts
// afterward inherits the binding even though it uses context.Background(),
// never t.Context(), and that it gets the same root as a call made directly
// on the test's own goroutine.
func TestAutomaticBindingCoversBackgroundGoroutines(t *testing.T) {
	sub := autoRun(t, "background", func(t *testing.T, ctx context.Context) {
		detachedWorkWithContext(ctx, t.Name()+"/first") // triggers the automatic bind
		var wg sync.WaitGroup
		wg.Go(func() { detachedWork(t.Name() + "/background") })
		wg.Wait()
	})
	assertChild(t, span(t, sub+"/background"), parentOf(t, span(t, sub+"/first")))
}

// TestAutomaticBindingParallelTestsKeepTheirOwnParent is the automatic-path
// counterpart of TestParallelTestsKeepTheirOwnParent: no test calls Hook.
// Every parallel subtest shares the same closure, so testtrace's stack walk
// gives their automatic root spans the same name; the test instead checks
// that no two parallel subtests' app spans share a parent span.
func TestAutomaticBindingParallelTestsKeepTheirOwnParent(t *testing.T) {
	const n = 16
	names := make([]string, n)
	t.Run("group", func(t *testing.T) {
		for i := range n {
			t.Run(strconv.Itoa(i), func(t *testing.T) {
				t.Parallel()
				names[i] = t.Name()
				detachedWorkWithContext(t.Context(), t.Name()+"/app")
			})
		}
	})
	parents := map[trace.SpanID]string{}
	for _, name := range names {
		s := span(t, name+"/app")
		if !s.Parent.IsValid() {
			t.Fatalf("%q has no parent", name+"/app")
		}
		if other, ok := parents[s.Parent.SpanID()]; ok {
			t.Errorf("%q and %q share a parent span", name, other)
		}
		parents[s.Parent.SpanID()] = name
	}
}

// FuzzAutomaticBinding checks that the automatic path covers a fuzz target
// too: testing.F.Fuzz runs each corpus entry with go tRunner(t, ...), the
// same way a subtest does, so it needs no special case. `go test`, with no
// -fuzz flag, runs the seed corpus below as a regular subtest, synchronously
// within f.Fuzz, so the check below runs after that subtest has returned.
func FuzzAutomaticBinding(f *testing.F) {
	f.Add("seed")
	f.Fuzz(func(t *testing.T, s string) {
		detachedWorkWithContext(t.Context(), t.Name()+"/inner")
	})
	s := span(f, "FuzzAutomaticBinding/seed#0/inner")
	parentOf(f, s) // only fails if there's no parent at all
}

// TestWithoutTContextStaysUnbound documents the trade-off: a test that
// never touches t.Context() anywhere gets no automatic span, because
// testtrace has no context whose cancellation it can use to end one.
func TestWithoutTContextStaysUnbound(t *testing.T) {
	detachedWork(t.Name() + "/app")
	if s := span(t, t.Name()+"/app"); s.Parent.IsValid() {
		t.Errorf("span in a test that never touched t.Context() has parent %s", s.Parent.SpanID())
	}
}

// TestAutomaticRootSpanName checks that the automatic path names a root
// span after the calling function, using a call site that no other test in
// this file shares, so the name is unique in the exporter.
func TestAutomaticRootSpanName(t *testing.T) {
	var want, appName string
	t.Run("sub", func(t *testing.T) {
		want = runningTestName(t)
		appName = t.Name() + "/app"
		detachedWorkWithContext(t.Context(), appName)
	})
	root := parentOf(t, span(t, appName))
	if root.Name != want {
		t.Errorf("automatic root span name = %q, want %q", root.Name, want)
	}
}

// TestHookDoesNotCreateASpuriousAutomaticRoot guards against a real bug
// this package once had: Hook starts its own span from t.Context(), and
// since that context has no span yet, the automatic path could mistake
// Hook's own call for an ordinary traced call and wrap Hook's span in an
// extra, unwanted root.
func TestHookDoesNotCreateASpuriousAutomaticRoot(t *testing.T) {
	before := len(exporter.GetSpans())
	var name string
	t.Run("sub", func(t *testing.T) {
		name = t.Name()
		testtrace.Hook(t)
	})
	waitForSpans(t, func() bool { return len(exporter.GetSpans()) > before })
	if got := len(exporter.GetSpans()) - before; got != 1 {
		t.Fatalf("got %d spans from a single Hook call, want exactly 1", got)
	}
	if s := span(t, name); s.Parent.IsValid() {
		t.Errorf("Hook's own span has parent %s, want a root span", s.Parent.SpanID())
	}
}

// TestHookStillRegistersIdentityForOtherGoroutines checks that Hook's
// binding also resolves when a goroutine the test didn't start, but that
// received the literal t.Context() value (over a channel, say), uses it.
func TestHookStillRegistersIdentityForOtherGoroutines(t *testing.T) {
	var ctx context.Context
	test := hooked(t, "test", func(t *testing.T, c context.Context) {
		ctx = c
	})
	ch := make(chan struct{})
	go func() {
		defer close(ch)
		detachedWorkWithContext(ctx, test+"/unlabeled-goroutine")
	}()
	<-ch
	assertChild(t, span(t, test+"/unlabeled-goroutine"), span(t, test))
}

// runningTestName returns the function name testtrace's stack walk would
// attach to a span that t's own goroutine starts right now, mirroring
// runningTest's own frame-skipping rule, so tests can find the span that
// the automatic path created without hardcoding its naming scheme.
func runningTestName(t *testing.T) string {
	t.Helper()
	pc := make([]uintptr, 32)
	n := runtime.Callers(2, pc)
	frames := runtime.CallersFrames(pc[:n])
	var name string
	for {
		f, more := frames.Next()
		if f.Function == "testing.tRunner" {
			return name
		}
		name = f.Function
		if !more {
			t.Fatal("runningTestName: testing.tRunner not found on the stack")
		}
	}
}

// detachedWorkWithContext is like detachedWork, but takes the context to
// start the span from, so a test can pass t.Context() explicitly.
func detachedWorkWithContext(ctx context.Context, name string) {
	_, span := appTracer.Start(ctx, name)
	span.End()
}

func BenchmarkStartDetached(b *testing.B) {
	testtrace.Hook(b)
	b.Run("testtrace", func(b *testing.B) {
		tr := testtrace.WrapTracerProvider(sdktrace.NewTracerProvider()).Tracer("bench")
		if _, s := tr.Start(b.Context(), "x"); !s.(sdktrace.ReadOnlySpan).Parent().IsValid() {
			b.Fatal("benchmark span isn't stitched to the benchmark span")
		}
		for b.Loop() {
			_, s := tr.Start(b.Context(), "x")
			s.End()
		}
	})
	b.Run("sdk-only", func(b *testing.B) {
		sdk := sdktrace.NewTracerProvider().Tracer("bench")
		for b.Loop() {
			_, s := sdk.Start(b.Context(), "x")
			s.End()
		}
	})
	b.Run("goroutine-id-lookup", func(b *testing.B) {
		for b.Loop() {
			_ = goroutineID()
		}
	})
}
