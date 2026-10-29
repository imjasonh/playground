package testtrace_test

import (
	"context"
	"flag"
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
// The automatic path ends the test's span from a context.AfterFunc
// callback on another goroutine, so the span can be exported after the
// subtest returns.
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

// parentOf returns the exported span that is child's parent, looked up by
// span ID, because automatic spans of tests that share a function share a
// name.
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
// subtest's span once the subtest and its cleanups finish. f uses
// t.Context(). A test that needs the span Hook returns calls Hook itself.
func hooked(t *testing.T, name string, f func(t *testing.T)) string {
	t.Helper()
	var full string
	t.Run(name, func(t *testing.T) {
		full = t.Name()
		testtrace.Hook(t)
		f(t)
	})
	return full
}

func TestDetachedSpanOnTestGoroutine(t *testing.T) {
	test := hooked(t, "test", func(t *testing.T) {
		detachedWork(t.Name() + "/app")
	})
	assertChild(t, span(t, test+"/app"), span(t, test))
}

func TestDetachedSpanInBackgroundGoroutines(t *testing.T) {
	test := hooked(t, "test", func(t *testing.T) {
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
	test := hooked(t, "parent", func(t *testing.T) {
		sub = hooked(t, "sub", func(t *testing.T) {
			detachedWork(t.Name() + "/app")
		})
	})
	assertChild(t, span(t, sub), span(t, test))
	assertChild(t, span(t, sub+"/app"), span(t, sub))
}

func TestExplicitParentWins(t *testing.T) {
	var name string
	test := hooked(t, "test", func(t *testing.T) {
		name = t.Name()
		ctx, outer := appTracer.Start(t.Context(), name+"/outer")
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
	hooked(t, "test", func(t *testing.T) {
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

func TestHookReturnsContextWithTestSpan(t *testing.T) {
	var got trace.SpanContext
	var test string
	t.Run("test", func(t *testing.T) {
		test = t.Name()
		got = trace.SpanContextFromContext(testtrace.Hook(t))
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

// autoRun runs f as a subtest without Hook and returns the subtest's name.
func autoRun(t *testing.T, name string, f func(t *testing.T)) (subName string) {
	t.Helper()
	t.Run(name, func(t *testing.T) {
		subName = t.Name()
		f(t)
	})
	return subName
}

// TestAutomaticBindingWithoutHook checks that passing t.Context() to traced
// code is enough to start the test's span and parent a span on it.
func TestAutomaticBindingWithoutHook(t *testing.T) {
	sub := autoRun(t, "direct", func(t *testing.T) {
		detachedWorkWithContext(t.Context(), t.Name()+"/direct")
	})
	root := parentOf(t, span(t, sub+"/direct"))
	if root.EndTime.IsZero() {
		t.Errorf("automatic root span %q never ended", root.Name)
	}
}

// TestAutomaticBindingThroughAppCode checks that the stack walk finds the
// test when a helper, not the test body, starts the span.
func TestAutomaticBindingThroughAppCode(t *testing.T) {
	sub := autoRun(t, "through-app-code", func(t *testing.T) {
		func() { // an extra call frame, standing in for application code
			detachedWorkWithContext(t.Context(), t.Name()+"/via-helper")
		}()
	})
	parentOf(t, span(t, sub+"/via-helper")) // only fails if there's no parent at all
}

// TestAutomaticBindingCoversBackgroundGoroutines checks that a goroutine
// the test starts after the automatic path binds it inherits the binding,
// even from context.Background().
func TestAutomaticBindingCoversBackgroundGoroutines(t *testing.T) {
	sub := autoRun(t, "background", func(t *testing.T) {
		detachedWorkWithContext(t.Context(), t.Name()+"/first") // triggers the automatic bind
		var wg sync.WaitGroup
		wg.Go(func() { detachedWork(t.Name() + "/background") })
		wg.Wait()
	})
	assertChild(t, span(t, sub+"/background"), parentOf(t, span(t, sub+"/first")))
}

// TestAutomaticBindingParallelTestsKeepTheirOwnParent is
// TestParallelTestsKeepTheirOwnParent without Hook. The subtests share one
// closure, so their spans share a name, and the test compares span IDs.
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

// FuzzAutomaticBinding checks that F.Fuzz, which runs each input with
// testing.tRunner, gets a span named after the function passed to F.Fuzz.
// Without -fuzz, F.Fuzz runs the seed corpus before it returns. With -fuzz,
// worker processes run the inputs, so this process exports no spans.
func FuzzAutomaticBinding(f *testing.F) {
	f.Add("seed")
	f.Fuzz(func(t *testing.T, s string) {
		detachedWorkWithContext(t.Context(), t.Name()+"/inner")
	})
	if flag.Lookup("test.fuzz").Value.String() != "" {
		return
	}
	root := parentOf(f, span(f, "FuzzAutomaticBinding/seed#0/inner"))
	if want := pkg + ".FuzzAutomaticBinding.func1"; root.Name != want {
		f.Errorf("fuzz span name = %q, want %q", root.Name, want)
	}
}

// TestWithoutTContextStaysUnbound checks that a test that never passes a
// cancelable context gets no span, because nothing would end it.
func TestWithoutTContextStaysUnbound(t *testing.T) {
	detachedWork(t.Name() + "/app")
	if s := span(t, t.Name()+"/app"); s.Parent.IsValid() {
		t.Errorf("span in a test that never touched t.Context() has parent %s", s.Parent.SpanID())
	}
}

// pkg is the import path of this test package, the prefix of the names
// that the automatic path gives spans.
const pkg = "github.com/imjasonh/playground/testtrace_test"

func TestAutomaticRootSpanName(t *testing.T) {
	var appName string
	t.Run("sub", func(t *testing.T) {
		appName = t.Name() + "/app"
		detachedWorkWithContext(t.Context(), appName)
	})
	root := parentOf(t, span(t, appName))
	if want := pkg + ".TestAutomaticRootSpanName.func1"; root.Name != want {
		t.Errorf("automatic root span name = %q, want %q", root.Name, want)
	}
}

// TestAutomaticSubtestOfBoundTestGetsItsOwnSpan checks that a subtest,
// whose goroutine inherits its parent's binding, still gets its own span,
// as a child of the parent's span.
func TestAutomaticSubtestOfBoundTestGetsItsOwnSpan(t *testing.T) {
	var parentName, subName string
	t.Run("parent", func(t *testing.T) {
		parentName = t.Name() + "/app"
		detachedWorkWithContext(t.Context(), parentName)
		t.Run("sub", func(t *testing.T) {
			subName = t.Name() + "/app"
			detachedWorkWithContext(t.Context(), subName)
		})
	})
	parentRoot := parentOf(t, span(t, parentName))
	subRoot := parentOf(t, span(t, subName))
	if want := pkg + ".TestAutomaticSubtestOfBoundTestGetsItsOwnSpan.func1.1"; subRoot.Name != want {
		t.Errorf("subtest span name = %q, want %q", subRoot.Name, want)
	}
	assertChild(t, subRoot, parentRoot)
}

// TestAutomaticBindingReusesSpanForDerivedContext checks that a context
// derived from t.Context() with its own Done channel doesn't start a second
// span for the same test.
func TestAutomaticBindingReusesSpanForDerivedContext(t *testing.T) {
	var first, derived string
	t.Run("sub", func(t *testing.T) {
		first, derived = t.Name()+"/first", t.Name()+"/derived"
		detachedWorkWithContext(t.Context(), first)
		ctx, cancel := context.WithTimeout(t.Context(), time.Minute)
		defer cancel()
		detachedWorkWithContext(ctx, derived)
	})
	if a, b := span(t, first), span(t, derived); a.Parent.SpanID() != b.Parent.SpanID() {
		t.Errorf("%q and %q have different parents", first, derived)
	}
}

// TestAutomaticBindingNamesCleanupFunction checks that a span started in a
// t.Cleanup function is named after that function, not a testing frame.
func TestAutomaticBindingNamesCleanupFunction(t *testing.T) {
	var appName string
	t.Run("sub", func(t *testing.T) {
		appName = t.Name() + "/app"
		t.Cleanup(func() { detachedWorkWithContext(t.Context(), appName) })
	})
	root := parentOf(t, span(t, appName))
	if want := pkg + ".TestAutomaticBindingNamesCleanupFunction.func1.1"; root.Name != want {
		t.Errorf("cleanup span name = %q, want %q", root.Name, want)
	}
}

// TestDerivedContextOnUnlabeledGoroutine checks that a context derived from
// t.Context() with context.WithValue, which shares its Done channel, finds
// the test on a goroutine that didn't inherit the test's labels.
func TestDerivedContextOnUnlabeledGoroutine(t *testing.T) {
	type key struct{}
	work := make(chan context.Context)
	finished := make(chan struct{})
	go func() { // started before Hook, so it has no test labels
		for ctx := range work {
			detachedWorkWithContext(ctx, ctx.Value(key{}).(string))
			finished <- struct{}{}
		}
	}()
	var name string
	t.Run("sub", func(t *testing.T) {
		testtrace.Hook(t)
		name = t.Name() + "/app"
		work <- context.WithValue(t.Context(), key{}, name)
		<-finished
	})
	close(work)
	assertChild(t, span(t, name), span(t, strings.TrimSuffix(name, "/app")))
}

// TestHookDoesNotCreateASpuriousAutomaticRoot checks that Hook's span is a
// root, not a child of a span that the automatic path starts for
// t.Context().
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

// TestHookContextOnUnlabeledGoroutine checks that the context Hook returns
// finds the test on a goroutine that the test didn't start.
func TestHookContextOnUnlabeledGoroutine(t *testing.T) {
	var ctx context.Context
	var test string
	t.Run("test", func(t *testing.T) {
		test = t.Name()
		ctx = testtrace.Hook(t)
	})
	ch := make(chan struct{})
	go func() {
		defer close(ch)
		detachedWorkWithContext(ctx, test+"/unlabeled-goroutine")
	}()
	<-ch
	assertChild(t, span(t, test+"/unlabeled-goroutine"), span(t, test))
}

// detachedWorkWithContext starts and ends a span from ctx.
func detachedWorkWithContext(ctx context.Context, name string) {
	_, span := appTracer.Start(ctx, name)
	span.End()
}

func BenchmarkStartDetached(b *testing.B) {
	testtrace.Hook(b)
	b.Run("testtrace", func(b *testing.B) {
		tr := testtrace.WrapTracerProvider(sdktrace.NewTracerProvider()).Tracer("bench")
		if _, s := tr.Start(b.Context(), "x"); !s.(sdktrace.ReadOnlySpan).Parent().IsValid() {
			b.Fatal("benchmark span has no parent")
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
