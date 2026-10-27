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

// span returns the one exported span named name.
func span(t *testing.T, name string) tracetest.SpanStub {
	t.Helper()
	var found []tracetest.SpanStub
	for _, s := range exporter.GetSpans() {
		if s.Name == name {
			found = append(found, s)
		}
	}
	if len(found) != 1 {
		t.Fatalf("got %d spans named %q, want 1", len(found), name)
	}
	return found[0]
}

func assertChild(t *testing.T, child, parent tracetest.SpanStub) {
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
