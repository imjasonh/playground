# testtrace

`testtrace` parents OpenTelemetry spans on the span of the Go test that
starts them. Code under test that starts a span from `context.Background()`,
or from any context without a span, gets the test's span as its parent. That
includes code that runs in goroutines the test starts, and each parallel test
keeps its own parent.

## Usage

Wrap your TracerProvider once in `TestMain`, then call `Hook` at the top of
each test that you want traced:

```go
func TestMain(m *testing.M) {
	exporter := tracetest.NewInMemoryExporter()
	tp := sdktrace.NewTracerProvider(sdktrace.WithSyncer(exporter))
	testtrace.Install(tp)
	os.Exit(m.Run())
}

func TestPipeline(t *testing.T) {
	t.Parallel()
	ctx := testtrace.Hook(t)

	// Spans that RunPipeline starts from context.Background(), on this
	// goroutine or on goroutines it starts, are children of the test span.
	if err := RunPipeline(context.Background()); err != nil {
		t.Fatal(err)
	}
	// ctx carries the test span, for code that takes a context.
	_ = ctx
}
```

`Hook` returns `t.Context()` with the test span. When the test ends, `Hook`
ends the span and sets an error status if the test failed. A subtest that
calls `Hook` gets a span that's a child of its parent test's span.

If code under test takes a TracerProvider instead of using the global one,
pass it `testtrace.WrapTracerProvider(tp)`.

## How it works

`Install` sets a TracerProvider that wraps yours. Its tracers check, on
every `Start`, whether the context already carries a valid span context. If
it doesn't, and the calling goroutine is bound to a test, the tracer starts
the span with the test span as its parent.

`Hook` binds a test by setting a profiler label (`otel.test=<test name>`) on
the test's goroutine, and it keys a registry by the runtime's label pointer.
The runtime copies that pointer into every goroutine that a goroutine starts,
so a goroutine that the test starts, directly or through code under test,
finds the same binding. Reading the pointer costs one function call. The
package reads it with a `go:linkname` to
`runtime/pprof.runtime_getProfLabel`, which the runtime keeps for external
packages.

An earlier design keyed the registry by goroutine ID, parsed from
`runtime.Stack` on every span start. That lookup takes about 2 µs, and it
misses spans in goroutines that the test starts. On the benchmark in
`testtrace_test.go`, `testtrace` adds about 45 ns to a span start.

## Limits

- Call `Install` before any other `otel.SetTracerProvider` call. Tracers
  that packages got from `otel.Tracer` earlier forward to the first provider
  set and to no later one. A provider that's set in a package `init` function
  and then replaced in `TestMain` traces nothing through the wrapper.
- If code under test replaces the goroutine's profiler labels with
  `pprof.Do` or `pprof.SetGoroutineLabels`, using a context that doesn't come
  from the test, spans in that goroutine lose the binding.
- Goroutines that the runtime starts, such as `time.AfterFunc` callbacks,
  don't inherit labels and aren't bound.
- Spans that a goroutine starts after its test ends have no test parent.
- `WrapTracerProvider` and `Install` panic outside a test binary.

## Test

```bash
go test -race ./...
go test -run '^$' -bench . ./...
```
