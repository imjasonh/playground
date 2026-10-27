# testtrace

`testtrace` parents OpenTelemetry spans on the span of the Go test that
starts them. When code under test starts a span from `t.Context()`, or from
a context derived from it, the span is a child of the test's span. The test
only has to pass that context through. Spans in goroutines that the test
starts are children of the test's span too, and each parallel test has its
own span.

## Usage

Wrap your TracerProvider once in `TestMain`:

```go
func TestMain(m *testing.M) {
	exporter := tracetest.NewInMemoryExporter()
	tp := sdktrace.NewTracerProvider(sdktrace.WithSyncer(exporter))
	testtrace.Install(tp)
	os.Exit(m.Run())
}
```

Tests don't call anything else. Pass `t.Context()`, or a context derived
from it, to code under test:

```go
func TestPipeline(t *testing.T) {
	t.Parallel()
	// RunPipeline's spans are children of a span named after TestPipeline,
	// including spans it starts from context.Background() in goroutines.
	if err := RunPipeline(t.Context()); err != nil {
		t.Fatal(err)
	}
}
```

The first traced call from the test's goroutine with such a context starts
the test's span. testtrace names that span after the function that
`testing.tRunner` called, such as `example.com/pkg.TestPipeline`, and ends
it when the context is done. A subtest gets its own span, a child of its
parent test's span.

If code under test takes a TracerProvider instead of using the global one,
pass it `testtrace.WrapTracerProvider(tp)`.

### Hook

Call `Hook(t)` at the start of a test to start the test's span yourself:

```go
func TestPipeline(t *testing.T) {
	t.Parallel()
	ctx := testtrace.Hook(t)
	if err := RunPipeline(ctx); err != nil {
		t.Fatal(err)
	}
}
```

`Hook` returns `t.Context()` with the test's span. Use it when:

- The span needs the test's name. The automatic path uses a Go function
  name, and the subtests of a table-driven test usually share one function
  literal, so their spans all get a name like `pkg.TestFoo.func1`:

  ```go
  for _, tc := range cases {
  	t.Run(tc.name, func(t *testing.T) {
  		ctx := testtrace.Hook(t) // span named TestFoo/<tc.name>
  		RunPipeline(ctx)
  	})
  }
  ```

  Each subtest still gets its own span without `Hook`. Only the names are
  the same.
- The span must be ended and exported when the test's cleanups finish.
  The automatic path ends its span from a `context.AfterFunc` callback,
  which runs on a new goroutine, so the span can end a moment later.
  `Hook` ends its span from `t.Cleanup`.
- The span needs an error status when the test fails. Only `Hook` can see
  the test's result.
- The test never passes a cancelable context to traced code. See
  [Limits](#limits).

A test that calls `Hook` as a subtest of a bound test gets a span that's a
child of the parent test's span.

## How it works

`Install` sets a TracerProvider that wraps yours. When a tracer from it
starts a span from a context with no valid span context, it looks for a
parent in this order:

1. A test bound to the context's `Done` channel. A context that
   `context.WithValue` derives from `t.Context()` has the same channel, so
   this lookup works on any goroutine.
2. A test bound to the calling goroutine. When testtrace binds a test, it
   sets a profiler label (`otel.test=<span name>`) on the test's goroutine.
   The runtime copies the goroutine's label pointer into every goroutine it
   starts, and testtrace keys bindings by that pointer.
3. If the context is cancelable and the calling goroutine runs a test that
   isn't bound yet, testtrace binds it. It walks the call stack to find
   `testing.tRunner` and the function below it. A subtest's goroutine
   inherits its parent test's label, so testtrace compares that function
   with the one the inherited binding recorded to tell a subtest from its
   parent.

If none of these find a test, the span starts with no parent.

A `go:linkname` to `runtime/pprof.runtime_getProfLabel`, which the runtime
keeps for external packages, reads the label pointer. On the benchmark in
`testtrace_test.go`, a span start through testtrace costs about 60 ns more
than through the SDK alone. Parsing a goroutine ID from `runtime.Stack`, the
other way to key bindings, costs about 2 µs, and goroutines that the test
starts have IDs of their own.

## Limits

- The automatic path needs `testing.tRunner` on the call stack, so only a
  test's own goroutine can start the test's span. Fuzz targets work,
  because `F.Fuzz` runs each input under `tRunner`, and their spans are
  named after the function passed to `F.Fuzz`.
- Benchmarks don't run under `tRunner`, and `b.Context()` is a new context
  on each run that calibrates `b.N`. Call `Hook(b)` to give a benchmark a
  span. Spans started inside the timed loop add their cost to `ns/op`.
- A test that only passes contexts that are never canceled, such as
  `context.Background()`, gets no span, because nothing would end it.
  Every context derived from `t.Context()` is cancelable, except one from
  `context.WithoutCancel`.
- The test's span lasts as long as the first cancelable context the test
  passes. If that's a `context.WithTimeout` context that the test cancels
  early, the span ends then, and the test's next traced call starts a new
  span.
- If a goroutine that a subtest started uses the subtest's `t.Context()`
  before the subtest's own goroutine does, the subtest's spans are children
  of its parent test's span rather than of a span of their own.
- If code under test replaces the goroutine's profiler labels with
  `pprof.Do` or `pprof.SetGoroutineLabels`, using a context that doesn't
  come from the test, spans in that goroutine lose the binding.
- Goroutines that the runtime starts, such as `time.AfterFunc` callbacks,
  don't inherit labels and aren't bound.
- Spans that a goroutine starts after its test ends have no test parent.
- `WrapTracerProvider` and `Install` panic outside a test binary.

## Test

```bash
go test -race ./...
go test -run '^$' -bench . ./...
go test -run '^$' -fuzz FuzzAutomaticBinding -fuzztime 10s .
```
