# testtrace

`testtrace` parents OpenTelemetry spans on the span of the Go test that
starts them. Code under test that starts a span from `t.Context()`, or from
any context derived from it, gets the test's span as its parent, with no
code in the test besides passing that context through. That includes code
that runs in goroutines the test starts, and each parallel test keeps its
own parent.

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

From there, a test doesn't need to call anything else. Pass `t.Context()`
(or a context derived from it) to code under test, the way Go 1.24 already
recommends:

```go
func TestPipeline(t *testing.T) {
	t.Parallel()
	// Spans that RunPipeline starts, from this context, from
	// context.Background() on a goroutine it starts, or from any other
	// context with no span of its own, are children of a span testtrace
	// starts and names after TestPipeline.
	if err := RunPipeline(t.Context()); err != nil {
		t.Fatal(err)
	}
}
```

The first time a traced call sees a context with no span, while the test is
still synchronously running, testtrace starts a span named after the
calling function, and ends it once that context is done.

### Hook, for more control

Call `Hook(t)` at the top of a test when the automatic span isn't good
enough:

```go
func TestPipeline(t *testing.T) {
	t.Parallel()
	ctx := testtrace.Hook(t)
	if err := RunPipeline(ctx); err != nil {
		t.Fatal(err)
	}
}
```

`Hook` returns `t.Context()` with the test span, and reasons to prefer it
over the automatic path:

- The exact test name, including a subtest's `Parent/sub` form. The
  automatic path names a span after the calling Go function instead, so two
  tests that share a helper function get spans with the same name.
- A span that starts before the test's first traced call, instead of on
  first use.
- A span that's guaranteed to be ended and exported by the time the test
  returns. The automatic path ends its span from a `context.AfterFunc`
  callback, which the `context` package always runs on a new goroutine, so
  that span can still be open for a moment after a subtest that triggered it
  returns. `Hook` ends its span synchronously, from `t.Cleanup`.
- A test that never cancels its context — `Hook` ends its span from
  `t.Cleanup` regardless, where the automatic path needs a context that
  eventually becomes done.

`Hook` sets an error status on its span if the test fails. A subtest that
calls `Hook` gets a span that's a child of its parent test's span.

If code under test takes a TracerProvider instead of using the global one,
pass it `testtrace.WrapTracerProvider(tp)`.

## How it works

`Install` sets a TracerProvider that wraps yours. Its tracers check, on
every `Start`, whether the context already carries a valid span context. If
it doesn't:

1. If the calling goroutine, or the exact context value, is already bound to
   a test (by `Hook`, or by an earlier automatic span), the new span is
   parented on that test's span.
2. Otherwise, if the context can be canceled and the calling goroutine is
   still synchronously inside `testing.tRunner` — found by walking the call
   stack — testtrace starts a span named after the function one level below
   `tRunner`, binds it the same way `Hook` would, and arranges to end it
   once the context is done.
3. Otherwise, the span starts with no parent, same as always.

The binding itself sets a profiler label (`otel.test=<name>`) on the test's
goroutine, and keys a registry by the runtime's label pointer. The runtime
copies that pointer into every goroutine that a goroutine starts, so a
goroutine the test starts, directly or through code under test, finds the
same binding. Reading the pointer costs one function call, through a
`go:linkname` to `runtime/pprof.runtime_getProfLabel`, which the runtime
keeps for external packages. The registry also keys bindings by the exact
`context.Context` value the test first used, so that value resolves even on
a goroutine that didn't inherit the label — for example, one from a worker
pool the test sends work to over a channel.

An earlier design keyed the registry by goroutine ID, parsed from
`runtime.Stack` on every span start. That lookup takes about 2 µs, and it
missed spans in goroutines that the test started. On the benchmark in
`testtrace_test.go`, the profiler-label lookup adds about 45 ns to a span
start.

## Limits

- Step 2 above needs `testing.tRunner` on the call stack, so the automatic
  path only triggers from a test's own goroutine, synchronously (through
  any number of function calls), the first time that goroutine passes a
  no-span, cancelable context to a traced call. It doesn't trigger in a
  benchmark or fuzz target, which don't run under `tRunner`; call `Hook`
  there. It also can't trigger from a context that never cancels — pass
  `t.Context()` somewhere, or call `Hook`.
- A context derived from `t.Context()` with `context.WithValue` isn't equal
  to `t.Context()` itself, so the exact-context-value lookup in step 1 only
  matches a literal, unmodified `t.Context()` passed to a second goroutine.
  The goroutine-label lookup, which covers derived contexts too, still
  applies within the original goroutine's own descendants.
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
```
