# testtrace to Google Cloud Trace

Wiring `testtrace` to Google Cloud Trace is wiring it to OTLP/HTTP, the same
as any other OpenTelemetry backend. There's no GCP-specific exporter in the
Go code: a Collector receives OTLP and forwards it with its own `googlecloud`
exporter (the dedicated Go Cloud Trace exporter is deprecated; see
[the migration guide](https://github.com/GoogleCloudPlatform/opentelemetry-operations-go/blob/main/MIGRATION.md)).

```go
exporter, err := otlptracehttp.New(ctx) // OTEL_EXPORTER_OTLP_ENDPOINT picks the Collector
if err != nil {
	log.Fatal(err)
}
tp := sdktrace.NewTracerProvider(sdktrace.WithBatcher(exporter))
testtrace.Install(tp)
```

`gcp_test.go` runs that exact code against a fake Collector it starts on
`localhost`, so `go test ./testtrace/examples/gcp/ -v` needs no GCP project
or credentials.

Run it against a real Collector and project instead:

```bash
gcloud auth application-default login
docker run --rm -p 4318:4318 \
  -v "$PWD/collector-config.yaml:/etc/otelcol/config.yaml" \
  -v "$HOME/.config/gcloud:/root/.config/gcloud:ro" \
  otel/opentelemetry-collector-contrib:latest
OTEL_EXPORTER_OTLP_ENDPOINT=http://localhost:4318 go test ./testtrace/examples/gcp/ -v
```

Spans appear in
[Cloud Trace's trace list](https://console.cloud.google.com/traces/list)
for the project named in `collector-config.yaml`, usually within a few
seconds. `testtrace.Hook(t)`'s span carries the test's name, and every span
the test's goroutine starts afterward, including `RunPipeline`'s, nests
under it in the trace view the same way it does in the in-memory exporter
the rest of this repository's tests use.
