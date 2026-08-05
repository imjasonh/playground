# sshcloud observability and privacy runbook

## Non-negotiable privacy boundary

Operators may inspect platform logs, metadata-only lifecycle events, bounded
app-owned serial-console logs, and aggregate metrics. The platform must never
tap, log, store, trace, mirror, or reconstruct any SSH channel:

- stdin, stdout, or stderr bytes
- exec commands or subsystem names
- environment requests
- PTY/window/signal request payloads
- exit-signal payloads
- session recordings or replay data

Do not add logging middleware around `gateway.ProxySSHStreams`, `ssh.Channel`,
`SessionSpec`, or any `io.Reader`/`io.Writer` in the SSH proxy. Do not add
channel-byte attributes to traces or metrics.

`gateway.migrationInput` is the one apparent exception and is not an
observability feature. It is a bounded (1 MiB by default), in-memory,
single-consumer transport-continuity queue used while swapping backend SSH
connections. It is never copied to logs, metrics, traces, diagnostics, or disk.
Its bytes are deleted as the replacement transport consumes them.

An app may itself print sensitive information to its serial console. Such
output is app-owned logging, not a platform tap. App authors remain responsible
for what their process writes there.

## Data paths

Platform binaries install `internal/observability` as the standard Go logger's
output once at startup. Existing `log.Printf` calls therefore become one
JSON-escaped object per line without mechanically rewriting every caller.
Platform messages are opaque and capped at 8 KiB.

On production Firecracker hosts:

1. Jailer/Firecracker stdout (the guest serial console) goes to the app-log
   drain.
2. Jailer/Firecracker stderr goes to the platform-diagnostic drain.
3. Both writers enqueue without waiting for Cloud Logging or journald.
4. Queue, line, byte, record-rate, and telemetry-cardinality limits apply.
5. Guest JSON remains the `message` string. Guest keys such as `severity`,
   `user`, or `log_type` are never promoted.
6. `user`, `app`, `generation`, `run_id`, and host attribution come from the
   authenticated agent request. The root helper verifies that user/app/gen
   derives the VM's fixed host ID. The guest cannot override it.

The default hard controls are:

| Control | Default | Hard maximum |
|---|---:|---:|
| In-memory VMM output queue | 1 MiB | 4 MiB |
| One console line | 16 KiB | 64 KiB |
| Emitted lines | 200/s | 1,000/s |
| Emitted bytes | 256 KiB/s | 4 MiB/s |
| Telemetry names per VMM run | 32 | 64 |
| Telemetry records | 20/s | 100/s |

Output over a limit is dropped rather than backpressuring Firecracker.
`sshcloud_app_log_bytes_total{result="accepted|dropped"}` and
`sshcloud_console_records_total` expose the result without tenant labels.

The direct Firecracker runtime is test-only and retains its local diagnostic
file behavior. Production Terraform never enables it.

## App telemetry convention

Normal serial-console lines are app logs. A line is telemetry only when it has
exactly these four whitespace-separated tokens:

```text
SSHCLOUD_TELEMETRY_V1 <counter|gauge> <name> <number>
```

Examples:

```text
SSHCLOUD_TELEMETRY_V1 counter requests_total 1
SSHCLOUD_TELEMETRY_V1 gauge queue.depth 4
```

Names must match `[a-z][a-z0-9_.-]{0,63}`. Values must be finite, at most
`1e15` in magnitude, and counters cannot be negative. Labels, attributes,
histograms, identity, timestamps, and JSON are unsupported. Valid telemetry is
emitted as a fixed structured app record with authoritative host identity.
Within one VMM run, a telemetry name cannot switch between counter and gauge.
Invalid or over-cardinality telemetry is never promoted; it remains subject to
the ordinary app-log limits.

There is no guest telemetry listener, firewall exception, metadata credential,
Ops Agent credential, or service-account token. Telemetry uses the existing
serial console only.

## GCP layout

Terraform installs and configures the GCP Ops Agent on gateway, orchestrator,
snapshotd, and every agent host. Service accounts receive the three standard
observability writer roles only:

- `roles/logging.logWriter`
- `roles/monitoring.metricWriter`
- `roles/cloudtrace.agent`

Logging, Monitoring, and Trace APIs are enabled. Trace permission is reserved
for future metadata-only platform spans; the current implementation does not
export SSH-channel spans.

Cloud Logging routes records into:

| Bucket | Retention | Contents |
|---|---:|---|
| `<prefix>-platform` | 30 days | platform JSON, Firecracker diagnostics, host logs |
| `<prefix>-app` | 7 days | app console and strict app telemetry |

An exclusion prevents duplicate sshcloud retention in `_Default`; `_Required`
is unchanged. App and platform sinks are mutually filtered on the
host-controlled `jsonPayload.log_type`.

Example queries:

```text
# One app's console and telemetry (run against the app bucket)
jsonPayload.log_type="app"
jsonPayload.user="alice"
jsonPayload.app="fortune"

# Firecracker diagnostics for one run (run against the platform bucket)
jsonPayload.component="firecracker"
jsonPayload.run_id="r..."

# Metadata-only failed migrations
jsonPayload.event="migration"
jsonPayload.outcome="failure"
```

Do not export either bucket to a data lake that has broader access or longer
retention without a separate privacy review.

## Metrics, dashboard, and alerts

`/metrics` endpoints expose Prometheus text accepted by the Ops Agent's
OpenTelemetry pipeline. The VMM helper endpoint is loopback-only. Metric APIs
have no user, app, generation, run, or session labels; the Ops Agent also drops
those label names defensively.

Core series cover:

- a fixed per-process scrape heartbeat (`sshcloud_up`)
- app log accepted/dropped bytes and bounded console outcomes
- host vCPU/memory capacity, reservations, inventory, and cordon state
- lifecycle/session/deploy/snapshot/migration operation outcomes and durations
- aggregate bounded VMM output queue bytes
- Ops Agent host CPU, memory, disk, and process metrics

The Ops Agent keeps its built-in host-metrics pipeline and adds a strictly
bounded Prometheus scrape. Its built-in syslog tailer is disabled so the
bounded journal is not ingested twice. Terraform creates the `sshcloud
operations` dashboard and alerts for missing scrape heartbeats, disk usage
above 90%, app-log drops, and structured platform errors.
`notification_email` optionally attaches an email channel. Setting
`billing_account_id` and `monthly_budget_usd` together optionally creates 50%,
90%, and 100% budget thresholds.

The orchestrator's root-only diagnostics response is metadata-only and bounded
to 200 placements, 100 hosts, 100 instances per returned host, and 512 bytes
per error string. Totals show truncation.

## Host disk bounds

All roles configure persistent journald with:

- 512 MiB total persistent use
- 128 MiB runtime use
- 64 MiB files
- 2 GiB kept free
- seven-day maximum age and one-day file rotation
- journald burst limiting

Docker platform services use the journald log driver, avoiding unbounded Docker
JSON logs. Production app console output has no separate on-disk spool.

The OCI rootfs cache defaults to an 8 GiB hard budget
(`agent_rootfs_cache_bytes`). Digest ext4/spec pairs are touched on use and
least-recently-used inactive pairs are removed before materializing another
image. Active materializations are protected from eviction.

## Operator checks and incident response

After the first apply:

1. Confirm all four role types report both Ops Agent CPU samples and
   `sshcloud_up` scrape heartbeats.
2. Emit one harmless platform startup record and verify it appears only in the
   30-day platform bucket.
3. Run an app that prints one harmless console line and one telemetry line;
   verify both appear only in the seven-day app bucket with authoritative
   identity.
4. Print guest JSON containing fake `severity`, `user`, and `log_type` fields;
   verify they remain inside `jsonPayload.message`.
5. Generate a bounded app log flood; verify SSH/VM responsiveness and increases
   in the dropped-byte counter.
6. Exercise one alert with a temporary threshold override, verify the
   notification, then restore Terraform state.
7. Confirm `_Default` does not contain duplicate sshcloud records.
8. Confirm no guest can reach metadata, an Ops Agent listener, or a telemetry
   firewall port.

CI and local tests validate schemas, queue behavior, limits, cache eviction,
and Terraform structure. They do **not** prove real GCP log ingestion, sink
routing, metric descriptor creation, alert delivery, email delivery, budget
delivery, or retention enforcement. Those ingestion and alert drills still
require manual validation in the operator-owned GCP project before production.

Secret and control-certificate rotation is intentionally not changed here.
