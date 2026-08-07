# Observability — current state

The firmware ships structured `tracing` events to **Google Cloud
Logging** and periodic chip-health snapshots to **Google Cloud
Monitoring**. Both are opt-in per device: without a `[gcp]` block in
`provisioning.toml`, the firmware boots normally and emits to serial
only.

One service account, one private key, one cached access token covers
both APIs (the JWT requests `logging.write` + `monitoring.write`
scopes; the cached bearer is shared between the two sender threads).

## Architecture

```
┌──────────────────── ESP32 ────────────────────┐         ┌──── GCP ─────┐
│                                                │         │              │
│  tracing event ──┐                             │         │              │
│  (any module)    ├─▶ ring buffer ──▶ cloud_log │ HTTPS   │  Logging     │
│  tracing event ──┘   (256 entries)   thread    │────────▶│  /v2/        │
│                       drop-oldest              │         │  entries:    │
│                                                │         │  write       │
│                                                │         │              │
│  metrics thread ─ snapshot heap/stack/wifi/... │ HTTPS   │  Monitoring  │
│  (every N s)      build CreateTimeSeries       │────────▶│  /v3/.../    │
│                                                │         │  timeSeries  │
│                                                │         │              │
│  gcp_auth: shared TokenProvider                │ HTTPS   │  oauth2      │
│  - mints multi-scope JWT                       │────────▶│  /token      │
│  - caches bearer for ~1h                       │         │              │
│                                                │         │              │
└────────────────────────────────────────────────┘         └──────────────┘
```

## Modules

| File | What it owns |
|------|--------------|
| `src/gcp_auth.rs` | `TokenProvider` (multi-scope JWT mint + bearer cache), `ShortHttpsLock`, `OtaDownloadGuard`, shared HTTPS / time / base64url helpers, `device_mac()`. |
| `src/cloud_log.rs` | `GcpConfig` NVS load, `LogEntry`, `LogQueue` (bounded ring buffer), `CloudLogLayer` (tracing subscriber), sender thread that POSTs to `logging.googleapis.com`. |
| `src/metrics.rs` | Per-task `TaskHandle_t` registry, snapshot collector (FFI calls into ESP-IDF), sender thread that POSTs to `monitoring.googleapis.com`. |

## Auth

The `TokenProvider` mints a single OAuth2 access token covering both
APIs:

```
JWT claims.scope = "https://www.googleapis.com/auth/logging.write
                    https://www.googleapis.com/auth/monitoring.write"
```

Standard service-account flow: build header + claims, base64url-encode,
sign with the SA's RSA private key (RS256), POST to
`oauth2.googleapis.com/token`, cache the returned `access_token` for
its `expires_in` minus a 5-minute safety margin.

The cache lives in a `Mutex<Option<CachedToken>>` inside the provider;
`get_or_refresh()` returns the bearer directly on hit, mints under the
lock on miss. cloud_log + metrics share an `Arc<TokenProvider>` so
neither pays for its own RSA sign.

## Cloud Logging

### Capture

`CloudLogLayer` is a `tracing_subscriber::Layer`. Every emitted event:

- Severity mapped: `TRACE`/`DEBUG → DEBUG`, `INFO → INFO`, `WARN →
  WARNING`, `ERROR → ERROR`.
- Wall-clock timestamp from `SystemTime::now()` if NTP has synced
  (anything before 2020-01-01 is treated as not-yet-synced → entry
  goes without a timestamp; Cloud Logging assigns server-side time).
- All structured fields captured into `serde_json::Map`.
- Pushed onto a 256-entry bounded queue. When full, oldest is dropped
  and a counter is bumped; the next entry pushed carries
  `dropped_before` so readers can spot lossy windows in the cloud.
- The layer's own module path (`esp32_blinky::cloud_log`),
  `esp32_blinky::metrics`, and `esp32_blinky::gcp_auth` are
  **excluded** from capture — otherwise the senders' own tracing
  calls would land on the queue they're draining and create a tight
  feedback loop.

The layer composes with `EspLogger`, so events still print to serial
in addition to being queued.

### Sender thread

Background pthread, ~32 KB stack. Wakes every 5 s (or backoff if the
last POST failed):

1. Skip the cycle if `OTA_DOWNLOAD_IN_PROGRESS` is set (see "Heap
   budget" below).
2. Drain up to 50 entries from the queue.
3. Acquire `ShortHttpsLock` (serialises against metrics + OTA short
   fetches).
4. `auth.get_or_refresh()` — may transparently mint a token.
5. POST to `https://logging.googleapis.com/v2/entries:write`.
6. Drop the lock.

On 4xx/5xx the batch is dropped (rather than re-queued) — long outages
otherwise grow the queue unboundedly. Drop count is surfaced on the
next entry pushed.

### Schema

```json
{
  "logName": "projects/<project-id>/logs/esp32-firmware",
  "resource": {
    "type": "generic_node",
    "labels": {
      "project_id": "<project-id>",
      "location":   "global",
      "namespace":  "esp32",
      "node_id":    "<chip-mac>"
    }
  },
  "entries": [
    {
      "severity": "INFO",
      "timestamp": "2026-05-02T19:45:00Z",
      "jsonPayload": {
        "message":    "ota: boot summary",
        "module":     "esp32_blinky::ota",
        "fw_version": "abc1234",
        "fw":         "abc1234",
        "repo":       "ghcr.io/imjasonh/esp32",
        "tag":        "latest",
        "poll_secs":  60,
        "last_digest":"sha256:..."
      }
    }
  ]
}
```

Single `logName` for both app + OTA; `jsonPayload.module` lets
queries split by component:

```
jsonPayload.module="esp32_blinky::ota"   AND jsonPayload.fw_version="abc1234"
```

## Cloud Monitoring

### Snapshot

Every `metrics_interval_secs` (default 300, NVS-tunable, 0 disables
the thread entirely), `metrics::collect()` reads:

| Metric type (`custom.googleapis.com/esp32/…`) | Source                                                  | Unit | Kind  |
|-----------------------------------------------|---------------------------------------------------------|------|-------|
| `free_heap`                                   | `esp_get_free_heap_size()`                              | By   | GAUGE |
| `free_heap_internal`                          | `heap_caps_get_free_size(MALLOC_CAP_INTERNAL)`          | By   | GAUGE |
| `min_free_heap`                               | `esp_get_minimum_free_heap_size()` (water-mark / boot)  | By   | GAUGE |
| `largest_free_block`                          | `heap_caps_get_largest_free_block(MALLOC_CAP_DEFAULT)`  | By   | GAUGE |
| `stack_hwm` *(label `task`)*                  | `uxTaskGetStackHighWaterMark` per published task        | By   | GAUGE |
| `wifi_rssi`                                   | `esp_wifi_sta_get_ap_info().rssi`                       | dBm  | GAUGE |
| `wifi_channel`                                | …`.primary`                                             | 1    | GAUGE |
| `cpu_freq_mhz`                                | `CONFIG_ESP_DEFAULT_CPU_FREQ_MHZ`                       | MHz  | GAUGE |
| `uptime_secs`                                 | `esp_timer_get_time() / 1_000_000`                      | s    | GAUGE |
| `nvs_used_entries`                            | `nvs_get_stats().used_entries`                          | 1    | GAUGE |
| `nvs_free_entries`                            | …`.free_entries`                                        | 1    | GAUGE |
| `cloud_log_queue_depth`                       | `LogQueue::stats().0`                                   | 1    | GAUGE |
| `cloud_log_dropped_total`                     | lifetime drop counter on `LogQueue`                     | 1    | GAUGE |

`stack_hwm` carries a `task` label (`main` / `ota` / `cloud_log` /
`metrics`) so all four series chart on one graph. Each thread
publishes its own `TaskHandle_t` via
`metrics::publish_self(&handles::<NAME>)` at the top of its run loop;
`metrics::collect()` reads the FFI handle out of an `AtomicUsize` (0 =
unpublished, field omitted from the snapshot).

Note: ESP-IDF Xtensa `StackType_t = uint8_t`, so
`uxTaskGetStackHighWaterMark` returns **bytes** (not "words" as
upstream FreeRTOS docs say). No multiplication.

### Sender thread

Background pthread, ~16 KB stack. Wakes every `metrics_interval_secs`:

1. Skip the cycle if `OTA_DOWNLOAD_IN_PROGRESS`.
2. `collect()` — pure FFI, no allocations beyond the snapshot struct.
3. Acquire `ShortHttpsLock`.
4. `auth.get_or_refresh()`.
5. POST one `CreateTimeSeries` request containing all ~16 series in a
   single body to `monitoring.googleapis.com/v3/projects/<id>/timeSeries`.

Cloud Monitoring auto-creates `MetricDescriptor`s on first write;
no separate provisioning step on the GCP side.

### Schema

```json
{
  "timeSeries": [
    {
      "metric": {
        "type":   "custom.googleapis.com/esp32/free_heap",
        "labels": { "fw_version": "abc1234" }
      },
      "resource": {
        "type": "generic_node",
        "labels": {
          "project_id": "<project-id>",
          "location":   "global",
          "namespace":  "esp32",
          "node_id":    "<chip-mac>"
        }
      },
      "metricKind": "GAUGE",
      "valueType":  "INT64",
      "points": [
        { "interval": { "endTime": "2026-05-02T22:30:00Z" },
          "value":    { "int64Value": "182456" } }
      ]
    }
  ]
}
```

`fw_version` rides on every metric as a **metric label** (resource
labels can't carry it — `generic_node` has a fixed schema). Adding
new label keys to an existing `MetricDescriptor` is forbidden by Cloud
Monitoring; if the fleet's running fw doesn't match the descriptor
schema you'll see HTTP 500 on the POST. Migration in that case is
manual:

```bash
TOKEN=$(gcloud auth print-access-token)
URL='https://monitoring.googleapis.com/v3/projects/<id>/metricDescriptors'
for m in $(curl -sG "$URL" -H "Authorization: Bearer $TOKEN" \
    --data-urlencode 'filter=metric.type=starts_with("custom.googleapis.com/esp32/")' \
    | jq -r '.metricDescriptors[].type'); do
  curl -s -X DELETE "$URL/$m" -H "Authorization: Bearer $TOKEN"
done
```

This deletes all historical points for those metrics. There's no
in-place schema migration in Cloud Monitoring.

## Heap budget + serialization

Each TLS handshake on this chip allocates ~25–35 KB of mbedtls
context. With cloud_log + metrics + OTA each potentially holding a
TLS session, the worst case is three concurrent handshakes pinning
~90 KB — past the heap budget, producing
`MBEDTLS_ERR_SSL_ALLOC_FAILED` (-0x7F00).

Three knobs work together to keep this in budget:

1. **mbedtls config** (`sdkconfig.defaults.in`):
   - `CONFIG_MBEDTLS_DYNAMIC_BUFFER` — I/O buffers grow as needed,
     freed between handshakes (vs. pinned 16+16 KB).
   - `CONFIG_MBEDTLS_DYNAMIC_FREE_CONFIG_DATA` — frees handshake
     config struct after handshake.
   - `CONFIG_MBEDTLS_DYNAMIC_FREE_CA_CERT` — frees the CA bundle
     after handshake; re-attached on the next handshake.
   - `CONFIG_MBEDTLS_SSL_KEEP_PEER_CERTIFICATE=n` — drops the parsed
     peer cert after handshake (~3–5 KB/session). We don't reuse
     sessions or do mutual TLS.

2. **Short HTTPS serialised** (`gcp_auth::ShortHttpsLock`): cloud_log
   POST + metrics POST + OTA's manifest fetch + sig-bundle fetch all
   take this `Mutex<()>` at their call sites. Held *at the call site*
   (not inside `http_post`) so token mints inside `get_or_refresh()`
   are covered by the caller's lock — std `Mutex` isn't reentrant.
   OTA's poll_once releases between phases (token+manifest, then
   verify which is CPU-only, then sig bundle) so cloud_log/metrics
   aren't blocked behind ~2 s of pure-Rust X.509/ECDSA work.

3. **OTA download pause** (`gcp_auth::OTA_DOWNLOAD_IN_PROGRESS`):
   `ota::download_and_apply` flips this `AtomicBool` true via an RAII
   guard for the duration of the multi-second blob download (which
   intentionally **does not** take `ShortHttpsLock` — it'd otherwise
   block per-5-s log flushes for tens of seconds). cloud_log + metrics
   check the flag at the top of each cycle and skip — but don't
   drain — when set. Entries accumulate in the bounded queue and
   flush in one batched POST after the download finishes.

Even with all three, peak heap during a 2-way concurrent TLS
(OTA + cloud_log handshake on top of OTA's held-open download) was
historically tight — the gate in #3 is what made downloads reliably
complete.

## Provisioning (NVS)

Optional `[gcp]` block in `provisioning.toml` (see
`provisioning.toml.example`):

```toml
[gcp]
project_id = "..."
sa_email = "esp32-logger@my-project.iam.gserviceaccount.com"
sa_key_id = "abc123..."           # `private_key_id` from the SA JSON key
sa_key_pem = "gcp-sa-key.pem"     # path; tool reads + embeds the bytes
min_severity = "info"             # debug / info / warn / error; default info
metrics_interval_secs = 300       # 0 disables metrics; cloud_log keeps running
```

NVS keys (15-char limit):

| ns  | key            | type | notes                                              |
|-----|----------------|------|----------------------------------------------------|
| gcp | project_id     | str  | GCP project (logs + metrics land in)               |
| gcp | sa_email       | str  | service-account email                              |
| gcp | sa_key_id      | str  | private-key id (JWT `kid` header)                  |
| gcp | sa_key_pem     | blob | RSA private key, PKCS#8 PEM (~1.7 KB)              |
| gcp | min_severity   | u8   | 0=TRACE..4=ERROR; default 2=INFO                   |
| gcp | metric_intvl   | u32  | metrics snapshot interval in seconds; default 300  |

Missing the namespace entirely or any of the four required string/blob
fields disables both pipelines. Missing optional fields fall back to
defaults.

The OTA-distributed firmware contains no GCP secrets — the SA key
lives in NVS and is written via USB by `make provision`.

## Concerns / known limitations

- **NVS unencrypted**: anyone with physical access can dump the SA
  key. Mitigation is strict scoping (only `logging.logWriter` +
  `monitoring.metricWriter`, on a logs-tolerant project). Real fix is
  Flash Encryption + Secure Boot v2; deferred (see [`ota.md`](ota.md)
  Future work).
- **Wi-Fi outages**: the cloud_log queue is bounded at 256 entries.
  Long offline periods are lossy; drops are surfaced via
  `dropped_before` on subsequent entries.
- **Metric descriptor sticky labels**: see "Schema" above. Adding a
  new metric label key requires a one-time descriptor delete.
- **CPU freq metric is build-time**: `esp_clk_cpu_freq` isn't in the
  esp-idf-svc bindings, so we report the configured default. Becomes
  inaccurate if/when `CONFIG_PM_ENABLE` is turned on.

## Future work

- **Per-task CPU runtime stats** via `vTaskGetRunTimeStats` — needs
  `CONFIG_FREERTOS_USE_TRACE_FACILITY=y` + `CONFIG_FREERTOS_GENERATE_RUN_TIME_STATS=y`.
- **Light-sleep stats** once `esp_pm_*` is adopted — pairs with
  modem-sleep work for power telemetry.
- **External power telemetry** (INA219/INA226 over I2C) — would warrant its own plan.
- **Pre-declared MetricDescriptors** with units + descriptions for nicer Cloud Monitoring UI.
- **Alerting policies** as Terraform / `gcloud alpha monitoring` resources, checked in.
- **Cumulative metrics with `startTime`** for proper rate aggregation
  (drops/sec, polls/sec) instead of GAUGE snapshots of running totals.
- **OIDC instead of SA key** — would remove the key-leak concern, but
  ESP32 has no source of a usable OIDC token today.
