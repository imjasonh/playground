//! Ship structured logs from the device to Google Cloud Logging.
//!
//! - `CloudLogLayer` is a `tracing_subscriber::Layer` that captures
//!   events into a bounded ring buffer.
//! - `run()` is a background sender thread that drains the buffer and
//!   POSTs batches to `logging.googleapis.com/v2/entries:write` using
//!   a Bearer token from `gcp_auth::TokenProvider` (shared with
//!   `metrics`).
//!
//! Cloud logging is opt-in per device. If the `gcp` NVS namespace is
//! missing required keys (`project_id`, `sa_email`, `sa_key_id`,
//! `sa_key_pem`), the firmware boots normally with serial-only logs.

use anyhow::{anyhow, Result};
use esp_idf_svc::nvs::{EspDefaultNvsPartition, EspNvs};
use serde::Serialize;
use std::collections::VecDeque;
use std::sync::atomic::{AtomicU32, Ordering};
use std::sync::{Arc, Mutex};
use std::time::Duration;
use tracing::{Event, Level, Subscriber};
use tracing_subscriber::layer::Context as LayerContext;
use tracing_subscriber::Layer;

use crate::gcp_auth::{
    device_mac, http_post, now_unix_secs, ota_download_in_progress, unix_to_rfc3339,
    ShortHttpsLock, TokenProvider,
};
use crate::nvs_util::{read_blob, read_str};

/// `module_path!()` value for this module. Cross-referenced by other
/// modules that want to filter events from cloud_log without
/// hardcoding the crate name (which would silently break if
/// `Cargo.toml [package].name` changes).
pub const TARGET: &str = module_path!();

const NVS_GCP_NS: &str = "gcp";
const NVS_PROJECT_ID: &str = "project_id";
const NVS_SA_EMAIL: &str = "sa_email";
const NVS_SA_KEY_ID: &str = "sa_key_id";
const NVS_SA_KEY_PEM: &str = "sa_key_pem";
const NVS_MIN_SEVERITY: &str = "min_severity";
// 15-char NVS key limit forces the abbreviation; the toml field stays
// readable as `metrics_interval_secs`.
const NVS_METRICS_INTERVAL_SECS: &str = "metric_intvl";

/// Capacity of the in-RAM log queue. When the queue is full, oldest
/// entries are dropped and counted; the count surfaces as
/// `LogEntry::dropped_before` on the next entry pushed.
pub const QUEUE_CAPACITY: usize = 256;
const FLUSH_INTERVAL: Duration = Duration::from_secs(5);
const BATCH_MAX_ENTRIES: usize = 50;

/// Default snapshot cadence if `metrics_interval` is absent in NVS.
pub const DEFAULT_METRICS_INTERVAL_SECS: u32 = 300;

/// GCP-side config + opt-in flag, read from NVS at boot. Shared by
/// `cloud_log` (logs) and `metrics` (Cloud Monitoring time series).
#[derive(Clone)]
pub struct GcpConfig {
    pub project_id: String,
    pub sa_email: String,
    pub sa_key_id: String,
    pub sa_key_pem: Vec<u8>,
    pub min_severity: Level,
    /// 0 = metrics disabled (cloud_log still runs); >0 = sample period.
    pub metrics_interval_secs: u32,
}

impl GcpConfig {
    /// Load from NVS. `Ok(None)` means the device is intentionally not
    /// configured for cloud logging (cloud logging is opt-in, missing
    /// keys or missing namespace = disabled, no error).
    pub fn load(partition: EspDefaultNvsPartition) -> Result<Option<Self>> {
        let nvs = match EspNvs::new(partition, NVS_GCP_NS, false) {
            Ok(n) => n,
            Err(e)
                if e.code() == esp_idf_svc::sys::ESP_ERR_NVS_NOT_FOUND as i32 =>
            {
                // Namespace has never been written. Cloud logging is
                // opt-in; this is the normal state for a device that
                // wasn't provisioned with a [gcp] block.
                return Ok(None);
            }
            Err(e) => {
                return Err(anyhow!("open NVS namespace {}: {:?}", NVS_GCP_NS, e));
            }
        };

        let project_id = read_str(&nvs, NVS_GCP_NS, NVS_PROJECT_ID, 96)?;
        let sa_email = read_str(&nvs, NVS_GCP_NS, NVS_SA_EMAIL, 128)?;
        let sa_key_id = read_str(&nvs, NVS_GCP_NS, NVS_SA_KEY_ID, 96)?;
        let sa_key_pem = read_blob(&nvs, NVS_GCP_NS, NVS_SA_KEY_PEM, 4096)?;

        match (project_id, sa_email, sa_key_id, sa_key_pem) {
            (Some(p), Some(e), Some(k), Some(pem)) => Ok(Some(Self {
                project_id: p,
                sa_email: e,
                sa_key_id: k,
                sa_key_pem: pem,
                min_severity: read_severity(&nvs),
                metrics_interval_secs: nvs
                    .get_u32(NVS_METRICS_INTERVAL_SECS)
                    .ok()
                    .flatten()
                    .unwrap_or(DEFAULT_METRICS_INTERVAL_SECS),
            })),
            _ => Ok(None),
        }
    }
}

fn read_severity(nvs: &EspNvs<esp_idf_svc::nvs::NvsDefault>) -> Level {
    // 0=TRACE, 1=DEBUG, 2=INFO (default), 3=WARN, 4=ERROR
    match nvs.get_u8(NVS_MIN_SEVERITY).ok().flatten() {
        Some(0) => Level::TRACE,
        Some(1) => Level::DEBUG,
        Some(3) => Level::WARN,
        Some(4) => Level::ERROR,
        _ => Level::INFO,
    }
}

/// One captured log event.
#[derive(Debug, Clone)]
pub struct LogEntry {
    /// UNIX time in seconds when the event was emitted, or None if
    /// captured before NTP sync. Cloud Logging accepts None and assigns
    /// server-side time.
    pub timestamp_unix_secs: Option<u64>,
    pub severity: Level,
    pub target: String,
    pub message: String,
    pub fields: serde_json::Map<String, serde_json::Value>,
    /// Number of entries dropped from the queue *before* this entry was
    /// pushed. Cloud Logging readers can use this to spot lossy windows.
    pub dropped_before: u32,
}

/// Bounded ring-buffer of pending log entries. Drop-oldest when full.
#[derive(Clone)]
pub struct LogQueue {
    inner: Arc<Mutex<QueueInner>>,
}

struct QueueInner {
    deque: VecDeque<LogEntry>,
    capacity: usize,
    pending_dropped: u32,
    /// Lifetime drop count (for the metrics path; never reset).
    dropped_total: u64,
}

impl LogQueue {
    pub fn new(capacity: usize) -> Self {
        Self {
            inner: Arc::new(Mutex::new(QueueInner {
                deque: VecDeque::with_capacity(capacity),
                capacity,
                pending_dropped: 0,
                dropped_total: 0,
            })),
        }
    }

    pub fn push(&self, mut entry: LogEntry) {
        // Recover from a poisoned mutex rather than silently dropping
        // every subsequent log entry forever (poisoning sticks for the
        // life of the process). The protected state is just a deque +
        // counters, so a partial mutation from a panicking caller is
        // safe to keep using.
        let mut g = self.inner.lock().unwrap_or_else(|e| e.into_inner());
        // Apply any pending drop-counter to this entry, then drop oldest
        // if we're at capacity.
        entry.dropped_before = g.pending_dropped;
        g.pending_dropped = 0;
        if g.deque.len() == g.capacity {
            g.deque.pop_front();
            g.pending_dropped = g.pending_dropped.saturating_add(1);
            g.dropped_total = g.dropped_total.saturating_add(1);
        }
        g.deque.push_back(entry);
    }

    /// Drain up to `max` entries.
    pub fn drain(&self, max: usize) -> Vec<LogEntry> {
        let mut g = self.inner.lock().unwrap_or_else(|e| e.into_inner());
        let n = g.deque.len().min(max);
        g.deque.drain(..n).collect()
    }

    /// Current queue depth + lifetime drop count, for the metrics path.
    pub fn stats(&self) -> (usize, u64) {
        let g = self.inner.lock().unwrap_or_else(|e| e.into_inner());
        (g.deque.len(), g.dropped_total)
    }
}

/// `tracing_subscriber::Layer` that captures events into a `LogQueue`.
pub struct CloudLogLayer {
    queue: LogQueue,
    min_level: Level,
}

impl CloudLogLayer {
    pub fn new(queue: LogQueue, min_level: Level) -> Self {
        Self { queue, min_level }
    }
}

impl<S: Subscriber> Layer<S> for CloudLogLayer {
    fn on_event(&self, event: &Event<'_>, _ctx: LayerContext<'_, S>) {
        // Skip events emitted by the modules that drive the cloud
        // pipeline themselves — otherwise their tracing calls land on
        // the queue they're draining (or that the metrics POST path
        // uses) and create a tight feedback loop.
        // `TARGET` constants come from each module's `module_path!()`,
        // so renaming the firmware crate doesn't silently break this.
        let target = event.metadata().target();
        if target == TARGET
            || target == crate::gcp_auth::TARGET
            || target == crate::metrics::TARGET
        {
            return;
        }
        let level = *event.metadata().level();
        if level > self.min_level {
            // tracing's Level ordering: TRACE > DEBUG > INFO > WARN > ERROR.
            // We want events whose level is <= min_level (i.e. equally
            // verbose or louder).
            return;
        }
        let mut visitor = FieldCapture::default();
        event.record(&mut visitor);
        let entry = LogEntry {
            timestamp_unix_secs: now_unix_secs(),
            severity: level,
            target: target.to_string(),
            message: visitor.message,
            fields: visitor.fields,
            dropped_before: 0,
        };
        self.queue.push(entry);
    }
}

#[derive(Default)]
struct FieldCapture {
    message: String,
    fields: serde_json::Map<String, serde_json::Value>,
}

impl tracing::field::Visit for FieldCapture {
    fn record_str(&mut self, field: &tracing::field::Field, value: &str) {
        self.put(field.name(), serde_json::Value::String(value.to_string()));
    }
    fn record_i64(&mut self, field: &tracing::field::Field, value: i64) {
        self.put(field.name(), serde_json::Value::Number(value.into()));
    }
    fn record_u64(&mut self, field: &tracing::field::Field, value: u64) {
        self.put(field.name(), serde_json::Value::Number(value.into()));
    }
    fn record_bool(&mut self, field: &tracing::field::Field, value: bool) {
        self.put(field.name(), serde_json::Value::Bool(value));
    }
    fn record_f64(&mut self, field: &tracing::field::Field, value: f64) {
        let v = serde_json::Number::from_f64(value)
            .map(serde_json::Value::Number)
            .unwrap_or(serde_json::Value::Null);
        self.put(field.name(), v);
    }
    fn record_debug(
        &mut self,
        field: &tracing::field::Field,
        value: &dyn std::fmt::Debug,
    ) {
        self.put(
            field.name(),
            serde_json::Value::String(format!("{:?}", value)),
        );
    }
}

impl FieldCapture {
    fn put(&mut self, name: &str, value: serde_json::Value) {
        if name == "message" {
            // The macro's positional message string is captured via
            // record_debug → Display formatting; pull it out as the
            // top-level message rather than a nested field.
            if let serde_json::Value::String(s) = value {
                self.message = s;
            } else {
                self.message = value.to_string();
            }
        } else {
            self.fields.insert(name.to_string(), value);
        }
    }
}

/// Sender thread main loop. Drains the queue every `FLUSH_INTERVAL`,
/// pulls the bearer from the shared `TokenProvider`, and POSTs batches
/// to Cloud Logging.
pub fn run(
    cfg: GcpConfig,
    fw_version: &'static str,
    auth: Arc<TokenProvider>,
    queue: LogQueue,
    short_https: ShortHttpsLock,
) -> ! {
    crate::metrics::publish_self(&crate::metrics::handles::CLOUD_LOG);
    tracing::info!(
        project = %cfg.project_id,
        sa = %cfg.sa_email,
        min_severity = ?cfg.min_severity,
        "cloud_log: sender starting",
    );

    let mac = device_mac();
    let log_name = format!("projects/{}/logs/esp32-firmware", cfg.project_id);

    let mut consecutive_failures: u32 = 0;
    // Monotonic per-process counter used (with the device MAC) to
    // build a unique `insertId` for each log entry, so Cloud Logging
    // preserves stable order within a single second of wall time.
    // u32 wraps at ~4.3 B which is plenty for our flush rate; the
    // xtensa-esp32-espidf target only supports atomics up to 32 bits
    // (max-atomic-width=32, no native 64-bit CAS), so AtomicU64 won't
    // even compile here.
    let insert_seq: AtomicU32 = AtomicU32::new(0);
    loop {
        let sleep_for = if consecutive_failures > 0 {
            // Exponential backoff capped at 5 min for cloud-logging
            // failures (separate budget from the OTA loop). With
            // FLUSH_INTERVAL = 5 s, exp = 6 hits the 320 s peak which
            // we then cap at 300 s; smaller exp caps would never reach
            // the 5-min ceiling at all.
            let exp = consecutive_failures.min(6);
            Duration::from_secs(FLUSH_INTERVAL.as_secs() << exp).min(Duration::from_secs(300))
        } else {
            FLUSH_INTERVAL
        };
        std::thread::sleep(sleep_for);

        // Skip — but don't drain — when an OTA download is streaming.
        // Our handshake's ~25-30 KB doesn't fit alongside the held-open
        // download TLS session on this chip's heap. Entries accumulate
        // in the bounded queue and flush in a single batched POST once
        // the download completes (or fails). See OTA_DOWNLOAD_IN_PROGRESS.
        if ota_download_in_progress() {
            tracing::debug!("cloud_log: ota download in progress, skipping flush");
            continue;
        }

        let batch = queue.drain(BATCH_MAX_ENTRIES);
        if batch.is_empty() {
            consecutive_failures = 0;
            continue;
        }

        // Hold the short-https lock from token-refresh through POST.
        // `auth.get_or_refresh()` may transparently mint a new token,
        // which is itself an HTTPS POST to oauth2.googleapis.com — both
        // the mint and the entries:write call need to be inside the
        // lock to actually serialise vs metrics + OTA short fetches.
        let _lock = short_https.lock().unwrap_or_else(|e| e.into_inner());
        let bearer = match auth.get_or_refresh() {
            Ok(b) => b,
            Err(e) => {
                consecutive_failures = consecutive_failures.saturating_add(1);
                tracing::warn!(
                    failures = consecutive_failures,
                    error = %format!("{:#}", e),
                    "cloud_log: token mint failed",
                );
                continue;
            }
        };

        match post_batch(
            &log_name,
            &cfg.project_id,
            &mac,
            fw_version,
            &bearer,
            &batch,
            &insert_seq,
        ) {
            Ok(()) => {
                tracing::debug!(
                    entries = batch.len(),
                    "cloud_log: posted batch",
                );
                consecutive_failures = 0;
            }
            Err(e) => {
                consecutive_failures = consecutive_failures.saturating_add(1);
                tracing::warn!(
                    entries = batch.len(),
                    failures = consecutive_failures,
                    error = %format!("{:#}", e),
                    "cloud_log: post failed; dropping batch",
                );
                // Drop the batch on failure rather than re-enqueue
                // (avoids unbounded growth on a long outage). Loss is
                // already surfaced via dropped_before on subsequent
                // entries.
            }
        }
    }
}

#[derive(Serialize)]
struct WriteEntriesRequest<'a> {
    #[serde(rename = "logName")]
    log_name: &'a str,
    resource: MonitoredResource<'a>,
    entries: Vec<Entry>,
}

#[derive(Serialize)]
struct MonitoredResource<'a> {
    #[serde(rename = "type")]
    type_: &'static str,
    labels: ResourceLabels<'a>,
}

#[derive(Serialize)]
struct ResourceLabels<'a> {
    project_id: &'a str,
    location: &'static str,
    namespace: &'static str,
    node_id: &'a str,
}

#[derive(Serialize)]
struct Entry {
    severity: &'static str,
    #[serde(rename = "jsonPayload")]
    json_payload: serde_json::Value,
    #[serde(rename = "timestamp", skip_serializing_if = "Option::is_none")]
    timestamp: Option<String>,
    /// Cloud Logging uses `insertId` to break ties on equal timestamps
    /// (and to dedupe re-sent entries). Our timestamps are
    /// second-resolution, so without this, Cloud Logging UI tends to
    /// shuffle within-second log lines on read.
    #[serde(rename = "insertId")]
    insert_id: String,
}

fn post_batch(
    log_name: &str,
    project_id: &str,
    mac: &str,
    fw_version: &str,
    bearer: &str,
    batch: &[LogEntry],
    insert_seq: &AtomicU32,
) -> Result<()> {
    let entries: Vec<Entry> = batch
        .iter()
        .map(|e| Entry {
            severity: severity_str(e.severity),
            json_payload: build_payload(e, fw_version),
            timestamp: e.timestamp_unix_secs.and_then(unix_to_rfc3339),
            insert_id: format!("{}-{}", mac, insert_seq.fetch_add(1, Ordering::Relaxed)),
        })
        .collect();

    let req = WriteEntriesRequest {
        log_name,
        resource: MonitoredResource {
            type_: "generic_node",
            labels: ResourceLabels {
                project_id,
                location: "global",
                namespace: "esp32",
                node_id: mac,
            },
        },
        entries,
    };
    let body = serde_json::to_vec(&req)?;
    let auth = format!("Bearer {}", bearer);
    http_post(
        "https://logging.googleapis.com/v2/entries:write",
        "application/json",
        &body,
        Some(&auth),
    )
    .map(|_| ())
}

fn severity_str(level: Level) -> &'static str {
    // Cloud Logging severities (LogSeverity enum):
    // https://cloud.google.com/logging/docs/reference/v2/rest/v2/LogEntry#logseverity
    match level {
        Level::TRACE => "DEBUG",
        Level::DEBUG => "DEBUG",
        Level::INFO => "INFO",
        Level::WARN => "WARNING",
        Level::ERROR => "ERROR",
    }
}

fn build_payload(e: &LogEntry, fw_version: &str) -> serde_json::Value {
    let mut map = e.fields.clone();
    map.insert(
        "message".to_string(),
        serde_json::Value::String(e.message.clone()),
    );
    map.insert(
        "module".to_string(),
        serde_json::Value::String(e.target.clone()),
    );
    // Tag every entry with the firmware git SHA so behaviour can be
    // bucketed by release in Cloud Logging
    // (`jsonPayload.fw_version="..."`). Adds ~15 bytes/entry.
    map.insert(
        "fw_version".to_string(),
        serde_json::Value::String(fw_version.to_string()),
    );
    if e.dropped_before > 0 {
        map.insert(
            "dropped_before".to_string(),
            serde_json::Value::Number(e.dropped_before.into()),
        );
    }
    serde_json::Value::Object(map)
}
