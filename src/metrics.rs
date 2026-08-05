//! Periodic device-health snapshots → Cloud Monitoring time series.
//!
//! Wakes every `metrics_interval_secs`, collects a chip-wide snapshot
//! (heap, stack hwm per task, wifi RSSI/channel, cpu freq, uptime,
//! NVS stats, log queue depth + drops), and POSTs one
//! `CreateTimeSeries` request to
//! `https://monitoring.googleapis.com/v3/projects/<id>/timeSeries`.
//!
//! Cloud Monitoring auto-creates a `MetricDescriptor` on first write
//! per metric type, so there's no separate provisioning step. All
//! metrics are GAUGE INT64 in v1.

use anyhow::{Context, Result};
use serde::Serialize;
use std::sync::atomic::{AtomicUsize, Ordering};
use std::sync::Arc;
use std::time::Duration;

use crate::cloud_log::{GcpConfig, LogQueue};
use crate::gcp_auth::{
    device_mac, http_post, ota_download_in_progress, unix_to_rfc3339, ShortHttpsLock,
    TokenProvider,
};

const METRIC_PREFIX: &str = "custom.googleapis.com/esp32";

/// `module_path!()` for this module — used by cloud_log to filter out
/// our own tracing events without hardcoding the crate name.
pub const TARGET: &str = module_path!();

/// FreeRTOS task handles published by each spawned thread so the
/// metrics loop can call `uxTaskGetStackHighWaterMark` per task.
/// Stored as `usize` (not `*mut c_void`) so we can use atomics; 0
/// means "not yet published, omit this field from the snapshot".
pub mod handles {
    use std::sync::atomic::AtomicUsize;
    pub static MAIN: AtomicUsize = AtomicUsize::new(0);
    pub static OTA: AtomicUsize = AtomicUsize::new(0);
    pub static CLOUD_LOG: AtomicUsize = AtomicUsize::new(0);
    pub static METRICS: AtomicUsize = AtomicUsize::new(0);
}

/// Each thread calls this once at start of its run loop.
pub fn publish_self(slot: &AtomicUsize) {
    let h = unsafe { esp_idf_svc::sys::xTaskGetCurrentTaskHandle() } as usize;
    slot.store(h, Ordering::Relaxed);
}

fn read_handle(slot: &AtomicUsize) -> Option<esp_idf_svc::sys::TaskHandle_t> {
    let v = slot.load(Ordering::Relaxed);
    if v == 0 {
        None
    } else {
        Some(v as esp_idf_svc::sys::TaskHandle_t)
    }
}

pub fn run(
    cfg: GcpConfig,
    fw_version: &'static str,
    auth: Arc<TokenProvider>,
    queue: LogQueue,
    short_https: ShortHttpsLock,
) -> ! {
    publish_self(&handles::METRICS);

    tracing::info!(
        project = %cfg.project_id,
        interval_secs = cfg.metrics_interval_secs,
        "metrics: sender starting",
    );

    let mac = device_mac();
    let url = format!(
        "https://monitoring.googleapis.com/v3/projects/{}/timeSeries",
        cfg.project_id
    );
    let interval = Duration::from_secs(cfg.metrics_interval_secs.max(1) as u64);
    let mut consecutive_failures: u32 = 0;

    loop {
        // Backoff on failure, otherwise sleep the configured interval.
        let sleep_for = if consecutive_failures > 0 {
            let exp = consecutive_failures.min(4);
            interval.saturating_mul(1 << exp).min(Duration::from_secs(3600))
        } else {
            interval
        };
        std::thread::sleep(sleep_for);

        // Skip the POST cycle while an OTA download is streaming —
        // our handshake's ~25-30 KB doesn't fit alongside the
        // held-open download TLS session on this chip's heap. We lose
        // at most one snapshot per download. See OTA_DOWNLOAD_IN_PROGRESS.
        if ota_download_in_progress() {
            tracing::debug!("metrics: ota download in progress, skipping snapshot");
            continue;
        }

        let snapshot = collect(&queue);

        // Lock spans token refresh + POST so both TLS handshakes
        // serialise against cloud_log and OTA short fetches. See the
        // matching comment in cloud_log.rs.
        let _lock = short_https.lock().unwrap_or_else(|e| e.into_inner());
        let bearer = match auth.get_or_refresh() {
            Ok(b) => b,
            Err(e) => {
                consecutive_failures = consecutive_failures.saturating_add(1);
                tracing::warn!(
                    failures = consecutive_failures,
                    error = %format!("{:#}", e),
                    "metrics: token mint failed",
                );
                continue;
            }
        };

        match post_time_series(&url, &cfg.project_id, &mac, fw_version, &bearer, &snapshot) {
            Ok(()) => {
                tracing::debug!(
                    series = snapshot.series_count(),
                    "metrics: posted",
                );
                consecutive_failures = 0;
            }
            Err(e) => {
                consecutive_failures = consecutive_failures.saturating_add(1);
                tracing::warn!(
                    failures = consecutive_failures,
                    error = %format!("{:#}", e),
                    "metrics: post failed",
                );
            }
        }
    }
}

#[derive(Default)]
struct Snapshot {
    // Memory
    free_heap: Option<i64>,
    free_heap_internal: Option<i64>,
    min_free_heap: Option<i64>,
    largest_free_block: Option<i64>,
    // Per-task stack high-water-mark (bytes remaining), task name → value
    stack_hwm: Vec<(&'static str, i64)>,
    // Wifi
    wifi_rssi: Option<i64>,
    wifi_channel: Option<i64>,
    // CPU
    cpu_freq_mhz: Option<i64>,
    // Boot / uptime
    uptime_secs: Option<i64>,
    // NVS
    nvs_used_entries: Option<i64>,
    nvs_free_entries: Option<i64>,
    // Cloud_log queue
    cloud_log_queue_depth: Option<i64>,
    cloud_log_dropped_total: Option<i64>,
}

impl Snapshot {
    fn series_count(&self) -> usize {
        let scalars = [
            self.free_heap.is_some(),
            self.free_heap_internal.is_some(),
            self.min_free_heap.is_some(),
            self.largest_free_block.is_some(),
            self.wifi_rssi.is_some(),
            self.wifi_channel.is_some(),
            self.cpu_freq_mhz.is_some(),
            self.uptime_secs.is_some(),
            self.nvs_used_entries.is_some(),
            self.nvs_free_entries.is_some(),
            self.cloud_log_queue_depth.is_some(),
            self.cloud_log_dropped_total.is_some(),
        ];
        scalars.iter().filter(|b| **b).count() + self.stack_hwm.len()
    }
}

fn collect(queue: &LogQueue) -> Snapshot {
    let mut s = Snapshot::default();

    // Memory
    unsafe {
        s.free_heap = Some(esp_idf_svc::sys::esp_get_free_heap_size() as i64);
        s.min_free_heap =
            Some(esp_idf_svc::sys::esp_get_minimum_free_heap_size() as i64);
        let largest = esp_idf_svc::sys::heap_caps_get_largest_free_block(
            esp_idf_svc::sys::MALLOC_CAP_DEFAULT,
        );
        s.largest_free_block = Some(largest as i64);
        let internal = esp_idf_svc::sys::heap_caps_get_free_size(
            esp_idf_svc::sys::MALLOC_CAP_INTERNAL,
        );
        s.free_heap_internal = Some(internal as i64);
    }

    // Stack high-water-mark per published task. ESP-IDF's
    // `uxTaskGetStackHighWaterMark` returns the value in StackType_t
    // units; on Xtensa StackType_t is uint8_t, so the return is bytes
    // remaining at low-water. (Generic FreeRTOS docs say "words"; the
    // ESP-IDF port differs.)
    for (name, slot) in [
        ("main", &handles::MAIN),
        ("ota", &handles::OTA),
        ("cloud_log", &handles::CLOUD_LOG),
        ("metrics", &handles::METRICS),
    ] {
        if let Some(h) = read_handle(slot) {
            let bytes = unsafe { esp_idf_svc::sys::uxTaskGetStackHighWaterMark(h) };
            s.stack_hwm.push((name, bytes as i64));
        }
    }

    // Wifi (rssi + channel, only meaningful when associated)
    let mut ap_info: esp_idf_svc::sys::wifi_ap_record_t = unsafe { core::mem::zeroed() };
    let err = unsafe { esp_idf_svc::sys::esp_wifi_sta_get_ap_info(&mut ap_info) };
    if err == esp_idf_svc::sys::ESP_OK {
        s.wifi_rssi = Some(ap_info.rssi as i64);
        s.wifi_channel = Some(ap_info.primary as i64);
    }

    // CPU clock. The runtime accessor `esp_clk_cpu_freq` isn't exposed
    // through esp-idf-svc's bindings, so report the build-time
    // configured default. Accurate while CONFIG_PM_ENABLE=n (our
    // setup); when we adopt esp_pm_* this needs to use a runtime API.
    s.cpu_freq_mhz = Some(esp_idf_svc::sys::CONFIG_ESP_DEFAULT_CPU_FREQ_MHZ as i64);

    // Uptime (esp_timer_get_time returns microseconds since boot)
    unsafe {
        let micros = esp_idf_svc::sys::esp_timer_get_time();
        s.uptime_secs = Some(micros / 1_000_000);
    }

    // NVS stats (default partition; partition_name = NULL)
    let mut nvs_stats: esp_idf_svc::sys::nvs_stats_t = unsafe { core::mem::zeroed() };
    let err = unsafe {
        esp_idf_svc::sys::nvs_get_stats(core::ptr::null(), &mut nvs_stats)
    };
    if err == esp_idf_svc::sys::ESP_OK {
        s.nvs_used_entries = Some(nvs_stats.used_entries as i64);
        s.nvs_free_entries = Some(nvs_stats.free_entries as i64);
    }

    // Log queue stats
    let (depth, dropped) = queue.stats();
    s.cloud_log_queue_depth = Some(depth as i64);
    s.cloud_log_dropped_total = Some(dropped as i64);

    s
}

#[derive(Serialize)]
struct CreateTimeSeriesRequest {
    #[serde(rename = "timeSeries")]
    time_series: Vec<TimeSeries>,
}

#[derive(Serialize)]
struct TimeSeries {
    metric: Metric,
    resource: MonitoredResource,
    #[serde(rename = "metricKind")]
    metric_kind: &'static str,
    #[serde(rename = "valueType")]
    value_type: &'static str,
    points: Vec<Point>,
}

#[derive(Serialize)]
struct Metric {
    #[serde(rename = "type")]
    type_: String,
    #[serde(skip_serializing_if = "serde_json::Map::is_empty")]
    labels: serde_json::Map<String, serde_json::Value>,
}

#[derive(Serialize, Clone)]
struct MonitoredResource {
    #[serde(rename = "type")]
    type_: &'static str,
    labels: serde_json::Map<String, serde_json::Value>,
}

#[derive(Serialize)]
struct Point {
    interval: Interval,
    value: PointValue,
}

#[derive(Serialize)]
struct Interval {
    #[serde(rename = "endTime")]
    end_time: String,
}

#[derive(Serialize)]
struct PointValue {
    #[serde(rename = "int64Value")]
    int64_value: String,
}

fn post_time_series(
    url: &str,
    project_id: &str,
    mac: &str,
    fw_version: &str,
    bearer: &str,
    snapshot: &Snapshot,
) -> Result<()> {
    let now_secs = crate::gcp_auth::now_unix_secs()
        .ok_or_else(|| anyhow::anyhow!("NTP not synced; cannot stamp metric points"))?;
    let end_time = unix_to_rfc3339(now_secs)
        .ok_or_else(|| anyhow::anyhow!("RFC3339 format failed"))?;

    let resource = MonitoredResource {
        type_: "generic_node",
        labels: {
            let mut m = serde_json::Map::new();
            m.insert("project_id".into(), project_id.into());
            m.insert("location".into(), "global".into());
            m.insert("namespace".into(), "esp32".into());
            m.insert("node_id".into(), mac.into());
            m
        },
    };

    let mut series = Vec::with_capacity(snapshot.series_count());
    // `fw_version` rides on every metric as a label so Cloud Monitoring
    // can split / group by release. Resource labels can't carry it
    // because `generic_node` has a fixed schema; metric labels are
    // per-series and let queries split heap, rssi, etc. by fw.
    let mut push = |name: &str,
                    extra_labels: serde_json::Map<String, serde_json::Value>,
                    value: i64| {
        let mut labels = extra_labels;
        labels.insert(
            "fw_version".into(),
            serde_json::Value::String(fw_version.to_string()),
        );
        series.push(TimeSeries {
            metric: Metric {
                type_: format!("{}/{}", METRIC_PREFIX, name),
                labels,
            },
            resource: resource.clone(),
            metric_kind: "GAUGE",
            value_type: "INT64",
            points: vec![Point {
                interval: Interval {
                    end_time: end_time.clone(),
                },
                value: PointValue {
                    int64_value: value.to_string(),
                },
            }],
        });
    };

    let no_labels = serde_json::Map::new();
    if let Some(v) = snapshot.free_heap { push("free_heap", no_labels.clone(), v); }
    if let Some(v) = snapshot.free_heap_internal { push("free_heap_internal", no_labels.clone(), v); }
    if let Some(v) = snapshot.min_free_heap { push("min_free_heap", no_labels.clone(), v); }
    if let Some(v) = snapshot.largest_free_block { push("largest_free_block", no_labels.clone(), v); }
    if let Some(v) = snapshot.wifi_rssi { push("wifi_rssi", no_labels.clone(), v); }
    if let Some(v) = snapshot.wifi_channel { push("wifi_channel", no_labels.clone(), v); }
    if let Some(v) = snapshot.cpu_freq_mhz { push("cpu_freq_mhz", no_labels.clone(), v); }
    if let Some(v) = snapshot.uptime_secs { push("uptime_secs", no_labels.clone(), v); }
    if let Some(v) = snapshot.nvs_used_entries { push("nvs_used_entries", no_labels.clone(), v); }
    if let Some(v) = snapshot.nvs_free_entries { push("nvs_free_entries", no_labels.clone(), v); }
    if let Some(v) = snapshot.cloud_log_queue_depth { push("cloud_log_queue_depth", no_labels.clone(), v); }
    if let Some(v) = snapshot.cloud_log_dropped_total { push("cloud_log_dropped_total", no_labels.clone(), v); }
    for (task, value) in &snapshot.stack_hwm {
        let mut labels = serde_json::Map::new();
        labels.insert("task".into(), serde_json::Value::String((*task).into()));
        push("stack_hwm", labels, *value);
    }

    let req = CreateTimeSeriesRequest { time_series: series };
    let body = serde_json::to_vec(&req).context("serialize CreateTimeSeries body")?;
    let auth = format!("Bearer {}", bearer);
    http_post(url, "application/json", &body, Some(&auth)).map(|_| ())
}
