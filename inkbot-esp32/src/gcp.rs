//! Slim Cloud Logging + Cloud Monitoring client.
//!
//! JWT RS256 uses mbedTLS already linked for HTTPS, so the firmware
//! does not pull the Rust `rsa` crate. One cached access token covers
//! both APIs. Posts run on the inkbot main loop (no extra stacks).

use anyhow::{anyhow, bail, Context, Result};
use esp_idf_svc::nvs::{EspDefaultNvsPartition, EspNvs};
use log::{Level, Log, Metadata, Record};
use serde::Deserialize;
use std::collections::VecDeque;
use std::sync::{Arc, Mutex};
use std::time::Instant;

use crate::https::{
    device_mac, http_post, now_unix_secs, ota_download_in_progress, ShortHttpsLock,
};
use crate::nvs_util::{is_not_found, read_blob, read_str};
use inkbot_esp32::ota_format::b64url;

const NVS_GCP_NS: &str = "gcp";
pub const QUEUE_CAPACITY: usize = 64;
const BATCH_MAX: usize = 20;
const DEFAULT_METRICS_INTERVAL_SECS: u32 = 300;

const SCOPES: &str =
    "https://www.googleapis.com/auth/logging.write https://www.googleapis.com/auth/monitoring.write";

#[derive(Clone)]
pub struct GcpConfig {
    pub project_id: String,
    pub sa_email: String,
    pub sa_key_id: String,
    pub sa_key_pem: Vec<u8>,
    pub min_level: Level,
    pub metrics_interval_secs: u32,
}

impl GcpConfig {
    pub fn load(partition: EspDefaultNvsPartition) -> Result<Option<Self>> {
        let nvs = match EspNvs::new(partition, NVS_GCP_NS, false) {
            Ok(n) => n,
            Err(e) if is_not_found(&e) => return Ok(None),
            Err(e) => return Err(anyhow!("open NVS {NVS_GCP_NS}: {e:?}")),
        };
        let project_id = read_str(&nvs, NVS_GCP_NS, "project_id", 96)?;
        let sa_email = read_str(&nvs, NVS_GCP_NS, "sa_email", 128)?;
        let sa_key_id = read_str(&nvs, NVS_GCP_NS, "sa_key_id", 96)?;
        let sa_key_pem = read_blob(&nvs, NVS_GCP_NS, "sa_key_pem", 4096)?;
        match (project_id, sa_email, sa_key_id, sa_key_pem) {
            (Some(p), Some(e), Some(k), Some(pem)) => Ok(Some(Self {
                project_id: p,
                sa_email: e,
                sa_key_id: k,
                sa_key_pem: pem,
                min_level: match nvs.get_u8("min_severity").ok().flatten() {
                    Some(0) | Some(1) => Level::Debug,
                    Some(3) => Level::Warn,
                    Some(4) => Level::Error,
                    _ => Level::Info,
                },
                metrics_interval_secs: nvs
                    .get_u32("metric_intvl")
                    .ok()
                    .flatten()
                    .unwrap_or(DEFAULT_METRICS_INTERVAL_SECS),
            })),
            _ => Ok(None),
        }
    }
}

#[derive(Clone)]
pub struct LogQueue {
    inner: Arc<Mutex<QueueInner>>,
}

struct QueueInner {
    deque: VecDeque<LogEntry>,
    capacity: usize,
    pending_dropped: u32,
    dropped_total: u64,
}

#[derive(Clone)]
struct LogEntry {
    timestamp_unix_secs: Option<u64>,
    severity: &'static str,
    target: String,
    message: String,
    dropped_before: u32,
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

    fn push(&self, mut entry: LogEntry) {
        let mut g = self.inner.lock().unwrap_or_else(|e| e.into_inner());
        entry.dropped_before = g.pending_dropped;
        g.pending_dropped = 0;
        if g.deque.len() == g.capacity {
            g.deque.pop_front();
            g.pending_dropped = g.pending_dropped.saturating_add(1);
            g.dropped_total = g.dropped_total.saturating_add(1);
        }
        g.deque.push_back(entry);
    }

    fn drain(&self, max: usize) -> Vec<LogEntry> {
        let mut g = self.inner.lock().unwrap_or_else(|e| e.into_inner());
        let n = g.deque.len().min(max);
        g.deque.drain(..n).collect()
    }

    fn stats(&self) -> (usize, u64) {
        let g = self.inner.lock().unwrap_or_else(|e| e.into_inner());
        (g.deque.len(), g.dropped_total)
    }
}

/// Serial + optional Cloud Logging sink.
pub struct ForkLogger {
    queue: Option<LogQueue>,
    min: Level,
}

impl ForkLogger {
    pub fn install(queue: Option<(LogQueue, Level)>) {
        let (queue, min) = match queue {
            Some((q, l)) => (Some(q), l),
            None => (None, Level::Info),
        };
        let _ = log::set_boxed_logger(Box::new(Self { queue, min }));
        log::set_max_level(log::LevelFilter::Info);
    }
}

impl Log for ForkLogger {
    fn enabled(&self, _metadata: &Metadata) -> bool {
        true
    }

    fn log(&self, record: &Record) {
        // EspLogger is a type alias (not a unit struct) in esp-idf-svc 0.52.
        // Compose the IDF logger with a no-op filter so serial format matches
        // `make monitor` without installing it as the global logger.
        static SERIAL: esp_idf_svc::log::EspIdfLogger = esp_idf_svc::log::EspIdfLogger::new(());
        SERIAL.log(record);
        let Some(queue) = &self.queue else {
            return;
        };
        if record.level() > self.min {
            return;
        }
        if record.target().contains("gcp") || record.target().contains("https") {
            return;
        }
        queue.push(LogEntry {
            timestamp_unix_secs: now_unix_secs(),
            severity: gcp_severity(record.level()),
            target: record.target().to_string(),
            message: record.args().to_string(),
            dropped_before: 0,
        });
    }

    fn flush(&self) {}
}

fn gcp_severity(level: Level) -> &'static str {
    match level {
        Level::Error => "ERROR",
        Level::Warn => "WARNING",
        Level::Info => "INFO",
        Level::Debug | Level::Trace => "DEBUG",
    }
}

struct CachedToken {
    token: String,
    expires_at_unix: u64,
}

pub struct TokenProvider {
    cfg: GcpConfig,
    cache: Mutex<Option<CachedToken>>,
}

impl TokenProvider {
    pub fn new(cfg: GcpConfig) -> Self {
        Self {
            cfg,
            cache: Mutex::new(None),
        }
    }

    pub fn get_or_refresh(&self) -> Result<String> {
        let mut g = self
            .cache
            .lock()
            .map_err(|_| anyhow!("token cache mutex poisoned"))?;
        if let Some(t) = g.as_ref() {
            if let Some(now) = now_unix_secs() {
                if now + 300 < t.expires_at_unix {
                    return Ok(t.token.clone());
                }
            }
        }
        let new = mint_access_token(&self.cfg)?;
        let bearer = new.token.clone();
        *g = Some(new);
        Ok(bearer)
    }
}

#[derive(Deserialize)]
struct TokenResp {
    access_token: String,
    expires_in: u64,
}

fn mint_access_token(cfg: &GcpConfig) -> Result<CachedToken> {
    let now = now_unix_secs().ok_or_else(|| anyhow!("NTP not synced; cannot mint JWT"))?;
    let header = format!(
        r#"{{"alg":"RS256","typ":"JWT","kid":"{}"}}"#,
        json_escape(&cfg.sa_key_id)
    );
    let claims = format!(
        r#"{{"iss":"{}","scope":"{}","aud":"https://oauth2.googleapis.com/token","iat":{},"exp":{}}}"#,
        json_escape(&cfg.sa_email),
        SCOPES,
        now,
        now + 3600
    );
    let signing_input = format!(
        "{}.{}",
        b64url(header.as_bytes()),
        b64url(claims.as_bytes())
    );
    let sig = mbedtls_rs256_sign(&cfg.sa_key_pem, signing_input.as_bytes())?;
    let jwt = format!("{}.{}", signing_input, b64url(&sig));
    let body =
        format!("grant_type=urn%3Aietf%3Aparams%3Aoauth%3Agrant-type%3Ajwt-bearer&assertion={jwt}");
    let resp_bytes = http_post(
        "https://oauth2.googleapis.com/token",
        "application/x-www-form-urlencoded",
        body.as_bytes(),
        None,
    )
    .context("POST oauth2/token")?;
    let resp: TokenResp =
        serde_json::from_slice(&resp_bytes).context("parse token response JSON")?;
    Ok(CachedToken {
        token: resp.access_token,
        expires_at_unix: now + resp.expires_in,
    })
}

fn json_escape(s: &str) -> String {
    s.replace('\\', "\\\\").replace('"', "\\\"")
}

fn mbedtls_rs256_sign(pem: &[u8], message: &[u8]) -> Result<Vec<u8>> {
    use core::ffi::c_void;
    use esp_idf_svc::sys::{
        esp_fill_random, mbedtls_md_type_t_MBEDTLS_MD_SHA256, mbedtls_pk_context, mbedtls_pk_free,
        mbedtls_pk_init, mbedtls_pk_parse_key, mbedtls_pk_sign, mbedtls_sha256,
        MBEDTLS_PK_SIGNATURE_MAX_SIZE,
    };

    unsafe extern "C" fn rng(_p: *mut c_void, output: *mut u8, len: usize) -> i32 {
        unsafe {
            esp_fill_random(output as *mut c_void, len);
        }
        0
    }

    let mut pem_z = pem.to_vec();
    while pem_z.last() == Some(&b'\n') || pem_z.last() == Some(&b'\r') || pem_z.last() == Some(&0) {
        pem_z.pop();
    }
    pem_z.push(0);

    unsafe {
        let mut pk: mbedtls_pk_context = core::mem::zeroed();
        mbedtls_pk_init(&mut pk);
        let parsed = mbedtls_pk_parse_key(
            &mut pk,
            pem_z.as_ptr(),
            pem_z.len(),
            core::ptr::null(),
            0,
            Some(rng),
            core::ptr::null_mut(),
        );
        if parsed != 0 {
            mbedtls_pk_free(&mut pk);
            bail!("mbedtls_pk_parse_key {parsed}");
        }
        let mut hash = [0u8; 32];
        mbedtls_sha256(message.as_ptr(), message.len(), hash.as_mut_ptr(), 0);
        let mut sig = vec![0u8; MBEDTLS_PK_SIGNATURE_MAX_SIZE as usize];
        let mut sig_len = 0usize;
        let signed = mbedtls_pk_sign(
            &mut pk,
            mbedtls_md_type_t_MBEDTLS_MD_SHA256,
            hash.as_ptr(),
            hash.len(),
            sig.as_mut_ptr(),
            sig.len(),
            &mut sig_len,
            Some(rng),
            core::ptr::null_mut(),
        );
        mbedtls_pk_free(&mut pk);
        if signed != 0 {
            bail!("mbedtls_pk_sign {signed}");
        }
        sig.truncate(sig_len);
        Ok(sig)
    }
}

/// Optional GCP handle owned by the main loop.
pub struct GcpClient {
    cfg: GcpConfig,
    auth: TokenProvider,
    queue: LogQueue,
    lock: ShortHttpsLock,
    next_metrics: Instant,
    fw_version: &'static str,
}

impl GcpClient {
    pub fn start(
        cfg: GcpConfig,
        queue: LogQueue,
        lock: ShortHttpsLock,
        fw_version: &'static str,
    ) -> Self {
        let interval = cfg.metrics_interval_secs;
        Self {
            auth: TokenProvider::new(cfg.clone()),
            cfg,
            queue,
            lock,
            next_metrics: Instant::now() + std::time::Duration::from_secs(interval.max(30) as u64),
            fw_version,
        }
    }

    pub fn tick(&mut self) {
        if ota_download_in_progress() {
            return;
        }
        if let Err(e) = self.flush_logs() {
            log::warn!("gcp log flush: {e:#}");
        }
        if self.cfg.metrics_interval_secs > 0 && Instant::now() >= self.next_metrics {
            match self.post_metrics() {
                Ok(()) => {
                    self.next_metrics = Instant::now()
                        + std::time::Duration::from_secs(self.cfg.metrics_interval_secs as u64);
                }
                Err(e) => {
                    log::warn!("gcp metrics: {e:#}");
                    self.next_metrics = Instant::now() + std::time::Duration::from_secs(60);
                }
            }
        }
    }

    fn flush_logs(&self) -> Result<()> {
        let entries = self.queue.drain(BATCH_MAX);
        if entries.is_empty() {
            return Ok(());
        }
        let _g = crate::https::lock_or_poison(&self.lock);
        let bearer = self.auth.get_or_refresh()?;
        let mac = device_mac();
        let mut body = String::from("{\"logName\":\"projects/");
        body.push_str(&self.cfg.project_id);
        body.push_str("/logs/inkbot-esp32\",\"resource\":{\"type\":\"generic_node\",\"labels\":{");
        body.push_str("\"project_id\":\"");
        body.push_str(&json_escape(&self.cfg.project_id));
        body.push_str("\",\"location\":\"global\",\"namespace\":\"inkbot\",\"node_id\":\"");
        body.push_str(&mac);
        body.push_str("\"}},\"entries\":[");
        for (i, e) in entries.iter().enumerate() {
            if i > 0 {
                body.push(',');
            }
            body.push('{');
            body.push_str("\"severity\":\"");
            body.push_str(e.severity);
            body.push('"');
            if let Some(secs) = e.timestamp_unix_secs {
                body.push_str(&format!(
                    ",\"timestamp\":{{\"seconds\":\"{secs}\",\"nanos\":0}}"
                ));
            }
            body.push_str(",\"jsonPayload\":{\"message\":\"");
            body.push_str(&json_escape(&e.message));
            body.push_str("\",\"module\":\"");
            body.push_str(&json_escape(&e.target));
            body.push_str("\",\"fw\":\"");
            body.push_str(self.fw_version);
            body.push('"');
            if e.dropped_before > 0 {
                body.push_str(",\"dropped_before\":");
                body.push_str(&e.dropped_before.to_string());
            }
            body.push_str("}}");
        }
        body.push_str("]}");
        let auth = format!("Bearer {bearer}");
        http_post(
            "https://logging.googleapis.com/v2/entries:write",
            "application/json",
            body.as_bytes(),
            Some(&auth),
        )
        .map(|_| ())
    }

    fn post_metrics(&self) -> Result<()> {
        let now = now_unix_secs().ok_or_else(|| anyhow!("NTP not synced"))?;
        let _g = crate::https::lock_or_poison(&self.lock);
        let bearer = self.auth.get_or_refresh()?;
        let mac = device_mac();
        let (depth, dropped) = self.queue.stats();
        let (free, min, big, rssi, uptime) = unsafe {
            let mut ap: esp_idf_svc::sys::wifi_ap_record_t = core::mem::zeroed();
            let rssi = if esp_idf_svc::sys::esp_wifi_sta_get_ap_info(&mut ap)
                == esp_idf_svc::sys::ESP_OK
            {
                Some(ap.rssi as i64)
            } else {
                None
            };
            (
                esp_idf_svc::sys::esp_get_free_heap_size() as i64,
                esp_idf_svc::sys::esp_get_minimum_free_heap_size() as i64,
                esp_idf_svc::sys::heap_caps_get_largest_free_block(
                    esp_idf_svc::sys::MALLOC_CAP_8BIT,
                ) as i64,
                rssi,
                esp_idf_svc::sys::esp_timer_get_time() / 1_000_000,
            )
        };
        let mut series: Vec<(&str, i64)> = vec![
            ("free_heap", free),
            ("min_free_heap", min),
            ("largest_free_block", big),
            ("uptime_secs", uptime),
            ("cloud_log_queue_depth", depth as i64),
            ("cloud_log_dropped_total", dropped as i64),
        ];
        if let Some(r) = rssi {
            series.push(("wifi_rssi", r));
        }
        let mut body = String::from("{\"timeSeries\":[");
        for (i, (name, value)) in series.iter().enumerate() {
            if i > 0 {
                body.push(',');
            }
            body.push_str("{\"metric\":{\"type\":\"custom.googleapis.com/inkbot/");
            body.push_str(name);
            body.push_str("\",\"labels\":{\"fw_version\":\"");
            body.push_str(self.fw_version);
            body.push_str(
                "\"}},\"resource\":{\"type\":\"generic_node\",\"labels\":{\"project_id\":\"",
            );
            body.push_str(&json_escape(&self.cfg.project_id));
            body.push_str("\",\"location\":\"global\",\"namespace\":\"inkbot\",\"node_id\":\"");
            body.push_str(&mac);
            body.push_str(
                "\"}},\"metricKind\":\"GAUGE\",\"valueType\":\"INT64\",\"points\":[{\"interval\":{\"endTime\":{\"seconds\":\"",
            );
            body.push_str(&now.to_string());
            body.push_str("\"}},\"value\":{\"int64Value\":\"");
            body.push_str(&value.to_string());
            body.push_str("\"}}]}");
        }
        body.push_str("]}");
        let url = format!(
            "https://monitoring.googleapis.com/v3/projects/{}/timeSeries",
            self.cfg.project_id
        );
        let auth = format!("Bearer {bearer}");
        http_post(&url, "application/json", body.as_bytes(), Some(&auth)).map(|_| ())
    }
}
