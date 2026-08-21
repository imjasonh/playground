//! Shared HTTPS helpers and heap gates for OTA + GCP + Worker fetches.

use anyhow::{bail, Context, Result};
use embedded_svc::http::client::Client;
use embedded_svc::http::Method;
use embedded_svc::io::Write;
use esp_idf_svc::http::client::{
    Configuration as HttpConfig, EspHttpConnection, FollowRedirectsPolicy,
};
use std::sync::atomic::{AtomicBool, Ordering};
use std::sync::{Arc, Mutex};
use std::time::Duration;

/// Set while an OTA blob download holds a TLS session open. Frame
/// fetches and GCP posts skip that window so a second handshake does
/// not OOM the 48 KB framebuffer path.
pub static OTA_DOWNLOAD_IN_PROGRESS: AtomicBool = AtomicBool::new(false);

pub struct OtaDownloadGuard;

impl OtaDownloadGuard {
    pub fn enter() -> Self {
        OTA_DOWNLOAD_IN_PROGRESS.store(true, Ordering::Release);
        Self
    }
}

impl Drop for OtaDownloadGuard {
    fn drop(&mut self) {
        OTA_DOWNLOAD_IN_PROGRESS.store(false, Ordering::Release);
    }
}

pub fn ota_download_in_progress() -> bool {
    OTA_DOWNLOAD_IN_PROGRESS.load(Ordering::Acquire)
}

pub type ShortHttpsLock = Arc<Mutex<()>>;

pub fn new_short_https_lock() -> ShortHttpsLock {
    Arc::new(Mutex::new(()))
}

/// Wall-clock UNIX seconds, or None if SNTP has not synced (clock still
/// before 2020-01-01).
pub fn now_unix_secs() -> Option<u64> {
    use std::time::{SystemTime, UNIX_EPOCH};
    let secs = SystemTime::now().duration_since(UNIX_EPOCH).ok()?.as_secs();
    if secs < 1_577_836_800 {
        None
    } else {
        Some(secs)
    }
}

/// Chip MAC as `aabbccddeeff`.
pub fn device_mac() -> String {
    let mut mac = [0u8; 8];
    unsafe {
        esp_idf_svc::sys::esp_efuse_mac_get_default(mac.as_mut_ptr());
    }
    let mut s = String::with_capacity(12);
    for b in &mac[..6] {
        use std::fmt::Write as _;
        let _ = write!(s, "{b:02x}");
    }
    s
}

pub fn http_get(
    url: &str,
    headers: &[(&str, &str)],
    buf: &mut Vec<u8>,
    max_bytes: usize,
) -> Result<()> {
    let conn = EspHttpConnection::new(&HttpConfig {
        crt_bundle_attach: Some(esp_idf_svc::sys::esp_crt_bundle_attach),
        follow_redirects_policy: FollowRedirectsPolicy::FollowAll,
        timeout: Some(Duration::from_secs(30)),
        buffer_size: Some(1024),
        buffer_size_tx: Some(1024),
        ..Default::default()
    })?;
    let mut client = Client::wrap(conn);
    let req = client.request(Method::Get, url, headers)?;
    let mut resp = req.submit()?;
    let status = resp.status();
    if status != 200 {
        bail!("GET {url} -> {status}");
    }
    let mut chunk = [0u8; 1024];
    loop {
        let n = resp.read(&mut chunk)?;
        if n == 0 {
            break;
        }
        if buf.len().saturating_add(n) > max_bytes {
            bail!("GET {url} body exceeded {max_bytes} bytes");
        }
        buf.extend_from_slice(&chunk[..n]);
    }
    Ok(())
}

/// HTTPS POST. Returns the response body. Errors on any non-2xx.
pub fn http_post(
    url: &str,
    content_type: &str,
    body: &[u8],
    bearer: Option<&str>,
) -> Result<Vec<u8>> {
    let conn = EspHttpConnection::new(&HttpConfig {
        crt_bundle_attach: Some(esp_idf_svc::sys::esp_crt_bundle_attach),
        follow_redirects_policy: FollowRedirectsPolicy::FollowAll,
        timeout: Some(Duration::from_secs(30)),
        buffer_size: Some(2048),
        buffer_size_tx: Some(4096),
        ..Default::default()
    })?;
    let mut client = Client::wrap(conn);
    let body_len = body.len().to_string();
    let mut headers: Vec<(&str, &str)> = vec![
        ("content-type", content_type),
        ("content-length", body_len.as_str()),
        ("accept", "application/json"),
    ];
    if let Some(b) = bearer {
        headers.push(("authorization", b));
    }
    let mut req = client.request(Method::Post, url, &headers)?;
    req.write_all(body).context("write request body")?;
    req.flush().ok();
    let mut resp = req.submit()?;
    let status = resp.status();
    const MAX_BODY: usize = 32 * 1024;
    let mut buf = Vec::with_capacity(1024);
    let mut chunk = [0u8; 1024];
    loop {
        let n = resp.read(&mut chunk).context("read response chunk")?;
        if n == 0 {
            break;
        }
        if buf.len().saturating_add(n) > MAX_BODY {
            bail!("POST {url} response exceeded {MAX_BODY} bytes");
        }
        buf.extend_from_slice(&chunk[..n]);
    }
    if !(200..300).contains(&status) {
        bail!(
            "POST {} -> HTTP {} body={}",
            url,
            status,
            String::from_utf8_lossy(&buf)
        );
    }
    Ok(buf)
}

pub fn lock_or_poison(lock: &ShortHttpsLock) -> std::sync::MutexGuard<'_, ()> {
    lock.lock().unwrap_or_else(|e| e.into_inner())
}
