//! inkbot-esp32 — poll the inkbot Worker and show frames on Waveshare 7.5″.

mod device_config;
mod display;
#[cfg(feature = "gcp")]
mod gcp;
mod https;
mod nvs_util;
mod ota;
mod ota_slot;
mod sig;
mod trust;

use std::sync::OnceLock;
use std::thread;
use std::time::{Duration, Instant};

use anyhow::{anyhow, Result};
use embedded_svc::http::client::Client as HttpClient;
use embedded_svc::http::Method;
use embedded_svc::io::{Read, Write};
use esp_idf_svc::eventloop::EspSystemEventLoop;
use esp_idf_svc::hal::peripherals::Peripherals;
use esp_idf_svc::http::client::{Configuration as HttpConfig, EspHttpConnection};
use esp_idf_svc::nvs::{EspDefaultNvsPartition, EspNvs, NvsDefault};
use esp_idf_svc::sntp::{EspSntp, SyncStatus};
use esp_idf_svc::sys::{
    esp_get_free_heap_size, esp_get_minimum_free_heap_size, esp_random, esp_reset_reason,
    esp_timer_get_time, esp_wifi_set_max_tx_power, esp_wifi_set_ps,
    heap_caps_get_largest_free_block, wifi_ps_type_t_WIFI_PS_NONE, MALLOC_CAP_8BIT,
};
use esp_idf_svc::wifi::{
    AuthMethod, BlockingWifi, ClientConfiguration, Configuration as WifiConfig, EspWifi,
};
use log::{error, info, warn};

use device_config::AppConfig;
use display::Panel;
use inkbot_esp32::{
    crash_after_reset, format_error_chain, format_panic_message, incident_needs_post,
    is_http_connect_failure, should_post_status, should_refresh_wifi, Catalog, CrashStatus,
    DeviceTelemetry, FetchStatus, IncidentContext, LastIncident, StatusReport, WifiRefresh,
    WifiStatus, FIRMWARE_ID, FRAME_BYTES,
};
use trust::TrustConfig;

const GIT_SHA: &str = match option_env!("GIT_SHA") {
    Some(s) => s,
    None => "unknown",
};

static APP: OnceLock<AppConfig> = OnceLock::new();

fn app() -> &'static AppConfig {
    APP.get().expect("AppConfig not loaded")
}

const NVS_NS: &str = "inkbot";
const NVS_NAME: &str = "name";
const NVS_ETAG: &str = "etag";
const NVS_LATEST: &str = "latest";
const NVS_LAST_OP: &str = "op";
/// JSON blob for an unposted FETCH/WIFI incident (survives reboot / USB reset).
const NVS_INCIDENT: &str = "inc";
const INCIDENT_BLOB: usize = 1024;

const HTTP_ATTEMPTS: u32 = 3;
const WIFI_ATTEMPTS: u32 = 5;
/// Avoid tight-looping STA reconnect when the AP is actually gone.
const WIFI_RECONNECT_COOLDOWN_SECS: u64 = 120;

fn main() -> Result<()> {
    esp_idf_svc::sys::link_patches();
    install_panic_hook();

    let reset = unsafe { esp_reset_reason() } as i32;
    let heap = HeapSnap::now();

    let peripherals = Peripherals::take()?;
    let sysloop = EspSystemEventLoop::take()?;
    let nvs_part = EspDefaultNvsPartition::take()?;

    #[cfg(feature = "gcp")]
    let (gcp_cfg, pending_log_queue) = {
        let gcp_cfg = gcp::GcpConfig::load(nvs_part.clone())?;
        let pending_log_queue = if let Some(cfg) = gcp_cfg.as_ref() {
            let q = gcp::LogQueue::new(gcp::QUEUE_CAPACITY);
            gcp::ForkLogger::install(Some((q.clone(), cfg.min_level)));
            Some(q)
        } else {
            gcp::ForkLogger::install(None);
            None
        };
        (gcp_cfg, pending_log_queue)
    };
    #[cfg(not(feature = "gcp"))]
    esp_idf_svc::log::EspLogger::initialize_default();

    info!(
        "inkbot-esp32: boot fw={FIRMWARE_ID} git={GIT_SHA} reset_reason={} ({}) {}",
        inkbot_esp32::reset_reason_name(reset),
        reset,
        heap
    );

    let mut nvs = EspNvs::new(nvs_part.clone(), NVS_NS, true)
        .map_err(|e| anyhow!("open NVS {NVS_NS}: {e:?}"))?;

    let mut panel = Panel::new(
        peripherals.spi2,
        peripherals.pins.gpio13,
        peripherals.pins.gpio14,
        peripherals.pins.gpio15,
        peripherals.pins.gpio25,
        peripherals.pins.gpio27,
        peripherals.pins.gpio26,
    )?;

    let Some(cfg) = AppConfig::load(nvs_part.clone())? else {
        let _ = panel.show_status_only("NOT PROVISIONED — make provision");
        loop {
            error!("NOT PROVISIONED — run `make provision` to write NVS, then reboot");
            thread::sleep(Duration::from_secs(30));
        }
    };
    let Some(trust) = TrustConfig::load(nvs_part.clone())? else {
        let _ = panel.show_status_only("NOT PROVISIONED — trust keys missing");
        loop {
            error!("NOT PROVISIONED — trust/identities or Fulcio PEMs missing in NVS");
            thread::sleep(Duration::from_secs(30));
        }
    };
    APP.set(cfg).map_err(|_| anyhow!("AppConfig already set"))?;
    info!(
        "provisioned ssid={} base={} ota_app={} ota={}:{} poll={}s",
        app().wifi_ssid,
        app().base_url,
        app().ota_app,
        app().ota_repo,
        app().ota_tag,
        app().ota_poll_secs
    );

    let pending_verify = ota::is_pending_verify();
    if pending_verify {
        info!("ota: image is PENDING_VERIFY — Worker fetch must succeed");
    } else if let Err(e) = ota::remember_rolled_back_digest(nvs_part.clone()) {
        warn!("ota: reconcile rolled-back digest: {e:#}");
    }

    let mut status = StatusReport::default();
    let mut remote = RemoteStatus::from_nvs(&nvs);
    let nvs_last_op = read_str(&nvs, NVS_LAST_OP)?;
    let last_op = rtc_take_last_op().or(nvs_last_op);
    if crash_after_reset(reset, last_op.as_deref()) {
        status.crash = Some(CrashStatus {
            reset_code: reset,
            panic_message: rtc_take_panic(),
            last_op: last_op.clone(),
            heap: heap.free,
            heap_min: heap.min,
            heap_largest: heap.largest,
        });
        warn!("abnormal reset: {}", status.render().unwrap_or_default());
    }

    let mut wifi = BlockingWifi::wrap(
        EspWifi::new(peripherals.modem, sysloop.clone(), Some(nvs_part.clone()))?,
        sysloop,
    )?;
    thread::sleep(Duration::from_millis(500));
    loop {
        note_op(&mut nvs, "wifi");
        match connect_wifi(&mut wifi) {
            Ok(()) => {
                status.wifi = None;
                break;
            }
            Err(e) => {
                warn!("wifi failed: {e:#}");
                status.wifi = Some(wifi_status_from_err(&e, WIFI_ATTEMPTS, WIFI_ATTEMPTS));
                capture_incident(&mut remote, &nvs, &wifi, &status, "wifi");
                paint_error(&mut panel, None, &status);
                thread::sleep(Duration::from_secs(3));
            }
        }
    }
    let mut ip_str = sta_ip(&wifi)?;
    info!("wifi connected, ip={ip_str}, {}", HeapSnap::now());
    // Keep the SNTP handle so unix_secs, Sigstore validity, and GCP JWT stay valid.
    let _sntp = start_sntp();
    let https_lock = https::new_short_https_lock();
    #[cfg(feature = "gcp")]
    let mut gcp_client = match (gcp_cfg, pending_log_queue) {
        (Some(cfg), Some(queue)) => {
            info!(
                "gcp: Cloud Logging + Monitoring enabled project={}",
                cfg.project_id
            );
            Some(gcp::GcpClient::start(
                cfg,
                queue,
                https_lock.clone(),
                FIRMWARE_ID,
            ))
        }
        _ => {
            info!("gcp: not provisioned, serial only");
            None
        }
    };
    let mut ota_state = ota::OtaState::new();
    let mut last_wifi_refresh = Instant::now();
    // None = never reconnected this boot, so the first CONNECT failure
    // can recover immediately (associated-but-no-internet is common).
    let mut last_reconnect: Option<Instant> = None;

    let mut current_name = read_str(&nvs, NVS_NAME)?;
    let mut current_etag = read_str(&nvs, NVS_ETAG)?;
    let mut seen_latest = read_str(&nvs, NVS_LATEST)?;
    info!("nvs: name={current_name:?} etag={current_etag:?} latest={seen_latest:?}");

    let mut last_rotate = Instant::now();
    let mut last_frame: Option<Vec<u8>> = None;
    let mut panel_has_status;

    // Boot: one HTTPS GET of /latest.bin — a catalog+frame pair back-to-back
    // fragments the classic ESP32 heap so the 48 KB alloc fails.
    note_op(&mut nvs, "GET /latest.bin");
    match boot_latest(
        &mut panel,
        &mut nvs,
        &mut current_name,
        &mut current_etag,
        &mut seen_latest,
        &mut last_frame,
        &status,
        &ip_str,
    ) {
        Ok(Boot::Displayed(name)) => {
            last_rotate = Instant::now();
            panel_has_status = !status.is_empty();
            info!("boot displayed {name}");
        }
        Ok(Boot::Empty) => {
            info!("no images on server yet");
            if let Some(text) = status.render() {
                let _ = panel.show_status_only(&text);
                panel_has_status = true;
            } else {
                // Blank panel, no "ready" / "no errors" banner — that steals
                // image pixels. Empty catalog is not an error.
                let _ = panel.show_frame(&vec![0xffu8; FRAME_BYTES]);
                panel_has_status = false;
            }
        }
        Err(e) => {
            warn!("boot poll failed: {e:#}");
            status.fetch = Some(fetch_status_from_err(
                "boot /latest.bin",
                &format!("{}/latest.bin", app().base_url),
                &e,
                HTTP_ATTEMPTS,
                HTTP_ATTEMPTS,
                Some(ip_str.as_str()),
            ));
            capture_incident(&mut remote, &nvs, &wifi, &status, "fetch");
            paint_error(&mut panel, last_frame.as_deref(), &status);
            panel_has_status = true;
            if pending_verify {
                error!("ota: Worker fetch failed during PENDING_VERIFY; rolling back");
                note_op(&mut nvs, "ota:rollback");
                thread::sleep(Duration::from_secs(2));
                ota::reject_pending_and_reboot(nvs_part.clone());
            }
        }
    }
    if pending_verify && status.fetch.is_none() {
        match ota::mark_valid_after_pending_verify_passed(nvs_part.clone()) {
            Ok(()) => info!("ota: pending-verify passed (Worker reachable)"),
            Err(e) => {
                error!("ota: mark-valid failed ({e:#}); rolling back");
                note_op(&mut nvs, "ota:rollback");
                thread::sleep(Duration::from_secs(2));
                ota::reject_pending_and_reboot(nvs_part.clone());
            }
        }
    }

    maybe_post_device(
        &mut remote,
        &mut nvs,
        &wifi,
        true,
        &status,
        reset,
        current_name.as_deref(),
        panel_has_status,
    );

    loop {
        thread::sleep(Duration::from_secs(app().poll_secs));
        // After the first successful image the crash line has been on-screen
        // for a full poll period; drop it so the next paint is a full frame.
        if last_frame.is_some() {
            status.crash = None;
        }
        if !https::ota_download_in_progress() {
            match ota_state.tick(nvs_part.clone(), app(), &trust, &https_lock) {
                Ok(ota::PollOutcome::Updated(d)) => {
                    info!("ota: applied {d}, rebooting");
                    note_op(&mut nvs, "ota:reboot");
                    thread::sleep(Duration::from_secs(1));
                    unsafe { esp_idf_svc::sys::esp_restart() };
                }
                Ok(ota::PollOutcome::NoChange) => info!("ota: no change"),
                Ok(ota::PollOutcome::Skipped) => {}
                Err(e) => warn!("ota: poll failed: {e:#}"),
            }
        }
        #[cfg(feature = "gcp")]
        if let Some(client) = gcp_client.as_mut() {
            client.tick();
        }
        if https::ota_download_in_progress() {
            continue;
        }
        let mut recovered = maybe_refresh_wifi(
            &mut wifi,
            &mut nvs,
            &mut remote,
            &mut ip_str,
            &mut last_wifi_refresh,
            &mut last_reconnect,
            &mut status,
            false,
        );
        let mut result = tick(
            &mut panel,
            &mut nvs,
            &mut current_name,
            &mut current_etag,
            &mut seen_latest,
            &mut last_rotate,
            &mut last_frame,
            &mut status,
            &ip_str,
        );
        if let Err(ref e) = result {
            capture_incident(&mut remote, &nvs, &wifi, &status, "fetch");
            if is_http_connect_failure(&format_error_chain(e))
                && maybe_refresh_wifi(
                    &mut wifi,
                    &mut nvs,
                    &mut remote,
                    &mut ip_str,
                    &mut last_wifi_refresh,
                    &mut last_reconnect,
                    &mut status,
                    true,
                )
            {
                recovered = true;
                info!("retrying poll after wifi recovery");
                result = tick(
                    &mut panel,
                    &mut nvs,
                    &mut current_name,
                    &mut current_etag,
                    &mut seen_latest,
                    &mut last_rotate,
                    &mut last_frame,
                    &mut status,
                    &ip_str,
                );
                if result.is_err() {
                    capture_incident(&mut remote, &nvs, &wifi, &status, "fetch");
                }
            }
        }
        match result {
            Ok(Action::Displayed { name, reason }) => {
                status.fetch = None;
                panel_has_status = !status.is_empty();
                note_last_ok(&mut remote, &nvs);
                info!("displayed {name} ({reason})")
            }
            Ok(Action::Idle) => {
                status.fetch = None;
                note_last_ok(&mut remote, &nvs);
                if panel_has_status && status.is_empty() {
                    if let Some(ref frame) = last_frame {
                        if let Err(e) = panel.show_frame(frame) {
                            warn!("clear status bar failed: {e:#}");
                        } else {
                            panel_has_status = false;
                        }
                    }
                }
                info!("no change")
            }
            Err(e) => {
                warn!("poll failed: {e:#}");
                paint_error(&mut panel, last_frame.as_deref(), &status);
                panel_has_status = true;
            }
        }
        let force = incident_needs_post(!remote.incident_posted, recovered);
        maybe_post_device(
            &mut remote,
            &mut nvs,
            &wifi,
            force,
            &status,
            reset,
            current_name.as_deref(),
            panel_has_status,
        );
    }
}

fn paint_error(panel: &mut Panel, last_frame: Option<&[u8]>, status: &StatusReport) {
    let Some(text) = status.render() else {
        return;
    };
    let result = match last_frame {
        Some(frame) => panel.show_with_status(frame, Some(&text)),
        None => panel.show_status_only(&text),
    };
    if let Err(e) = result {
        warn!("status paint failed: {e:#}");
    }
}

fn wifi_status_from_err(err: &anyhow::Error, attempt: u32, attempts: u32) -> WifiStatus {
    let heap = HeapSnap::now();
    let top = err.to_string();
    WifiStatus {
        ssid: app().wifi_ssid.clone(),
        step: wifi_step_from(&top).to_string(),
        cause: format_error_chain(err),
        attempt,
        attempts,
        heap: heap.free,
        heap_min: heap.min,
        heap_largest: heap.largest,
        uptime_secs: uptime_secs(),
        disconnect_reason: None,
    }
}

fn wifi_step_from(s: &str) -> &'static str {
    for step in ["configure", "start", "connect", "dhcp"] {
        if s.starts_with(step) {
            return step;
        }
    }
    "wifi"
}

fn fetch_status_from_err(
    op: &str,
    url: &str,
    err: &anyhow::Error,
    attempt: u32,
    attempts: u32,
    ip: Option<&str>,
) -> FetchStatus {
    let heap = HeapSnap::now();
    FetchStatus {
        op: op.to_string(),
        url: url.to_string(),
        http_status: parse_http_status(err),
        cause: format_error_chain(err),
        attempt,
        attempts,
        bytes_read: parse_bytes_read(err),
        heap: heap.free,
        heap_min: heap.min,
        heap_largest: heap.largest,
        uptime_secs: uptime_secs(),
        ip: ip.map(str::to_string),
    }
}

fn parse_http_status(err: &anyhow::Error) -> Option<u16> {
    for cause in err.chain() {
        let s = cause.to_string();
        if let Some(idx) = s.rfind("HTTP ") {
            let rest = &s[idx + 5..];
            let digits: String = rest.chars().take_while(|c| c.is_ascii_digit()).collect();
            if let Ok(n) = digits.parse() {
                return Some(n);
            }
        }
    }
    None
}

fn parse_bytes_read(err: &anyhow::Error) -> Option<usize> {
    for cause in err.chain() {
        let s = cause.to_string();
        if let Some(rest) = s.split("after ").nth(1) {
            let digits: String = rest.chars().take_while(|c| c.is_ascii_digit()).collect();
            if rest.contains('B') {
                return digits.parse().ok();
            }
        }
        if let Some(rest) = s.split("bytes=").nth(1) {
            let digits: String = rest.chars().take_while(|c| c.is_ascii_digit()).collect();
            return digits.parse().ok();
        }
    }
    None
}

enum Boot {
    Displayed(String),
    Empty,
}

fn boot_latest(
    panel: &mut Panel,
    nvs: &mut EspNvs<NvsDefault>,
    current_name: &mut Option<String>,
    current_etag: &mut Option<String>,
    seen_latest: &mut Option<String>,
    last_frame: &mut Option<Vec<u8>>,
    status: &StatusReport,
    ip: &str,
) -> Result<Boot> {
    let url = format!("{}/latest.bin", app().base_url);
    info!("GET {url} ({})", HeapSnap::now());
    let response = http_get(&url, None)?;
    match response.status {
        404 => Ok(Boot::Empty),
        200 => {
            if response.body.len() != FRAME_BYTES {
                return Err(anyhow!(
                    "framebuffer must be {FRAME_BYTES} bytes, got {} ip={ip}",
                    response.body.len()
                ));
            }
            panel.show_with_status(&response.body, status.render().as_deref())?;
            if let Some(ref etag) = response.etag {
                write_str(nvs, NVS_ETAG, etag)?;
                *current_etag = Some(etag.clone());
            }
            *last_frame = Some(response.body);
            // Probe catalog after a breath so heap can coalesce; best-effort.
            thread::sleep(Duration::from_millis(200));
            if let Ok(cat) = fetch_catalog() {
                if let Some(latest) = cat.latest {
                    write_str(nvs, NVS_NAME, &latest)?;
                    write_str(nvs, NVS_LATEST, &latest)?;
                    *current_name = Some(latest.clone());
                    *seen_latest = Some(latest.clone());
                    return Ok(Boot::Displayed(latest));
                }
            }
            Ok(Boot::Displayed("latest".into()))
        }
        other => Err(anyhow!("GET {url} -> HTTP {other} ip={ip}")),
    }
}

enum Action {
    Displayed { name: String, reason: &'static str },
    Idle,
}

#[allow(clippy::too_many_arguments)]
fn tick(
    panel: &mut Panel,
    nvs: &mut EspNvs<NvsDefault>,
    current_name: &mut Option<String>,
    current_etag: &mut Option<String>,
    seen_latest: &mut Option<String>,
    last_rotate: &mut Instant,
    last_frame: &mut Option<Vec<u8>>,
    status: &mut StatusReport,
    ip: &str,
) -> Result<Action> {
    note_op(nvs, "GET /");
    let catalog = match fetch_catalog() {
        Ok(c) => {
            status.fetch = None;
            c
        }
        Err(e) => {
            status.fetch = Some(fetch_status_from_err(
                "catalog",
                &format!("{}/", app().base_url),
                &e,
                HTTP_ATTEMPTS,
                HTTP_ATTEMPTS,
                Some(ip),
            ));
            return Err(e);
        }
    };
    info!(
        "catalog rev={} latest={:?} n={}",
        catalog.revision,
        catalog.latest,
        catalog.images.len()
    );
    if catalog.images.is_empty() {
        return Ok(Action::Idle);
    }

    // Pause so TLS buffers from the catalog GET can free before the 48 KB frame.
    thread::sleep(Duration::from_millis(200));

    // 1) Newly uploaded image → show `latest` right away.
    if let Some(latest) = catalog.latest.as_deref() {
        let is_new = seen_latest.as_deref() != Some(latest);
        if is_new {
            show_named(
                panel,
                nvs,
                current_name,
                current_etag,
                last_frame,
                status,
                latest,
                ip,
            )?;
            write_str(nvs, NVS_LATEST, latest)?;
            *seen_latest = Some(latest.to_string());
            *last_rotate = Instant::now();
            return Ok(Action::Displayed {
                name: latest.to_string(),
                reason: "new",
            });
        }
    }

    // 2) Periodic random rotation among the library.
    if last_rotate.elapsed() >= Duration::from_secs(app().rotate_secs) {
        let rand = unsafe { esp_random() };
        if let Some(name) = catalog
            .pick_random(current_name.as_deref(), rand)
            .map(str::to_string)
        {
            if current_name.as_deref() == Some(name.as_str()) {
                *last_rotate = Instant::now();
                return Ok(Action::Idle);
            }
            show_named(
                panel,
                nvs,
                current_name,
                current_etag,
                last_frame,
                status,
                &name,
                ip,
            )?;
            *last_rotate = Instant::now();
            return Ok(Action::Displayed {
                name,
                reason: "rotate",
            });
        }
    }

    Ok(Action::Idle)
}

#[allow(clippy::too_many_arguments)]
fn show_named(
    panel: &mut Panel,
    nvs: &mut EspNvs<NvsDefault>,
    current_name: &mut Option<String>,
    current_etag: &mut Option<String>,
    last_frame: &mut Option<Vec<u8>>,
    status: &mut StatusReport,
    name: &str,
    ip: &str,
) -> Result<()> {
    let url = format!("{}/{name}.bin", app().base_url);
    note_op(nvs, &format!("GET /{name}.bin"));
    // Drop the last framebuffer before the 48 KB HTTPS body so TLS + frame
    // can share the classic ESP32 heap. Restore it if the GET fails.
    let saved = last_frame.take();
    info!("GET {url} ({})", HeapSnap::now());
    let if_none_match = if current_name.as_deref() == Some(name) {
        current_etag.as_deref()
    } else {
        None
    };
    let response = match http_get(&url, if_none_match) {
        Ok(r) => r,
        Err(e) => {
            *last_frame = saved;
            status.fetch = Some(fetch_status_from_err(
                &format!("frame {name}"),
                &url,
                &e,
                HTTP_ATTEMPTS,
                HTTP_ATTEMPTS,
                Some(ip),
            ));
            return Err(e);
        }
    };
    match response.status {
        304 => {
            *last_frame = saved;
            Ok(())
        }
        200 => {
            if response.body.len() != FRAME_BYTES {
                *last_frame = saved;
                let err = anyhow!(
                    "framebuffer must be {FRAME_BYTES} bytes, got {} ip={ip}",
                    response.body.len()
                );
                status.fetch = Some(fetch_status_from_err(
                    &format!("frame {name}"),
                    &url,
                    &err,
                    1,
                    1,
                    Some(ip),
                ));
                return Err(err);
            }
            panel.show_with_status(&response.body, status.render().as_deref())?;
            write_str(nvs, NVS_NAME, name)?;
            *current_name = Some(name.to_string());
            if let Some(etag) = response.etag {
                write_str(nvs, NVS_ETAG, &etag)?;
                *current_etag = Some(etag);
            }
            *last_frame = Some(response.body);
            Ok(())
        }
        404 => {
            *last_frame = saved;
            let err = anyhow!("image {name} missing on server (HTTP 404) ip={ip}");
            status.fetch = Some(fetch_status_from_err(
                &format!("frame {name}"),
                &url,
                &err,
                1,
                1,
                Some(ip),
            ));
            Err(err)
        }
        other => {
            *last_frame = saved;
            let err = anyhow!("GET {url} -> HTTP {other} ip={ip}");
            status.fetch = Some(fetch_status_from_err(
                &format!("frame {name}"),
                &url,
                &err,
                1,
                1,
                Some(ip),
            ));
            Err(err)
        }
    }
}

fn fetch_catalog() -> Result<Catalog> {
    let url = format!("{}/", app().base_url);
    info!("GET {url} ({})", HeapSnap::now());
    let response = http_get(&url, None)?;
    if response.status != 200 {
        return Err(anyhow!(
            "GET {url} -> HTTP {} bytes={}",
            response.status,
            response.body.len()
        ));
    }
    Catalog::parse(&response.body).map_err(|e| {
        let preview = String::from_utf8_lossy(&response.body);
        let preview: String = preview.chars().take(80).collect();
        anyhow!(
            "catalog json: {e} body={preview:?} bytes={}",
            response.body.len()
        )
    })
}

fn sta_ip(wifi: &BlockingWifi<EspWifi<'static>>) -> Result<String> {
    Ok(net_snap(wifi).ip)
}

struct NetSnap {
    ip: String,
    gateway: Option<String>,
    dns: Option<String>,
    rssi: Option<i32>,
}

fn net_snap(wifi: &BlockingWifi<EspWifi<'static>>) -> NetSnap {
    let info = wifi.wifi().sta_netif().get_ip_info().ok();
    let ip = info
        .as_ref()
        .map(|i| i.ip.to_string())
        .unwrap_or_else(|| "0.0.0.0".into());
    let gateway = info.as_ref().map(|i| i.subnet.gateway.to_string());
    let dns = info
        .as_ref()
        .and_then(|i| i.dns)
        .map(|d| d.to_string())
        .filter(|s| s != "0.0.0.0");
    let rssi = wifi
        .wifi()
        .get_ap_info()
        .ok()
        .map(|ap| i32::from(ap.signal_strength))
        .filter(|r| *r < 0);
    NetSnap {
        ip,
        gateway,
        dns,
        rssi,
    }
}

/// SNTP after STA is up. The handle must be kept so time does not stop.
fn start_sntp() -> Option<EspSntp<'static>> {
    match EspSntp::new_default() {
        Ok(sntp) => {
            for i in 0..20 {
                if matches!(sntp.get_sync_status(), SyncStatus::Completed) {
                    info!("sntp synced after {}ms unix={:?}", i * 250, wall_unix());
                    return Some(sntp);
                }
                thread::sleep(Duration::from_millis(250));
            }
            warn!(
                "sntp still in progress after 5s unix={:?} status={:?}",
                wall_unix(),
                sntp.get_sync_status()
            );
            Some(sntp)
        }
        Err(e) => {
            warn!("sntp init failed: {e:?}");
            None
        }
    }
}

/// Wall clock after SNTP; `None` until the clock is past 2020-01-01.
fn wall_unix() -> Option<i64> {
    https::now_unix_secs().map(|s| s as i64)
}

/// Re-run DHCP without dropping Wi-Fi association.
fn renew_dhcp(wifi: &mut BlockingWifi<EspWifi<'static>>) -> Result<String> {
    use esp_idf_svc::handle::RawHandle;
    use esp_idf_svc::sys::{esp_netif_dhcpc_start, esp_netif_dhcpc_stop};

    let handle = wifi.wifi().sta_netif().handle();
    // ALREADY_STOPPED is fine — we still want a fresh start.
    let _ = unsafe { esp_netif_dhcpc_stop(handle) };
    thread::sleep(Duration::from_millis(250));
    let start = unsafe { esp_netif_dhcpc_start(handle) };
    if start != 0 {
        return Err(anyhow!("dhcp start: {start}"));
    }
    wifi.wait_netif_up()
        .map_err(|e| anyhow!("dhcp renew: {e:?}"))?;
    sta_ip(wifi)
}

fn reconnect_wifi(wifi: &mut BlockingWifi<EspWifi<'static>>) -> Result<String> {
    let _ = wifi.disconnect();
    let _ = wifi.stop();
    thread::sleep(Duration::from_millis(300));
    connect_wifi(wifi)?;
    sta_ip(wifi)
}

/// Periodic DHCP renew, dropped-STA reconnect, or connect-failure recovery.
/// Returns true when a refresh actually ran and succeeded.
fn maybe_refresh_wifi(
    wifi: &mut BlockingWifi<EspWifi<'static>>,
    nvs: &mut EspNvs<NvsDefault>,
    remote: &mut RemoteStatus,
    ip_str: &mut String,
    last_wifi_refresh: &mut Instant,
    last_reconnect: &mut Option<Instant>,
    status: &mut StatusReport,
    connect_failure: bool,
) -> bool {
    let sta_connected = wifi.is_connected().unwrap_or(false);
    let netif_up = wifi.is_up().unwrap_or(false);
    let action = should_refresh_wifi(
        sta_connected,
        netif_up,
        connect_failure,
        last_wifi_refresh.elapsed().as_secs(),
        app().dhcp_renew_secs,
        last_reconnect
            .map(|t| t.elapsed().as_secs())
            .unwrap_or(WIFI_RECONNECT_COOLDOWN_SECS),
        WIFI_RECONNECT_COOLDOWN_SECS,
    );
    match action {
        WifiRefresh::None => false,
        WifiRefresh::RenewDhcp => {
            note_op(nvs, "wifi-dhcp");
            info!(
                "wifi dhcp renew (up={}s ip={ip_str}) {}",
                uptime_secs(),
                HeapSnap::now()
            );
            match renew_dhcp(wifi) {
                Ok(ip) => {
                    if ip != *ip_str {
                        info!("wifi dhcp renew: ip {ip_str} -> {ip}");
                    }
                    *ip_str = ip;
                    *last_wifi_refresh = Instant::now();
                    status.wifi = None;
                    remote.note_refresh("dhcp", true);
                    true
                }
                Err(e) => {
                    warn!("wifi dhcp renew failed: {e:#}; reconnecting");
                    match reconnect_wifi(wifi) {
                        Ok(ip) => {
                            info!("wifi reconnect after dhcp fail, ip={ip}");
                            *ip_str = ip;
                            *last_wifi_refresh = Instant::now();
                            *last_reconnect = Some(Instant::now());
                            status.wifi = None;
                            remote.note_refresh("reconnect-after-dhcp", true);
                            true
                        }
                        Err(re) => {
                            warn!("wifi reconnect failed: {re:#}");
                            *last_reconnect = Some(Instant::now());
                            status.wifi =
                                Some(wifi_status_from_err(&re, WIFI_ATTEMPTS, WIFI_ATTEMPTS));
                            remote.note_refresh("reconnect-fail", false);
                            capture_incident(remote, nvs, wifi, status, "wifi");
                            false
                        }
                    }
                }
            }
        }
        WifiRefresh::Reconnect => {
            note_op(nvs, "wifi-reconnect");
            info!(
                "wifi reconnect (connected={sta_connected} netif={netif_up} connect_fail={connect_failure}) {}",
                HeapSnap::now()
            );
            match reconnect_wifi(wifi) {
                Ok(ip) => {
                    info!("wifi reconnect ok, ip={ip}");
                    *ip_str = ip;
                    *last_wifi_refresh = Instant::now();
                    *last_reconnect = Some(Instant::now());
                    status.wifi = None;
                    remote.note_refresh("reconnect", true);
                    true
                }
                Err(e) => {
                    warn!("wifi reconnect failed: {e:#}");
                    *last_reconnect = Some(Instant::now());
                    status.wifi = Some(wifi_status_from_err(&e, WIFI_ATTEMPTS, WIFI_ATTEMPTS));
                    remote.note_refresh("reconnect-fail", false);
                    capture_incident(remote, nvs, wifi, status, "wifi");
                    false
                }
            }
        }
    }
}

fn connect_wifi(wifi: &mut BlockingWifi<EspWifi<'static>>) -> Result<()> {
    let mut last_err: Option<anyhow::Error> = None;
    for attempt in 1..=WIFI_ATTEMPTS {
        info!(
            "wifi attempt {attempt}/{WIFI_ATTEMPTS} ssid={} {}",
            app().wifi_ssid,
            HeapSnap::now()
        );
        match connect_wifi_once(wifi, attempt) {
            Ok(()) => return Ok(()),
            Err(e) => {
                warn!("wifi attempt {attempt}/{WIFI_ATTEMPTS} failed: {e:#}");
                let _ = wifi.disconnect();
                let _ = wifi.stop();
                last_err = Some(e);
                thread::sleep(Duration::from_secs(2));
            }
        }
    }
    Err(last_err.unwrap_or_else(|| anyhow!("wifi failed")))
}

fn connect_wifi_once(wifi: &mut BlockingWifi<EspWifi<'static>>, attempt: u32) -> Result<()> {
    let step = |name: &str| {
        info!("wifi[{attempt}] {name} {}", HeapSnap::now());
    };

    step("configure");
    wifi.set_configuration(&WifiConfig::Client(ClientConfiguration {
        ssid: app()
            .wifi_ssid
            .as_str()
            .try_into()
            .map_err(|_| anyhow!("ssid too long"))?,
        password: app()
            .wifi_pass
            .as_str()
            .try_into()
            .map_err(|_| anyhow!("pass too long"))?,
        auth_method: if app().wifi_pass.is_empty() {
            AuthMethod::None
        } else {
            AuthMethod::WPA2WPA3Personal
        },
        ..Default::default()
    }))
    .map_err(|e| anyhow!("configure: {e:?}"))?;

    step("start");
    wifi.start().map_err(|e| anyhow!("start: {e:?}"))?;

    match unsafe { esp_wifi_set_max_tx_power(44) } {
        0 => info!("wifi[{attempt}] max_tx_power=44 (~11 dBm)"),
        code => warn!("wifi[{attempt}] set_max_tx_power failed: {code}"),
    }

    step("connect");
    wifi.connect().map_err(|e| anyhow!("connect: {e:?}"))?;
    step("dhcp");
    wifi.wait_netif_up().map_err(|e| anyhow!("dhcp: {e:?}"))?;

    // Modem sleep (default WIFI_PS_MIN_MODEM) routinely stalls mbedtls reads of
    // multi-KB HTTPS bodies on classic ESP32 — surfaces as EspIOError / EAGAIN.
    match unsafe { esp_wifi_set_ps(wifi_ps_type_t_WIFI_PS_NONE) } {
        0 => info!("wifi[{attempt}] power_save=NONE"),
        code => warn!("wifi[{attempt}] set_ps(NONE) failed: {code}"),
    }

    step("up");
    Ok(())
}

fn read_str(nvs: &EspNvs<NvsDefault>, key: &str) -> Result<Option<String>> {
    let mut buf = [0u8; 128];
    match nvs.get_str(key, &mut buf) {
        Ok(Some(s)) if !s.is_empty() => Ok(Some(s.to_string())),
        Ok(_) => Ok(None),
        Err(e) => Err(anyhow!("read {key}: {e:?}")),
    }
}

fn write_str(nvs: &mut EspNvs<NvsDefault>, key: &str, value: &str) -> Result<()> {
    nvs.set_str(key, value)
        .map_err(|e| anyhow!("write {key}: {e:?}"))?;
    Ok(())
}

fn note_op(nvs: &mut EspNvs<NvsDefault>, op: &str) {
    rtc_write_op(op);
    if let Err(e) = write_str(nvs, NVS_LAST_OP, op) {
        warn!("note_op {op}: {e:#}");
    }
}

fn read_incident(nvs: &EspNvs<NvsDefault>) -> Result<Option<LastIncident>> {
    let mut buf = [0u8; INCIDENT_BLOB];
    match nvs.get_blob(NVS_INCIDENT, &mut buf) {
        Ok(Some(bytes)) if !bytes.is_empty() => serde_json::from_slice(bytes)
            .map(Some)
            .map_err(|e| anyhow!("incident json: {e}")),
        Ok(_) => Ok(None),
        Err(e) => Err(anyhow!("read inc: {e:?}")),
    }
}

fn write_incident(nvs: &EspNvs<NvsDefault>, inc: &LastIncident) -> Result<()> {
    let mut inc = inc.clone();
    loop {
        let bytes = serde_json::to_vec(&inc).map_err(|e| anyhow!("incident json: {e}"))?;
        if bytes.len() <= INCIDENT_BLOB {
            nvs.set_blob(NVS_INCIDENT, &bytes)
                .map_err(|e| anyhow!("write inc: {e:?}"))?;
            return Ok(());
        }
        if inc.error.len() <= 32 {
            return Err(anyhow!("incident too large ({})", bytes.len()));
        }
        inc.error.truncate(inc.error.len() / 2);
    }
}

fn clear_incident(nvs: &EspNvs<NvsDefault>) -> Result<()> {
    nvs.remove(NVS_INCIDENT)
        .map(|_| ())
        .map_err(|e| anyhow!("erase inc: {e:?}"))
}

fn capture_incident(
    remote: &mut RemoteStatus,
    nvs: &EspNvs<NvsDefault>,
    wifi: &BlockingWifi<EspWifi<'static>>,
    status: &StatusReport,
    kind: &str,
) {
    let net = net_snap(wifi);
    let op = read_str(nvs, NVS_LAST_OP).ok().flatten();
    let Some(inc) = LastIncident::from_status(
        kind,
        status,
        IncidentContext {
            uptime_secs: uptime_secs(),
            unix_secs: wall_unix(),
            ip: Some(net.ip),
            op,
            rssi: net.rssi,
            gateway: net.gateway,
        },
    ) else {
        return;
    };
    info!(
        "incident queued kind={} up={}s rssi={:?} gw={:?}",
        inc.kind, inc.uptime_secs, inc.rssi, inc.gateway
    );
    remote.queue_incident(nvs, inc);
}

fn note_last_ok(remote: &mut RemoteStatus, nvs: &EspNvs<NvsDefault>) {
    remote.last_ok_uptime_secs = Some(uptime_secs());
    remote.last_ok_op = read_str(nvs, NVS_LAST_OP).ok().flatten();
}

struct RemoteStatus {
    last_post: Instant,
    last_error: Option<String>,
    posts_ok: u32,
    posts_fail: u32,
    last_post_error: Option<String>,
    last_incident: Option<LastIncident>,
    /// False while NVS still holds an incident that has not POSTed 2xx.
    incident_posted: bool,
    last_ok_uptime_secs: Option<u64>,
    last_ok_op: Option<String>,
    dhcp_renews: u32,
    reconnects_ok: u32,
    reconnects_fail: u32,
    last_refresh: Option<String>,
    last_refresh_uptime: Option<u64>,
}

impl RemoteStatus {
    fn new() -> Self {
        Self {
            last_post: Instant::now(),
            last_error: None,
            posts_ok: 0,
            posts_fail: 0,
            last_post_error: None,
            last_incident: None,
            incident_posted: true,
            last_ok_uptime_secs: None,
            last_ok_op: None,
            dhcp_renews: 0,
            reconnects_ok: 0,
            reconnects_fail: 0,
            last_refresh: None,
            last_refresh_uptime: None,
        }
    }

    fn from_nvs(nvs: &EspNvs<NvsDefault>) -> Self {
        let mut s = Self::new();
        match read_incident(nvs) {
            Ok(Some(inc)) => {
                info!(
                    "restored unposted incident kind={} up={}s",
                    inc.kind, inc.uptime_secs
                );
                s.last_incident = Some(inc);
                s.incident_posted = false;
            }
            Ok(None) => {}
            Err(e) => warn!("read incident: {e:#}"),
        }
        s
    }

    fn queue_incident(&mut self, nvs: &EspNvs<NvsDefault>, inc: LastIncident) {
        if let Err(e) = write_incident(nvs, &inc) {
            warn!("persist incident: {e:#}");
        }
        self.last_incident = Some(inc);
        self.incident_posted = false;
    }

    fn mark_incident_posted(&mut self, nvs: &EspNvs<NvsDefault>) {
        if self.incident_posted {
            return;
        }
        if let Err(e) = clear_incident(nvs) {
            warn!("clear incident: {e:#}");
        }
        self.incident_posted = true;
    }

    fn note_refresh(&mut self, kind: &str, ok: bool) {
        match kind {
            "dhcp" => {
                self.dhcp_renews = self.dhcp_renews.saturating_add(1);
            }
            "reconnect" | "reconnect-after-dhcp" => {
                if ok {
                    self.reconnects_ok = self.reconnects_ok.saturating_add(1);
                } else {
                    self.reconnects_fail = self.reconnects_fail.saturating_add(1);
                }
            }
            "reconnect-fail" => {
                self.reconnects_fail = self.reconnects_fail.saturating_add(1);
            }
            _ => {}
        }
        self.last_refresh = Some(kind.to_string());
        self.last_refresh_uptime = Some(uptime_secs());
    }
}

#[allow(clippy::too_many_arguments)]
fn maybe_post_device(
    remote: &mut RemoteStatus,
    nvs: &mut EspNvs<NvsDefault>,
    wifi: &BlockingWifi<EspWifi<'static>>,
    force: bool,
    status: &StatusReport,
    reset_code: i32,
    current_image: Option<&str>,
    panel_has_status: bool,
) {
    let secret_ok = !app().upload_secret.is_empty();
    let err = status.render();
    let error_changed = err != remote.last_error;
    let secs = remote.last_post.elapsed().as_secs();
    if !should_post_status(secret_ok, force, error_changed, secs, app().status_secs) {
        return;
    }
    let last_op = read_str(nvs, NVS_LAST_OP).ok().flatten();
    let heap = HeapSnap::now();
    let net = net_snap(wifi);
    let mut tel = DeviceTelemetry::from_parts(
        status,
        uptime_secs(),
        reset_code,
        heap.free,
        heap.min,
        heap.largest,
        Some(net.ip),
        Some(app().wifi_ssid.clone()),
        current_image.map(str::to_string),
        last_op,
        panel_has_status,
        remote.posts_ok,
        remote.posts_fail,
        remote.last_post_error.clone(),
    );
    tel.unix_secs = wall_unix();
    tel.rssi = net.rssi;
    tel.gateway = net.gateway;
    tel.dns = net.dns;
    tel.last_ok_uptime_secs = remote.last_ok_uptime_secs;
    tel.last_ok_op = remote.last_ok_op.clone();
    tel.last_incident = remote.last_incident.clone();
    tel.dhcp_renews = remote.dhcp_renews;
    tel.reconnects_ok = remote.reconnects_ok;
    tel.reconnects_fail = remote.reconnects_fail;
    tel.last_refresh = remote.last_refresh.clone();
    tel.last_refresh_uptime = remote.last_refresh_uptime;
    thread::sleep(Duration::from_millis(200));
    note_op(nvs, "POST /device");
    match post_device_report(&tel) {
        Ok(()) => {
            remote.posts_ok = remote.posts_ok.saturating_add(1);
            remote.last_post_error = None;
            remote.last_error = err;
            remote.last_post = Instant::now();
            remote.mark_incident_posted(nvs);
            info!("POST /device ok");
        }
        Err(e) => {
            remote.posts_fail = remote.posts_fail.saturating_add(1);
            remote.last_post_error = Some(format_error_chain(&e));
            remote.last_post = Instant::now();
            warn!("POST /device failed: {e:#}");
        }
    }
}

fn post_device_report(tel: &DeviceTelemetry) -> Result<()> {
    let body = serde_json::to_vec(tel).map_err(|e| anyhow!("status json: {e}"))?;
    let url = format!("{}/device", app().base_url);
    const ATTEMPTS: u32 = 2;
    let mut last_err: Option<anyhow::Error> = None;
    for attempt in 1..=ATTEMPTS {
        match http_post_json(&url, &body) {
            Ok(status) if (200..300).contains(&status) => return Ok(()),
            Ok(status) => {
                warn!("POST {url} attempt {attempt}/{ATTEMPTS} HTTP {status}");
                last_err = Some(anyhow!("POST {url} -> HTTP {status}"));
            }
            Err(e) => {
                warn!("POST {url} attempt {attempt}/{ATTEMPTS}: {e:#}");
                last_err = Some(e);
            }
        }
        thread::sleep(Duration::from_millis(300 * u64::from(attempt)));
    }
    Err(last_err.unwrap_or_else(|| anyhow!("POST /device failed")))
}

fn http_post_json(url: &str, body: &[u8]) -> Result<u16> {
    let auth = format!("Bearer {}", app().upload_secret);
    let len = body.len().to_string();
    let mut client = HttpClient::wrap(
        EspHttpConnection::new(&HttpConfig {
            buffer_size: Some(1024),
            buffer_size_tx: Some(1024),
            timeout: Some(Duration::from_secs(30)),
            crt_bundle_attach: Some(esp_idf_svc::sys::esp_crt_bundle_attach),
            ..Default::default()
        })
        .map_err(|e| anyhow!("http client: {e:?} {}", HeapSnap::now()))?,
    );
    let headers = [
        ("User-Agent", FIRMWARE_ID),
        ("Authorization", auth.as_str()),
        ("Content-Type", "application/json"),
        ("Content-Length", len.as_str()),
    ];
    let mut request = client
        .request(Method::Post, url, &headers)
        .map_err(|e| anyhow!("http request: {e} {}", HeapSnap::now()))?;
    request
        .write_all(body)
        .map_err(|e| anyhow!("http write: {e} {}", HeapSnap::now()))?;
    let response = request
        .submit()
        .map_err(|e| anyhow!("http submit: {e} {}", HeapSnap::now()))?;
    Ok(response.status())
}

struct HttpResponse {
    status: u16,
    etag: Option<String>,
    body: Vec<u8>,
}

fn http_get(url: &str, if_none_match: Option<&str>) -> Result<HttpResponse> {
    let mut last_err: Option<anyhow::Error> = None;
    for attempt in 1..=HTTP_ATTEMPTS {
        match http_get_once(url, if_none_match) {
            Ok(r) => return Ok(r),
            Err(e) => {
                warn!("GET {url} attempt {attempt}/{HTTP_ATTEMPTS}: {e:#}");
                last_err = Some(e);
                thread::sleep(Duration::from_millis(400 * u64::from(attempt)));
            }
        }
    }
    let heap = HeapSnap::now();
    Err(last_err
        .unwrap_or_else(|| anyhow!("http get failed"))
        .context(format!(
            "GET {url} failed after {HTTP_ATTEMPTS} tries {heap}"
        )))
}

fn http_get_once(url: &str, if_none_match: Option<&str>) -> Result<HttpResponse> {
    let mut client = HttpClient::wrap(
        EspHttpConnection::new(&HttpConfig {
            buffer_size: Some(1024),
            buffer_size_tx: Some(1024),
            timeout: Some(Duration::from_secs(30)),
            crt_bundle_attach: Some(esp_idf_svc::sys::esp_crt_bundle_attach),
            ..Default::default()
        })
        .map_err(|e| anyhow!("http client: {e:?} {}", HeapSnap::now()))?,
    );

    let mut headers: Vec<(&str, &str)> = vec![("User-Agent", FIRMWARE_ID)];
    if let Some(etag) = if_none_match {
        headers.push(("If-None-Match", etag));
    }

    let request = client
        .request(Method::Get, url, &headers)
        .map_err(|e| anyhow!("http request: {e} {}", HeapSnap::now()))?;
    let mut response = request
        .submit()
        .map_err(|e| anyhow!("http submit: {e} {}", HeapSnap::now()))?;
    let status = response.status();

    let etag = response
        .header("ETag")
        .or_else(|| response.header("etag"))
        .map(str::to_string);

    let mut body = Vec::new();
    if status == 200 {
        // Catalog is small; frames are exactly FRAME_BYTES.
        let reserve = if url.ends_with('/') { 512 } else { FRAME_BYTES };
        body.reserve(reserve);
        let mut buf = [0u8; 512];
        loop {
            let n = Read::read(&mut response, &mut buf)
                .map_err(|e| anyhow!("http read after {}B: {e} {}", body.len(), HeapSnap::now()))?;
            if n == 0 {
                break;
            }
            body.extend_from_slice(&buf[..n]);
            if body.len() > FRAME_BYTES + 2048 {
                return Err(anyhow!(
                    "response body too large bytes={} {}",
                    body.len(),
                    HeapSnap::now()
                ));
            }
        }
    }

    Ok(HttpResponse { status, etag, body })
}

#[derive(Clone, Copy)]
struct HeapSnap {
    free: u32,
    min: u32,
    largest: u32,
}

impl HeapSnap {
    fn now() -> Self {
        Self {
            free: unsafe { esp_get_free_heap_size() },
            min: unsafe { esp_get_minimum_free_heap_size() },
            largest: unsafe { heap_caps_get_largest_free_block(MALLOC_CAP_8BIT) } as u32,
        }
    }
}

impl core::fmt::Display for HeapSnap {
    fn fmt(&self, f: &mut core::fmt::Formatter<'_>) -> core::fmt::Result {
        write!(
            f,
            "heap={} min={} big={}",
            self.free, self.min, self.largest
        )
    }
}

fn uptime_secs() -> u64 {
    let us = unsafe { esp_timer_get_time() };
    if us < 0 {
        0
    } else {
        (us / 1_000_000) as u64
    }
}

// --- crash breadcrumbs in RTC slow memory (survives panic reboot, not brownout) ---

const PANIC_MAGIC: u32 = 0x504E_4331; // PNC1
const OP_MAGIC: u32 = 0x4F50_3031; // OP01

#[repr(C)]
struct DebugSlot {
    panic_magic: u32,
    op_magic: u32,
    panic_len: u8,
    op_len: u8,
    _pad: [u8; 2],
    panic_msg: [u8; 160],
    last_op: [u8; 48],
}

#[link_section = ".rtc_noinit"]
#[used]
static mut DEBUG_SLOT: DebugSlot = DebugSlot {
    panic_magic: 0,
    op_magic: 0,
    panic_len: 0,
    op_len: 0,
    _pad: [0; 2],
    panic_msg: [0; 160],
    last_op: [0; 48],
};

fn install_panic_hook() {
    std::panic::set_hook(Box::new(|info| {
        let payload = if let Some(s) = info.payload().downcast_ref::<&str>() {
            *s
        } else if let Some(s) = info.payload().downcast_ref::<String>() {
            s.as_str()
        } else {
            "panic"
        };
        let (file, line) = match info.location() {
            Some(loc) => (loc.file(), loc.line()),
            None => ("?", 0),
        };
        let msg = format_panic_message(payload, file, line);
        error!("PANIC {msg}");
        rtc_write_panic(&msg);
    }));
}

fn rtc_slot() -> &'static mut DebugSlot {
    // Single-threaded firmware; panic hook runs on this thread before abort.
    unsafe { &mut *core::ptr::addr_of_mut!(DEBUG_SLOT) }
}

fn rtc_write_panic(msg: &str) {
    let bytes = msg.as_bytes();
    let n = bytes.len().min(160);
    let slot = rtc_slot();
    slot.panic_msg[..n].copy_from_slice(&bytes[..n]);
    if n < 160 {
        slot.panic_msg[n..].fill(0);
    }
    slot.panic_len = n as u8;
    slot.panic_magic = PANIC_MAGIC;
}

fn rtc_take_panic() -> Option<String> {
    let slot = rtc_slot();
    if slot.panic_magic != PANIC_MAGIC {
        return None;
    }
    let n = (slot.panic_len as usize).min(160);
    let s = String::from_utf8_lossy(&slot.panic_msg[..n])
        .trim_end_matches('\0')
        .to_string();
    slot.panic_magic = 0;
    slot.panic_len = 0;
    if s.is_empty() {
        None
    } else {
        Some(s)
    }
}

fn rtc_write_op(op: &str) {
    let bytes = op.as_bytes();
    let n = bytes.len().min(48);
    let slot = rtc_slot();
    slot.last_op[..n].copy_from_slice(&bytes[..n]);
    if n < 48 {
        slot.last_op[n..].fill(0);
    }
    slot.op_len = n as u8;
    slot.op_magic = OP_MAGIC;
}

fn rtc_take_last_op() -> Option<String> {
    let slot = rtc_slot();
    if slot.op_magic != OP_MAGIC {
        return None;
    }
    let n = (slot.op_len as usize).min(48);
    let s = String::from_utf8_lossy(&slot.last_op[..n])
        .trim_end_matches('\0')
        .to_string();
    slot.op_magic = 0;
    slot.op_len = 0;
    if s.is_empty() {
        None
    } else {
        Some(s)
    }
}
