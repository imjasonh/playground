//! inkbot-esp32 — poll the inkbot Worker and show frames on Waveshare 7.5″.

mod display;

use std::thread;
use std::time::{Duration, Instant};

use anyhow::{anyhow, Result};
use embedded_svc::http::client::Client as HttpClient;
use embedded_svc::http::Method;
use embedded_svc::io::Read;
use esp_idf_svc::eventloop::EspSystemEventLoop;
use esp_idf_svc::hal::peripherals::Peripherals;
use esp_idf_svc::http::client::{Configuration as HttpConfig, EspHttpConnection};
use esp_idf_svc::nvs::{EspDefaultNvsPartition, EspNvs, NvsDefault};
use esp_idf_svc::sys::{
    esp_get_free_heap_size, esp_get_minimum_free_heap_size, esp_random, esp_reset_reason,
    esp_timer_get_time, esp_wifi_set_max_tx_power, esp_wifi_set_ps,
    heap_caps_get_largest_free_block, wifi_ps_type_t_WIFI_PS_NONE, MALLOC_CAP_8BIT,
};
use esp_idf_svc::wifi::{
    AuthMethod, BlockingWifi, ClientConfiguration, Configuration as WifiConfig, EspWifi,
};
use log::{error, info, warn};

use display::Panel;
use inkbot_esp32::{
    format_error_chain, format_panic_message, reset_is_abnormal, Catalog, CrashStatus, FetchStatus,
    StatusReport, WifiStatus, FRAME_BYTES,
};

include!(concat!(env!("OUT_DIR"), "/config_gen.rs"));

const NVS_NS: &str = "inkbot";
const NVS_NAME: &str = "name";
const NVS_ETAG: &str = "etag";
const NVS_LATEST: &str = "latest";
const NVS_LAST_OP: &str = "op";

const HTTP_ATTEMPTS: u32 = 3;
const WIFI_ATTEMPTS: u32 = 5;

fn main() -> Result<()> {
    esp_idf_svc::sys::link_patches();
    esp_idf_svc::log::EspLogger::initialize_default();
    install_panic_hook();

    let reset = unsafe { esp_reset_reason() } as i32;
    let heap = HeapSnap::now();
    info!(
        "inkbot-esp32: boot reset_reason={} ({}) {}",
        inkbot_esp32::reset_reason_name(reset),
        reset,
        heap
    );

    let peripherals = Peripherals::take()?;
    let sysloop = EspSystemEventLoop::take()?;
    let nvs_part = EspDefaultNvsPartition::take()?;
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

    let mut status = StatusReport::default();
    let nvs_last_op = read_str(&nvs, NVS_LAST_OP)?;
    let last_op = rtc_take_last_op().or(nvs_last_op);
    if reset_is_abnormal(reset) {
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
        EspWifi::new(peripherals.modem, sysloop.clone(), Some(nvs_part))?,
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
                paint_error(&mut panel, None, &status);
                thread::sleep(Duration::from_secs(3));
            }
        }
    }
    let ip = wifi
        .wifi()
        .sta_netif()
        .get_ip_info()
        .map_err(|e| anyhow!("sta ip: {e:?}"))?
        .ip;
    let ip_str = ip.to_string();
    info!("wifi connected, ip={ip_str}, {}", HeapSnap::now());

    let mut current_name = read_str(&nvs, NVS_NAME)?;
    let mut current_etag = read_str(&nvs, NVS_ETAG)?;
    let mut seen_latest = read_str(&nvs, NVS_LATEST)?;
    info!("nvs: name={current_name:?} etag={current_etag:?} latest={seen_latest:?}");

    let mut last_rotate = Instant::now();
    let mut last_frame: Option<Vec<u8>> = None;
    let mut panel_has_status = !status.is_empty();

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
                &format!("{INKBOT_BASE_URL}/latest.bin"),
                &e,
                HTTP_ATTEMPTS,
                HTTP_ATTEMPTS,
                Some(ip_str.as_str()),
            ));
            paint_error(&mut panel, last_frame.as_deref(), &status);
            panel_has_status = true;
        }
    }

    loop {
        thread::sleep(Duration::from_secs(POLL_SECS));
        // After the first successful image the crash line has been on-screen
        // for a full poll period; drop it so the next paint is a full frame.
        if last_frame.is_some() {
            status.crash = None;
        }
        match tick(
            &mut panel,
            &mut nvs,
            &mut current_name,
            &mut current_etag,
            &mut seen_latest,
            &mut last_rotate,
            &mut last_frame,
            &mut status,
            &ip_str,
        ) {
            Ok(Action::Displayed { name, reason }) => {
                status.fetch = None;
                panel_has_status = !status.is_empty();
                info!("displayed {name} ({reason})")
            }
            Ok(Action::Idle) => {
                status.fetch = None;
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
        ssid: WIFI_SSID.to_string(),
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
    let url = format!("{INKBOT_BASE_URL}/latest.bin");
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
                &format!("{INKBOT_BASE_URL}/"),
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
    if last_rotate.elapsed() >= Duration::from_secs(ROTATE_SECS) {
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
    let url = format!("{INKBOT_BASE_URL}/{name}.bin");
    note_op(nvs, &format!("GET /{name}.bin"));
    // Drop the last framebuffer before the 48 KB HTTPS body so TLS + frame
    // can share the classic ESP32 heap. Restore it if the GET fails.
    let saved = last_frame.take();
    info!("GET {url} ({})", HeapSnap::now());
    let response = match http_get(&url, None) {
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
    let url = format!("{INKBOT_BASE_URL}/");
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

fn connect_wifi(wifi: &mut BlockingWifi<EspWifi<'static>>) -> Result<()> {
    let mut last_err: Option<anyhow::Error> = None;
    for attempt in 1..=WIFI_ATTEMPTS {
        info!(
            "wifi attempt {attempt}/{WIFI_ATTEMPTS} ssid={WIFI_SSID} {}",
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
        ssid: WIFI_SSID.try_into().map_err(|_| anyhow!("ssid too long"))?,
        password: WIFI_PASS.try_into().map_err(|_| anyhow!("pass too long"))?,
        auth_method: if WIFI_PASS.is_empty() {
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

    let mut headers: Vec<(&str, &str)> = vec![("User-Agent", "inkbot-esp32/0.1")];
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
    if s.is_empty() {
        None
    } else {
        Some(s)
    }
}
