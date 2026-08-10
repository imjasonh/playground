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
    esp_get_free_heap_size, esp_random, esp_reset_reason, esp_wifi_set_max_tx_power,
};
use esp_idf_svc::wifi::{
    AuthMethod, BlockingWifi, ClientConfiguration, Configuration as WifiConfig, EspWifi,
};
use log::{info, warn};

use display::Panel;
use inkbot_esp32::{Catalog, FRAME_BYTES};

include!(concat!(env!("OUT_DIR"), "/config_gen.rs"));

const NVS_NS: &str = "inkbot";
const NVS_NAME: &str = "name";
const NVS_ETAG: &str = "etag";
const NVS_LATEST: &str = "latest";

fn main() -> Result<()> {
    esp_idf_svc::sys::link_patches();
    esp_idf_svc::log::EspLogger::initialize_default();
    let reset = unsafe { esp_reset_reason() };
    info!(
        "inkbot-esp32: boot reset_reason={reset:?} ({}) free_heap={}",
        reset as i32,
        unsafe { esp_get_free_heap_size() }
    );

    let peripherals = Peripherals::take()?;
    let sysloop = EspSystemEventLoop::take()?;
    let nvs_part = EspDefaultNvsPartition::take()?;

    let mut panel = Panel::new(
        peripherals.spi2,
        peripherals.pins.gpio13,
        peripherals.pins.gpio14,
        peripherals.pins.gpio15,
        peripherals.pins.gpio25,
        peripherals.pins.gpio27,
        peripherals.pins.gpio26,
    )?;

    let mut wifi = BlockingWifi::wrap(
        EspWifi::new(peripherals.modem, sysloop.clone(), Some(nvs_part.clone()))?,
        sysloop,
    )?;
    thread::sleep(Duration::from_millis(500));
    if let Err(e) = connect_wifi(&mut wifi) {
        warn!("wifi failed: {e:#}");
        let mut msg = format!("WiFi: {e}");
        if msg.len() > 48 {
            msg.truncate(47);
            msg.push('…');
        }
        let _ = panel.show_message(&msg);
        return Err(e);
    }
    let ip = wifi.wifi().sta_netif().get_ip_info()?.ip;
    info!("wifi connected, ip={ip}, free_heap={}", unsafe {
        esp_get_free_heap_size()
    });

    let mut nvs =
        EspNvs::new(nvs_part, NVS_NS, true).map_err(|e| anyhow!("open NVS {NVS_NS}: {e:?}"))?;
    let mut current_name = read_str(&nvs, NVS_NAME)?;
    let mut current_etag = read_str(&nvs, NVS_ETAG)?;
    let mut seen_latest = read_str(&nvs, NVS_LATEST)?;
    info!("nvs: name={current_name:?} etag={current_etag:?} latest={seen_latest:?}");

    let mut last_rotate = Instant::now();

    // Boot: one HTTPS GET of /latest.bin — a catalog+frame pair back-to-back
    // fragments the classic ESP32 heap so the 48 KB alloc fails.
    match boot_latest(
        &mut panel,
        &mut nvs,
        &mut current_name,
        &mut current_etag,
        &mut seen_latest,
    ) {
        Ok(Some(name)) => {
            last_rotate = Instant::now();
            info!("boot displayed {name}");
        }
        Ok(None) => {
            info!("no images on server yet");
            let _ = panel.show_message("inkbot ready");
        }
        Err(e) => {
            warn!("boot poll failed: {e:#}");
            let _ = panel.show_message(&short_err("poll", &e));
        }
    }

    loop {
        thread::sleep(Duration::from_secs(POLL_SECS));
        match tick(
            &mut panel,
            &mut nvs,
            &mut current_name,
            &mut current_etag,
            &mut seen_latest,
            &mut last_rotate,
        ) {
            Ok(Action::Displayed { name, reason }) => {
                info!("displayed {name} ({reason})")
            }
            Ok(Action::Idle) => info!("no change"),
            Err(e) => {
                warn!("poll failed: {e:#}");
                // Don't refresh the panel on steady-state errors — keep the
                // last good frame. Serial / next success recovers.
            }
        }
    }
}

fn short_err(prefix: &str, err: &anyhow::Error) -> String {
    let mut msg = format!("{prefix}: {err}");
    if msg.len() > 48 {
        msg.truncate(47);
        msg.push('…');
    }
    msg
}

fn boot_latest(
    panel: &mut Panel,
    nvs: &mut EspNvs<NvsDefault>,
    current_name: &mut Option<String>,
    current_etag: &mut Option<String>,
    seen_latest: &mut Option<String>,
) -> Result<Option<String>> {
    let url = format!("{INKBOT_BASE_URL}/latest.bin");
    info!("GET {url} (free_heap={})", unsafe {
        esp_get_free_heap_size()
    });
    let response = http_get(&url, None)?;
    match response.status {
        404 => Ok(None),
        200 => {
            if response.body.len() != FRAME_BYTES {
                return Err(anyhow!(
                    "framebuffer must be {FRAME_BYTES} bytes, got {}",
                    response.body.len()
                ));
            }
            panel.show_frame(&response.body)?;
            // Name comes from Content-Disposition? We don't have it — learn
            // from the next catalog poll. Persist etag only.
            if let Some(etag) = response.etag {
                write_str(nvs, NVS_ETAG, &etag)?;
                *current_etag = Some(etag);
            }
            // Probe catalog after a breath so heap can coalesce; best-effort.
            thread::sleep(Duration::from_millis(200));
            if let Ok(cat) = fetch_catalog() {
                if let Some(latest) = cat.latest {
                    write_str(nvs, NVS_NAME, &latest)?;
                    write_str(nvs, NVS_LATEST, &latest)?;
                    *current_name = Some(latest.clone());
                    *seen_latest = Some(latest.clone());
                    return Ok(Some(latest));
                }
            }
            Ok(Some("latest".into()))
        }
        other => Err(anyhow!("GET {url} → HTTP {other}")),
    }
}

enum Action {
    Displayed { name: String, reason: &'static str },
    Idle,
}

fn tick(
    panel: &mut Panel,
    nvs: &mut EspNvs<NvsDefault>,
    current_name: &mut Option<String>,
    current_etag: &mut Option<String>,
    seen_latest: &mut Option<String>,
    last_rotate: &mut Instant,
) -> Result<Action> {
    let catalog = fetch_catalog()?;
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
            show_named(panel, nvs, current_name, current_etag, latest, false)?;
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
            show_named(panel, nvs, current_name, current_etag, &name, false)?;
            *last_rotate = Instant::now();
            return Ok(Action::Displayed {
                name,
                reason: "rotate",
            });
        }
    }

    Ok(Action::Idle)
}

fn show_named(
    panel: &mut Panel,
    nvs: &mut EspNvs<NvsDefault>,
    current_name: &mut Option<String>,
    current_etag: &mut Option<String>,
    name: &str,
    use_etag: bool,
) -> Result<()> {
    let url = format!("{INKBOT_BASE_URL}/{name}.bin");
    let if_none = if use_etag && current_name.as_deref() == Some(name) {
        current_etag.as_deref()
    } else {
        None
    };
    info!("GET {url} (free_heap={})", unsafe {
        esp_get_free_heap_size()
    });
    let response = http_get(&url, if_none)?;
    match response.status {
        304 => Ok(()),
        200 => {
            if response.body.len() != FRAME_BYTES {
                return Err(anyhow!(
                    "framebuffer must be {FRAME_BYTES} bytes, got {}",
                    response.body.len()
                ));
            }
            panel.show_frame(&response.body)?;
            write_str(nvs, NVS_NAME, name)?;
            *current_name = Some(name.to_string());
            if let Some(etag) = response.etag {
                write_str(nvs, NVS_ETAG, &etag)?;
                *current_etag = Some(etag);
            }
            Ok(())
        }
        404 => Err(anyhow!("image {name} missing on server")),
        other => Err(anyhow!("GET {url} → HTTP {other}")),
    }
}

fn fetch_catalog() -> Result<Catalog> {
    let url = format!("{INKBOT_BASE_URL}/");
    info!("GET {url} (free_heap={})", unsafe {
        esp_get_free_heap_size()
    });
    let response = http_get(&url, None)?;
    if response.status != 200 {
        return Err(anyhow!("GET {url} → HTTP {}", response.status));
    }
    Catalog::parse(&response.body).map_err(|e| anyhow!("catalog json: {e}"))
}

fn connect_wifi(wifi: &mut BlockingWifi<EspWifi<'static>>) -> Result<()> {
    const ATTEMPTS: u32 = 5;
    let mut last_err: Option<anyhow::Error> = None;
    for attempt in 1..=ATTEMPTS {
        info!(
            "wifi attempt {attempt}/{ATTEMPTS} ssid={WIFI_SSID} free_heap={}",
            unsafe { esp_get_free_heap_size() }
        );
        match connect_wifi_once(wifi, attempt) {
            Ok(()) => return Ok(()),
            Err(e) => {
                warn!("wifi attempt {attempt}/{ATTEMPTS} failed: {e:#}");
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
        info!("wifi[{attempt}] {name} free_heap={}", unsafe {
            esp_get_free_heap_size()
        });
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
        0 => info!("wifi[{attempt}] max_tx_power=44 (≈11 dBm)"),
        code => warn!("wifi[{attempt}] set_max_tx_power failed: {code}"),
    }

    step("connect");
    wifi.connect().map_err(|e| anyhow!("connect: {e:?}"))?;
    step("dhcp");
    wifi.wait_netif_up().map_err(|e| anyhow!("dhcp: {e:?}"))?;
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

struct HttpResponse {
    status: u16,
    etag: Option<String>,
    body: Vec<u8>,
}

fn http_get(url: &str, if_none_match: Option<&str>) -> Result<HttpResponse> {
    let mut client = HttpClient::wrap(EspHttpConnection::new(&HttpConfig {
        buffer_size: Some(1024),
        buffer_size_tx: Some(1024),
        timeout: Some(Duration::from_secs(30)),
        crt_bundle_attach: Some(esp_idf_svc::sys::esp_crt_bundle_attach),
        ..Default::default()
    })?);

    let mut headers: Vec<(&str, &str)> = vec![("User-Agent", "inkbot-esp32/0.1")];
    if let Some(etag) = if_none_match {
        headers.push(("If-None-Match", etag));
    }

    let request = client
        .request(Method::Get, url, &headers)
        .map_err(|e| anyhow!("http request: {e:?}"))?;
    let mut response = request
        .submit()
        .map_err(|e| anyhow!("http submit: {e:?}"))?;
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
            let n = Read::read(&mut response, &mut buf).map_err(|e| anyhow!("http read: {e:?}"))?;
            if n == 0 {
                break;
            }
            body.extend_from_slice(&buf[..n]);
            if body.len() > FRAME_BYTES + 2048 {
                return Err(anyhow!("response body too large"));
            }
        }
    }

    Ok(HttpResponse { status, etag, body })
}
