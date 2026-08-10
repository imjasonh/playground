//! inkbot-esp32 — poll the inkbot Worker and show frames on Waveshare 7.5″.

mod display;

use std::thread;
use std::time::Duration;

use anyhow::{anyhow, Result};
use embedded_svc::http::client::Client as HttpClient;
use embedded_svc::http::Method;
use embedded_svc::io::Read;
use esp_idf_svc::eventloop::EspSystemEventLoop;
use esp_idf_svc::hal::peripherals::Peripherals;
use esp_idf_svc::http::client::{Configuration as HttpConfig, EspHttpConnection};
use esp_idf_svc::nvs::{EspDefaultNvsPartition, EspNvs, NvsDefault};
use esp_idf_svc::sys::{esp_get_free_heap_size, esp_reset_reason, esp_wifi_set_max_tx_power};
use esp_idf_svc::wifi::{
    AuthMethod, BlockingWifi, ClientConfiguration, Configuration as WifiConfig, EspWifi,
};
use log::{info, warn};

use display::Panel;
use inkbot_esp32::FRAME_BYTES;

include!(concat!(env!("OUT_DIR"), "/config_gen.rs"));

const NVS_NS: &str = "inkbot";
const NVS_ETAG: &str = "etag";

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
    // Give a weak USB PSU a moment after panel bring-up before Wi-Fi TX peaks.
    thread::sleep(Duration::from_millis(500));
    if let Err(e) = connect_wifi(&mut wifi) {
        warn!("wifi failed: {e:#}");
        // Short panel text so wall-powered boots (no serial) still show the stage.
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
    let mut etag = read_etag(&nvs)?;
    info!("nvs: last etag={etag:?}");

    // Boot always downloads the current frame (no If-None-Match). A matching
    // NVS etag used to yield 304 + an "inkbot ready" splash, which wiped the
    // bistable panel even when the server image was already current.
    match poll_once(&mut panel, &mut nvs, &mut etag, false) {
        Ok(true) => info!("displayed boot frame"),
        Ok(false) => {
            info!("no image on server yet");
            let _ = panel.show_message("inkbot ready");
        }
        Err(e) => {
            warn!("boot poll failed: {e:#}");
            let _ = panel.show_message("poll failed");
        }
    }

    loop {
        thread::sleep(Duration::from_secs(POLL_SECS));
        match poll_once(&mut panel, &mut nvs, &mut etag, true) {
            Ok(true) => info!("displayed new frame"),
            Ok(false) => info!("no change"),
            Err(e) => warn!("poll failed: {e:#}"),
        }
    }
}

/// Connect with retries. Weak 5 V adapters often brown out during the first
/// association TX burst; laptop USB usually does not.
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
        // NY Sphere is WPA3-SAE; WPA2/WPA3 personal lets ESP-IDF negotiate.
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

    // Cap TX power (~11 dBm) so weak wall-wart supplies are less likely to sag
    // during association. Unit is 0.25 dBm (ESP-IDF).
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

fn read_etag(nvs: &EspNvs<NvsDefault>) -> Result<Option<String>> {
    let mut buf = [0u8; 128];
    match nvs.get_str(NVS_ETAG, &mut buf) {
        Ok(Some(s)) if !s.is_empty() => Ok(Some(s.to_string())),
        Ok(_) => Ok(None),
        Err(e) => Err(anyhow!("read etag: {e:?}")),
    }
}

fn write_etag(nvs: &mut EspNvs<NvsDefault>, etag: &str) -> Result<()> {
    nvs.set_str(NVS_ETAG, etag)
        .map_err(|e| anyhow!("write etag: {e:?}"))?;
    Ok(())
}

/// Returns true when a new frame was displayed.
///
/// When `use_etag` is false, skips `If-None-Match` so the server always
/// returns the body (used on boot to repaint after power-on).
fn poll_once(
    panel: &mut Panel,
    nvs: &mut EspNvs<NvsDefault>,
    etag: &mut Option<String>,
    use_etag: bool,
) -> Result<bool> {
    // Fetch the pre-packed 48 KB framebuffer — no on-device zlib/PNG inflate.
    let url = format!("{INKBOT_BASE_URL}/image.bin");
    info!("GET {url} (free_heap={})", unsafe {
        esp_get_free_heap_size()
    });
    let if_none_match = if use_etag { etag.as_deref() } else { None };
    let response = http_get(&url, if_none_match)?;
    match response.status {
        304 => Ok(false),
        200 => {
            if response.body.len() != FRAME_BYTES {
                return Err(anyhow!(
                    "framebuffer must be {FRAME_BYTES} bytes, got {}",
                    response.body.len()
                ));
            }
            panel.show_frame(&response.body)?;
            if let Some(new_etag) = response.etag {
                write_etag(nvs, &new_etag)?;
                *etag = Some(new_etag);
            }
            Ok(true)
        }
        404 => {
            warn!("no image on server yet");
            Ok(false)
        }
        other => Err(anyhow!("GET {url} → HTTP {other}")),
    }
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
        // Exact panel framebuffer size; reserve so we don't fragment while reading.
        body.reserve(FRAME_BYTES);
        let mut buf = [0u8; 512];
        loop {
            let n = Read::read(&mut response, &mut buf).map_err(|e| anyhow!("http read: {e:?}"))?;
            if n == 0 {
                break;
            }
            body.extend_from_slice(&buf[..n]);
            if body.len() > FRAME_BYTES + 1024 {
                return Err(anyhow!("response body too large"));
            }
        }
    }

    Ok(HttpResponse { status, etag, body })
}
