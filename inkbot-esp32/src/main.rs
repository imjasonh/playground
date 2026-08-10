//! inkbot-esp32 — poll the inkbot Worker and show frames on Waveshare 7.5″.

mod display;

use std::thread;
use std::time::Duration;

use anyhow::{anyhow, Context, Result};
use embedded_svc::http::client::Client as HttpClient;
use embedded_svc::http::Method;
use embedded_svc::io::Read;
use esp_idf_svc::eventloop::EspSystemEventLoop;
use esp_idf_svc::hal::peripherals::Peripherals;
use esp_idf_svc::http::client::{Configuration as HttpConfig, EspHttpConnection};
use esp_idf_svc::nvs::{EspDefaultNvsPartition, EspNvs, NvsDefault};
use esp_idf_svc::wifi::{
    AuthMethod, BlockingWifi, ClientConfiguration, Configuration as WifiConfig, EspWifi,
};
use log::{info, warn};

use display::Panel;
use inkbot_esp32::decode_bw_png;

include!(concat!(env!("OUT_DIR"), "/config_gen.rs"));

const NVS_NS: &str = "inkbot";
const NVS_ETAG: &str = "etag";

fn main() -> Result<()> {
    esp_idf_svc::sys::link_patches();
    esp_idf_svc::log::EspLogger::initialize_default();
    info!("inkbot-esp32: boot");

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
    if let Err(e) = connect_wifi(&mut wifi) {
        warn!("wifi failed: {e:#}");
        let _ = panel.show_message("WiFi failed");
        return Err(e);
    }
    let ip = wifi.wifi().sta_netif().get_ip_info()?.ip;
    info!("wifi connected, ip={ip}");

    let mut nvs =
        EspNvs::new(nvs_part, NVS_NS, true).map_err(|e| anyhow!("open NVS {NVS_NS}: {e:?}"))?;
    let mut etag = read_etag(&nvs)?;
    info!("nvs: last etag={etag:?}");

    let _ = panel.show_message("inkbot ready");

    loop {
        match poll_once(&mut panel, &mut nvs, &mut etag) {
            Ok(true) => info!("displayed new frame"),
            Ok(false) => info!("no change"),
            Err(e) => warn!("poll failed: {e:#}"),
        }
        thread::sleep(Duration::from_secs(POLL_SECS));
    }
}

fn connect_wifi(wifi: &mut BlockingWifi<EspWifi<'static>>) -> Result<()> {
    wifi.set_configuration(&WifiConfig::Client(ClientConfiguration {
        ssid: WIFI_SSID
            .try_into()
            .map_err(|_| anyhow!("WiFi SSID exceeds 32 bytes"))?,
        password: WIFI_PASS
            .try_into()
            .map_err(|_| anyhow!("WiFi password exceeds 64 bytes"))?,
        auth_method: if WIFI_PASS.is_empty() {
            AuthMethod::None
        } else {
            AuthMethod::WPA2Personal
        },
        ..Default::default()
    }))?;
    wifi.start()?;
    info!("wifi started; connecting to {WIFI_SSID}");
    wifi.connect()?;
    wifi.wait_netif_up()?;
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
fn poll_once(
    panel: &mut Panel,
    nvs: &mut EspNvs<NvsDefault>,
    etag: &mut Option<String>,
) -> Result<bool> {
    let url = format!("{INKBOT_BASE_URL}/image.png");
    let response = http_get(&url, etag.as_deref())?;
    match response.status {
        304 => Ok(false),
        200 => {
            let frame = decode_bw_png(&response.body).context("decode panel png")?;
            panel.show_frame(&frame)?;
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
        let mut buf = [0u8; 1024];
        loop {
            let n = response
                .read(&mut buf)
                .map_err(|e| anyhow!("http read: {e:?}"))?;
            if n == 0 {
                break;
            }
            body.extend_from_slice(&buf[..n]);
            if body.len() > 256 * 1024 {
                return Err(anyhow!("response body too large"));
            }
        }
    }

    Ok(HttpResponse { status, etag, body })
}
