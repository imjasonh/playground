//! Per-device settings loaded from NVS (written by `make provision`).

use anyhow::{anyhow, Result};
use esp_idf_svc::nvs::{EspDefaultNvsPartition, EspNvs};

use crate::nvs_util::{is_not_found, read_str};
use inkbot_esp32::require_https_url;

const NVS_WIFI_NS: &str = "wifi";
const NVS_INKBOT_NS: &str = "inkbot";
const NVS_OTA_NS: &str = "ota";

/// Compile-time OTA defaults. NVS `ota/*` keys override these.
pub const DEFAULT_OTA_REPO: &str = "ghcr.io/imjasonh/playground/inkbot-esp32";
pub const DEFAULT_OTA_TAG: &str = "latest";
pub const DEFAULT_OTA_POLL_SECS: u64 = 600;

/// Runtime config. Secrets live in NVS, not in the OTA image.
pub struct AppConfig {
    pub wifi_ssid: String,
    pub wifi_pass: String,
    pub base_url: String,
    pub poll_secs: u64,
    pub rotate_secs: u64,
    pub upload_secret: String,
    pub status_secs: u64,
    pub dhcp_renew_secs: u64,
    pub ota_repo: String,
    pub ota_tag: String,
    pub ota_poll_secs: u64,
}

impl AppConfig {
    /// Load required Wi-Fi + Worker settings. Returns `Ok(None)` if
    /// `wifi/ssid`, `wifi/pass`, or `inkbot/base_url` is missing.
    pub fn load(partition: EspDefaultNvsPartition) -> Result<Option<Self>> {
        let wifi = match EspNvs::new(partition.clone(), NVS_WIFI_NS, false) {
            Ok(n) => n,
            Err(e) if is_not_found(&e) => return Ok(None),
            Err(e) => return Err(anyhow!("open NVS {NVS_WIFI_NS}: {e:?}")),
        };
        let ssid = read_str(&wifi, NVS_WIFI_NS, "ssid", 64)?;
        let pass = read_str(&wifi, NVS_WIFI_NS, "pass", 96)?;

        let inkbot = match EspNvs::new(partition.clone(), NVS_INKBOT_NS, false) {
            Ok(n) => n,
            Err(e) if is_not_found(&e) => return Ok(None),
            Err(e) => return Err(anyhow!("open NVS {NVS_INKBOT_NS}: {e:?}")),
        };
        let base_url = read_str(&inkbot, NVS_INKBOT_NS, "base_url", 256)?;

        let (Some(ssid), Some(pass), Some(base_url)) = (ssid, pass, base_url) else {
            return Ok(None);
        };
        if ssid.is_empty() || base_url.is_empty() {
            return Ok(None);
        }
        require_https_url(&base_url).map_err(|e| anyhow!("inkbot/base_url: {e}"))?;

        let poll_secs = inkbot
            .get_u32("poll_secs")
            .ok()
            .flatten()
            .filter(|n| *n > 0)
            .unwrap_or(60) as u64;
        let rotate_secs = inkbot
            .get_u32("rotate_secs")
            .ok()
            .flatten()
            .filter(|n| *n > 0)
            .unwrap_or(1800) as u64;
        let upload_secret =
            read_str(&inkbot, NVS_INKBOT_NS, "upload_secret", 128)?.unwrap_or_default();
        let status_secs = inkbot
            .get_u32("status_secs")
            .ok()
            .flatten()
            .filter(|n| *n > 0)
            .unwrap_or(900) as u64;
        let dhcp_renew_secs = inkbot.get_u32("dhcp_renew").ok().flatten().unwrap_or(21600) as u64;

        let (ota_repo, ota_tag, ota_poll_secs) = load_ota(partition)?;

        Ok(Some(Self {
            wifi_ssid: ssid,
            wifi_pass: pass,
            base_url: base_url.trim_end_matches('/').to_string(),
            poll_secs,
            rotate_secs,
            upload_secret,
            status_secs,
            dhcp_renew_secs,
            ota_repo,
            ota_tag,
            ota_poll_secs,
        }))
    }
}

fn load_ota(partition: EspDefaultNvsPartition) -> Result<(String, String, u64)> {
    let nvs = match EspNvs::new(partition, NVS_OTA_NS, false) {
        Ok(n) => n,
        Err(_) => {
            return Ok((
                DEFAULT_OTA_REPO.into(),
                DEFAULT_OTA_TAG.into(),
                DEFAULT_OTA_POLL_SECS,
            ));
        }
    };
    let repo = read_str(&nvs, NVS_OTA_NS, "repo", 256)?
        .filter(|s| !s.is_empty())
        .unwrap_or_else(|| DEFAULT_OTA_REPO.into());
    let tag = read_str(&nvs, NVS_OTA_NS, "tag", 64)?
        .filter(|s| !s.is_empty())
        .unwrap_or_else(|| DEFAULT_OTA_TAG.into());
    // 0 means "do not poll" and must survive as 0. Missing uses the default.
    let poll = match nvs.get_u32("poll_secs").ok().flatten() {
        Some(0) => 0,
        Some(n) => n as u64,
        None => DEFAULT_OTA_POLL_SECS,
    };
    Ok((repo, tag, poll))
}
