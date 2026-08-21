//! Runtime device settings loaded from NVS at boot (not compiled into the ELF).
//!
//! Flash with `nvs/device.csv` via `make nvs` — see `docs/device-config.md`.

use std::fmt;

use serde::{Deserialize, Serialize};

/// NVS namespace for Wi-Fi STA credentials.
pub const NVS_NS_WIFI: &str = "wifi";
/// NVS namespace for Worker URL, cadence, and upload secret.
///
/// Shares the partition with catalog keys (`name` / `etag` / …) under the same
/// namespace in the firmware; those keys are separate from the ones below.
pub const NVS_NS_INKBOT: &str = "inkbot";

pub const NVS_KEY_SSID: &str = "ssid";
pub const NVS_KEY_PASS: &str = "pass";
pub const NVS_KEY_BASE_URL: &str = "base_url";
pub const NVS_KEY_POLL_SECS: &str = "poll_secs";
pub const NVS_KEY_ROTATE_SECS: &str = "rotate_secs";
pub const NVS_KEY_UPLOAD_SECRET: &str = "upload_sec";
pub const NVS_KEY_STATUS_SECS: &str = "status_secs";
pub const NVS_KEY_DHCP_RENEW_SECS: &str = "dhcp_renew";

/// Default catalog poll interval when `poll_secs` is absent from NVS.
pub const DEFAULT_POLL_SECS: u64 = 60;
/// Default library rotate interval when `rotate_secs` is absent from NVS.
pub const DEFAULT_ROTATE_SECS: u64 = 1800;
/// Default `POST /device` interval when `status_secs` is absent from NVS.
pub const DEFAULT_STATUS_SECS: u64 = 900;
/// Default DHCP renew interval when `dhcp_renew` is absent from NVS.
pub const DEFAULT_DHCP_RENEW_SECS: u64 = 21600;

/// Wi-Fi + Worker settings for the inkbot poll loop.
#[derive(Debug, Clone, PartialEq, Eq, Serialize, Deserialize)]
pub struct DeviceConfig {
    pub wifi_ssid: String,
    pub wifi_pass: String,
    /// Worker base URL, no trailing slash.
    pub base_url: String,
    pub poll_secs: u64,
    pub rotate_secs: u64,
    /// Empty disables `POST /device`.
    pub upload_secret: String,
    pub status_secs: u64,
    pub dhcp_renew_secs: u64,
}

/// Missing or invalid flash-time settings.
#[derive(Debug, Clone, PartialEq, Eq)]
pub enum DeviceConfigError {
    MissingSsid,
    MissingBaseUrl,
}

impl fmt::Display for DeviceConfigError {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            Self::MissingSsid => write!(f, "wifi.ssid not set in NVS"),
            Self::MissingBaseUrl => write!(f, "inkbot.base_url not set in NVS"),
        }
    }
}

impl std::error::Error for DeviceConfigError {}

/// Raw optional values as read from NVS (or a CSV / test fixture).
#[derive(Debug, Clone, Default, PartialEq, Eq)]
pub struct DeviceConfigRaw {
    pub wifi_ssid: Option<String>,
    pub wifi_pass: Option<String>,
    pub base_url: Option<String>,
    pub poll_secs: Option<u64>,
    pub rotate_secs: Option<u64>,
    pub upload_secret: Option<String>,
    pub status_secs: Option<u64>,
    pub dhcp_renew_secs: Option<u64>,
}

impl DeviceConfig {
    /// Build config from flash-time values. SSID and base URL are required;
    /// password and upload secret may be empty; cadence falls back to defaults.
    pub fn from_raw(raw: DeviceConfigRaw) -> Result<Self, DeviceConfigError> {
        let wifi_ssid = raw
            .wifi_ssid
            .map(|s| s.trim().to_string())
            .filter(|s| !s.is_empty())
            .ok_or(DeviceConfigError::MissingSsid)?;
        let base_url = raw
            .base_url
            .map(|s| s.trim().trim_end_matches('/').to_string())
            .filter(|s| !s.is_empty())
            .ok_or(DeviceConfigError::MissingBaseUrl)?;
        let wifi_pass = raw.wifi_pass.unwrap_or_default();
        let upload_secret = raw.upload_secret.unwrap_or_default();
        Ok(Self {
            wifi_ssid,
            wifi_pass,
            base_url,
            poll_secs: raw.poll_secs.unwrap_or(DEFAULT_POLL_SECS).max(1),
            rotate_secs: raw.rotate_secs.unwrap_or(DEFAULT_ROTATE_SECS).max(1),
            upload_secret,
            status_secs: raw.status_secs.unwrap_or(DEFAULT_STATUS_SECS).max(1),
            dhcp_renew_secs: raw.dhcp_renew_secs.unwrap_or(DEFAULT_DHCP_RENEW_SECS),
        })
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn requires_ssid_and_base_url() {
        assert_eq!(
            DeviceConfig::from_raw(DeviceConfigRaw {
                base_url: Some("https://example.workers.dev".into()),
                ..Default::default()
            }),
            Err(DeviceConfigError::MissingSsid)
        );
        assert_eq!(
            DeviceConfig::from_raw(DeviceConfigRaw {
                wifi_ssid: Some("home".into()),
                ..Default::default()
            }),
            Err(DeviceConfigError::MissingBaseUrl)
        );
    }

    #[test]
    fn applies_cadence_defaults_and_trims_url() {
        let cfg = DeviceConfig::from_raw(DeviceConfigRaw {
            wifi_ssid: Some("  home  ".into()),
            wifi_pass: Some("secret".into()),
            base_url: Some("https://inkbot.example.workers.dev/".into()),
            upload_secret: Some("tok".into()),
            ..Default::default()
        })
        .unwrap();
        assert_eq!(cfg.wifi_ssid, "home");
        assert_eq!(cfg.wifi_pass, "secret");
        assert_eq!(cfg.base_url, "https://inkbot.example.workers.dev");
        assert_eq!(cfg.upload_secret, "tok");
        assert_eq!(cfg.poll_secs, DEFAULT_POLL_SECS);
        assert_eq!(cfg.rotate_secs, DEFAULT_ROTATE_SECS);
        assert_eq!(cfg.status_secs, DEFAULT_STATUS_SECS);
        assert_eq!(cfg.dhcp_renew_secs, DEFAULT_DHCP_RENEW_SECS);
    }

    #[test]
    fn zero_poll_becomes_one() {
        let cfg = DeviceConfig::from_raw(DeviceConfigRaw {
            wifi_ssid: Some("x".into()),
            base_url: Some("https://x".into()),
            poll_secs: Some(0),
            ..Default::default()
        })
        .unwrap();
        assert_eq!(cfg.poll_secs, 1);
    }

    #[test]
    fn nvs_key_names_fit_esp_idf_limit() {
        for key in [
            NVS_KEY_SSID,
            NVS_KEY_PASS,
            NVS_KEY_BASE_URL,
            NVS_KEY_POLL_SECS,
            NVS_KEY_ROTATE_SECS,
            NVS_KEY_UPLOAD_SECRET,
            NVS_KEY_STATUS_SECS,
            NVS_KEY_DHCP_RENEW_SECS,
        ] {
            assert!(
                key.len() <= 15,
                "{key} is {} bytes (NVS max key length is 15)",
                key.len()
            );
        }
    }
}
