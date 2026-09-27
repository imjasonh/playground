//! BLE GATT contract for the future iOS app.
//!
//! The S3 advertises one service. Text writes select apps and store Wi-Fi
//! credentials. A separate pair of characteristics carries the OTA image.
//! UUIDs here are the ones the iOS app must use.

use crate::ota::{self, OtaSession};

/// Advertised GAP name.
pub const DEVICE_NAME: &str = "PlaygroundKnob";

/// On-wire id of the S3 image. Bump when the GATT contract changes.
pub const FIRMWARE_ID_S3: &str = "knob-s3/0.1";

/// On-wire id of the companion image.
pub const FIRMWARE_ID_ESP32: &str = "knob-esp32/0.1";

pub const SERVICE_UUID: &str = "7d3a1c10-6e2b-4f8a-9c11-5b0e4a6d1001";
pub const INFO_UUID: &str = "7d3a1c10-6e2b-4f8a-9c11-5b0e4a6d1002";
pub const TEXT_UUID: &str = "7d3a1c10-6e2b-4f8a-9c11-5b0e4a6d1003";
pub const STATUS_UUID: &str = "7d3a1c10-6e2b-4f8a-9c11-5b0e4a6d1004";
pub const OTA_CONTROL_UUID: &str = "7d3a1c10-6e2b-4f8a-9c11-5b0e4a6d1005";
pub const OTA_DATA_UUID: &str = "7d3a1c10-6e2b-4f8a-9c11-5b0e4a6d1006";
pub const OTA_STATUS_UUID: &str = "7d3a1c10-6e2b-4f8a-9c11-5b0e4a6d1007";
/// Two-byte HID consumer report. The phone reads a press, then a zero release.
pub const HID_UUID: &str = "7d3a1c10-6e2b-4f8a-9c11-5b0e4a6d1008";

/// Largest OTA data payload the firmware accepts in one write.
pub const MAX_OTA_CHUNK: usize = 240;

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum ChipId {
    S3,
    Esp32,
}

/// A line written to the text characteristic.
#[derive(Clone, Debug, PartialEq, Eq)]
pub enum TextCmd {
    Ping,
    Apps,
    Open(String),
    Status,
    Reboot(ChipId),
    Wifi { ssid: String, pass: String },
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub enum TextError {
    Empty,
    Unknown,
    BadArgs,
}

pub fn parse_text(raw: &str) -> Result<TextCmd, TextError> {
    let line = raw.trim();
    if line.is_empty() {
        return Err(TextError::Empty);
    }
    let mut parts = line.split_whitespace();
    let verb = parts.next().unwrap_or("");
    match verb.to_ascii_lowercase().as_str() {
        "ping" => Ok(TextCmd::Ping),
        "apps" => Ok(TextCmd::Apps),
        "status" => Ok(TextCmd::Status),
        "open" => {
            let id = parts.next().ok_or(TextError::BadArgs)?;
            if parts.next().is_some() || !valid_id(id) {
                return Err(TextError::BadArgs);
            }
            Ok(TextCmd::Open(id.to_ascii_lowercase()))
        }
        "reboot" => {
            let which = parts.next().unwrap_or("s3");
            if parts.next().is_some() {
                return Err(TextError::BadArgs);
            }
            let chip = match which.to_ascii_lowercase().as_str() {
                "s3" => ChipId::S3,
                "esp32" => ChipId::Esp32,
                _ => return Err(TextError::BadArgs),
            };
            Ok(TextCmd::Reboot(chip))
        }
        "wifi" => {
            let ssid = parts.next().ok_or(TextError::BadArgs)?;
            let pass = parts.next().ok_or(TextError::BadArgs)?;
            if parts.next().is_some() || ssid.len() > 32 || pass.len() > 64 {
                return Err(TextError::BadArgs);
            }
            Ok(TextCmd::Wifi {
                ssid: ssid.to_string(),
                pass: pass.to_string(),
            })
        }
        _ => Err(TextError::Unknown),
    }
}

fn valid_id(id: &str) -> bool {
    !id.is_empty()
        && id.len() <= 16
        && id.bytes().all(|b| {
            b.is_ascii_lowercase() || b.is_ascii_uppercase() || b.is_ascii_digit() || b == b'-'
        })
}

pub fn reply_apps(ids: &[&str]) -> String {
    ids.join(",")
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub struct Status {
    pub firmware: &'static str,
    pub app: String,
    pub uptime_s: u32,
    pub battery_mv: u32,
    pub link_up: bool,
    pub bt: &'static str,
}

pub fn format_status(status: &Status) -> String {
    format!(
        "fw={} app={} up={} bat={} link={} bt={}",
        status.firmware,
        status.app,
        status.uptime_s,
        status.battery_mv,
        if status.link_up { "up" } else { "down" },
        status.bt
    )
}

/// Info characteristic, read by the iOS app before an update.
///
/// `KNOB` magic, version 1, chip (0 S3, 1 is not used here), firmware id,
/// max chunk, slot limit.
pub fn encode_info(firmware_id: &str, slot_limit: u32) -> Vec<u8> {
    let id = firmware_id.as_bytes();
    let mut out = Vec::with_capacity(4 + 1 + 1 + id.len() + 2 + 4);
    out.extend_from_slice(b"KNOB");
    out.push(1);
    out.push(id.len() as u8);
    out.extend_from_slice(id);
    out.extend_from_slice(&(MAX_OTA_CHUNK as u16).to_le_bytes());
    out.extend_from_slice(&slot_limit.to_le_bytes());
    out
}

pub fn encode_ota_status(session: &OtaSession) -> [u8; 7] {
    ota::encode_status(session)
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn parses_the_text_commands() {
        assert_eq!(parse_text("ping\n").unwrap(), TextCmd::Ping);
        assert_eq!(
            parse_text("open Clock").unwrap(),
            TextCmd::Open("clock".into())
        );
        assert_eq!(
            parse_text("reboot esp32").unwrap(),
            TextCmd::Reboot(ChipId::Esp32)
        );
        assert_eq!(
            parse_text("wifi home secret").unwrap(),
            TextCmd::Wifi {
                ssid: "home".into(),
                pass: "secret".into()
            }
        );
        assert_eq!(parse_text("nope"), Err(TextError::Unknown));
        assert_eq!(parse_text("open"), Err(TextError::BadArgs));
    }

    #[test]
    fn status_line_and_info_blob() {
        let line = format_status(&Status {
            firmware: FIRMWARE_ID_S3,
            app: "dial".into(),
            uptime_s: 4,
            battery_mv: 3900,
            link_up: true,
            bt: "connected",
        });
        assert_eq!(
            line,
            "fw=knob-s3/0.1 app=dial up=4 bat=3900 link=up bt=connected"
        );
        let info = encode_info(FIRMWARE_ID_S3, 0x600000);
        assert_eq!(&info[..4], b"KNOB");
        assert!(info
            .windows(FIRMWARE_ID_S3.len())
            .any(|w| w == FIRMWARE_ID_S3.as_bytes()));
    }
}
