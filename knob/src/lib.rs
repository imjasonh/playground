//! Host-testable core of the Waveshare knob firmware.
//!
//! Device GPIO, QSPI, I2S, SDMMC, Wi-Fi, and Bluetooth live in the
//! `knob-s3` and `knob-esp32` binaries. This library is the part both
//! chips and the future iOS app share: pin facts, the inter-chip frame
//! codec, the BLE control and OTA state machine, and the ten example apps.

mod crc;
mod font;

pub mod apps;
pub mod audio;
pub mod battery;
pub mod ble;
pub mod board;
pub mod canvas;
pub mod encoder;
pub mod haptic;
pub mod hid;
pub mod link;
pub mod mic;
pub mod ota;
pub mod shell;
pub mod st77916;
pub mod touch;

pub use apps::{catalog, App, AppId, Effects, Event, World};
pub use ble::{
    format_status, parse_text, ChipId, Status, TextCmd, DEVICE_NAME, FIRMWARE_ID_ESP32,
    FIRMWARE_ID_S3, HID_UUID, INFO_UUID, OTA_CONTROL_UUID, OTA_DATA_UUID, OTA_STATUS_UUID,
    SERVICE_UUID, STATUS_UUID, TEXT_UUID,
};
pub use board::{
    esp32, s3, APP_SLOT_ESP32, APP_SLOT_S3, CLASSIC_BT_NAME, LINK_BAUD, PANEL_H, PANEL_W,
};
pub use ota::{OtaError, OtaSession, OtaTarget};
pub use shell::Shell;
