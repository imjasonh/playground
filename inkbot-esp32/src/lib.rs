//! Host-testable pieces of the inkbot ESP32 firmware.
//!
//! Device Wi-Fi / HTTP / e-paper code lives in `main.rs` (feature `firmware`).

pub mod catalog;
pub mod net;
pub mod panel;
pub mod png_frame;
pub mod status;

pub use catalog::Catalog;
pub use net::{is_http_connect_failure, should_refresh_wifi, WifiRefresh};
pub use panel::{FRAME_BYTES, PANEL_HEIGHT, PANEL_WIDTH};
pub use png_frame::{decode_bw_png, PngFrameError};
pub use status::{
    format_error_chain, format_panic_message, overlay_status_line, reset_is_abnormal,
    reset_reason_hint, reset_reason_name, should_post_status, wifi_reason_name, CrashStatus,
    DeviceTelemetry, FetchStatus, StatusReport, WifiStatus, FIRMWARE_ID, STATUS_MAX_COLS,
    STATUS_MAX_LINES,
};
