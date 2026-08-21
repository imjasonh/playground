//! Host-testable pieces of the inkbot ESP32 firmware.
//!
//! Device Wi-Fi / HTTP / e-paper code lives in `main.rs` (feature `firmware`).
//! The maze firmware (`maze_main.rs`) uses [`maze`] plus a local panel driver.
//! On `espidf`, `inkbot-lib` / `maze-lib` select which app modules are compiled
//! into that OTA image.

pub mod ota_format;
pub mod panel;

#[cfg(any(not(target_os = "espidf"), feature = "maze-lib"))]
pub mod maze;

#[cfg(any(not(target_os = "espidf"), feature = "inkbot-lib"))]
pub mod catalog;
#[cfg(any(not(target_os = "espidf"), feature = "inkbot-lib"))]
pub mod net;
#[cfg(any(not(target_os = "espidf"), feature = "inkbot-lib"))]
pub mod png_frame;
#[cfg(any(not(target_os = "espidf"), feature = "inkbot-lib"))]
pub mod status;

#[cfg(any(not(target_os = "espidf"), feature = "inkbot-lib"))]
pub use catalog::Catalog;
#[cfg(any(not(target_os = "espidf"), feature = "inkbot-lib"))]
pub use net::{is_http_connect_failure, should_refresh_wifi, WifiRefresh};
pub use ota_format::{
    ca_cert_window_ok, cert_window, check_ota_image, cosign_manifest_digest_hex,
    cosign_signature_tags, decode_fulcio_issuer_value, default_ota_repo, fulcio_leaf_window_ok,
    json_escape, known_ota_app, require_https_url, CertWindow, FirmwareConfig,
    COSIGN_SIMPLE_SIGNING_MEDIA_TYPE, GHCR_NAMESPACE, OTA_APPS, OTA_APP_INKBOT, OTA_APP_MAZE,
    OTA_CONFIG_MEDIA_TYPE, OTA_LAYER_MEDIA_TYPE, OTA_SLOT_BYTES, OTA_TARGET_CHIP,
    SIGSTORE_BUNDLE_MEDIA_TYPE_PREFIX,
};
pub use panel::{FRAME_BYTES, PANEL_HEIGHT, PANEL_WIDTH};
#[cfg(any(not(target_os = "espidf"), feature = "inkbot-lib"))]
pub use png_frame::{decode_bw_png, PngFrameError};
#[cfg(any(not(target_os = "espidf"), feature = "inkbot-lib"))]
pub use status::{
    crash_after_reset, format_error_chain, format_panic_message, incident_needs_post,
    overlay_status_line, reset_is_abnormal, reset_reason_hint, reset_reason_name,
    should_post_status, wifi_reason_name, CrashStatus, DeviceTelemetry, FetchStatus,
    IncidentContext, LastIncident, StatusReport, WifiStatus, FIRMWARE_ID, STATUS_MAX_COLS,
    STATUS_MAX_LINES,
};
