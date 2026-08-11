//! Host-testable pieces of the inkbot ESP32 firmware.
//!
//! Device Wi-Fi / HTTP / e-paper code lives in `main.rs` (feature `firmware`).

pub mod catalog;
pub mod panel;
pub mod png_frame;

pub use catalog::Catalog;
pub use panel::{FRAME_BYTES, PANEL_HEIGHT, PANEL_WIDTH};
pub use png_frame::{decode_bw_png, PngFrameError};
