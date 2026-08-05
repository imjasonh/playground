//! Shared ESP32 platform services.
//!
//! The original firmware and the e-ink SSH client are separate binaries, but
//! they deliberately share the same OTA verifier, trust policy, NVS helpers,
//! and optional observability implementation. Keeping those security-sensitive
//! pieces in one library prevents the two firmware images from drifting.

#[cfg(feature = "observability")]
pub mod cloud_log;
#[cfg(feature = "observability")]
pub mod gcp_auth;
#[cfg(feature = "observability")]
pub mod metrics;
pub mod net_coord;
pub mod nvs_util;
pub mod ota;
pub mod sig;
#[cfg(feature = "observability")]
pub mod time_sync;
pub mod trust;
