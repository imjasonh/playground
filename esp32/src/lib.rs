//! Shared ESP32 platform services.
//!
//! The original firmware and the e-ink SSH client are separate binaries, but
//! they deliberately share the same OTA verifier, trust policy, NVS helpers,
//! and optional observability implementation. Keeping those security-sensitive
//! pieces in one library prevents the two firmware images from drifting.

pub mod cloud_log;
pub mod gcp_auth;
pub mod metrics;
pub mod nvs_util;
pub mod ota;
pub mod sig;
pub mod trust;
