#![cfg_attr(not(test), no_std)]
#![forbid(unsafe_code)]

//! Core logic for the inkbot-magsafe firmware, kept free of hardware so it can
//! be unit-tested on the host. The bare-metal entry point in `main.rs` wires
//! these modules to the nRF52840 peripherals.
//!
//! - [`charger`]: fail-closed BQ25186 register configuration.
//! - [`memory`]: nonoverlapping nRF52840 flash regions.
//! - [`panel`]: geometry and command set for the 3.97-inch SSD1677-class panel.
//! - [`power`]: battery state-of-charge estimate and refresh/charge gating.
//! - [`protocol`]: the resumable, idempotent BLE frame-transfer state machine.
//! - [`storage`]: power-fail-safe metadata for alternating frame slots.

pub mod charger;
pub mod memory;
pub mod panel;
pub mod power;
pub mod protocol;
pub mod recovery;
pub mod storage;
