#![cfg_attr(not(test), no_std)]

//! Core logic for the inkbot-magsafe firmware, kept free of hardware so it can
//! be unit-tested on the host. The bare-metal entry point in `main.rs` wires
//! these modules to the nRF52833 peripherals.
//!
//! - [`charger`]: fail-closed BQ25186 register configuration.
//! - [`panel`]: geometry and command set for the 3.97-inch SSD1677-class panel.
//! - [`power`]: battery state-of-charge estimate and refresh/charge gating.
//! - [`protocol`]: the resumable, idempotent BLE frame-transfer state machine.

pub mod charger;
pub mod panel;
pub mod power;
pub mod protocol;
