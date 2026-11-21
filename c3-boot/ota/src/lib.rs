//! Host-side tools for c3-boot: build and sign everything a slot holds, and
//! check a slot with the same `c3-verify` code the bootloader runs.
//!
//! This crate runs in CI and on key holders' machines, not on the device, so
//! it may use `std` and parsing libraries. Nothing it produces is trusted by
//! the device without the device's own checks.

pub mod blob;
pub mod container;
pub mod image;
pub mod keys;
pub mod slot;
pub mod time;
