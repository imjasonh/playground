//! The checks the c3-boot bootloader applies to a slot.
//!
//! Every function is pure: it reads byte slices and returns a value or an
//! [`Error`]. The bootloader crate does the flash reads, eFuse access, and
//! jump. `docs/formats.md` defines each format, and each parser rejects
//! anything it doesn't allow.
//!
//! This crate is the code that the machine-code proofs cover, so it follows
//! the rules in `docs/esp32c3-verified-ota-plan.md`: no heap, no `unsafe`, no
//! function pointers, and checked arithmetic and indexing throughout.

#![cfg_attr(not(test), no_std)]

pub mod bootstate;
pub mod chain;
pub mod error;
pub mod image;
pub mod keys;
pub mod layout;
pub mod level;
pub mod manifest;
mod reader;
pub mod trustroot;

pub use error::Error;
