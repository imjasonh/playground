//! Reusable applications built on top of [`crate::boards::Board`] and
//! [`crate::platform::App`].

pub mod base;
pub mod bench;
pub mod grayscale;
pub mod maze;
pub mod photo;
#[cfg(mcu_esp32s3)]
pub mod recorder;
