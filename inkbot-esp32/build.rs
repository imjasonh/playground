//! Device settings live in NVS (see `docs/device-config.md`), not in this crate.
//!
//! On esp-idf targets, wire embuild's ESP-IDF sysenv for the link.

use std::env;

fn main() {
    println!("cargo:rerun-if-changed=sdkconfig.defaults");

    // Build.rs always compiles for the host; CARGO_CFG_TARGET_OS reflects
    // the crate target. Only wire ESP-IDF link flags when cross-compiling.
    if env::var("CARGO_CFG_TARGET_OS").as_deref() == Ok("espidf") {
        embuild::espidf::sysenv::output();
    }
}
