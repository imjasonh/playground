//! Put the selected memory map on the linker search path for the bare-metal
//! build. The host build ignores it because `.cargo/config.toml` references the
//! linker script only for `thumbv7em-none-eabihf`.

use std::env;
use std::fs;
use std::path::PathBuf;

fn main() {
    let out = PathBuf::from(env::var("OUT_DIR").expect("OUT_DIR is set by cargo"));
    let factory_bringup = env::var_os("CARGO_FEATURE_FACTORY_BRINGUP").is_some();
    let memory = if factory_bringup {
        include_bytes!("memory-factory.x").as_slice()
    } else {
        include_bytes!("memory.x").as_slice()
    };
    fs::write(out.join("memory.x"), memory).expect("write memory.x");
    println!("cargo:rustc-link-search={}", out.display());
    println!("cargo:rerun-if-changed=memory.x");
    println!("cargo:rerun-if-changed=memory-factory.x");
    println!("cargo:rerun-if-changed=build.rs");
    println!("cargo:rerun-if-env-changed=CARGO_FEATURE_FACTORY_BRINGUP");
}
