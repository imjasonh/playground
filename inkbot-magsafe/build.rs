//! Put the application memory map on the linker search path for the bare-metal
//! build. The host build ignores it because `.cargo/config.toml` references the
//! linker script only for `thumbv7em-none-eabihf`.

use std::env;
use std::fs;
use std::path::PathBuf;

fn main() {
    let out = PathBuf::from(env::var("OUT_DIR").expect("OUT_DIR is set by cargo"));
    fs::write(out.join("memory.x"), include_bytes!("memory-app.x")).expect("write memory.x");
    println!("cargo:rustc-link-search={}", out.display());
    println!("cargo:rerun-if-changed=memory-app.x");
    println!("cargo:rerun-if-changed=build.rs");
}
