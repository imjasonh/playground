//! Links the lockstep test firmware with the bootloader's memory layout and
//! assembles the cases that `c3-ota`'s `rv_cases` example generated into
//! the directory named by `C3_RVTEST_CASES`. Without it, the firmware has
//! no cases, so the crate still builds and lints.

use std::env;
use std::fs;
use std::path::PathBuf;

fn main() {
    let dir = PathBuf::from(env::var("CARGO_MANIFEST_DIR").expect("Cargo sets CARGO_MANIFEST_DIR"));
    let out = PathBuf::from(env::var("OUT_DIR").expect("Cargo sets OUT_DIR"));
    println!("cargo:rustc-link-search={}", dir.display());
    println!(
        "cargo:rustc-link-search={}",
        dir.join("../bootloader").display()
    );
    println!("cargo:rustc-link-arg-bins=-Trvtest.x");
    println!("cargo:rustc-link-arg-bins=-Trom.x");
    println!("cargo:rerun-if-changed=rvtest.x");
    println!("cargo:rerun-if-env-changed=C3_RVTEST_CASES");
    let cases = match env::var("C3_RVTEST_CASES") {
        Ok(d) => {
            let path = PathBuf::from(d).join("cases.S");
            println!("cargo:rerun-if-changed={}", path.display());
            fs::read_to_string(path).expect("cases.S is readable")
        }
        Err(_) => ".section .rodata.rvcases, \"a\"\n.balign 4\n.globl rv_cases\nrv_cases:\n\
            .globl rv_case_count\nrv_case_count:\n  .word 0\n"
            .to_string(),
    };
    fs::write(out.join("cases.S"), cases).expect("OUT_DIR is writable");
}
