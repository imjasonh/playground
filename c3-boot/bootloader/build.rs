//! Links the bootloader with its memory layout and embeds the genesis keys.

use std::env;
use std::fs;
use std::path::PathBuf;

fn main() {
    let dir = PathBuf::from(env::var("CARGO_MANIFEST_DIR").expect("Cargo sets CARGO_MANIFEST_DIR"));
    println!("cargo:rustc-link-search={}", dir.display());
    println!("cargo:rustc-link-arg-bins=-Tbootloader.x");
    println!("cargo:rustc-link-arg-bins=-Trom.x");
    println!("cargo:rerun-if-changed=rom.x");
    println!("cargo:rerun-if-changed=bootloader.x");

    // C3_GENESIS names a file holding the four genesis public keys, 128 bytes.
    // There is no default: the development keys' seeds are public, so a
    // build must ask for them by name with C3_GENESIS=dev, and that build
    // warns on every boot.
    println!("cargo:rerun-if-env-changed=C3_GENESIS");
    let choice = env::var("C3_GENESIS").expect(
        "set C3_GENESIS to the production genesis key file, or to `dev` for the public development keys",
    );
    let dev = choice == "dev";
    let genesis = if dev {
        dir.join("../testdata/keys/genesis-dev.pub")
    } else {
        PathBuf::from(choice)
    };
    if dev {
        println!("cargo:rustc-cfg=c3_dev_genesis");
    }
    println!("cargo:rustc-check-cfg=cfg(c3_dev_genesis)");
    println!("cargo:rerun-if-changed={}", genesis.display());
    let keys = fs::read(&genesis).expect("genesis key file is readable");
    assert_eq!(keys.len(), 128, "genesis key file holds four 32-byte keys");
    let out = PathBuf::from(env::var("OUT_DIR").expect("Cargo sets OUT_DIR"));
    fs::write(out.join("genesis.bin"), keys).expect("OUT_DIR is writable");
}
