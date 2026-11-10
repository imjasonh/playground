//! Links the demo application with its memory layout.

fn main() {
    let dir = std::env::var("CARGO_MANIFEST_DIR").expect("Cargo sets CARGO_MANIFEST_DIR");
    println!("cargo:rustc-link-search={dir}");
    println!("cargo:rustc-link-arg-bins=-Tapp.x");
    println!("cargo:rustc-link-arg-bins=-Trom.x");
    println!("cargo:rerun-if-changed=rom.x");
    println!("cargo:rerun-if-changed=app.x");
    println!("cargo:rerun-if-env-changed=C3_DEMO_VERSION");
}
