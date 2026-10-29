#![feature(never_type)] // want "unstable Rust feature"

#[feature(arbitrary_self_types)] // want "unstable Rust feature"
fn f() {}

#[cfg(feature = "wasm")]
fn g() {}

fn h() {
    let _ = "feature";
}
