//! Wire embuild's ESP-IDF sysenv on device builds.

use std::env;

fn main() {
    println!("cargo:rerun-if-changed=sdkconfig.defaults");
    println!("cargo:rerun-if-changed=sdkconfig.defaults.in");
    println!("cargo:rerun-if-changed=partitions.csv");
    println!("cargo:rerun-if-env-changed=GIT_SHA");

    if env::var("CARGO_CFG_TARGET_OS").as_deref() == Ok("espidf") {
        embuild::espidf::sysenv::output();
    }
}
