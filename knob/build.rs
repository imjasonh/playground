//! Wire embuild's ESP-IDF sysenv on device builds.

fn main() {
    println!("cargo:rerun-if-changed=sdkconfig.defaults.s3.in");
    println!("cargo:rerun-if-changed=sdkconfig.defaults.esp32.in");
    println!("cargo:rerun-if-changed=partitions-s3.csv");
    println!("cargo:rerun-if-changed=partitions-esp32.csv");

    if std::env::var("CARGO_CFG_TARGET_OS").as_deref() == Ok("espidf") {
        embuild::espidf::sysenv::output();
    }
}
