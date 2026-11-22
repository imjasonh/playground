//! Wire embuild's ESP-IDF sysenv on device builds.

fn main() {
    println!("cargo:rerun-if-changed=partitions.csv");
    println!("cargo:rerun-if-changed=sdkconfig.defaults");
    println!("cargo:rerun-if-changed=sdkconfig.defaults.in");

    println!("cargo:rerun-if-env-changed=GITHUB_SHA");
    let git_sha = std::env::var("GITHUB_SHA")
        .ok()
        .filter(|s| s.len() == 40 && s.bytes().all(|b| b.is_ascii_hexdigit()))
        .or_else(|| {
            std::process::Command::new("git")
                .args(["rev-parse", "HEAD"])
                .output()
                .ok()
                .filter(|o| o.status.success())
                .and_then(|o| String::from_utf8(o.stdout).ok())
                .map(|s| s.trim().to_ascii_lowercase())
                .filter(|s| s.len() == 40 && s.bytes().all(|b| b.is_ascii_hexdigit()))
        })
        .unwrap_or_default();
    println!(
        "cargo:rustc-env=XIAO_GIT_SHA={}",
        git_sha.to_ascii_lowercase()
    );

    if std::env::var("CARGO_CFG_TARGET_OS").as_deref() == Ok("espidf") {
        embuild::espidf::sysenv::output();
    }
}
