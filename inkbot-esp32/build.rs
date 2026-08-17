//! Embed Wi-Fi / Worker settings from `config.toml` and (on esp-idf targets)
//! wire embuild's ESP-IDF sysenv.

use std::env;
use std::fs;
use std::path::PathBuf;

fn main() {
    println!("cargo:rerun-if-changed=config.toml");
    println!("cargo:rerun-if-changed=config.toml.example");
    println!("cargo:rerun-if-changed=sdkconfig.defaults");

    generate_config();

    // Build.rs always compiles for the host; CARGO_CFG_TARGET_OS reflects
    // the crate target. Only wire ESP-IDF link flags when cross-compiling.
    if env::var("CARGO_CFG_TARGET_OS").as_deref() == Ok("espidf") {
        embuild::espidf::sysenv::output();
    }
}

fn generate_config() {
    let manifest = PathBuf::from(env::var("CARGO_MANIFEST_DIR").unwrap());
    let path = if manifest.join("config.toml").is_file() {
        manifest.join("config.toml")
    } else {
        // Host tests / first clone: fall back to the example so the crate
        // still compiles. Device flashes should copy config.toml.example.
        manifest.join("config.toml.example")
    };

    let raw = fs::read_to_string(&path).unwrap_or_else(|e| {
        panic!("failed to read {}: {e}", path.display());
    });
    let value: toml::Value = toml::from_str(&raw).unwrap_or_else(|e| {
        panic!("invalid {}: {e}", path.display());
    });

    let wifi = value.get("wifi").expect("config missing [wifi]");
    let inkbot = value.get("inkbot").expect("config missing [inkbot]");

    let ssid = wifi
        .get("ssid")
        .and_then(|v| v.as_str())
        .expect("wifi.ssid");
    let pass = wifi
        .get("pass")
        .and_then(|v| v.as_str())
        .expect("wifi.pass");
    let base_url = inkbot
        .get("base_url")
        .and_then(|v| v.as_str())
        .expect("inkbot.base_url");
    let poll_secs = inkbot
        .get("poll_secs")
        .and_then(|v| v.as_integer())
        .unwrap_or(60) as u64;
    let rotate_secs = inkbot
        .get("rotate_secs")
        .and_then(|v| v.as_integer())
        .unwrap_or(1800) as u64;
    let upload_secret = inkbot
        .get("upload_secret")
        .and_then(|v| v.as_str())
        .unwrap_or("");
    let status_secs = inkbot
        .get("status_secs")
        .and_then(|v| v.as_integer())
        .unwrap_or(900) as u64;
    let dhcp_renew_secs = inkbot
        .get("dhcp_renew_secs")
        .and_then(|v| v.as_integer())
        .unwrap_or(21600) as u64;

    let out = PathBuf::from(env::var("OUT_DIR").unwrap()).join("config_gen.rs");
    fs::write(
        &out,
        format!(
            "pub const WIFI_SSID: &str = {ssid:?};\n\
             pub const WIFI_PASS: &str = {pass:?};\n\
             pub const INKBOT_BASE_URL: &str = {base_url:?};\n\
             pub const POLL_SECS: u64 = {poll_secs};\n\
             pub const ROTATE_SECS: u64 = {rotate_secs};\n\
             pub const INKBOT_UPLOAD_SECRET: &str = {upload_secret:?};\n\
             pub const STATUS_SECS: u64 = {status_secs};\n\
             pub const DHCP_RENEW_SECS: u64 = {dhcp_renew_secs};\n"
        ),
    )
    .expect("write config_gen.rs");
}
