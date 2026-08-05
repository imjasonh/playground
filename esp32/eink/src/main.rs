use std::time::Duration;

use anyhow::{Result, anyhow};
use esp_idf_svc::{
    eventloop::EspSystemEventLoop,
    hal::peripherals::Peripherals,
    nvs::{EspDefaultNvsPartition, EspNvs},
    wifi::{AuthMethod, BlockingWifi, ClientConfiguration, Configuration as WifiConfig, EspWifi},
};

use esp32_blinky::{net_coord, nvs_util, ota, trust};
use esp32_eink::terminal::TerminalBuffer;

mod display;
mod ssh_client;
mod ssh_config;

const FW_VERSION: &str = env!("GIT_SHA");
const TRUST_MAINTENANCE_EPOCH: &str = include_str!("../../trust/maintenance-epoch.txt");
const EINK_OTA_REPO: &str = "ghcr.io/imjasonh/esp32-eink";
const WIFI_NAMESPACE: &str = "wifi";
const SSH_THREAD_STACK_SIZE: usize = 32 * 1024;

fn main() -> Result<()> {
    esp_idf_svc::sys::link_patches();
    esp_idf_svc::log::EspLogger::initialize_default();
    install_panic_restart_hook();
    tracing::info!(
        version = FW_VERSION,
        trust_epoch = TRUST_MAINTENANCE_EPOCH.trim(),
        "eink: booting"
    );

    let nvs = EspDefaultNvsPartition::take()?;
    let (ssid, pass) = read_wifi_creds(nvs.clone())?
        .ok_or_else(|| anyhow!("wifi/ssid or wifi/pass missing; run `make provision`"))?;
    let ota_trust = trust::TrustConfig::load(nvs.clone())?
        .ok_or_else(|| anyhow!("Sigstore trust configuration missing; run `make provision`"))?;
    let ssh_config = ssh_config::SshConfig::load(nvs.clone())?;
    let pending_verify = ota::is_pending_verify();

    let peripherals = Peripherals::take()?;
    let sysloop = EspSystemEventLoop::take()?;
    let mut wifi = BlockingWifi::wrap(
        EspWifi::new(peripherals.modem, sysloop.clone(), Some(nvs.clone()))?,
        sysloop,
    )?;
    connect_wifi(&mut wifi, &ssid, &pass)?;
    let ip = wifi.wifi().sta_netif().get_ip_info()?.ip;
    tracing::info!(%ip, "wifi connected");

    // Generate only after WiFi starts so ESP-IDF's hardware RNG has its
    // strongest entropy source enabled.
    let client_key = ssh_config::load_or_generate_key(nvs.clone())?;
    let authorized_key = ssh_config::authorized_key(&client_key)?;
    let fingerprint = ssh_config::fingerprint(&client_key)?;
    tracing::info!(%fingerprint, "ssh: device key ready");
    // This is intentionally copyable from the USB monitor for manual
    // enrollment in the server's authorized_keys.
    tracing::info!("ssh: authorize this key:\n{}", authorized_key);

    let mut terminal = TerminalBuffer::new();
    terminal.write_line("ESP32 e-ink SSH client");
    terminal.write_line(&format!("IP: {ip}"));
    terminal.write_line(&format!("Device key: {fingerprint}"));
    terminal.write_line("Add this key to the server's authorized_keys:");
    terminal.feed(authorized_key.as_bytes());
    terminal.feed(b"\r\n\r\n");

    match ssh_config {
        Some(config) => {
            run_ssh_on_worker(&config, &client_key, &mut terminal)?;
        }
        None => {
            terminal.write_line("SSH is not provisioned.");
            terminal.write_line("Fill in [ssh] in provisioning.toml and re-run:");
            terminal.write_line("  make provision");
        }
    }

    let display_result = display::show(
        &terminal,
        peripherals.spi2,
        peripherals.pins.gpio13,
        peripherals.pins.gpio14,
        peripherals.pins.gpio15,
        peripherals.pins.gpio25,
        peripherals.pins.gpio27,
        peripherals.pins.gpio26,
    );
    if let Err(error) = display_result {
        tracing::error!(error = %format!("{error:#}"), "eink: display refresh failed");
        if pending_verify {
            tracing::error!("ota: display bringup failed; rebooting for rollback");
            std::thread::sleep(Duration::from_secs(2));
            unsafe { esp_idf_svc::sys::esp_restart() };
        }
        return Err(error);
    }

    if pending_verify {
        ota::mark_valid_after_pending_verify_passed(nvs.clone())?;
        tracing::info!("ota: WiFi + display bringup passed; image marked valid");
    }

    let short_https = net_coord::new_short_https_lock();
    std::thread::Builder::new()
        .name("signed-ota".into())
        .stack_size(48 * 1024)
        .spawn(move || {
            ota::run(
                nvs,
                FW_VERSION,
                ota_trust,
                EINK_OTA_REPO,
                "eink",
                "esp32",
                Some(short_https),
            )
        })
        .expect("spawn signed OTA thread");

    tracing::info!("eink: panel asleep; signed OTA loop running");
    loop {
        std::thread::sleep(Duration::from_secs(3600));
    }
}

fn run_ssh_on_worker(
    config: &ssh_config::SshConfig,
    client_key: &sunset::SignKey,
    terminal: &mut TerminalBuffer,
) -> Result<()> {
    // Sunset's borrowed packet buffers, network buffer, and channel buffer
    // total roughly 10 KiB before its protocol state and call frames. Keep
    // them off the 10 KiB ESP-IDF main task stack. This scoped worker is
    // joined before the 48 KiB display framebuffer is allocated, and OTA
    // starts only after the display refresh, so the large allocations do not
    // overlap.
    std::thread::scope(|scope| {
        let worker = std::thread::Builder::new()
            .name("ssh-client".into())
            .stack_size(SSH_THREAD_STACK_SIZE)
            .spawn_scoped(scope, || {
                tracing::info!(
                    host = %config.host,
                    port = config.port,
                    username = %config.username,
                    "ssh: connecting",
                );
                match ssh_client::connect_display_disconnect(config, client_key, terminal) {
                    Ok(()) => {
                        terminal.feed(b"\r\n");
                        terminal.write_line("Disconnected.");
                        tracing::info!("ssh: display command completed");
                    }
                    Err(error) => {
                        tracing::error!(error = %format!("{error:#}"), "ssh session failed");
                        terminal.feed(b"\r\n");
                        terminal.write_line("SSH ERROR:");
                        terminal.write_line(&format!("{error:#}"));
                    }
                }
            })
            .map_err(|error| anyhow!("spawn 32 KiB SSH worker: {error}"))?;

        worker
            .join()
            .map_err(|_| anyhow!("SSH worker panicked before producing display output"))
    })
}

fn read_wifi_creds(partition: EspDefaultNvsPartition) -> Result<Option<(String, String)>> {
    let nvs = EspNvs::new(partition, WIFI_NAMESPACE, false)
        .map_err(|error| anyhow!("open NVS namespace {WIFI_NAMESPACE}: {error:?}"))?;
    let ssid = nvs_util::read_str(&nvs, WIFI_NAMESPACE, "ssid", 64)?;
    let pass = nvs_util::read_str(&nvs, WIFI_NAMESPACE, "pass", 96)?;
    Ok(match (ssid, pass) {
        (Some(ssid), Some(pass)) => Some((ssid, pass)),
        _ => None,
    })
}

fn connect_wifi(wifi: &mut BlockingWifi<EspWifi<'static>>, ssid: &str, pass: &str) -> Result<()> {
    let auth_method = if pass.is_empty() {
        AuthMethod::None
    } else {
        AuthMethod::WPA2Personal
    };
    wifi.set_configuration(&WifiConfig::Client(ClientConfiguration {
        ssid: ssid
            .try_into()
            .map_err(|_| anyhow!("SSID exceeds 32 bytes"))?,
        password: pass
            .try_into()
            .map_err(|_| anyhow!("WiFi password exceeds 64 bytes"))?,
        auth_method,
        ..Default::default()
    }))?;
    wifi.start()?;
    wifi.connect()?;
    wifi.wait_netif_up()?;
    Ok(())
}

fn install_panic_restart_hook() {
    let previous = std::panic::take_hook();
    std::panic::set_hook(Box::new(move |info| {
        previous(info);
        std::thread::sleep(Duration::from_millis(500));
        unsafe { esp_idf_svc::sys::esp_restart() };
    }));
}
