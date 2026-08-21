//! Build a binary NVS partition image from a `provisioning.toml` and
//! optionally flash it to the device.
//!
//! ESP-IDF's `nvs_partition_gen.py` (cloned under `.embuild/` by
//! `make build`) generates the binary format. This tool writes the CSV
//! that script expects, then shells out.

use anyhow::{anyhow, bail, Context, Result};
use clap::Parser;
use serde::Deserialize;
use std::path::{Path, PathBuf};
use std::process::Command;

#[derive(Parser)]
#[command(
    version,
    about = "Build + flash NVS partition image from provisioning.toml"
)]
struct Cli {
    /// Path to provisioning.toml.
    #[arg(long, default_value = "provisioning.toml")]
    config: PathBuf,

    /// Where to write the generated NVS .bin.
    #[arg(long, default_value = "target/nvs.bin")]
    out: PathBuf,

    /// NVS partition size in bytes. Must match `partitions.csv` (the `nvs`
    /// row's size column). Default matches the current 0x6000 (24 KB) NVS.
    #[arg(long, default_value_t = 0x6000)]
    nvs_size: u32,

    /// Offset in flash to write to. Must match `partitions.csv` nvs offset.
    #[arg(long, default_value = "0x9000")]
    nvs_offset: String,

    /// If true, also flash the generated image to the device via espflash.
    #[arg(long)]
    flash: bool,

    /// Serial port for flashing.
    #[arg(long, default_value = "/dev/cu.usbserial-0001")]
    port: String,

    /// Path to ESP-IDF's nvs_partition_gen.py. Defaults to the in-repo
    /// embuild copy that gets cloned by `make build`.
    #[arg(
        long,
        default_value = ".embuild/espressif/esp-idf/v5.2.2/components/nvs_flash/nvs_partition_generator/nvs_partition_gen.py"
    )]
    nvs_gen: PathBuf,

    /// Path to the python interpreter to run nvs_partition_gen.py with.
    /// Defaults to the embuild-bootstrapped 3.12 venv (matches what the
    /// firmware build uses; ensures script deps are present).
    #[arg(
        long,
        default_value = ".embuild/espressif/python_env/idf5.2_py3.12_env/bin/python"
    )]
    python: PathBuf,

    /// If true, only emit the NVS CSV and identities staging file; do
    /// NOT run nvs_partition_gen.py. Useful for CI parsing checks where
    /// the embuild artifacts aren't installed.
    #[arg(long)]
    dry_run: bool,
}

#[derive(Deserialize, Debug)]
struct ProvisioningConfig {
    wifi: WifiConfig,
    inkbot: InkbotConfig,
    trust: TrustConfig,
    /// Optional. If absent, the device boots with serial-only logging.
    gcp: Option<GcpConfig>,
    /// Optional. If absent, OTA uses compile-time defaults
    /// (`ghcr.io/imjasonh/playground/inkbot-esp32:latest`, 600 s).
    /// Each field is independently optional.
    ota: Option<OtaProvisioningConfig>,
}

#[derive(Deserialize, Debug)]
struct WifiConfig {
    ssid: String,
    pass: String,
}

#[derive(Deserialize, Debug)]
struct InkbotConfig {
    base_url: String,
    #[serde(default = "default_poll_secs")]
    poll_secs: u32,
    #[serde(default = "default_rotate_secs")]
    rotate_secs: u32,
    #[serde(default)]
    upload_secret: String,
    #[serde(default = "default_status_secs")]
    status_secs: u32,
    /// Written as NVS key `dhcp_renew` (15-character limit).
    #[serde(default = "default_dhcp_renew_secs")]
    dhcp_renew_secs: u32,
}

fn default_poll_secs() -> u32 {
    60
}

fn default_rotate_secs() -> u32 {
    1800
}

fn default_status_secs() -> u32 {
    900
}

fn default_dhcp_renew_secs() -> u32 {
    21600
}

#[derive(Deserialize, Debug)]
struct TrustConfig {
    identities: Vec<TrustedIdentity>,
    fulcio_root_pem: PathBuf,
    fulcio_intermediate_pem: PathBuf,
}

#[derive(Deserialize, serde::Serialize, Debug)]
struct TrustedIdentity {
    identity: String,
    issuer: String,
}

#[derive(Deserialize, Debug)]
struct GcpConfig {
    project_id: String,
    sa_email: String,
    sa_key_id: String,
    /// Path to a PKCS#8 PEM containing the service account's RSA
    /// private key. Resolved relative to provisioning.toml's directory.
    sa_key_pem: PathBuf,
    /// "trace" / "debug" / "info" / "warn" / "error". Default "info".
    /// Determines the minimum severity that gets shipped to Cloud
    /// Logging (everything still goes to serial).
    #[serde(default = "default_severity")]
    min_severity: String,
    /// Seconds between Cloud Monitoring metric snapshots. Default 300
    /// (5 min). 0 = metrics disabled (cloud log still runs).
    #[serde(default = "default_metrics_interval")]
    metrics_interval_secs: u32,
}

fn default_severity() -> String {
    "info".to_string()
}

fn default_metrics_interval() -> u32 {
    300
}

#[derive(Deserialize, Debug, Default)]
struct OtaProvisioningConfig {
    /// Which firmware image to pull: `inkbot-esp32` or `maze-esp32`.
    /// Default `inkbot-esp32`. Written as NVS `ota/app`.
    app: Option<String>,
    /// Override `ghcr.io/<owner>/<name>` repo. Default is
    /// `ghcr.io/imjasonh/playground/{app}`.
    repo: Option<String>,
    /// Override the image tag. Default `latest`.
    tag: Option<String>,
    /// Override the OTA poll interval in seconds. `0` disables OTA.
    poll_secs: Option<u32>,
}

const KNOWN_OTA_APPS: &[&str] = &["inkbot-esp32", "maze-esp32"];

/// Emit a loud warning if the resolved service-account key path lives
/// inside the repo. It's gitignored by convention but we'd rather
/// flag it explicitly — putting the SA key elsewhere (a `~/.config`
/// location with restricted perms) is the safer default.
fn warn_if_in_repo(sa_key: &Path, repo_dir: &Path) {
    let key = match sa_key.canonicalize() {
        Ok(p) => p,
        // If canonicalize fails the file probably doesn't exist yet;
        // nvs_partition_gen.py will fail loudly on its own.
        Err(_) => return,
    };
    let repo = match repo_dir.canonicalize() {
        Ok(p) => p,
        Err(_) => return,
    };
    if key.starts_with(&repo) {
        tracing::warn!(
            path = %key.display(),
            "sa_key_pem lives inside the repo — keep it gitignored, chmod 600, and consider moving it outside the worktree",
        );
    }
}

fn severity_to_u8(s: &str) -> Result<u8> {
    match s.to_ascii_lowercase().as_str() {
        "trace" => Ok(0),
        "debug" => Ok(1),
        "info" => Ok(2),
        "warn" => Ok(3),
        "error" => Ok(4),
        other => Err(anyhow!("unknown min_severity: {other}")),
    }
}

fn main() -> Result<()> {
    tracing_subscriber::fmt()
        .with_writer(std::io::stderr)
        .with_env_filter(
            tracing_subscriber::EnvFilter::try_from_default_env()
                .unwrap_or_else(|_| tracing_subscriber::EnvFilter::new("info")),
        )
        .init();

    let args = Cli::parse();

    let toml_str = std::fs::read_to_string(&args.config)
        .with_context(|| format!("read {}", args.config.display()))?;
    let mut cfg: ProvisioningConfig =
        toml::from_str(&toml_str).context("parse provisioning.toml")?;

    // Resolve PEM paths relative to the directory of provisioning.toml,
    // so the user can write `fulcio_root_pem = "trust/fulcio_root.pem"`
    // and it works regardless of where the tool is invoked from.
    let config_dir = args
        .config
        .canonicalize()
        .with_context(|| format!("canonicalize {}", args.config.display()))?
        .parent()
        .ok_or_else(|| anyhow!("no parent dir for {}", args.config.display()))?
        .to_path_buf();
    if cfg.trust.fulcio_root_pem.is_relative() {
        cfg.trust.fulcio_root_pem = config_dir.join(&cfg.trust.fulcio_root_pem);
    }
    if cfg.trust.fulcio_intermediate_pem.is_relative() {
        cfg.trust.fulcio_intermediate_pem = config_dir.join(&cfg.trust.fulcio_intermediate_pem);
    }
    if let Some(gcp) = cfg.gcp.as_mut() {
        if gcp.sa_key_pem.is_relative() {
            gcp.sa_key_pem = config_dir.join(&gcp.sa_key_pem);
        }
        // Validate severity now (before writing CSV) so a typo fails
        // fast with a clear error.
        severity_to_u8(&gcp.min_severity)?;
        warn_if_in_repo(&gcp.sa_key_pem, &config_dir);
    }

    if cfg.inkbot.base_url.is_empty() {
        bail!("inkbot.base_url must not be empty");
    }
    if !cfg.inkbot.base_url.starts_with("https://") {
        bail!("inkbot.base_url must start with https://");
    }
    if cfg.wifi.ssid.len() > 32 {
        bail!("wifi.ssid is longer than 32 bytes");
    }
    if cfg.wifi.pass.len() > 64 {
        bail!("wifi.pass is longer than 64 bytes");
    }
    if cfg.trust.identities.is_empty() {
        bail!("trust.identities must contain at least one entry");
    }
    if let Some(ota) = &cfg.ota {
        if let Some(app) = &ota.app {
            if !KNOWN_OTA_APPS.contains(&app.as_str()) {
                bail!(
                    "ota.app={app} is unknown; must be one of {}",
                    KNOWN_OTA_APPS.join(", ")
                );
            }
        }
    }

    tracing::info!(
        identities = cfg.trust.identities.len(),
        ssid = cfg.wifi.ssid,
        base_url = cfg.inkbot.base_url,
        gcp = cfg.gcp.is_some(),
        ota_app = cfg.ota.as_ref().and_then(|o| o.app.as_deref()),
        "loaded provisioning config",
    );

    if !args.dry_run && !args.nvs_gen.exists() {
        bail!(
            "{} not found — run `make build` once so embuild clones ESP-IDF",
            args.nvs_gen.display()
        );
    }

    // Stage the trust/identities JSON to a temp file (nvs_partition_gen
    // reads `binary` values from disk, not stdin).
    let target_dir = args
        .out
        .parent()
        .unwrap_or_else(|| Path::new("target"))
        .to_path_buf();
    std::fs::create_dir_all(&target_dir)
        .with_context(|| format!("create {}", target_dir.display()))?;
    let identities_json_path = target_dir.join("nvs-identities.json");
    let identities_json =
        serde_json::to_vec(&cfg.trust.identities).context("serialize identities")?;
    std::fs::write(&identities_json_path, &identities_json)
        .with_context(|| format!("write {}", identities_json_path.display()))?;
    tracing::info!(
        path = %identities_json_path.display(),
        bytes = identities_json.len(),
        "wrote identities JSON",
    );

    let csv_path = target_dir.join("nvs.csv");
    write_csv(&csv_path, &cfg, &identities_json_path).context("write NVS CSV")?;
    tracing::info!(path = %csv_path.display(), "wrote NVS CSV");

    if args.dry_run {
        tracing::info!(
            csv = %csv_path.display(),
            "dry-run: skipping nvs_partition_gen.py and flash",
        );
        let _ = std::fs::remove_file(&identities_json_path);
        return Ok(());
    }

    let status = Command::new(&args.python)
        .arg(&args.nvs_gen)
        .arg("generate")
        .arg(&csv_path)
        .arg(&args.out)
        .arg(args.nvs_size.to_string())
        .status()
        .with_context(|| format!("run {}", args.nvs_gen.display()))?;
    if !status.success() {
        bail!("nvs_partition_gen.py failed: {status}");
    }
    let bin_size = std::fs::metadata(&args.out)?.len();
    tracing::info!(
        path = %args.out.display(),
        bytes = bin_size,
        "generated NVS partition image",
    );
    let _ = std::fs::remove_file(&identities_json_path);

    if args.flash {
        tracing::info!(
            port = %args.port,
            offset = %args.nvs_offset,
            "flashing NVS image",
        );
        let status = Command::new("espflash")
            .args([
                "write-bin",
                "--port",
                &args.port,
                &args.nvs_offset,
                args.out.to_str().context("non-utf8 out path")?,
            ])
            .status()
            .context("run espflash write-bin")?;
        if !status.success() {
            bail!("espflash write-bin failed: {status}");
        }
        tracing::info!("NVS partition flashed; reboot the device to pick it up");
    } else {
        tracing::info!(
            "build complete; pass --flash to write to the device, or run `make provision`",
        );
    }

    Ok(())
}

fn write_csv(path: &Path, cfg: &ProvisioningConfig, identities_path: &Path) -> Result<()> {
    let mut wtr = csv::WriterBuilder::new()
        .quote_style(csv::QuoteStyle::Necessary)
        .from_path(path)?;
    wtr.write_record(["key", "type", "encoding", "value"])?;

    wtr.write_record(["wifi", "namespace", "", ""])?;
    wtr.write_record(["ssid", "data", "string", &cfg.wifi.ssid])?;
    wtr.write_record(["pass", "data", "string", &cfg.wifi.pass])?;

    wtr.write_record(["inkbot", "namespace", "", ""])?;
    wtr.write_record(["base_url", "data", "string", &cfg.inkbot.base_url])?;
    wtr.write_record([
        "poll_secs",
        "data",
        "u32",
        &cfg.inkbot.poll_secs.to_string(),
    ])?;
    wtr.write_record([
        "rotate_secs",
        "data",
        "u32",
        &cfg.inkbot.rotate_secs.to_string(),
    ])?;
    wtr.write_record(["upload_secret", "data", "string", &cfg.inkbot.upload_secret])?;
    wtr.write_record([
        "status_secs",
        "data",
        "u32",
        &cfg.inkbot.status_secs.to_string(),
    ])?;
    // NVS keys are limited to 15 characters.
    wtr.write_record([
        "dhcp_renew",
        "data",
        "u32",
        &cfg.inkbot.dhcp_renew_secs.to_string(),
    ])?;

    wtr.write_record(["trust", "namespace", "", ""])?;
    wtr.write_record([
        "identities",
        "file",
        "binary",
        identities_path
            .to_str()
            .ok_or_else(|| anyhow!("identities path not UTF-8"))?,
    ])?;
    wtr.write_record([
        "fulcio_root",
        "file",
        "binary",
        cfg.trust
            .fulcio_root_pem
            .to_str()
            .ok_or_else(|| anyhow!("fulcio_root_pem path not UTF-8"))?,
    ])?;
    wtr.write_record([
        "fulcio_inter",
        "file",
        "binary",
        cfg.trust
            .fulcio_intermediate_pem
            .to_str()
            .ok_or_else(|| anyhow!("fulcio_intermediate_pem path not UTF-8"))?,
    ])?;

    if let Some(gcp) = &cfg.gcp {
        wtr.write_record(["gcp", "namespace", "", ""])?;
        wtr.write_record(["project_id", "data", "string", &gcp.project_id])?;
        wtr.write_record(["sa_email", "data", "string", &gcp.sa_email])?;
        wtr.write_record(["sa_key_id", "data", "string", &gcp.sa_key_id])?;
        wtr.write_record([
            "sa_key_pem",
            "file",
            "binary",
            gcp.sa_key_pem
                .to_str()
                .ok_or_else(|| anyhow!("sa_key_pem path not UTF-8"))?,
        ])?;
        let severity = severity_to_u8(&gcp.min_severity)?;
        wtr.write_record(["min_severity", "data", "u8", &severity.to_string()])?;
        wtr.write_record([
            "metric_intvl",
            "data",
            "u32",
            &gcp.metrics_interval_secs.to_string(),
        ])?;
    }

    if let Some(ota) = &cfg.ota {
        wtr.write_record(["ota", "namespace", "", ""])?;
        if let Some(app) = &ota.app {
            wtr.write_record(["app", "data", "string", app])?;
        }
        if let Some(repo) = &ota.repo {
            wtr.write_record(["repo", "data", "string", repo])?;
        }
        if let Some(tag) = &ota.tag {
            wtr.write_record(["tag", "data", "string", tag])?;
        }
        if let Some(poll_secs) = ota.poll_secs {
            wtr.write_record(["poll_secs", "data", "u32", &poll_secs.to_string()])?;
        }
    }

    wtr.flush()?;
    Ok(())
}
