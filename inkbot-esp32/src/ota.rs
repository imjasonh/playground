//! OTA poll: fetch a signed GHCR firmware image and write the inactive slot.

use anyhow::{anyhow, bail, Context, Result};
use embedded_svc::http::client::Client;
use embedded_svc::http::Method;
use esp_idf_svc::http::client::{
    Configuration as HttpConfig, EspHttpConnection, FollowRedirectsPolicy,
};
use esp_idf_svc::nvs::{EspDefaultNvsPartition, EspNvs, NvsDefault};
use esp_idf_svc::ota::EspOta;
use serde::Deserialize;
use sha2::{Digest, Sha256};
use std::time::{Duration, Instant};

use crate::device_config::AppConfig;
use crate::https::{http_get, lock_or_poison, OtaDownloadGuard, ShortHttpsLock};
use crate::nvs_util::read_str;
use crate::trust::TrustConfig;
use inkbot_esp32::{
    check_ota_image, FirmwareConfig, OTA_CONFIG_MEDIA_TYPE, OTA_LAYER_MEDIA_TYPE, OTA_SLOT_BYTES,
};

const NVS_NAMESPACE: &str = "ota";
const NVS_LAST_DIGEST: &str = "last_digest";
const NVS_PENDING_DIGEST: &str = "pending_digest";
const NVS_DIGEST_BUF: usize = 96;
const BACKOFF_CAP: Duration = Duration::from_secs(3600);

const MAX_TOKEN: usize = 4 * 1024;
const MAX_MANIFEST: usize = 16 * 1024;
const MAX_CONFIG: usize = 8 * 1024;
const MAX_SIG_BUNDLE: usize = 128 * 1024;

pub enum PollOutcome {
    Skipped,
    NoChange,
    Updated(String),
}

pub struct OtaState {
    last_attempt: Instant,
    failures: u32,
    started: Instant,
}

impl OtaState {
    pub fn new() -> Self {
        Self {
            last_attempt: Instant::now(),
            failures: 0,
            started: Instant::now(),
        }
    }

    /// Poll GHCR when due. Skips the first 30 s so the panel can paint.
    pub fn tick(
        &mut self,
        nvs_partition: EspDefaultNvsPartition,
        cfg: &AppConfig,
        trust: &TrustConfig,
        short_https: &ShortHttpsLock,
    ) -> Result<PollOutcome> {
        if cfg.ota_poll_secs == 0 {
            return Ok(PollOutcome::Skipped);
        }
        if self.started.elapsed() < Duration::from_secs(30) {
            return Ok(PollOutcome::Skipped);
        }
        let interval = if self.failures > 0 {
            backoff(Duration::from_secs(cfg.ota_poll_secs), self.failures)
        } else {
            Duration::from_secs(cfg.ota_poll_secs)
        };
        if self.last_attempt.elapsed() < interval {
            return Ok(PollOutcome::Skipped);
        }
        self.last_attempt = Instant::now();

        let mut nvs = EspNvs::new(nvs_partition, NVS_NAMESPACE, true)
            .map_err(|e| anyhow!("open NVS {NVS_NAMESPACE}: {e:?}"))?;
        match poll_once(&mut nvs, cfg, trust, short_https) {
            Ok(PollOutcome::NoChange) => {
                self.failures = 0;
                Ok(PollOutcome::NoChange)
            }
            Ok(other) => Ok(other),
            Err(e) => {
                self.failures = self.failures.saturating_add(1);
                Err(e)
            }
        }
    }
}

fn backoff(base: Duration, failures: u32) -> Duration {
    let exp = failures.min(10);
    let multiplied = base.saturating_mul(1u32 << exp);
    multiplied.min(BACKOFF_CAP)
}

fn poll_once(
    nvs: &mut EspNvs<NvsDefault>,
    cfg: &AppConfig,
    trust: &TrustConfig,
    short_https: &ShortHttpsLock,
) -> Result<PollOutcome> {
    let (token, manifest, manifest_digest_hex) = {
        let _l = lock_or_poison(short_https);
        let token = fetch_anon_token(&cfg.ota_repo)?;
        let (manifest, mdig) = fetch_manifest(&cfg.ota_repo, &cfg.ota_tag, &token)?;
        (token, manifest, mdig)
    };

    if manifest.layers.len() != 1 {
        bail!(
            "firmware manifest has {} layers, expected exactly 1",
            manifest.layers.len()
        );
    }
    let layer = manifest
        .layers
        .into_iter()
        .next()
        .ok_or_else(|| anyhow!("manifest has no layers"))?;
    if layer.media_type != OTA_LAYER_MEDIA_TYPE {
        bail!("unexpected layer mediaType: {}", layer.media_type);
    }

    let last = read_digest(nvs).unwrap_or_default();
    if last == layer.digest {
        return Ok(PollOutcome::NoChange);
    }
    log::info!("ota: new digest {}, verifying", layer.digest);

    let fw_cfg = {
        let _l = lock_or_poison(short_https);
        fetch_firmware_config(&cfg.ota_repo, &manifest.config, &token)?
    };
    check_ota_image(&fw_cfg, layer.size).map_err(|e| anyhow!("{e}"))?;

    let bundle = {
        let _l = lock_or_poison(short_https);
        fetch_signature_bundle(&cfg.ota_repo, &manifest_digest_hex, &token)
            .context("fetch signature bundle")?
    };
    crate::sig::verify_bundle(&bundle, &manifest_digest_hex, trust)
        .context("verify signature bundle")?;

    {
        let _g = OtaDownloadGuard::enter();
        download_and_apply(&cfg.ota_repo, &layer, &token)?;
    }

    write_string(nvs, NVS_PENDING_DIGEST, &layer.digest)?;
    Ok(PollOutcome::Updated(layer.digest))
}

#[derive(Deserialize)]
struct Manifest {
    #[serde(default)]
    config: Option<Descriptor>,
    layers: Vec<Descriptor>,
}

#[derive(Deserialize)]
struct Descriptor {
    digest: String,
    size: u64,
    #[serde(rename = "mediaType")]
    media_type: String,
}

#[derive(Deserialize)]
struct TokenResponse {
    token: String,
}

fn repo_path(repo: &str) -> Result<&str> {
    repo.strip_prefix("ghcr.io/")
        .ok_or_else(|| anyhow!("only ghcr.io is supported (got {repo})"))
}

fn fetch_anon_token(repo: &str) -> Result<String> {
    let repo_path = repo_path(repo)?;
    let url = format!("https://ghcr.io/token?service=ghcr.io&scope=repository:{repo_path}:pull");
    let mut buf = Vec::with_capacity(1024);
    http_get(&url, &[], &mut buf, MAX_TOKEN)?;
    let resp: TokenResponse = serde_json::from_slice(&buf).context("parse token response JSON")?;
    Ok(resp.token)
}

fn fetch_manifest(repo: &str, tag: &str, token: &str) -> Result<(Manifest, String)> {
    let repo_path = repo_path(repo)?;
    let url = format!("https://ghcr.io/v2/{repo_path}/manifests/{tag}");
    let auth = format!("Bearer {token}");
    let mut buf = Vec::with_capacity(4096);
    http_get(
        &url,
        &[
            ("authorization", auth.as_str()),
            ("accept", "application/vnd.oci.image.manifest.v1+json"),
        ],
        &mut buf,
        MAX_MANIFEST,
    )?;
    let digest_hex = hex::encode(Sha256::digest(&buf));
    let m: Manifest = serde_json::from_slice(&buf)
        .with_context(|| format!("parse manifest JSON ({} bytes)", buf.len()))?;
    Ok((m, digest_hex))
}

fn fetch_firmware_config(
    repo: &str,
    config: &Option<Descriptor>,
    token: &str,
) -> Result<FirmwareConfig> {
    let desc = config
        .as_ref()
        .ok_or_else(|| anyhow!("firmware manifest has no config descriptor"))?;
    if desc.media_type != OTA_CONFIG_MEDIA_TYPE {
        bail!("unexpected config mediaType: {}", desc.media_type);
    }
    if desc.size > MAX_CONFIG as u64 {
        bail!("firmware config blob too large ({})", desc.size);
    }
    let repo_path = repo_path(repo)?;
    let url = format!("https://ghcr.io/v2/{repo_path}/blobs/{}", desc.digest);
    let auth = format!("Bearer {token}");
    let mut buf = Vec::with_capacity(desc.size as usize + 64);
    http_get(
        &url,
        &[
            ("authorization", auth.as_str()),
            ("accept", "application/json"),
        ],
        &mut buf,
        MAX_CONFIG,
    )
    .context("fetch firmware config blob")?;
    serde_json::from_slice(&buf).context("parse firmware config JSON")
}

fn fetch_signature_bundle(repo: &str, manifest_digest_hex: &str, token: &str) -> Result<Vec<u8>> {
    let repo_path = repo_path(repo)?;
    let auth = format!("Bearer {token}");
    let bundle_tag = format!("sha256-{manifest_digest_hex}");

    let url1 = format!("https://ghcr.io/v2/{repo_path}/manifests/{bundle_tag}");
    let mut buf1 = Vec::with_capacity(1024);
    http_get(
        &url1,
        &[
            ("authorization", auth.as_str()),
            (
                "accept",
                "application/vnd.oci.image.index.v1+json,application/vnd.oci.image.manifest.v1+json",
            ),
        ],
        &mut buf1,
        MAX_MANIFEST,
    )
    .context("fetch sig outer manifest/index")?;

    #[derive(Deserialize)]
    struct Index {
        manifests: Vec<IndexEntry>,
    }
    #[derive(Deserialize)]
    struct IndexEntry {
        digest: String,
    }
    let inner_digest = if let Ok(idx) = serde_json::from_slice::<Index>(&buf1) {
        if idx.manifests.len() != 1 {
            bail!(
                "sig index has {} manifests, expected exactly 1",
                idx.manifests.len()
            );
        }
        idx.manifests[0].digest.clone()
    } else {
        let m: Manifest =
            serde_json::from_slice(&buf1).context("sig outer is neither index nor manifest")?;
        return blob_for_sigstore_bundle(&m, repo_path, &auth);
    };

    let url2 = format!("https://ghcr.io/v2/{repo_path}/manifests/{inner_digest}");
    let mut buf2 = Vec::with_capacity(2048);
    http_get(
        &url2,
        &[
            ("authorization", auth.as_str()),
            ("accept", "application/vnd.oci.image.manifest.v1+json"),
        ],
        &mut buf2,
        MAX_MANIFEST,
    )
    .context("fetch sig inner manifest")?;
    let inner: Manifest = serde_json::from_slice(&buf2).context("parse sig inner manifest JSON")?;
    blob_for_sigstore_bundle(&inner, repo_path, &auth)
}

fn blob_for_sigstore_bundle(m: &Manifest, repo_path: &str, auth: &str) -> Result<Vec<u8>> {
    let layer = m
        .layers
        .iter()
        .find(|l| {
            l.media_type
                .starts_with("application/vnd.dev.sigstore.bundle.")
        })
        .ok_or_else(|| anyhow!("sig manifest has no Sigstore bundle layer"))?;
    if layer.size > MAX_SIG_BUNDLE as u64 {
        bail!("sig bundle too large ({})", layer.size);
    }
    let url = format!("https://ghcr.io/v2/{repo_path}/blobs/{}", layer.digest);
    let mut buf = Vec::with_capacity((layer.size as usize).saturating_add(256));
    http_get(
        &url,
        &[
            ("authorization", auth),
            ("accept", "application/octet-stream"),
        ],
        &mut buf,
        MAX_SIG_BUNDLE,
    )
    .context("fetch sig bundle blob")?;
    Ok(buf)
}

fn download_and_apply(repo: &str, layer: &Descriptor, token: &str) -> Result<()> {
    if layer.size == 0 || layer.size > OTA_SLOT_BYTES {
        bail!(
            "firmware layer size {} does not fit OTA slot ({OTA_SLOT_BYTES} bytes)",
            layer.size
        );
    }
    let repo_path = repo_path(repo)?;
    let url = format!("https://ghcr.io/v2/{repo_path}/blobs/{}", layer.digest);
    let auth = format!("Bearer {token}");

    let conn = EspHttpConnection::new(&HttpConfig {
        crt_bundle_attach: Some(esp_idf_svc::sys::esp_crt_bundle_attach),
        follow_redirects_policy: FollowRedirectsPolicy::FollowAll,
        timeout: Some(Duration::from_secs(120)),
        buffer_size: Some(4096),
        ..Default::default()
    })?;
    let mut client = Client::wrap(conn);
    let headers = [
        ("authorization", auth.as_str()),
        ("accept", "application/octet-stream"),
    ];
    let req = client.request(Method::Get, &url, &headers)?;
    let mut resp = req.submit()?;
    if resp.status() != 200 {
        bail!("blob GET {} -> {}", url, resp.status());
    }

    let mut ota = EspOta::new().context("EspOta::new")?;
    let mut update = ota.initiate_update().context("initiate OTA update")?;

    let expected_sha_hex = layer
        .digest
        .strip_prefix("sha256:")
        .ok_or_else(|| anyhow!("non-sha256 digest: {}", layer.digest))?;
    let mut hasher = Sha256::new();
    let mut buf = [0u8; 4096];
    let mut total: u64 = 0;
    let mut next_log = 256u64 * 1024;
    loop {
        let n = resp.read(&mut buf).context("read blob chunk")?;
        if n == 0 {
            break;
        }
        total += n as u64;
        if total > layer.size {
            update.abort().ok();
            bail!("blob larger than manifest size {}", layer.size);
        }
        update.write(&buf[..n]).context("OTA write")?;
        hasher.update(&buf[..n]);
        if total >= next_log {
            log::info!("ota: download progress {total}/{}", layer.size);
            next_log += 256 * 1024;
        }
    }
    if total != layer.size {
        update.abort().ok();
        bail!("blob size mismatch: got {total}, expected {}", layer.size);
    }
    let actual_sha_hex = hex::encode(hasher.finalize());
    if actual_sha_hex != expected_sha_hex {
        update.abort().ok();
        bail!("blob SHA mismatch: got {actual_sha_hex}, manifest says {expected_sha_hex}");
    }
    update
        .complete()
        .context("OTA complete (set boot partition)")?;
    Ok(())
}

fn read_digest(nvs: &EspNvs<NvsDefault>) -> Option<String> {
    read_str(nvs, NVS_NAMESPACE, NVS_LAST_DIGEST, NVS_DIGEST_BUF)
        .ok()
        .flatten()
}

fn write_string(nvs: &mut EspNvs<NvsDefault>, key: &str, value: &str) -> Result<()> {
    nvs.set_str(key, value)
        .with_context(|| format!("write NVS key {key}"))
}

pub fn is_pending_verify() -> bool {
    use esp_idf_svc::sys::*;
    unsafe {
        let part = esp_ota_get_running_partition();
        if part.is_null() {
            return false;
        }
        let mut state: esp_ota_img_states_t = 0;
        let err = esp_ota_get_state_partition(part, &mut state);
        if err != ESP_OK {
            log::warn!("ota: esp_ota_get_state_partition failed {err}");
            return false;
        }
        state == esp_ota_img_states_t_ESP_OTA_IMG_PENDING_VERIFY
    }
}

/// If this boot is not `PENDING_VERIFY` but `pending_digest` is still set,
/// the previous image rolled back. Record that digest as `last_digest` so
/// the next poll does not re-flash the same binary.
pub fn remember_rolled_back_digest(nvs_partition: EspDefaultNvsPartition) -> Result<()> {
    if is_pending_verify() {
        return Ok(());
    }
    persist_pending_as_last(nvs_partition)
}

fn persist_pending_as_last(nvs_partition: EspDefaultNvsPartition) -> Result<()> {
    let mut nvs =
        EspNvs::new(nvs_partition, NVS_NAMESPACE, true).context("open ota NVS namespace")?;
    if let Some(pending) = read_digest_pending(&nvs) {
        write_string(&mut nvs, NVS_LAST_DIGEST, &pending)?;
        let _ = nvs.remove(NVS_PENDING_DIGEST);
        log::info!("ota: recorded rejected digest {pending} (skip until GHCR changes)");
    }
    Ok(())
}

pub fn mark_valid_after_pending_verify_passed(nvs_partition: EspDefaultNvsPartition) -> Result<()> {
    use esp_idf_svc::sys::*;
    let err = unsafe { esp_ota_mark_app_valid_cancel_rollback() };
    if err != ESP_OK {
        bail!("esp_ota_mark_app_valid_cancel_rollback err={err}");
    }
    log::info!("ota: marked app valid, rollback cancelled");

    let mut nvs =
        EspNvs::new(nvs_partition, NVS_NAMESPACE, true).context("open ota NVS namespace")?;
    if let Some(pending) = read_digest_pending(&nvs) {
        write_string(&mut nvs, NVS_LAST_DIGEST, &pending)?;
        let _ = nvs.remove(NVS_PENDING_DIGEST);
        log::info!("ota: promoted pending -> last_digest {pending}");
    }
    Ok(())
}

/// Persist the pending digest as rejected, then ask the bootloader to
/// roll back. Does not return on success.
pub fn reject_pending_and_reboot(nvs_partition: EspDefaultNvsPartition) -> ! {
    if let Err(e) = persist_pending_as_last(nvs_partition) {
        log::error!("ota: persist rejected digest failed: {e:#}");
    }
    let err = unsafe { esp_idf_svc::sys::esp_ota_mark_app_invalid_rollback_and_reboot() };
    log::error!("ota: mark_invalid returned {err}; restarting");
    unsafe { esp_idf_svc::sys::esp_restart() }
}

fn read_digest_pending(nvs: &EspNvs<NvsDefault>) -> Option<String> {
    read_str(nvs, NVS_NAMESPACE, NVS_PENDING_DIGEST, NVS_DIGEST_BUF)
        .ok()
        .flatten()
}
