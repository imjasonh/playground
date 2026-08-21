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
use std::collections::HashMap;
use std::time::{Duration, Instant};

use crate::device_config::AppConfig;
use crate::https::{http_get, lock_or_poison, OtaDownloadGuard, ShortHttpsLock};
use crate::ota_slot::{self, NVS_NAMESPACE};
use crate::trust::TrustConfig;
use inkbot_esp32::{
    check_ota_image, cosign_signature_tags, layer_already_installed, FirmwareConfig,
    COSIGN_SIMPLE_SIGNING_MEDIA_TYPE, OTA_CONFIG_MEDIA_TYPE, OTA_LAYER_MEDIA_TYPE, OTA_SLOT_BYTES,
    SIGSTORE_BUNDLE_MEDIA_TYPE_PREFIX,
};

pub use crate::ota_slot::{
    is_pending_verify, mark_valid_after_pending_verify_passed, reject_pending_and_reboot,
    remember_rolled_back_digest,
};

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

    let last = ota_slot::read_last_digest(nvs).unwrap_or_default();
    let running = running_slot_digest(layer.size);
    if layer_already_installed(&layer.digest, &last, running.as_deref()) {
        if last != layer.digest {
            ota_slot::write_last_digest(nvs, &layer.digest)?;
        }
        return Ok(PollOutcome::NoChange);
    }
    log::info!("ota: new digest {}, verifying", layer.digest);

    let fw_cfg = {
        let _l = lock_or_poison(short_https);
        fetch_firmware_config(&cfg.ota_repo, &manifest.config, &token)?
    };
    check_ota_image(&fw_cfg, layer.size, &cfg.ota_app).map_err(|e| anyhow!("{e}"))?;

    {
        let _l = lock_or_poison(short_https);
        verify_ghcr_signature(&cfg.ota_repo, &manifest_digest_hex, &token, trust)
            .context("verify signature")?;
    }

    {
        let _g = OtaDownloadGuard::enter();
        download_and_apply(&cfg.ota_repo, &layer, &token)?;
    }

    ota_slot::write_pending_digest(nvs, &layer.digest)?;
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
    #[serde(default)]
    annotations: HashMap<String, String>,
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

const COSIGN_CERT_ANNOTATION: &str = "dev.sigstore.cosign/certificate";
const COSIGN_SIG_ANNOTATION: &str = "dev.cosignproject.cosign/signature";

fn verify_ghcr_signature(
    repo: &str,
    manifest_digest_hex: &str,
    token: &str,
    trust: &TrustConfig,
) -> Result<()> {
    let repo_path = repo_path(repo)?;
    let auth = format!("Bearer {token}");
    let buf1 = fetch_sig_outer(repo_path, manifest_digest_hex, &auth)?;

    #[derive(Deserialize)]
    struct Index {
        manifests: Vec<IndexEntry>,
    }
    #[derive(Deserialize)]
    struct IndexEntry {
        digest: String,
    }
    let manifest = if let Ok(idx) = serde_json::from_slice::<Index>(&buf1) {
        if idx.manifests.len() != 1 {
            bail!(
                "sig index has {} manifests, expected exactly 1",
                idx.manifests.len()
            );
        }
        let url2 = format!(
            "https://ghcr.io/v2/{repo_path}/manifests/{}",
            idx.manifests[0].digest
        );
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
        serde_json::from_slice(&buf2).context("parse sig inner manifest JSON")?
    } else {
        serde_json::from_slice(&buf1).context("sig outer is neither index nor manifest")?
    };
    verify_sig_layers(&manifest, repo_path, &auth, manifest_digest_hex, trust)
}

fn fetch_sig_outer(repo_path: &str, manifest_digest_hex: &str, auth: &str) -> Result<Vec<u8>> {
    let mut last_err = None;
    for tag in cosign_signature_tags(manifest_digest_hex) {
        let url = format!("https://ghcr.io/v2/{repo_path}/manifests/{tag}");
        let mut buf = Vec::with_capacity(1024);
        match http_get(
            &url,
            &[
                ("authorization", auth),
                (
                    "accept",
                    "application/vnd.oci.image.index.v1+json,application/vnd.oci.image.manifest.v1+json",
                ),
            ],
            &mut buf,
            MAX_MANIFEST,
        ) {
            Ok(()) => return Ok(buf),
            Err(e) if format!("{e:#}").contains(" -> 404") => last_err = Some(e),
            Err(e) => return Err(e).context("fetch sig outer manifest/index"),
        }
    }
    Err(last_err.unwrap_or_else(|| anyhow!("no Cosign signature tag")))
        .context("fetch sig outer manifest/index (tried sha256-<digest>.sig then sha256-<digest>)")
}

fn verify_sig_layers(
    m: &Manifest,
    repo_path: &str,
    auth: &str,
    manifest_digest_hex: &str,
    trust: &TrustConfig,
) -> Result<()> {
    if let Some(layer) = m
        .layers
        .iter()
        .find(|l| l.media_type.starts_with(SIGSTORE_BUNDLE_MEDIA_TYPE_PREFIX))
    {
        let bundle = fetch_layer_blob(layer, repo_path, auth, MAX_SIG_BUNDLE)
            .context("fetch sig bundle blob")?;
        return crate::sig::verify_bundle(&bundle, manifest_digest_hex, trust);
    }
    if let Some(layer) = m
        .layers
        .iter()
        .find(|l| l.media_type == COSIGN_SIMPLE_SIGNING_MEDIA_TYPE)
    {
        let payload = fetch_layer_blob(layer, repo_path, auth, MAX_SIG_BUNDLE)
            .context("fetch Cosign simple-signing payload")?;
        let cert = layer
            .annotations
            .get(COSIGN_CERT_ANNOTATION)
            .ok_or_else(|| anyhow!("Cosign layer missing {COSIGN_CERT_ANNOTATION}"))?;
        let sig = layer
            .annotations
            .get(COSIGN_SIG_ANNOTATION)
            .ok_or_else(|| anyhow!("Cosign layer missing {COSIGN_SIG_ANNOTATION}"))?;
        return crate::sig::verify_cosign_simple(
            &payload,
            cert.as_bytes(),
            sig,
            manifest_digest_hex,
            trust,
        );
    }
    bail!("sig manifest has no Sigstore bundle or Cosign simple-signing layer")
}

fn fetch_layer_blob(
    layer: &Descriptor,
    repo_path: &str,
    auth: &str,
    max_bytes: usize,
) -> Result<Vec<u8>> {
    if layer.size > max_bytes as u64 {
        bail!("sig blob too large ({})", layer.size);
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
        max_bytes,
    )?;
    Ok(buf)
}

/// GHCR blob GETs 307 to pkg-containers; those responses have fat headers.
const BLOB_HEADER_BUF: usize = 16 * 1024;
const BLOB_REDIRECTS: u8 = 5;

fn blob_http_config() -> HttpConfig {
    HttpConfig {
        crt_bundle_attach: Some(esp_idf_svc::sys::esp_crt_bundle_attach),
        follow_redirects_policy: FollowRedirectsPolicy::FollowNone,
        timeout: Some(Duration::from_secs(120)),
        buffer_size: Some(BLOB_HEADER_BUF),
        buffer_size_tx: Some(2048),
        ..Default::default()
    }
}

fn is_http_redirect(status: u16) -> bool {
    matches!(status, 301 | 302 | 303 | 307 | 308)
}

/// SHA-256 of the running slot's first `len` bytes, as `sha256:<hex>`.
///
/// USB `make flash` writes the same app image GHCR stores as the layer, so
/// this matches `layer.digest` when `:latest` is already on the board even
/// if NVS `last_digest` was never set.
fn running_slot_digest(len: u64) -> Option<String> {
    use esp_idf_svc::sys::{esp_ota_get_running_partition, esp_partition_read, ESP_OK};
    unsafe {
        let part = esp_ota_get_running_partition();
        if part.is_null() {
            return None;
        }
        let part_size = (*part).size as u64;
        if len == 0 || len > part_size {
            return None;
        }
        let mut hasher = Sha256::new();
        let mut buf = [0u8; 4096];
        let total = len as usize;
        let mut off = 0usize;
        while off < total {
            let n = (total - off).min(buf.len());
            let err = esp_partition_read(part, off, buf.as_mut_ptr().cast(), n);
            if err != ESP_OK {
                log::warn!("ota: running slot read failed {err} at {off}");
                return None;
            }
            hasher.update(&buf[..n]);
            off += n;
        }
        Some(format!("sha256:{}", hex::encode(hasher.finalize())))
    }
}

fn download_and_apply(repo: &str, layer: &Descriptor, token: &str) -> Result<()> {
    use embedded_svc::io::Read;

    if layer.size == 0 || layer.size > OTA_SLOT_BYTES {
        bail!(
            "firmware layer size {} does not fit OTA slot ({OTA_SLOT_BYTES} bytes)",
            layer.size
        );
    }
    let repo_path = repo_path(repo)?;
    let start_url = format!("https://ghcr.io/v2/{repo_path}/blobs/{}", layer.digest);
    let bearer = format!("Bearer {token}");

    let mut url = start_url;
    let mut use_auth = true;
    for _ in 0..BLOB_REDIRECTS {
        let conn = EspHttpConnection::new(&blob_http_config())?;
        let mut client = Client::wrap(conn);
        let mut resp = if use_auth {
            client
                .request(
                    Method::Get,
                    &url,
                    &[
                        ("authorization", bearer.as_str()),
                        ("accept", "application/octet-stream"),
                    ],
                )?
                .submit()?
        } else {
            client
                .request(Method::Get, &url, &[("accept", "application/octet-stream")])?
                .submit()?
        };
        let status = resp.status();
        if is_http_redirect(status) {
            let loc = resp
                .header("Location")
                .or_else(|| resp.header("location"))
                .ok_or_else(|| anyhow!("blob GET redirect {status} with no Location"))?
                .to_string();
            log::info!("ota: blob redirect {status}");
            url = loc;
            use_auth = false;
            continue;
        }
        if status != 200 {
            bail!("blob GET -> {status}");
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
        return Ok(());
    }
    bail!("blob GET exceeded {BLOB_REDIRECTS} redirects");
}
