use anyhow::{anyhow, Context, Result};
use clap::Parser;
use oci_distribution::{
    client::{ClientConfig, Config, ImageLayer},
    manifest::{OciDescriptor, OciImageManifest, OCI_IMAGE_MEDIA_TYPE},
    secrets::RegistryAuth,
    Client, Reference,
};
use serde::Serialize;
use sha2::{Digest, Sha256};
use std::collections::BTreeMap;
use std::path::PathBuf;
use std::time::SystemTime;
use time::format_description::well_known::Rfc3339;
use time::OffsetDateTime;

const CONFIG_MEDIA_TYPE: &str = "application/vnd.esp32.firmware.v1+json";
const LAYER_MEDIA_TYPE: &str = "application/vnd.esp32.firmware.bin";

#[derive(Parser)]
#[command(
    version,
    about = "Push ESP32 firmware bins to an OCI registry as artifacts."
)]
struct Cli {
    #[command(subcommand)]
    cmd: Cmd,
}

#[derive(clap::Subcommand)]
enum Cmd {
    /// Build an OCI artifact from a .bin and push it to a registry.
    Push(PushArgs),
    /// Pull an OCI artifact and verify its layer SHA matches a local .bin.
    /// Mirrors the device-side fetch flow we'll need in phase 2.
    PullVerify(PullVerifyArgs),
}

#[derive(clap::Args)]
struct PushArgs {
    /// Path to the firmware .bin (produced by `espflash save-image`).
    #[arg(long)]
    bin: PathBuf,

    /// Repository, e.g. ghcr.io/imjasonh/esp32
    #[arg(long)]
    repo: String,

    /// Primary tag to push (also pushed as :sha-<short> if --git-sha is given).
    #[arg(long, default_value = "latest")]
    tag: String,

    /// Short git SHA, used for the secondary tag and for image metadata.
    #[arg(long)]
    git_sha: Option<String>,

    /// org.opencontainers.image.source URL embedded in the manifest annotations.
    /// GHCR uses this to auto-link the package to a source repo on first push.
    #[arg(long, default_value = "https://github.com/imjasonh/playground")]
    source: String,

    /// Target chip, recorded in the artifact's config blob.
    #[arg(long, default_value = "esp32")]
    target_chip: String,

    /// Firmware application identifier, recorded in artifact metadata.
    #[arg(long)]
    app_id: String,

    /// IDF version, recorded in the artifact's config blob.
    #[arg(long, default_value = "v5.2.2")]
    idf_version: String,
}

#[derive(clap::Args)]
struct PullVerifyArgs {
    /// Repository, e.g. ghcr.io/imjasonh/esp32
    #[arg(long)]
    repo: String,

    /// Tag or digest (sha256:...) to pull.
    #[arg(long, default_value = "latest")]
    tag: String,

    /// Local .bin to compare against the pulled layer.
    #[arg(long)]
    bin: PathBuf,

    /// Use GH_TOKEN for auth instead of anonymous. Required while the GHCR
    /// package is private; harmless once it's public.
    #[arg(long)]
    auth: bool,
}

#[derive(Serialize)]
struct FirmwareConfig {
    app_id: String,
    target_chip: String,
    idf_version: String,
    git_sha: Option<String>,
    built_at: String,
    bin_size: u64,
    bin_sha256: String,
}

#[tokio::main]
async fn main() -> Result<()> {
    // Logs go to stderr so stdout is reserved for machine-readable output
    // (the `digest:` line emitted by the push subcommand for downstream
    // tooling — `make publish` parses it to feed `cosign sign` an
    // immutable digest reference).
    tracing_subscriber::fmt()
        .with_writer(std::io::stderr)
        .with_env_filter(
            tracing_subscriber::EnvFilter::try_from_default_env()
                .unwrap_or_else(|_| tracing_subscriber::EnvFilter::new("info")),
        )
        .init();

    let cli = Cli::parse();
    match cli.cmd {
        Cmd::Push(args) => push(args).await,
        Cmd::PullVerify(args) => pull_verify(args).await,
    }
}

async fn pull_verify(args: PullVerifyArgs) -> Result<()> {
    let local = tokio::fs::read(&args.bin)
        .await
        .with_context(|| format!("read {}", args.bin.display()))?;
    let local_sha = hex::encode(Sha256::digest(&local));
    tracing::info!(
        path = %args.bin.display(),
        bytes = local.len(),
        sha256 = %local_sha,
        "loaded local firmware",
    );

    let reference: Reference = format!("{}:{}", args.repo, args.tag)
        .parse()
        .with_context(|| format!("parse reference {}:{}", args.repo, args.tag))?;

    let auth = if args.auth {
        registry_auth(&args.repo)?
    } else {
        RegistryAuth::Anonymous
    };

    let client = Client::new(ClientConfig::default());

    let (manifest, manifest_digest) = client
        .pull_image_manifest(&reference, &auth)
        .await
        .with_context(|| format!("fetch manifest for {}", reference))?;
    tracing::info!(
        reference = %reference,
        manifest_digest = %manifest_digest,
        layer_count = manifest.layers.len(),
        "fetched manifest",
    );

    if manifest.layers.len() != 1 {
        return Err(anyhow!(
            "expected exactly 1 layer, got {}",
            manifest.layers.len()
        ));
    }
    let layer_descriptor = &manifest.layers[0];
    tracing::info!(
        media_type = %layer_descriptor.media_type,
        digest = %layer_descriptor.digest,
        size = layer_descriptor.size,
        "layer descriptor",
    );
    if layer_descriptor.media_type != LAYER_MEDIA_TYPE {
        return Err(anyhow!(
            "unexpected layer mediaType: got {}, want {}",
            layer_descriptor.media_type,
            LAYER_MEDIA_TYPE,
        ));
    }

    let mut layer_bytes = Vec::with_capacity(layer_descriptor.size as usize);
    client
        .pull_blob(&reference, layer_descriptor, &mut layer_bytes)
        .await
        .with_context(|| format!("fetch layer blob {}", layer_descriptor.digest))?;

    let pulled_sha = hex::encode(Sha256::digest(&layer_bytes));
    let descriptor_sha = layer_descriptor
        .digest
        .strip_prefix("sha256:")
        .unwrap_or("");
    if pulled_sha != descriptor_sha {
        return Err(anyhow!(
            "pulled layer SHA mismatch with manifest descriptor: got {}, manifest says {}",
            pulled_sha,
            descriptor_sha,
        ));
    }
    tracing::info!(sha256 = %pulled_sha, "pulled layer matches manifest digest");

    if pulled_sha != local_sha {
        return Err(anyhow!(
            "pulled layer SHA {} != local file SHA {}",
            pulled_sha,
            local_sha,
        ));
    }
    tracing::info!("✓ pulled layer SHA matches local .bin");
    Ok(())
}

async fn push(args: PushArgs) -> Result<()> {
    let bin_bytes = tokio::fs::read(&args.bin)
        .await
        .with_context(|| format!("read {}", args.bin.display()))?;
    let bin_size = bin_bytes.len() as u64;
    let bin_sha256 = hex::encode(Sha256::digest(&bin_bytes));
    tracing::info!(
        path = %args.bin.display(),
        bytes = bin_size,
        sha256 = %bin_sha256,
        "loaded firmware",
    );

    let cfg = FirmwareConfig {
        app_id: args.app_id.clone(),
        target_chip: args.target_chip.clone(),
        idf_version: args.idf_version.clone(),
        git_sha: args.git_sha.clone(),
        built_at: OffsetDateTime::from(SystemTime::now())
            .format(&Rfc3339)
            .unwrap(),
        bin_size,
        bin_sha256: bin_sha256.clone(),
    };
    let cfg_bytes = serde_json::to_vec_pretty(&cfg)?;

    let config = Config {
        data: cfg_bytes,
        media_type: CONFIG_MEDIA_TYPE.to_string(),
        annotations: None,
    };
    let layer = ImageLayer {
        data: bin_bytes,
        media_type: LAYER_MEDIA_TYPE.to_string(),
        annotations: None,
    };

    let mut annotations = BTreeMap::new();
    annotations.insert(
        "org.opencontainers.image.source".to_string(),
        args.source.clone(),
    );
    annotations.insert(
        "org.opencontainers.image.created".to_string(),
        cfg.built_at.clone(),
    );
    if let Some(sha) = &args.git_sha {
        annotations.insert("org.opencontainers.image.revision".to_string(), sha.clone());
    }

    let manifest = build_manifest(&config, &layer, &annotations)?;

    let auth = registry_auth(&args.repo)?;
    let client = Client::new(ClientConfig::default());

    let mut tags = vec![args.tag.clone()];
    if let Some(sha) = &args.git_sha {
        tags.push(format!("sha-{}", sha));
    }

    let mut printed_digest: Option<String> = None;
    for tag in &tags {
        let reference: Reference = format!("{}:{}", args.repo, tag)
            .parse()
            .with_context(|| format!("parse reference {}:{}", args.repo, tag))?;
        tracing::info!(reference = %reference, "pushing");
        let resp = client
            .push(
                &reference,
                &[layer.clone()],
                config.clone(),
                &auth,
                Some(manifest.clone()),
            )
            .await
            .with_context(|| format!("push {}", reference))?;
        let digest = digest_from_manifest_url(&resp.manifest_url)
            .ok_or_else(|| anyhow::anyhow!("could not parse digest from {}", resp.manifest_url))?;
        tracing::info!(
            reference = %reference,
            manifest_url = %resp.manifest_url,
            digest = %digest,
            "pushed",
        );
        // Print the manifest digest once on stdout, machine-readable, so
        // downstream tooling (cosign sign) can target the immutable
        // digest instead of a moving tag.
        if printed_digest.is_none() {
            println!("digest: {}", digest);
            printed_digest = Some(digest.to_string());
        } else if printed_digest.as_deref() != Some(digest) {
            // Both pushes are the same content, so digests must match.
            // If they don't, something's deeply wrong (different
            // manifest bytes between calls?). Fail loudly.
            return Err(anyhow::anyhow!(
                "tag {} pushed at digest {} but earlier push was at {}",
                tag,
                digest,
                printed_digest.as_deref().unwrap_or("?"),
            ));
        }
    }

    Ok(())
}

/// Extract `sha256:abc...` from a manifest URL like
/// `https://ghcr.io/v2/owner/name/manifests/sha256:abc...`.
fn digest_from_manifest_url(url: &str) -> Option<&str> {
    url.rsplit_once("/manifests/").map(|(_, d)| d)
}

fn build_manifest(
    config: &Config,
    layer: &ImageLayer,
    annotations: &BTreeMap<String, String>,
) -> Result<OciImageManifest> {
    let config_descriptor = OciDescriptor {
        media_type: config.media_type.clone(),
        digest: format!("sha256:{}", hex::encode(Sha256::digest(&config.data))),
        size: config.data.len() as i64,
        urls: None,
        annotations: None,
    };
    let layer_descriptor = OciDescriptor {
        media_type: layer.media_type.clone(),
        digest: format!("sha256:{}", hex::encode(Sha256::digest(&layer.data))),
        size: layer.data.len() as i64,
        urls: None,
        annotations: None,
    };
    Ok(OciImageManifest {
        schema_version: 2,
        media_type: Some(OCI_IMAGE_MEDIA_TYPE.to_string()),
        config: config_descriptor,
        layers: vec![layer_descriptor],
        artifact_type: None,
        annotations: Some(
            annotations
                .iter()
                .map(|(k, v)| (k.clone(), v.clone()))
                .collect(),
        ),
    })
}

fn registry_auth(repo: &str) -> Result<RegistryAuth> {
    let token = std::env::var("GH_TOKEN")
        .context("GH_TOKEN env var not set; needed to push to ghcr.io. Source gh.env first.")?;
    // GHCR accepts the GitHub username here, but the token is what actually
    // authorizes; any non-empty username works in practice.
    let username = repo
        .split('/')
        .nth(1)
        .ok_or_else(|| anyhow!("can't infer github username from repo {}", repo))?
        .to_string();
    Ok(RegistryAuth::Basic(username, token))
}
