//! Sigstore-backed OTA admission (host-tested).
//!
//! Full Cosign/Fulcio/Rekor verification does not fit in the ESP-IDF second-stage
//! bootloader (see `docs/sigstore-ota.md`). This module holds the identity
//! policy and digest checks the firmware and CI share. The Cosign CLI helper is
//! host-only (`cfg(not(target_os = "espidf"))`).
//!
//! Identity pins are **exact** Fulcio certificate identity strings (no regexp).
//! Device-side crypto verify lands later; until then CI must `verify-blob`
//! before publishing.

use serde::{Deserialize, Serialize};
use sha2::{Digest, Sha256};

#[cfg(not(target_os = "espidf"))]
use std::fmt;
#[cfg(not(target_os = "espidf"))]
use std::path::Path;
#[cfg(not(target_os = "espidf"))]
use std::process::Command;

/// GitHub Actions OIDC issuer Fulcio embeds in keyless certs.
pub const GITHUB_ACTIONS_OIDC_ISSUER: &str = "https://token.actions.githubusercontent.com";

/// Exact Fulcio certificate identity for inkbot firmware signed on `main`.
///
/// Format: `https://github.com/<owner>/<repo>/.github/workflows/<file>@<ref>`
pub const DEFAULT_CERTIFICATE_IDENTITY: &str = concat!(
    "https://github.com/imjasonh/playground/",
    ".github/workflows/inkbot-esp32.yml@refs/heads/main"
);

/// Who is allowed to mint a trusted firmware image.
#[derive(Debug, Clone, PartialEq, Eq, Serialize, Deserialize)]
pub struct OtaIdentityPolicy {
    /// Expected Fulcio OIDC issuer URL.
    pub certificate_oidc_issuer: String,
    /// Exact Cosign `--certificate-identity` value (Fulcio SAN URI).
    pub certificate_identity: String,
}

impl Default for OtaIdentityPolicy {
    fn default() -> Self {
        Self {
            certificate_oidc_issuer: GITHUB_ACTIONS_OIDC_ISSUER.to_string(),
            certificate_identity: DEFAULT_CERTIFICATE_IDENTITY.to_string(),
        }
    }
}

impl OtaIdentityPolicy {
    /// Policy for this playground's inkbot-esp32 workflow on `main`.
    pub fn inkbot_main() -> Self {
        Self::default()
    }

    /// True when the certificate identity equals the pinned string.
    pub fn identity_matches(&self, certificate_identity: &str) -> bool {
        certificate_identity == self.certificate_identity
    }

    /// True when the issuer string equals the pinned OIDC issuer.
    pub fn issuer_matches(&self, certificate_oidc_issuer: &str) -> bool {
        certificate_oidc_issuer == self.certificate_oidc_issuer
    }
}

/// Manifest the Worker / CD pipeline publishes next to the firmware blob.
#[derive(Debug, Clone, PartialEq, Eq, Serialize, Deserialize)]
pub struct FirmwareManifest {
    /// Same string the device reports as `firmware=` / User-Agent.
    pub firmware_id: String,
    /// Lowercase hex SHA-256 of the OTA app image bytes.
    pub sha256: String,
    /// Object name for the image (for example `inkbot-esp32.bin`).
    pub image: String,
    /// Object name for the Cosign bundle (for example `inkbot-esp32.sigstore.json`).
    pub bundle: String,
}

impl FirmwareManifest {
    pub fn from_image_bytes(firmware_id: &str, image_name: &str, image: &[u8]) -> Self {
        let bundle = bundle_name_for_image(image_name);
        Self {
            firmware_id: firmware_id.to_string(),
            sha256: hex_sha256(image),
            image: image_name.to_string(),
            bundle,
        }
    }

    /// True when `image` matches the pinned digest.
    pub fn digest_matches(&self, image: &[u8]) -> bool {
        self.sha256 == hex_sha256(image)
    }
}

/// Map `foo.bin` → `foo.sigstore.json` (Cosign `--bundle` sibling).
pub fn bundle_name_for_image(image_name: &str) -> String {
    if let Some(stem) = image_name.strip_suffix(".bin") {
        return format!("{stem}.sigstore.json");
    }
    format!("{image_name}.sigstore.json")
}

/// Lowercase hex SHA-256.
pub fn hex_sha256(bytes: &[u8]) -> String {
    let digest = Sha256::digest(bytes);
    let mut out = String::with_capacity(digest.len() * 2);
    for b in digest {
        out.push_str(&format!("{b:02x}"));
    }
    out
}

/// Errors from the host Cosign CLI helper.
#[cfg(not(target_os = "espidf"))]
#[derive(Debug, Clone, PartialEq, Eq)]
pub enum SigstoreVerifyError {
    CosignNotFound,
    CosignFailed { status: Option<i32>, stderr: String },
    Io(String),
}

#[cfg(not(target_os = "espidf"))]
impl fmt::Display for SigstoreVerifyError {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            Self::CosignNotFound => write!(f, "cosign binary not found on PATH"),
            Self::CosignFailed { status, stderr } => {
                write!(f, "cosign verify-blob failed (status={status:?}): {stderr}")
            }
            Self::Io(msg) => write!(f, "io: {msg}"),
        }
    }
}

#[cfg(not(target_os = "espidf"))]
impl std::error::Error for SigstoreVerifyError {}

/// Run `cosign verify-blob` with an exact identity pin.
///
/// Host / CI only. The ESP32 app will gain an equivalent check without shelling
/// out once a slim on-device verifier lands.
#[cfg(not(target_os = "espidf"))]
pub fn verify_blob_with_cosign(
    artifact: &Path,
    bundle: &Path,
    policy: &OtaIdentityPolicy,
) -> Result<(), SigstoreVerifyError> {
    let output = Command::new("cosign")
        .arg("verify-blob")
        .arg("--bundle")
        .arg(bundle)
        .arg("--certificate-oidc-issuer")
        .arg(&policy.certificate_oidc_issuer)
        .arg("--certificate-identity")
        .arg(&policy.certificate_identity)
        .arg(artifact)
        .output()
        .map_err(|e| {
            if e.kind() == std::io::ErrorKind::NotFound {
                SigstoreVerifyError::CosignNotFound
            } else {
                SigstoreVerifyError::Io(e.to_string())
            }
        })?;

    if output.status.success() {
        return Ok(());
    }

    Err(SigstoreVerifyError::CosignFailed {
        status: output.status.code(),
        stderr: String::from_utf8_lossy(&output.stderr).trim().to_string(),
    })
}

#[cfg(test)]
mod tests {
    use super::*;
    use std::fs;
    use std::path::PathBuf;
    use std::process::Command;

    #[test]
    fn default_policy_requires_exact_identity() {
        let p = OtaIdentityPolicy::inkbot_main();
        assert!(p.issuer_matches(GITHUB_ACTIONS_OIDC_ISSUER));
        assert!(!p.issuer_matches("https://oauth2.sigstore.dev/auth"));

        assert!(p.identity_matches(DEFAULT_CERTIFICATE_IDENTITY));
        assert!(!p.identity_matches(
            "https://github.com/imjasonh/playground/.github/workflows/inkbot-esp32.yml@refs/heads/evil"
        ));
        assert!(!p.identity_matches(
            "https://github.com/imjasonh/playground/.github/workflows/deps.yaml@refs/heads/main"
        ));
        assert!(!p.identity_matches(
            "https://github.com/other/playground/.github/workflows/inkbot-esp32.yml@refs/heads/main"
        ));
    }

    #[test]
    fn manifest_binds_sha256_and_bundle_name() {
        let image = b"fake-firmware-bytes";
        let m = FirmwareManifest::from_image_bytes("inkbot-esp32/0.2", "inkbot-esp32.bin", image);
        assert_eq!(m.bundle, "inkbot-esp32.sigstore.json");
        assert_eq!(m.sha256, hex_sha256(image));
        assert!(m.digest_matches(image));
        assert!(!m.digest_matches(b"other"));
    }

    #[test]
    fn cosign_key_sign_and_verify_blob_round_trip() {
        if Command::new("cosign").arg("version").output().is_err() {
            eprintln!("skip: cosign not on PATH");
            return;
        }

        let dir = unique_temp_dir("inkbot-sigstore");
        fs::create_dir_all(&dir).unwrap();
        let artifact = dir.join("artifact.bin");
        let bundle = dir.join("artifact.sigstore.json");
        let key = dir.join("cosign.key");
        let pub_key = dir.join("cosign.pub");
        fs::write(&artifact, b"inkbot-ota-fixture").unwrap();

        let gen = Command::new("cosign")
            .current_dir(&dir)
            .args(["generate-key-pair"])
            .env("COSIGN_PASSWORD", "")
            .output()
            .expect("generate-key-pair");
        assert!(
            gen.status.success(),
            "generate-key-pair: {}",
            String::from_utf8_lossy(&gen.stderr)
        );
        assert!(key.is_file());
        assert!(pub_key.is_file());

        let sign = Command::new("cosign")
            .args(["sign-blob", "--yes", "--key"])
            .arg(&key)
            .arg("--bundle")
            .arg(&bundle)
            .arg(&artifact)
            .env("COSIGN_PASSWORD", "")
            .output()
            .expect("sign-blob");
        assert!(
            sign.status.success(),
            "sign-blob: {}",
            String::from_utf8_lossy(&sign.stderr)
        );

        let manifest =
            FirmwareManifest::from_image_bytes("test/0.0", "artifact.bin", b"inkbot-ota-fixture");
        assert!(manifest.digest_matches(b"inkbot-ota-fixture"));

        let verify = Command::new("cosign")
            .args(["verify-blob", "--key"])
            .arg(&pub_key)
            .arg("--bundle")
            .arg(&bundle)
            .arg(&artifact)
            .output()
            .expect("verify-blob");
        assert!(
            verify.status.success(),
            "verify-blob: {}",
            String::from_utf8_lossy(&verify.stderr)
        );

        let _ = fs::remove_dir_all(&dir);
    }

    fn unique_temp_dir(prefix: &str) -> PathBuf {
        let nanos = std::time::SystemTime::now()
            .duration_since(std::time::UNIX_EPOCH)
            .unwrap()
            .as_nanos();
        std::env::temp_dir().join(format!("{prefix}-{nanos}"))
    }
}
