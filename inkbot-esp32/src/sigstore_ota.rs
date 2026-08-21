//! Sigstore-backed OTA admission (host-tested).
//!
//! Full Cosign/Fulcio/Rekor verification does not fit in the ESP-IDF second-stage
//! bootloader (see `docs/sigstore-ota.md`). This module holds digest checks and
//! an **exact** identity policy loaded at runtime from flash (NVS) — never baked
//! into the ELF. The Cosign CLI helper is host-only
//! (`cfg(not(target_os = "espidf"))`).
//!
//! Provision issuer + identity with the NVS CSV (see `nvs/sigstore.csv.example`)
//! when you flash; the same binary works for any repo/workflow pin.

use std::fmt;

use serde::{Deserialize, Serialize};
use sha2::{Digest, Sha256};

#[cfg(not(target_os = "espidf"))]
use std::path::Path;
#[cfg(not(target_os = "espidf"))]
use std::process::Command;

/// NVS namespace for Sigstore OTA pins (separate from image catalog keys).
pub const NVS_NAMESPACE: &str = "sigstore";

/// NVS key: exact Fulcio OIDC issuer URL (string).
pub const NVS_KEY_OIDC_ISSUER: &str = "oidc_iss";

/// NVS key: exact Fulcio certificate identity / SAN URI (string).
pub const NVS_KEY_CERT_IDENTITY: &str = "cert_id";

/// Who is allowed to mint a trusted firmware image.
///
/// Construct only from flash-time / runtime values ([`OtaIdentityPolicy::from_parts`]).
/// There is no compiled-in default identity.
#[derive(Debug, Clone, PartialEq, Eq, Serialize, Deserialize)]
pub struct OtaIdentityPolicy {
    /// Expected Fulcio OIDC issuer URL.
    pub certificate_oidc_issuer: String,
    /// Exact Cosign `--certificate-identity` value (Fulcio SAN URI).
    pub certificate_identity: String,
}

/// Why [`OtaIdentityPolicy::from_parts`] rejected the stored values.
#[derive(Debug, Clone, PartialEq, Eq)]
pub enum OtaIdentityPolicyError {
    MissingIssuer,
    MissingIdentity,
}

impl fmt::Display for OtaIdentityPolicyError {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            Self::MissingIssuer => write!(f, "sigstore OIDC issuer not set in NVS"),
            Self::MissingIdentity => write!(f, "sigstore certificate identity not set in NVS"),
        }
    }
}

impl std::error::Error for OtaIdentityPolicyError {}

impl OtaIdentityPolicy {
    /// Build a policy from flash-time strings. Both must be non-empty after trim.
    pub fn from_parts(
        certificate_oidc_issuer: &str,
        certificate_identity: &str,
    ) -> Result<Self, OtaIdentityPolicyError> {
        let issuer = certificate_oidc_issuer.trim();
        let identity = certificate_identity.trim();
        if issuer.is_empty() {
            return Err(OtaIdentityPolicyError::MissingIssuer);
        }
        if identity.is_empty() {
            return Err(OtaIdentityPolicyError::MissingIdentity);
        }
        Ok(Self {
            certificate_oidc_issuer: issuer.to_string(),
            certificate_identity: identity.to_string(),
        })
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

/// Run `cosign verify-blob` with an exact identity pin from runtime config.
///
/// Host / CI only. Pass the same issuer/identity you flash into NVS.
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
    fn policy_requires_both_parts_from_storage() {
        assert_eq!(
            OtaIdentityPolicy::from_parts("", "https://example/id"),
            Err(OtaIdentityPolicyError::MissingIssuer)
        );
        assert_eq!(
            OtaIdentityPolicy::from_parts("https://token.actions.githubusercontent.com", ""),
            Err(OtaIdentityPolicyError::MissingIdentity)
        );
        assert_eq!(
            OtaIdentityPolicy::from_parts("  ", "  id  "),
            Err(OtaIdentityPolicyError::MissingIssuer)
        );

        let p = OtaIdentityPolicy::from_parts(
            "https://token.actions.githubusercontent.com",
            "https://github.com/acme/app/.github/workflows/fw.yml@refs/heads/main",
        )
        .unwrap();
        assert!(p.issuer_matches("https://token.actions.githubusercontent.com"));
        assert!(p.identity_matches(
            "https://github.com/acme/app/.github/workflows/fw.yml@refs/heads/main"
        ));
        assert!(!p.identity_matches(
            "https://github.com/acme/app/.github/workflows/fw.yml@refs/heads/evil"
        ));
    }

    #[test]
    fn nvs_key_names_are_stable() {
        assert_eq!(NVS_NAMESPACE, "sigstore");
        assert_eq!(NVS_KEY_OIDC_ISSUER, "oidc_iss");
        assert_eq!(NVS_KEY_CERT_IDENTITY, "cert_id");
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
