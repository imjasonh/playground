//! Trust configuration loaded from NVS at boot.
//!
//! What used to be `const TRUSTED_IDENTITIES` and `include_str!`'d
//! Sigstore PEMs is now provisioned via USB into NVS (see
//! `provisioning-plan.md`). The OTA-distributed firmware contains
//! only the *code* that reads and uses these values, never the
//! values themselves — so the public OCI image is device-agnostic
//! and carries no policy data.
//!
//! Rekor shard keys and TSA certificates are public infrastructure trust
//! anchors rather than per-device policy. They are versioned with firmware so
//! overlapping shards can rotate through an OTA signed by the prior shard.
//!
//! Schema (must match what `tools/provision/` writes):
//!
//!   namespace=trust
//!     identities    blob   JSON: [{"identity":"...","issuer":"..."}, ...]
//!     fulcio_root   blob   PEM bytes (Sigstore root CA)
//!     fulcio_inter  blob   PEM bytes (Sigstore intermediate CA)

use anyhow::{anyhow, bail, Context, Result};
use esp_idf_svc::nvs::{EspDefaultNvsPartition, EspNvs};
use serde::Deserialize;
use sha2::{Digest, Sha256};
use x509_cert::der::pem;

use crate::nvs_util::read_blob;

const NVS_TRUST_NS: &str = "trust";
const NVS_IDENTITIES: &str = "identities";
const NVS_FULCIO_ROOT: &str = "fulcio_root";
const NVS_FULCIO_INTER: &str = "fulcio_inter";
const REKOR_V1_ORIGIN: &str = "rekor.sigstore.dev";
const REKOR_V2_ORIGIN: &str = "log2025-1.rekor.sigstore.dev";
const SIGSTORE_TSA_POLICY_OID: &str = "1.3.6.1.4.1.57264.2";

/// One entry from the allowlist. The OTA verifier accepts a signature
/// only if the leaf cert's SAN value matches `identity` AND the OIDC
/// issuer extension matches `issuer`.
#[derive(Deserialize, Clone, Debug)]
pub struct TrustedIdentity {
    pub identity: String,
    pub issuer: String,
}

/// The full set of trust roots needed to verify a Sigstore bundle.
#[derive(Clone)]
pub enum RekorPublicKey {
    EcdsaP256(Vec<u8>),
    Ed25519([u8; 32]),
}

#[derive(Clone)]
pub struct TrustedRekorLog {
    pub log_id: [u8; 32],
    pub valid_from: u64,
    pub valid_until: Option<u64>,
    pub checkpoint_origin: &'static str,
    pub public_key: RekorPublicKey,
}

#[derive(Clone)]
pub struct TrustedTimestampAuthority {
    pub leaf_der: Vec<u8>,
    pub root_der: Vec<u8>,
    pub valid_from: u64,
    pub valid_until: Option<u64>,
    pub policy_oid: &'static str,
}

#[derive(Clone)]
pub struct TrustConfig {
    pub identities: Vec<TrustedIdentity>,
    pub fulcio_root_pem: Vec<u8>,
    pub fulcio_intermediate_pem: Vec<u8>,
    pub rekor_logs: Vec<TrustedRekorLog>,
    pub timestamp_authority: TrustedTimestampAuthority,
}

impl TrustConfig {
    /// Load from NVS. Returns `Ok(None)` if any required key is absent
    /// (treat as "unprovisioned" — caller should refuse to verify).
    pub fn load(partition: EspDefaultNvsPartition) -> Result<Option<Self>> {
        let nvs = EspNvs::new(partition, NVS_TRUST_NS, false)
            .map_err(|e| anyhow!("open NVS namespace {}: {:?}", NVS_TRUST_NS, e))?;

        // PEMs are ~3KB; identities JSON is ~500 bytes. 4KB buffers
        // give comfortable headroom for now.
        let id_bytes = read_blob(&nvs, NVS_TRUST_NS, NVS_IDENTITIES, 4096)?;
        let root_bytes = read_blob(&nvs, NVS_TRUST_NS, NVS_FULCIO_ROOT, 4096)?;
        let inter_bytes = read_blob(&nvs, NVS_TRUST_NS, NVS_FULCIO_INTER, 4096)?;

        match (id_bytes, root_bytes, inter_bytes) {
            (Some(id), Some(root), Some(inter)) => {
                let identities: Vec<TrustedIdentity> = serde_json::from_slice(&id)
                    .context("parse trust/identities NVS blob as JSON")?;
                if identities.is_empty() {
                    return Err(anyhow!(
                        "trust/identities is provisioned but contains no entries"
                    ));
                }
                Ok(Some(Self {
                    identities,
                    fulcio_root_pem: root,
                    fulcio_intermediate_pem: inter,
                    rekor_logs: trusted_rekor_logs()?,
                    timestamp_authority: trusted_timestamp_authority()?,
                }))
            }
            _ => Ok(None),
        }
    }
}

fn trusted_rekor_logs() -> Result<Vec<TrustedRekorLog>> {
    use ed25519_dalek::pkcs8::DecodePublicKey as _;
    use p256::pkcs8::DecodePublicKey as _;

    let v1_der = decode_pem(include_bytes!("../trust/rekor.pub"), "PUBLIC KEY")?;
    p256::ecdsa::VerifyingKey::from_public_key_der(&v1_der)
        .context("parse built-in Rekor v1 P-256 key")?;
    let v1_log_id = Sha256::digest(&v1_der).into();

    let v2_der = decode_pem(include_bytes!("../trust/rekor-v2.pub"), "PUBLIC KEY")?;
    let v2_key = ed25519_dalek::VerifyingKey::from_public_key_der(&v2_der)
        .context("parse built-in Rekor v2 Ed25519 key")?;
    let mut id_hasher = Sha256::new();
    id_hasher.update(REKOR_V2_ORIGIN.as_bytes());
    id_hasher.update(b"\n\x01");
    id_hasher.update(v2_key.to_bytes());
    let v2_log_id = id_hasher.finalize().into();

    Ok(vec![
        TrustedRekorLog {
            log_id: v1_log_id,
            valid_from: 1_610_452_407,
            valid_until: None,
            checkpoint_origin: REKOR_V1_ORIGIN,
            public_key: RekorPublicKey::EcdsaP256(v1_der),
        },
        TrustedRekorLog {
            log_id: v2_log_id,
            valid_from: 1_767_225_600,
            valid_until: None,
            checkpoint_origin: REKOR_V2_ORIGIN,
            public_key: RekorPublicKey::Ed25519(v2_key.to_bytes()),
        },
    ])
}

fn trusted_timestamp_authority() -> Result<TrustedTimestampAuthority> {
    Ok(TrustedTimestampAuthority {
        leaf_der: decode_pem(include_bytes!("../trust/tsa-leaf.pem"), "CERTIFICATE")?,
        root_der: decode_pem(include_bytes!("../trust/tsa-root.pem"), "CERTIFICATE")?,
        valid_from: 1_751_587_200,
        valid_until: None,
        policy_oid: SIGSTORE_TSA_POLICY_OID,
    })
}

fn decode_pem(bytes: &[u8], expected_label: &str) -> Result<Vec<u8>> {
    let (label, der) = pem::decode_vec(bytes)
        .map_err(|error| anyhow!("decode {} PEM: {}", expected_label, error))?;
    if label != expected_label {
        bail!("expected {} PEM, got {}", expected_label, label);
    }
    Ok(der)
}
