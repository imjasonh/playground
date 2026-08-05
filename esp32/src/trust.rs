//! Trust configuration loaded from NVS at boot.
//!
//! What used to be `const TRUSTED_IDENTITIES` and `include_str!`'d
//! Sigstore PEMs is now provisioned via USB into NVS (see
//! `provisioning-plan.md`). The OTA-distributed firmware contains
//! only the *code* that reads and uses these values, never the
//! values themselves — so the public OCI image is device-agnostic
//! and carries no policy data.
//!
//! Schema (must match what `tools/provision/` writes):
//!
//!   namespace=trust
//!     identities    blob   JSON: [{"identity":"...","issuer":"..."}, ...]
//!     fulcio_root   blob   PEM bytes (Sigstore root CA)
//!     fulcio_inter  blob   PEM bytes (Sigstore intermediate CA)
//!     rekor_key     blob   PEM SubjectPublicKeyInfo for the trusted Rekor log
//!     rekor_from    u64    first UNIX second for which that log key is valid
//!     rekor_origin  str    checkpoint note signer name

use anyhow::{anyhow, Context, Result};
use esp_idf_svc::nvs::{EspDefaultNvsPartition, EspNvs};
use p256::pkcs8::DecodePublicKey;
use serde::Deserialize;
use sha2::{Digest, Sha256};
use x509_cert::der::pem;

use crate::nvs_util::read_blob;

const NVS_TRUST_NS: &str = "trust";
const NVS_IDENTITIES: &str = "identities";
const NVS_FULCIO_ROOT: &str = "fulcio_root";
const NVS_FULCIO_INTER: &str = "fulcio_inter";
const NVS_REKOR_KEY: &str = "rekor_key";
const NVS_REKOR_FROM: &str = "rekor_from";
const NVS_REKOR_ORIGIN: &str = "rekor_origin";

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
pub struct TrustConfig {
    pub identities: Vec<TrustedIdentity>,
    pub fulcio_root_pem: Vec<u8>,
    pub fulcio_intermediate_pem: Vec<u8>,
    pub rekor_public_key_der: Vec<u8>,
    pub rekor_log_id: [u8; 32],
    pub rekor_valid_from: u64,
    pub rekor_checkpoint_origin: String,
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
        let rekor_pem = read_blob(&nvs, NVS_TRUST_NS, NVS_REKOR_KEY, 1024)?;
        let rekor_valid_from = nvs
            .get_u64(NVS_REKOR_FROM)
            .map_err(|e| anyhow!("read NVS {}/{}: {:?}", NVS_TRUST_NS, NVS_REKOR_FROM, e))?;
        let rekor_checkpoint_origin =
            crate::nvs_util::read_str(&nvs, NVS_TRUST_NS, NVS_REKOR_ORIGIN, 64)?;

        match (
            id_bytes,
            root_bytes,
            inter_bytes,
            rekor_pem,
            rekor_valid_from,
            rekor_checkpoint_origin,
        ) {
            (
                Some(id),
                Some(root),
                Some(inter),
                Some(rekor_pem),
                Some(rekor_valid_from),
                Some(rekor_checkpoint_origin),
            ) => {
                let identities: Vec<TrustedIdentity> = serde_json::from_slice(&id)
                    .context("parse trust/identities NVS blob as JSON")?;
                if identities.is_empty() {
                    return Err(anyhow!(
                        "trust/identities is provisioned but contains no entries"
                    ));
                }
                let (label, rekor_public_key_der) =
                    pem::decode_vec(&rekor_pem).context("decode trust/rekor_key PEM")?;
                if label != "PUBLIC KEY" {
                    return Err(anyhow!("trust/rekor_key PEM label is {}", label));
                }
                p256::ecdsa::VerifyingKey::from_public_key_der(&rekor_public_key_der)
                    .context("parse trust/rekor_key as ECDSA P-256")?;
                let rekor_log_id: [u8; 32] = Sha256::digest(&rekor_public_key_der).into();
                Ok(Some(Self {
                    identities,
                    fulcio_root_pem: root,
                    fulcio_intermediate_pem: inter,
                    rekor_public_key_der,
                    rekor_log_id,
                    rekor_valid_from,
                    rekor_checkpoint_origin,
                }))
            }
            _ => Ok(None),
        }
    }
}
