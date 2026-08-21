//! Sigstore trust roots loaded from NVS at boot.
//!
//! Schema (must match `tools/provision/`):
//!
//!   namespace=trust
//!     identities    blob   JSON: [{"identity":"...","issuer":"..."}, ...]
//!     fulcio_root   blob   PEM bytes (Sigstore root CA)
//!     fulcio_inter  blob   PEM bytes (Sigstore intermediate CA)

use anyhow::{anyhow, Context, Result};
use esp_idf_svc::nvs::{EspDefaultNvsPartition, EspNvs};
use serde::Deserialize;

use crate::nvs_util::{is_not_found, read_blob};

const NVS_TRUST_NS: &str = "trust";
const NVS_IDENTITIES: &str = "identities";
const NVS_FULCIO_ROOT: &str = "fulcio_root";
const NVS_FULCIO_INTER: &str = "fulcio_inter";

/// One allowlist entry. The OTA verifier accepts a signature only if
/// the leaf cert SAN matches `identity` and the OIDC issuer matches
/// `issuer`.
#[derive(Deserialize, Clone, Debug)]
pub struct TrustedIdentity {
    pub identity: String,
    pub issuer: String,
}

/// Trust roots needed to verify a Sigstore bundle.
#[derive(Clone)]
pub struct TrustConfig {
    pub identities: Vec<TrustedIdentity>,
    pub fulcio_root_pem: Vec<u8>,
    pub fulcio_intermediate_pem: Vec<u8>,
}

impl TrustConfig {
    /// Load from NVS. Returns `Ok(None)` if any required key is absent.
    pub fn load(partition: EspDefaultNvsPartition) -> Result<Option<Self>> {
        let nvs = match EspNvs::new(partition, NVS_TRUST_NS, false) {
            Ok(n) => n,
            Err(e) if is_not_found(&e) => return Ok(None),
            Err(e) => return Err(anyhow!("open NVS namespace {NVS_TRUST_NS}: {e:?}")),
        };

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
                }))
            }
            _ => Ok(None),
        }
    }
}
