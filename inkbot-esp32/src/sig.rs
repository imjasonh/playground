//! Cosign Sigstore Bundle (v0.3) verification for OTA artifacts.

use anyhow::{anyhow, bail, Context, Result};
use base64::Engine;
use p256::ecdsa::signature::Verifier as _;
use serde::Deserialize;
use x509_cert::der::{oid::ObjectIdentifier, Decode, Encode};
use x509_cert::ext::pkix::name::GeneralName;
use x509_cert::ext::pkix::SubjectAltName;
use x509_cert::Certificate;

use crate::https::now_unix_secs;
use crate::trust::TrustConfig;
use inkbot_esp32::decode_fulcio_issuer_value;
use inkbot_esp32::ota_format::pae_dsse_v1;

const DSSE_INTOTO_PAYLOAD_TYPE: &str = "application/vnd.in-toto+json";
const OID_OIDC_ISSUER_V1: &str = "1.3.6.1.4.1.57264.1.1";
const OID_OIDC_ISSUER_V2: &str = "1.3.6.1.4.1.57264.1.8";
const OID_SAN: &str = "2.5.29.17";

#[derive(Deserialize)]
struct Bundle {
    #[serde(rename = "verificationMaterial")]
    verification_material: VerificationMaterial,
    #[serde(rename = "dsseEnvelope")]
    dsse_envelope: DsseEnvelope,
}

#[derive(Deserialize)]
struct VerificationMaterial {
    certificate: CertWrapper,
}

#[derive(Deserialize)]
struct CertWrapper {
    #[serde(rename = "rawBytes")]
    raw_bytes: String,
}

#[derive(Deserialize)]
struct DsseEnvelope {
    payload: String,
    #[serde(rename = "payloadType")]
    payload_type: String,
    signatures: Vec<DsseSignature>,
}

#[derive(Deserialize)]
struct DsseSignature {
    sig: String,
}

#[derive(Deserialize)]
struct InTotoStatement {
    subject: Vec<InTotoSubject>,
}

#[derive(Deserialize)]
struct InTotoSubject {
    digest: serde_json::Map<String, serde_json::Value>,
}

/// Verify a Sigstore bundle JSON against an expected manifest digest.
/// `expected_manifest_digest_hex` is the hex string (no `sha256:`).
pub fn verify_bundle(
    bundle_json: &[u8],
    expected_manifest_digest_hex: &str,
    trust: &TrustConfig,
) -> Result<()> {
    let bundle: Bundle = serde_json::from_slice(bundle_json).context("parse bundle JSON")?;

    if bundle.dsse_envelope.payload_type != DSSE_INTOTO_PAYLOAD_TYPE {
        bail!(
            "unexpected DSSE payloadType: {} (want {})",
            bundle.dsse_envelope.payload_type,
            DSSE_INTOTO_PAYLOAD_TYPE,
        );
    }

    let cert_der = b64_std()
        .decode(&bundle.verification_material.certificate.raw_bytes)
        .context("base64-decode leaf cert")?;
    let leaf = Certificate::from_der(&cert_der).context("parse leaf cert DER")?;
    verify_leaf_identity_and_chain(&leaf, trust)?;

    let dsse_sig = bundle
        .dsse_envelope
        .signatures
        .first()
        .ok_or_else(|| anyhow!("DSSE envelope has no signatures"))?;
    let sig_bytes = b64_std()
        .decode(&dsse_sig.sig)
        .context("base64-decode DSSE signature")?;
    let payload_bytes = b64_std()
        .decode(&bundle.dsse_envelope.payload)
        .context("base64-decode DSSE payload")?;
    let pae = pae_dsse_v1(&bundle.dsse_envelope.payload_type, &payload_bytes);

    verify_p256_ecdsa(&leaf, &pae, &sig_bytes).context("DSSE signature verify")?;
    log::info!("ota: DSSE signature verified");

    let stmt: InTotoStatement =
        serde_json::from_slice(&payload_bytes).context("parse in-toto Statement payload")?;
    let subj = stmt
        .subject
        .first()
        .ok_or_else(|| anyhow!("in-toto Statement has no subject"))?;
    let actual_digest_hex = subj
        .digest
        .get("sha256")
        .and_then(|v| v.as_str())
        .ok_or_else(|| anyhow!("in-toto subject has no sha256 digest"))?;
    if actual_digest_hex != expected_manifest_digest_hex {
        bail!(
            "in-toto subject digest mismatch: signed={actual_digest_hex} expected={expected_manifest_digest_hex}"
        );
    }
    log::info!("ota: in-toto subject binds to {actual_digest_hex}");
    Ok(())
}

/// Verify Cosign 2 simple-signing (`application/vnd.dev.cosign.simplesigning.v1+json`).
///
/// The payload JSON binds `docker-manifest-digest`. The ECDSA-P256 signature
/// and Fulcio leaf PEM live in the OCI layer annotations.
pub fn verify_cosign_simple(
    payload: &[u8],
    cert_pem: &[u8],
    sig_b64: &str,
    expected_manifest_digest_hex: &str,
    trust: &TrustConfig,
) -> Result<()> {
    let actual = inkbot_esp32::cosign_manifest_digest_hex(payload).map_err(anyhow::Error::msg)?;
    if actual != expected_manifest_digest_hex {
        bail!(
            "cosign payload digest mismatch: signed={actual} expected={expected_manifest_digest_hex}"
        );
    }
    let leaf = pem_to_cert(cert_pem).context("parse Cosign leaf PEM")?;
    verify_leaf_identity_and_chain(&leaf, trust)?;
    let sig_bytes = b64_std()
        .decode(sig_b64)
        .context("base64-decode Cosign signature")?;
    verify_p256_ecdsa(&leaf, payload, &sig_bytes).context("Cosign simple-signing verify")?;
    log::info!("ota: Cosign simple-signing verified {actual}");
    Ok(())
}

fn verify_leaf_identity_and_chain(leaf: &Certificate, trust: &TrustConfig) -> Result<()> {
    let identity = extract_san_identity(leaf).context("extract SAN identity")?;
    let issuer = extract_oidc_issuer(leaf).context("extract OIDC issuer")?;
    if !trust
        .identities
        .iter()
        .any(|t| t.identity == identity && t.issuer == issuer)
    {
        bail!("untrusted identity: {identity} (issuer {issuer})");
    }
    log::info!("ota: signer identity OK {identity}");
    verify_chain(leaf, trust).context("cert chain verification")?;
    log::info!("ota: cert chain to Sigstore root OK");
    Ok(())
}

fn b64_std() -> base64::engine::GeneralPurpose {
    base64::engine::general_purpose::STANDARD
}

fn extract_san_identity(cert: &Certificate) -> Result<String> {
    let san_oid: ObjectIdentifier = OID_SAN.parse().unwrap();
    let extensions = cert
        .tbs_certificate
        .extensions
        .as_ref()
        .ok_or_else(|| anyhow!("no extensions"))?;
    for ext in extensions {
        if ext.extn_id == san_oid {
            let san = SubjectAltName::from_der(ext.extn_value.as_bytes())
                .context("parse SubjectAltName")?;
            for name in &san.0 {
                match name {
                    GeneralName::Rfc822Name(email) => return Ok(email.to_string()),
                    GeneralName::UniformResourceIdentifier(uri) => return Ok(uri.to_string()),
                    _ => {}
                }
            }
            bail!("SAN extension has no rfc822Name (email) or URI");
        }
    }
    bail!("no SubjectAltName extension")
}

fn extract_oidc_issuer(cert: &Certificate) -> Result<String> {
    let oid_v2: ObjectIdentifier = OID_OIDC_ISSUER_V2.parse().unwrap();
    let oid_v1: ObjectIdentifier = OID_OIDC_ISSUER_V1.parse().unwrap();
    let extensions = cert
        .tbs_certificate
        .extensions
        .as_ref()
        .ok_or_else(|| anyhow!("no extensions"))?;
    let mut v1 = None;
    for ext in extensions {
        if ext.extn_id == oid_v2 {
            return decode_fulcio_issuer_value(ext.extn_value.as_bytes())
                .map_err(|e| anyhow!("Fulcio issuer v2: {e}"));
        }
        if ext.extn_id == oid_v1 {
            v1 = Some(ext.extn_value.as_bytes().to_vec());
        }
    }
    if let Some(bytes) = v1 {
        return decode_fulcio_issuer_value(&bytes).map_err(|e| anyhow!("Fulcio issuer v1: {e}"));
    }
    bail!("no OIDC issuer (1.3.6.1.4.1.57264.1.8 or .1.1) extension")
}

fn verify_chain(leaf: &Certificate, trust: &TrustConfig) -> Result<()> {
    let intermediate = pem_to_cert(&trust.fulcio_intermediate_pem)?;
    let root = pem_to_cert(&trust.fulcio_root_pem)?;

    check_validity(leaf, "leaf").context("leaf validity window")?;
    check_validity(&intermediate, "intermediate").context("intermediate validity window")?;
    check_validity(&root, "root").context("root validity window")?;

    verify_signed_by_p384(leaf, &intermediate).context("leaf -> intermediate")?;
    verify_signed_by_p384(&intermediate, &root).context("intermediate -> root")?;
    Ok(())
}

fn check_validity(cert: &Certificate, label: &str) -> Result<()> {
    let now = now_unix_secs()
        .ok_or_else(|| anyhow!("clock not synced; cannot check {label} validity"))?;
    let validity = &cert.tbs_certificate.validity;
    let nb = validity.not_before.to_unix_duration().as_secs();
    let na = validity.not_after.to_unix_duration().as_secs();
    if now < nb {
        bail!("{label} cert not yet valid: now={now} notBefore={nb}");
    }
    if now > na {
        bail!("{label} cert expired: now={now} notAfter={na}");
    }
    Ok(())
}

fn pem_to_cert(pem: &[u8]) -> Result<Certificate> {
    let (label, der) =
        x509_cert::der::pem::decode_vec(pem).map_err(|e| anyhow!("decode PEM: {e}"))?;
    if label != "CERTIFICATE" {
        bail!("unexpected PEM label: {label}");
    }
    Certificate::from_der(&der).context("parse PEM-decoded cert DER")
}

fn verify_signed_by_p384(child: &Certificate, parent: &Certificate) -> Result<()> {
    use p384::ecdsa::{signature::Verifier, Signature, VerifyingKey};

    let parent_pubkey_bytes = parent
        .tbs_certificate
        .subject_public_key_info
        .subject_public_key
        .raw_bytes();
    let key =
        VerifyingKey::from_sec1_bytes(parent_pubkey_bytes).context("parse parent P-384 pubkey")?;

    let tbs_der = child
        .tbs_certificate
        .to_der()
        .context("re-serialize TBS to DER")?;
    let sig = Signature::from_der(child.signature.raw_bytes())
        .context("parse child cert ECDSA signature")?;
    key.verify(&tbs_der, &sig)
        .context("ECDSA-P384 verify failed")?;
    Ok(())
}

fn verify_p256_ecdsa(cert: &Certificate, message: &[u8], sig_der: &[u8]) -> Result<()> {
    use p256::ecdsa::{Signature, VerifyingKey};

    let pubkey_bytes = cert
        .tbs_certificate
        .subject_public_key_info
        .subject_public_key
        .raw_bytes();
    let key = VerifyingKey::from_sec1_bytes(pubkey_bytes).context("parse leaf P-256 pubkey")?;
    let sig = Signature::from_der(sig_der).context("parse DSSE ECDSA signature")?;
    key.verify(message, &sig)
        .context("ECDSA-P256 verify failed")?;
    Ok(())
}
