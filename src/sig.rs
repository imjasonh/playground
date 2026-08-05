//! Cosign Sigstore Bundle (v0.3) verification for OTA artifacts.
//!
//! Phase 4a scope: verify the DSSE signature, the cert chain to the
//! bundled Sigstore intermediate (and root), the cert's identity
//! against `trust::TRUSTED_IDENTITIES`, the DSSE `payloadType`, and
//! each cert's notBefore/notAfter window against the device wall
//! clock. Also verifies the in-toto Statement payload binds to our
//! manifest digest.
//!
//! Phase 4b will add the Rekor SET (transparency log) check and use
//! the Rekor-attested signing time for the validity check (instead of
//! `now`), which closes the post-expiry-but-pre-attestation window.

use anyhow::{anyhow, bail, Context, Result};
use base64::Engine;
use p256::ecdsa::signature::Verifier as _;
use serde::Deserialize;
use x509_cert::der::{oid::ObjectIdentifier, Decode, Encode};
use x509_cert::ext::pkix::name::GeneralName;
use x509_cert::ext::pkix::SubjectAltName;
use x509_cert::Certificate;

use crate::gcp_auth::now_unix_secs;
use crate::trust::TrustConfig;

/// DSSE payload type cosign emits for OCI artifact signatures. We
/// reject anything else: a different payload type means the bundle
/// signs something other than an in-toto Statement, and our digest
/// binding check below would be against the wrong shape of payload.
const DSSE_INTOTO_PAYLOAD_TYPE: &str = "application/vnd.in-toto+json";

// X.509 OID for Sigstore's "OIDC issuer (legacy)" extension. The value
// is the raw issuer URL bytes (not DER-wrapped). Fulcio also emits
// .1.8 (a UTF8String DER wrapper); we use the legacy form because it's
// trivial to parse.
const OID_OIDC_ISSUER_V1: &str = "1.3.6.1.4.1.57264.1.1";
// Standard SAN OID
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

    let identity = extract_san_identity(&leaf).context("extract SAN identity")?;
    let issuer = extract_oidc_issuer_v1(&leaf).context("extract OIDC issuer")?;
    if !trust
        .identities
        .iter()
        .any(|t| t.identity == identity && t.issuer == issuer)
    {
        bail!("untrusted identity: {} (issuer {})", identity, issuer);
    }
    tracing::info!(identity = %identity, issuer = %issuer, "ota: signer identity OK");

    verify_chain(&leaf, trust).context("cert chain verification")?;
    tracing::info!("ota: cert chain to Sigstore root OK");

    // Use the first DSSE signature (cosign emits exactly one). `.first()`
    // rather than `[0]` so a malformed bundle returns an error instead
    // of panicking the OTA thread.
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
    tracing::info!("ota: DSSE signature verified");

    let stmt: InTotoStatement = serde_json::from_slice(&payload_bytes)
        .context("parse in-toto Statement payload")?;
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
            "in-toto subject digest mismatch: signed={} expected={}",
            actual_digest_hex,
            expected_manifest_digest_hex
        );
    }
    tracing::info!(
        digest = %actual_digest_hex,
        "ota: in-toto subject binds to our manifest digest",
    );

    Ok(())
}

fn b64_std() -> base64::engine::GeneralPurpose {
    base64::engine::general_purpose::STANDARD
}

/// DSSE Pre-Authentication Encoding (https://github.com/secure-systems-lab/dsse).
/// PAE("DSSEv1", payloadType, payload) = "DSSEv1 <len(t)> <t> <len(p)> <p>"
fn pae_dsse_v1(payload_type: &str, payload: &[u8]) -> Vec<u8> {
    let mut out = Vec::with_capacity(64 + payload_type.len() + payload.len());
    out.extend_from_slice(b"DSSEv1 ");
    out.extend_from_slice(payload_type.len().to_string().as_bytes());
    out.push(b' ');
    out.extend_from_slice(payload_type.as_bytes());
    out.push(b' ');
    out.extend_from_slice(payload.len().to_string().as_bytes());
    out.push(b' ');
    out.extend_from_slice(payload);
    out
}

/// Extract the signer identity from a Fulcio cert's SAN extension.
/// Returns the email (for OIDC issuers like accounts.google.com) or the
/// URI (for workflow-based issuers like GitHub Actions, where the URI
/// is e.g. `https://github.com/<owner>/<repo>/.github/workflows/<wf>.yml@<ref>`).
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

fn extract_oidc_issuer_v1(cert: &Certificate) -> Result<String> {
    let oid: ObjectIdentifier = OID_OIDC_ISSUER_V1.parse().unwrap();
    let extensions = cert
        .tbs_certificate
        .extensions
        .as_ref()
        .ok_or_else(|| anyhow!("no extensions"))?;
    for ext in extensions {
        if ext.extn_id == oid {
            let bytes = ext.extn_value.as_bytes();
            return String::from_utf8(bytes.to_vec()).context("issuer is not UTF-8");
        }
    }
    bail!("no OIDC issuer (1.3.6.1.4.1.57264.1.1) extension")
}

/// Verify leaf was signed by the provisioned Sigstore intermediate, and
/// that the provisioned intermediate was signed by the provisioned root.
/// Also checks each cert's `notBefore` / `notAfter` window against the
/// device's wall clock — without this, an exfiltrated Fulcio leaf cert
/// (10-min validity by design) would remain accepted indefinitely from
/// the verifier's perspective. Phase 4b will tighten this further by
/// using the Rekor SET's signing time instead of `now`, which closes
/// the post-expiry-but-pre-Rekor-attestation window.
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

/// Reject certs whose `notBefore`/`notAfter` window doesn't include
/// the current wall-clock time. Requires NTP sync; if the clock isn't
/// synced (caller should always have triggered SNTP before getting
/// here, but the OTA thread can in principle race with sync) we refuse
/// to verify rather than fall back to "always valid".
fn check_validity(cert: &Certificate, label: &str) -> Result<()> {
    let now =
        now_unix_secs().ok_or_else(|| anyhow!("clock not synced; cannot check {} validity", label))?;
    let validity = &cert.tbs_certificate.validity;
    let nb = validity.not_before.to_unix_duration().as_secs();
    let na = validity.not_after.to_unix_duration().as_secs();
    if now < nb {
        bail!("{} cert not yet valid: now={} notBefore={}", label, now, nb);
    }
    if now > na {
        bail!("{} cert expired: now={} notAfter={}", label, now, na);
    }
    Ok(())
}

fn pem_to_cert(pem: &[u8]) -> Result<Certificate> {
    let (label, der) =
        x509_cert::der::pem::decode_vec(pem).map_err(|e| anyhow!("decode PEM: {}", e))?;
    if label != "CERTIFICATE" {
        bail!("unexpected PEM label: {}", label);
    }
    Certificate::from_der(&der).context("parse PEM-decoded cert DER")
}

/// Verify `child.signature` is a valid P-384 ECDSA-SHA384 signature
/// over `child.tbs_certificate` made with `parent`'s public key.
fn verify_signed_by_p384(child: &Certificate, parent: &Certificate) -> Result<()> {
    use p384::ecdsa::{signature::Verifier, Signature, VerifyingKey};

    let parent_pubkey_bytes = parent
        .tbs_certificate
        .subject_public_key_info
        .subject_public_key
        .raw_bytes();
    let key = VerifyingKey::from_sec1_bytes(parent_pubkey_bytes)
        .context("parse parent P-384 pubkey")?;

    let tbs_der = child
        .tbs_certificate
        .to_der()
        .context("re-serialize TBS to DER")?;
    let sig = Signature::from_der(child.signature.raw_bytes())
        .context("parse child cert ECDSA signature")?;

    // p384's Verifier hashes with SHA-384 internally for ECDSA-P384.
    key.verify(&tbs_der, &sig)
        .context("ECDSA-P384 verify failed")?;
    Ok(())
}

/// Verify a P-256 ECDSA signature using the leaf cert's public key.
fn verify_p256_ecdsa(cert: &Certificate, message: &[u8], sig_der: &[u8]) -> Result<()> {
    use p256::ecdsa::{Signature, VerifyingKey};

    let pubkey_bytes = cert
        .tbs_certificate
        .subject_public_key_info
        .subject_public_key
        .raw_bytes();
    let key = VerifyingKey::from_sec1_bytes(pubkey_bytes)
        .context("parse leaf P-256 pubkey")?;
    let sig = Signature::from_der(sig_der).context("parse DSSE ECDSA signature")?;
    key.verify(message, &sig).context("ECDSA-P256 verify failed")?;
    Ok(())
}

