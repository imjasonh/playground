//! Cosign Sigstore Bundle (v0.3) verification for OTA artifacts.
//!
//! Verification is fully offline: verify the Rekor Signed Entry Timestamp,
//! signed checkpoint, RFC 6962 inclusion proof, and bundle↔log-body binding
//! using a provisioned Rekor public key. The authenticated Rekor integrated
//! time is then used for Fulcio certificate validity, so devices do not need
//! to contact Rekor—or have a current wall clock—to accept an older bundle.
//! Finally verify signer identity, the Fulcio chain, DSSE signature and
//! payload type, and the in-toto manifest-digest binding.

use anyhow::{Context, Result, anyhow, bail};
use base64::Engine;
use p256::ecdsa::signature::Verifier as _;
use serde::Deserialize;
use sha2::{Digest, Sha256};
use x509_cert::Certificate;
use x509_cert::der::{Decode, Encode, oid::ObjectIdentifier};
use x509_cert::ext::pkix::SubjectAltName;
use x509_cert::ext::pkix::name::GeneralName;

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
    #[serde(rename = "tlogEntries")]
    tlog_entries: Vec<TransparencyLogEntry>,
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
struct TransparencyLogEntry {
    #[serde(rename = "logIndex")]
    log_index: String,
    #[serde(rename = "logId")]
    log_id: LogId,
    #[serde(rename = "kindVersion")]
    kind_version: KindVersion,
    #[serde(rename = "integratedTime")]
    integrated_time: String,
    #[serde(rename = "inclusionPromise")]
    inclusion_promise: InclusionPromise,
    #[serde(rename = "inclusionProof")]
    inclusion_proof: InclusionProof,
    #[serde(rename = "canonicalizedBody")]
    canonicalized_body: String,
}

#[derive(Deserialize)]
struct LogId {
    #[serde(rename = "keyId")]
    key_id: String,
}

#[derive(Deserialize)]
struct KindVersion {
    kind: String,
    version: String,
}

#[derive(Deserialize)]
struct InclusionPromise {
    #[serde(rename = "signedEntryTimestamp")]
    signed_entry_timestamp: String,
}

#[derive(Deserialize)]
struct InclusionProof {
    #[serde(rename = "logIndex")]
    log_index: String,
    #[serde(rename = "rootHash")]
    root_hash: String,
    #[serde(rename = "treeSize")]
    tree_size: String,
    hashes: Vec<String>,
    checkpoint: Checkpoint,
}

#[derive(Deserialize)]
struct Checkpoint {
    envelope: String,
}

#[derive(Deserialize)]
struct RekorDsseBody {
    #[serde(rename = "apiVersion")]
    api_version: String,
    kind: String,
    spec: RekorDsseSpec,
}

#[derive(Deserialize)]
struct RekorDsseSpec {
    #[serde(rename = "payloadHash")]
    payload_hash: RekorHash,
    signatures: Vec<RekorSignature>,
}

#[derive(Deserialize)]
struct RekorHash {
    algorithm: String,
    value: String,
}

#[derive(Deserialize)]
struct RekorSignature {
    signature: String,
    verifier: String,
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

    if bundle.dsse_envelope.signatures.len() != 1 {
        bail!(
            "DSSE envelope has {} signatures, expected exactly 1",
            bundle.dsse_envelope.signatures.len()
        );
    }
    let dsse_sig = bundle.dsse_envelope.signatures.first().unwrap();
    let sig_bytes = b64_std()
        .decode(&dsse_sig.sig)
        .context("base64-decode DSSE signature")?;
    let payload_bytes = b64_std()
        .decode(&bundle.dsse_envelope.payload)
        .context("base64-decode DSSE payload")?;

    if bundle.verification_material.tlog_entries.len() != 1 {
        bail!(
            "bundle has {} transparency-log entries, expected exactly 1",
            bundle.verification_material.tlog_entries.len()
        );
    }
    let integrated_time = verify_rekor_entry(
        bundle.verification_material.tlog_entries.first().unwrap(),
        &cert_der,
        &sig_bytes,
        &payload_bytes,
        trust,
    )
    .context("offline Rekor verification")?;
    tracing::info!(integrated_time, "ota: Rekor evidence verified offline");

    verify_chain_at(&leaf, trust, integrated_time).context("cert chain verification")?;
    tracing::info!("ota: cert chain valid at Rekor integrated time");

    let pae = pae_dsse_v1(&bundle.dsse_envelope.payload_type, &payload_bytes);

    verify_p256_ecdsa(&leaf, &pae, &sig_bytes).context("DSSE signature verify")?;
    tracing::info!("ota: DSSE signature verified");

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

fn verify_rekor_entry(
    entry: &TransparencyLogEntry,
    cert_der: &[u8],
    dsse_signature: &[u8],
    payload: &[u8],
    trust: &TrustConfig,
) -> Result<u64> {
    if entry.kind_version.kind != "dsse" || entry.kind_version.version != "0.0.1" {
        bail!(
            "unsupported Rekor entry {}/{}",
            entry.kind_version.kind,
            entry.kind_version.version,
        );
    }

    let log_id = b64_std()
        .decode(&entry.log_id.key_id)
        .context("base64-decode Rekor log ID")?;
    if log_id.as_slice() != trust.rekor_log_id {
        bail!("Rekor log ID does not match provisioned public key");
    }

    let integrated_time = parse_u64("integratedTime", &entry.integrated_time)?;
    if integrated_time < trust.rekor_valid_from {
        bail!(
            "Rekor integrated time {} predates trusted key validity {}",
            integrated_time,
            trust.rekor_valid_from,
        );
    }
    let global_log_index = parse_u64("logIndex", &entry.log_index)?;

    let canonicalized_body = b64_std()
        .decode(&entry.canonicalized_body)
        .context("base64-decode Rekor canonicalized body")?;
    verify_rekor_body(
        &canonicalized_body,
        &entry.kind_version,
        cert_der,
        dsse_signature,
        payload,
    )?;

    let rekor_key = rekor_verifying_key(trust)?;
    verify_rekor_set(
        entry,
        integrated_time,
        global_log_index,
        &rekor_key,
        &trust.rekor_log_id,
    )?;
    verify_rekor_checkpoint_and_inclusion(entry, &canonicalized_body, &rekor_key, trust)?;

    Ok(integrated_time)
}

fn verify_rekor_body(
    canonicalized_body: &[u8],
    kind_version: &KindVersion,
    cert_der: &[u8],
    dsse_signature: &[u8],
    payload: &[u8],
) -> Result<()> {
    let body: RekorDsseBody =
        serde_json::from_slice(canonicalized_body).context("parse Rekor DSSE body")?;
    if body.kind != kind_version.kind || body.api_version != kind_version.version {
        bail!("Rekor kind/version metadata does not match canonicalized body");
    }
    if body.spec.payload_hash.algorithm != "sha256" {
        bail!(
            "unsupported Rekor payload hash algorithm: {}",
            body.spec.payload_hash.algorithm
        );
    }
    let expected_payload_hash = hex::encode(Sha256::digest(payload));
    if body.spec.payload_hash.value != expected_payload_hash {
        bail!("Rekor payload hash does not match DSSE payload");
    }
    if body.spec.signatures.len() != 1 {
        bail!(
            "Rekor body has {} signatures, expected exactly 1",
            body.spec.signatures.len()
        );
    }
    let signature = body.spec.signatures.first().unwrap();
    let logged_signature = b64_std()
        .decode(&signature.signature)
        .context("base64-decode Rekor DSSE signature")?;
    if logged_signature != dsse_signature {
        bail!("Rekor signature does not match DSSE envelope");
    }

    let verifier_pem = b64_std()
        .decode(&signature.verifier)
        .context("base64-decode Rekor verifier")?;
    let (label, logged_cert_der) = x509_cert::der::pem::decode_vec(&verifier_pem)
        .map_err(|error| anyhow!("decode Rekor verifier PEM: {}", error))?;
    if label != "CERTIFICATE" || logged_cert_der != cert_der {
        bail!("Rekor verifier does not match bundle certificate");
    }
    Ok(())
}

fn verify_rekor_set(
    entry: &TransparencyLogEntry,
    integrated_time: u64,
    log_index: u64,
    key: &p256::ecdsa::VerifyingKey,
    log_id: &[u8; 32],
) -> Result<()> {
    // RFC 8785 canonical JSON. These four keys are already in lexical order,
    // and every interpolated value is base64, lowercase hex, or an integer.
    let payload = format!(
        "{{\"body\":\"{}\",\"integratedTime\":{},\"logID\":\"{}\",\"logIndex\":{}}}",
        entry.canonicalized_body,
        integrated_time,
        hex::encode(log_id),
        log_index,
    );
    let signature_bytes = b64_std()
        .decode(&entry.inclusion_promise.signed_entry_timestamp)
        .context("base64-decode Rekor SET")?;
    let signature =
        p256::ecdsa::Signature::from_der(&signature_bytes).context("parse Rekor SET signature")?;
    key.verify(payload.as_bytes(), &signature)
        .context("verify Rekor Signed Entry Timestamp")
}

fn verify_rekor_checkpoint_and_inclusion(
    entry: &TransparencyLogEntry,
    canonicalized_body: &[u8],
    key: &p256::ecdsa::VerifyingKey,
    trust: &TrustConfig,
) -> Result<()> {
    let proof = &entry.inclusion_proof;
    let log_index = parse_u64("inclusionProof.logIndex", &proof.log_index)?;
    let tree_size = parse_u64("inclusionProof.treeSize", &proof.tree_size)?;
    if tree_size == 0 || log_index >= tree_size {
        bail!(
            "invalid Rekor inclusion coordinates: index={} tree_size={}",
            log_index,
            tree_size,
        );
    }
    if proof.hashes.len() > 64 {
        bail!("Rekor inclusion proof has too many hashes");
    }
    let root_hash = decode_hash("inclusionProof.rootHash", &proof.root_hash)?;

    verify_rekor_checkpoint(
        &proof.checkpoint.envelope,
        tree_size,
        &root_hash,
        key,
        trust,
    )?;
    verify_inclusion_proof(
        canonicalized_body,
        log_index,
        tree_size,
        &proof.hashes,
        &root_hash,
    )
}

fn verify_rekor_checkpoint(
    envelope: &str,
    expected_tree_size: u64,
    expected_root_hash: &[u8; 32],
    key: &p256::ecdsa::VerifyingKey,
    trust: &TrustConfig,
) -> Result<()> {
    let (note_text, signatures) = envelope
        .split_once("\n\n")
        .ok_or_else(|| anyhow!("malformed Rekor checkpoint note"))?;
    let mut lines = note_text.lines();
    let origin_line = lines
        .next()
        .ok_or_else(|| anyhow!("checkpoint has no origin"))?;
    let tree_size = lines
        .next()
        .ok_or_else(|| anyhow!("checkpoint has no tree size"))?
        .parse::<u64>()
        .context("parse checkpoint tree size")?;
    let root_hash = lines
        .next()
        .ok_or_else(|| anyhow!("checkpoint has no root hash"))?;
    if lines.next().is_some() {
        bail!("checkpoint note has unexpected fields");
    }
    let expected_origin_prefix = format!("{} - ", trust.rekor_checkpoint_origin);
    if !origin_line.starts_with(&expected_origin_prefix) {
        bail!("checkpoint origin is not trusted");
    }
    if tree_size != expected_tree_size {
        bail!("checkpoint tree size does not match inclusion proof");
    }
    if decode_hash("checkpoint root hash", root_hash)? != *expected_root_hash {
        bail!("checkpoint root hash does not match inclusion proof");
    }

    let signature_prefix = format!("— {} ", trust.rekor_checkpoint_origin);
    let encoded_signature = signatures
        .lines()
        .find_map(|line| line.strip_prefix(&signature_prefix))
        .ok_or_else(|| anyhow!("checkpoint has no signature from trusted origin"))?;
    let signature_with_hint = b64_std()
        .decode(encoded_signature)
        .context("base64-decode checkpoint signature")?;
    if signature_with_hint.len() <= 4 || signature_with_hint[..4] != trust.rekor_log_id[..4] {
        bail!("checkpoint signature key hint does not match Rekor key");
    }
    let signature = p256::ecdsa::Signature::from_der(&signature_with_hint[4..])
        .context("parse checkpoint signature")?;
    let signed_note = format!("{}\n", note_text);
    key.verify(signed_note.as_bytes(), &signature)
        .context("verify Rekor checkpoint signature")
}

fn verify_inclusion_proof(
    canonicalized_body: &[u8],
    log_index: u64,
    tree_size: u64,
    hashes: &[String],
    expected_root: &[u8; 32],
) -> Result<()> {
    let mut current = hash_leaf(canonicalized_body);
    let mut node = log_index;
    let mut last = tree_size - 1;

    for encoded_hash in hashes {
        if last == 0 {
            bail!("Rekor inclusion proof has extra hashes");
        }
        let sibling = decode_hash("inclusion proof hash", encoded_hash)?;
        if node == last || node & 1 == 1 {
            current = hash_children(&sibling, &current);
            while node != 0 && node & 1 == 0 {
                node >>= 1;
                last >>= 1;
            }
        } else {
            current = hash_children(&current, &sibling);
        }
        node >>= 1;
        last >>= 1;
    }

    if last != 0 || current != *expected_root {
        bail!("Rekor inclusion proof does not match checkpoint root");
    }
    Ok(())
}

fn hash_leaf(body: &[u8]) -> [u8; 32] {
    let mut hasher = Sha256::new();
    hasher.update([0x00]);
    hasher.update(body);
    hasher.finalize().into()
}

fn hash_children(left: &[u8; 32], right: &[u8; 32]) -> [u8; 32] {
    let mut hasher = Sha256::new();
    hasher.update([0x01]);
    hasher.update(left);
    hasher.update(right);
    hasher.finalize().into()
}

fn decode_hash(label: &str, encoded: &str) -> Result<[u8; 32]> {
    let decoded = b64_std()
        .decode(encoded)
        .with_context(|| format!("base64-decode {}", label))?;
    decoded
        .try_into()
        .map_err(|value: Vec<u8>| anyhow!("{} must be 32 bytes, got {}", label, value.len()))
}

fn parse_u64(label: &str, value: &str) -> Result<u64> {
    value
        .parse()
        .with_context(|| format!("parse {} as u64", label))
}

fn rekor_verifying_key(trust: &TrustConfig) -> Result<p256::ecdsa::VerifyingKey> {
    use p256::pkcs8::DecodePublicKey;
    p256::ecdsa::VerifyingKey::from_public_key_der(&trust.rekor_public_key_der)
        .context("parse provisioned Rekor P-256 public key")
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

/// Verify the Fulcio chain and require every certificate to be valid at the
/// Rekor integrated time authenticated by the bundle's SET.
fn verify_chain_at(leaf: &Certificate, trust: &TrustConfig, integrated_time: u64) -> Result<()> {
    let intermediate = pem_to_cert(&trust.fulcio_intermediate_pem)?;
    let root = pem_to_cert(&trust.fulcio_root_pem)?;

    check_validity_at(leaf, "leaf", integrated_time).context("leaf validity window")?;
    check_validity_at(&intermediate, "intermediate", integrated_time)
        .context("intermediate validity window")?;
    check_validity_at(&root, "root", integrated_time).context("root validity window")?;

    verify_signed_by_p384(leaf, &intermediate).context("leaf -> intermediate")?;
    verify_signed_by_p384(&intermediate, &root).context("intermediate -> root")?;
    Ok(())
}

fn check_validity_at(cert: &Certificate, label: &str, integrated_time: u64) -> Result<()> {
    let validity = &cert.tbs_certificate.validity;
    let nb = validity.not_before.to_unix_duration().as_secs();
    let na = validity.not_after.to_unix_duration().as_secs();
    if integrated_time < nb {
        bail!(
            "{} cert not yet valid at Rekor time: integratedTime={} notBefore={}",
            label,
            integrated_time,
            nb
        );
    }
    if integrated_time > na {
        bail!(
            "{} cert expired at Rekor time: integratedTime={} notAfter={}",
            label,
            integrated_time,
            na
        );
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
    use p384::ecdsa::{Signature, VerifyingKey, signature::Verifier};

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
    let key = VerifyingKey::from_sec1_bytes(pubkey_bytes).context("parse leaf P-256 pubkey")?;
    let sig = Signature::from_der(sig_der).context("parse DSSE ECDSA signature")?;
    key.verify(message, &sig)
        .context("ECDSA-P256 verify failed")?;
    Ok(())
}
