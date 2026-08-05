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

use crate::trust::{RekorPublicKey, TrustConfig, TrustedRekorLog};

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
    #[serde(rename = "timestampVerificationData")]
    timestamp_verification_data: Option<TimestampVerificationData>,
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
    integrated_time: Option<String>,
    #[serde(rename = "inclusionPromise")]
    inclusion_promise: Option<InclusionPromise>,
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
struct TimestampVerificationData {
    #[serde(rename = "rfc3161Timestamps")]
    rfc3161_timestamps: Vec<Rfc3161Timestamp>,
}

#[derive(Deserialize)]
struct Rfc3161Timestamp {
    #[serde(rename = "signedTimestamp")]
    signed_timestamp: String,
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
struct RekorV2Body {
    #[serde(rename = "apiVersion")]
    api_version: String,
    kind: String,
    spec: RekorV2Spec,
}

#[derive(Deserialize)]
struct RekorV2Spec {
    #[serde(rename = "hashedRekordV002")]
    entry: RekorV2Entry,
}

#[derive(Deserialize)]
struct RekorV2Entry {
    data: RekorV2Data,
    signature: RekorV2Signature,
}

#[derive(Deserialize)]
struct RekorV2Data {
    algorithm: String,
    digest: String,
}

#[derive(Deserialize)]
struct RekorV2Signature {
    content: String,
    verifier: RekorV2Verifier,
}

#[derive(Deserialize)]
struct RekorV2Verifier {
    #[serde(rename = "keyDetails")]
    key_details: String,
    #[serde(rename = "x509Certificate")]
    x509_certificate: CertWrapper,
}

#[derive(der::Sequence)]
struct TimeStampResp<'a> {
    status: PkiStatusInfo<'a>,
    time_stamp_token: Option<cms::content_info::ContentInfo>,
}

#[derive(der::Sequence)]
struct PkiStatusInfo<'a> {
    status: u8,
    status_string: Option<der::asn1::SequenceOfVec<der::asn1::Utf8StringRef<'a>>>,
    fail_info: Option<der::asn1::BitStringRef<'a>>,
}

#[derive(der::Sequence)]
struct MessageImprint {
    hash_algorithm: x509_cert::spki::AlgorithmIdentifierOwned,
    hashed_message: der::asn1::OctetString,
}

#[derive(der::Sequence)]
struct Accuracy {
    seconds: Option<u64>,
    #[asn1(context_specific = "0", tag_mode = "IMPLICIT", optional = "true")]
    millis: Option<u16>,
    #[asn1(context_specific = "1", tag_mode = "IMPLICIT", optional = "true")]
    micros: Option<u16>,
}

#[derive(der::Sequence)]
struct TstInfo<'a> {
    version: u8,
    policy: der::asn1::ObjectIdentifier,
    message_imprint: MessageImprint,
    serial_number: der::asn1::UintRef<'a>,
    gen_time: der::asn1::GeneralizedTime,
    accuracy: Option<Accuracy>,
    #[asn1(default = "Default::default")]
    ordering: bool,
    nonce: Option<der::asn1::UintRef<'a>>,
    #[asn1(
        context_specific = "0",
        tag_mode = "EXPLICIT",
        constructed = "true",
        optional = "true"
    )]
    tsa: Option<GeneralName>,
    #[asn1(
        context_specific = "1",
        tag_mode = "IMPLICIT",
        constructed = "true",
        optional = "true"
    )]
    extensions: Option<x509_cert::ext::Extensions>,
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
    let signed_time = verify_transparency_entry(
        bundle.verification_material.tlog_entries.first().unwrap(),
        bundle
            .verification_material
            .timestamp_verification_data
            .as_ref(),
        &cert_der,
        &sig_bytes,
        &payload_bytes,
        &bundle.dsse_envelope.payload_type,
        trust,
    )
    .context("offline Rekor verification")?;
    tracing::info!(signed_time, "ota: transparency evidence verified offline");

    verify_chain_at(&leaf, trust, signed_time).context("cert chain verification")?;
    tracing::info!("ota: cert chain valid at authenticated signing time");

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

fn verify_transparency_entry(
    entry: &TransparencyLogEntry,
    timestamp_data: Option<&TimestampVerificationData>,
    cert_der: &[u8],
    dsse_signature: &[u8],
    payload: &[u8],
    payload_type: &str,
    trust: &TrustConfig,
) -> Result<u64> {
    let log_id = decode_hash("Rekor log ID", &entry.log_id.key_id)?;
    let log = trust
        .rekor_logs
        .iter()
        .find(|candidate| candidate.log_id == log_id)
        .ok_or_else(|| anyhow!("transparency log ID is not in firmware trust set"))?;

    match (
        entry.kind_version.kind.as_str(),
        entry.kind_version.version.as_str(),
    ) {
        ("dsse", "0.0.1") => verify_rekor_v1_entry(entry, cert_der, dsse_signature, payload, log),
        ("hashedrekord", "0.0.2") => verify_rekor_v2_entry(
            entry,
            timestamp_data,
            cert_der,
            dsse_signature,
            payload,
            payload_type,
            log,
            trust,
        ),
        (kind, version) => bail!("unsupported Rekor entry {}/{}", kind, version),
    }
}

fn verify_rekor_v1_entry(
    entry: &TransparencyLogEntry,
    cert_der: &[u8],
    dsse_signature: &[u8],
    payload: &[u8],
    log: &TrustedRekorLog,
) -> Result<u64> {
    let integrated_time = parse_u64(
        "integratedTime",
        entry
            .integrated_time
            .as_deref()
            .ok_or_else(|| anyhow!("Rekor v1 entry has no integrated time"))?,
    )?;
    if integrated_time < log.valid_from
        || log
            .valid_until
            .is_some_and(|valid_until| integrated_time >= valid_until)
    {
        bail!(
            "Rekor integrated time {} is outside trusted key validity",
            integrated_time,
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

    let RekorPublicKey::EcdsaP256(key_der) = &log.public_key else {
        bail!("Rekor v1 entry requires an ECDSA P-256 checkpoint key");
    };
    let rekor_key = p256_verifying_key(key_der)?;
    verify_rekor_set(
        entry,
        integrated_time,
        global_log_index,
        &rekor_key,
        &log.log_id,
    )?;
    verify_rekor_v1_checkpoint_and_inclusion(entry, &canonicalized_body, &rekor_key, log)?;

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

#[allow(clippy::too_many_arguments)]
fn verify_rekor_v2_entry(
    entry: &TransparencyLogEntry,
    timestamp_data: Option<&TimestampVerificationData>,
    cert_der: &[u8],
    dsse_signature: &[u8],
    payload: &[u8],
    payload_type: &str,
    log: &TrustedRekorLog,
    trust: &TrustConfig,
) -> Result<u64> {
    if entry
        .integrated_time
        .as_deref()
        .is_some_and(|value| value != "0")
    {
        bail!("Rekor v2 entry unexpectedly contains an integrated time");
    }
    if entry.inclusion_promise.is_some() {
        bail!("Rekor v2 entry unexpectedly contains an inclusion promise");
    }

    let timestamps = timestamp_data
        .ok_or_else(|| anyhow!("Rekor v2 bundle has no timestamp verification data"))?;
    if timestamps.rfc3161_timestamps.len() != 1 {
        bail!(
            "bundle has {} RFC3161 timestamps, expected exactly 1",
            timestamps.rfc3161_timestamps.len()
        );
    }
    let timestamp_der = b64_std()
        .decode(
            &timestamps
                .rfc3161_timestamps
                .first()
                .unwrap()
                .signed_timestamp,
        )
        .context("base64-decode RFC3161 timestamp")?;
    let signed_time =
        verify_rfc3161_timestamp(&timestamp_der, dsse_signature, &trust.timestamp_authority)?;
    if signed_time < log.valid_from
        || log
            .valid_until
            .is_some_and(|valid_until| signed_time >= valid_until)
    {
        bail!("RFC3161 signing time is outside trusted Rekor shard validity");
    }

    let canonicalized_body = b64_std()
        .decode(&entry.canonicalized_body)
        .context("base64-decode Rekor v2 canonicalized body")?;
    let pae = pae_dsse_v1(payload_type, payload);
    verify_rekor_v2_body(&canonicalized_body, cert_der, dsse_signature, &pae)?;

    let RekorPublicKey::Ed25519(public_key) = &log.public_key else {
        bail!("Rekor v2 entry requires an Ed25519 checkpoint key");
    };
    verify_rekor_v2_checkpoint_and_inclusion(entry, &canonicalized_body, public_key, log)?;
    Ok(signed_time)
}

fn verify_rfc3161_timestamp(
    response_der: &[u8],
    dsse_signature: &[u8],
    trust: &crate::trust::TrustedTimestampAuthority,
) -> Result<u64> {
    use cms::cert::CertificateChoices;
    use cms::content_info::ContentInfo;
    use cms::signed_data::{SignedData, SignerIdentifier};

    let response = TimeStampResp::from_der(response_der).context("parse RFC3161 response")?;
    if response.status.status > 1 {
        bail!(
            "RFC3161 authority returned status {}",
            response.status.status
        );
    }
    let token = response
        .time_stamp_token
        .ok_or_else(|| anyhow!("RFC3161 response has no timestamp token"))?;
    let signed_data_oid: ObjectIdentifier = "1.2.840.113549.1.7.2".parse().unwrap();
    if token.content_type != signed_data_oid {
        bail!("RFC3161 token is not CMS SignedData");
    }
    let signed_data_der = token.content.to_der().context("encode CMS SignedData")?;
    let signed_data = SignedData::from_der(&signed_data_der).context("parse CMS SignedData")?;
    if signed_data.signer_infos.0.len() != 1 {
        bail!(
            "RFC3161 token has {} signers, expected exactly 1",
            signed_data.signer_infos.0.len()
        );
    }
    let signer = signed_data.signer_infos.0.iter().next().unwrap();

    let tst_info_oid: ObjectIdentifier = "1.2.840.113549.1.9.16.1.4".parse().unwrap();
    if signed_data.encap_content_info.econtent_type != tst_info_oid {
        bail!("RFC3161 signed content is not TSTInfo");
    }
    let tst_info_der = signed_data
        .encap_content_info
        .econtent
        .as_ref()
        .ok_or_else(|| anyhow!("RFC3161 token has no TSTInfo content"))?
        .value();
    let tst_info = TstInfo::from_der(tst_info_der).context("parse RFC3161 TSTInfo")?;
    if tst_info.version != 1 {
        bail!("unsupported RFC3161 TSTInfo version {}", tst_info.version);
    }
    let expected_policy: ObjectIdentifier = trust.policy_oid.parse().unwrap();
    if tst_info.policy != expected_policy {
        bail!("RFC3161 timestamp policy is not trusted");
    }
    require_sha256_algorithm(
        &tst_info.message_imprint.hash_algorithm,
        "RFC3161 message imprint",
    )?;
    if tst_info.message_imprint.hashed_message.as_bytes()
        != Sha256::digest(dsse_signature).as_slice()
    {
        bail!("RFC3161 message imprint does not match DSSE signature");
    }

    let signed_time = tst_info.gen_time.to_unix_duration().as_secs();
    if signed_time < trust.valid_from
        || trust
            .valid_until
            .is_some_and(|valid_until| signed_time >= valid_until)
    {
        bail!("RFC3161 timestamp is outside trusted TSA validity");
    }

    let tsa_leaf = Certificate::from_der(&trust.leaf_der).context("parse trusted TSA leaf")?;
    let tsa_root = Certificate::from_der(&trust.root_der).context("parse trusted TSA root")?;
    match &signer.sid {
        SignerIdentifier::IssuerAndSerialNumber(sid)
            if sid.issuer == tsa_leaf.tbs_certificate.issuer
                && sid.serial_number == tsa_leaf.tbs_certificate.serial_number => {}
        _ => bail!("RFC3161 signer identifier does not match trusted TSA leaf"),
    }
    if let Some(certificates) = &signed_data.certificates {
        for certificate in certificates.0.iter() {
            let CertificateChoices::Certificate(certificate) = certificate else {
                bail!("RFC3161 token contains an unsupported certificate type");
            };
            let der = certificate.to_der().context("encode RFC3161 certificate")?;
            if der != trust.leaf_der && der != trust.root_der {
                bail!("RFC3161 token contains an untrusted certificate");
            }
        }
    }

    check_validity_at(&tsa_leaf, "TSA leaf", signed_time)?;
    check_validity_at(&tsa_root, "TSA root", signed_time)?;
    verify_signed_by_p384(&tsa_leaf, &tsa_root).context("TSA leaf -> root")?;
    verify_cms_signed_attributes(signer, &signed_data, tst_info_der, &tsa_leaf)?;
    Ok(signed_time)
}

fn verify_cms_signed_attributes(
    signer: &cms::signed_data::SignerInfo,
    signed_data: &cms::signed_data::SignedData,
    content: &[u8],
    tsa_leaf: &Certificate,
) -> Result<()> {
    use p384::ecdsa::signature::hazmat::PrehashVerifier;

    require_sha256_algorithm(&signer.digest_alg, "CMS signer digest")?;
    if signed_data.digest_algorithms.len() != 1 {
        bail!("CMS SignedData must declare exactly one digest algorithm");
    }
    require_sha256_algorithm(
        signed_data.digest_algorithms.iter().next().unwrap(),
        "CMS SignedData digest",
    )?;

    let attributes = signer
        .signed_attrs
        .as_ref()
        .ok_or_else(|| anyhow!("RFC3161 signer has no signed attributes"))?;
    let content_type_oid: ObjectIdentifier = "1.2.840.113549.1.9.3".parse().unwrap();
    let message_digest_oid: ObjectIdentifier = "1.2.840.113549.1.9.4".parse().unwrap();
    let tst_info_oid: ObjectIdentifier = "1.2.840.113549.1.9.16.1.4".parse().unwrap();

    let content_type = single_attribute_value(attributes, content_type_oid)?
        .decode_as::<ObjectIdentifier>()
        .context("decode CMS contentType attribute")?;
    if content_type != tst_info_oid {
        bail!("CMS contentType attribute is not TSTInfo");
    }
    let message_digest = single_attribute_value(attributes, message_digest_oid)?
        .decode_as::<der::asn1::OctetString>()
        .context("decode CMS messageDigest attribute")?;
    if message_digest.as_bytes() != Sha256::digest(content).as_slice() {
        bail!("CMS messageDigest does not match TSTInfo");
    }

    let signed_attributes_der = attributes
        .to_der()
        .context("encode CMS signed attributes")?;
    let signature = p384::ecdsa::Signature::from_der(signer.signature.as_bytes())
        .context("parse RFC3161 CMS signature")?;
    let public_key_bytes = tsa_leaf
        .tbs_certificate
        .subject_public_key_info
        .subject_public_key
        .raw_bytes();
    let key = p384::ecdsa::VerifyingKey::from_sec1_bytes(public_key_bytes)
        .context("parse TSA P-384 public key")?;

    let ecdsa_sha256_oid: ObjectIdentifier = "1.2.840.10045.4.3.2".parse().unwrap();
    if signer.signature_algorithm.oid != ecdsa_sha256_oid {
        bail!("unsupported RFC3161 CMS signature algorithm");
    }
    let digest = Sha256::digest(&signed_attributes_der);
    key.verify_prehash(digest.as_slice(), &signature)
        .context("verify RFC3161 CMS signature")
}

fn single_attribute_value(
    attributes: &x509_cert::attr::Attributes,
    oid: ObjectIdentifier,
) -> Result<&der::Any> {
    let mut matches = attributes.iter().filter(|attribute| attribute.oid == oid);
    let attribute = matches
        .next()
        .ok_or_else(|| anyhow!("required CMS signed attribute is missing"))?;
    if matches.next().is_some() || attribute.values.len() != 1 {
        bail!("CMS signed attribute must occur exactly once with one value");
    }
    Ok(attribute.values.iter().next().unwrap())
}

fn require_sha256_algorithm(
    algorithm: &x509_cert::spki::AlgorithmIdentifierOwned,
    label: &str,
) -> Result<()> {
    let sha256_oid: ObjectIdentifier = "2.16.840.1.101.3.4.2.1".parse().unwrap();
    if algorithm.oid != sha256_oid {
        bail!("{} is not SHA-256", label);
    }
    Ok(())
}

fn verify_rekor_v2_body(
    canonicalized_body: &[u8],
    cert_der: &[u8],
    dsse_signature: &[u8],
    pae: &[u8],
) -> Result<()> {
    let body: RekorV2Body =
        serde_json::from_slice(canonicalized_body).context("parse Rekor v2 hashedrekord body")?;
    if body.kind != "hashedrekord" || body.api_version != "0.0.2" {
        bail!(
            "unsupported Rekor v2 body {}/{}",
            body.kind,
            body.api_version
        );
    }
    if body.spec.entry.data.algorithm != "SHA2_256" {
        bail!(
            "unsupported Rekor v2 digest algorithm: {}",
            body.spec.entry.data.algorithm
        );
    }
    let logged_digest = b64_std()
        .decode(&body.spec.entry.data.digest)
        .context("base64-decode Rekor v2 PAE digest")?;
    if logged_digest.as_slice() != Sha256::digest(pae).as_slice() {
        bail!("Rekor v2 digest does not match DSSE PAE");
    }
    let logged_signature = b64_std()
        .decode(&body.spec.entry.signature.content)
        .context("base64-decode Rekor v2 signature")?;
    if logged_signature != dsse_signature {
        bail!("Rekor v2 signature does not match DSSE envelope");
    }
    if body.spec.entry.signature.verifier.key_details != "PKIX_ECDSA_P256_SHA_256" {
        bail!("unsupported Rekor v2 bundle verifier key details");
    }
    let logged_cert = b64_std()
        .decode(
            &body
                .spec
                .entry
                .signature
                .verifier
                .x509_certificate
                .raw_bytes,
        )
        .context("base64-decode Rekor v2 certificate")?;
    if logged_cert != cert_der {
        bail!("Rekor v2 certificate does not match bundle certificate");
    }
    Ok(())
}

fn verify_rekor_v2_checkpoint_and_inclusion(
    entry: &TransparencyLogEntry,
    canonicalized_body: &[u8],
    public_key: &[u8; 32],
    log: &TrustedRekorLog,
) -> Result<()> {
    use ed25519_dalek::Verifier as _;

    let envelope = &entry.inclusion_proof.checkpoint.envelope;
    let (note_text, signatures) = envelope
        .rsplit_once("\n\n")
        .ok_or_else(|| anyhow!("malformed Rekor v2 checkpoint note"))?;
    let mut lines = note_text.lines();
    let origin = lines
        .next()
        .ok_or_else(|| anyhow!("Rekor v2 checkpoint has no origin"))?;
    if origin != log.checkpoint_origin {
        bail!("Rekor v2 checkpoint origin is not trusted");
    }
    let tree_size = lines
        .next()
        .ok_or_else(|| anyhow!("Rekor v2 checkpoint has no tree size"))?
        .parse::<u64>()
        .context("parse Rekor v2 checkpoint tree size")?;
    let root_hash = decode_hash(
        "Rekor v2 checkpoint root",
        lines
            .next()
            .ok_or_else(|| anyhow!("Rekor v2 checkpoint has no root hash"))?,
    )?;

    let signature_prefix = format!("— {} ", log.checkpoint_origin);
    let encoded_signature = signatures
        .lines()
        .find_map(|line| line.strip_prefix(&signature_prefix))
        .ok_or_else(|| anyhow!("Rekor v2 checkpoint has no trusted log signature"))?;
    let signature_with_hint = b64_std()
        .decode(encoded_signature)
        .context("base64-decode Rekor v2 checkpoint signature")?;
    if signature_with_hint.len() != 68 || signature_with_hint[..4] != log.log_id[..4] {
        bail!("Rekor v2 checkpoint key hint does not match trusted log");
    }
    let signature = ed25519_dalek::Signature::try_from(&signature_with_hint[4..])
        .map_err(|_| anyhow!("parse Rekor v2 Ed25519 checkpoint signature"))?;
    let key = ed25519_dalek::VerifyingKey::from_bytes(public_key)
        .map_err(|_| anyhow!("parse trusted Rekor v2 Ed25519 key"))?;
    let signed_note = format!("{}\n", note_text);
    key.verify_strict(signed_note.as_bytes(), &signature)
        .context("verify Rekor v2 checkpoint signature")?;

    let log_index = parse_u64("logIndex", &entry.log_index)?;
    verify_inclusion_proof(
        canonicalized_body,
        log_index,
        tree_size,
        &entry.inclusion_proof.hashes,
        &root_hash,
    )
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
        .decode(
            &entry
                .inclusion_promise
                .as_ref()
                .ok_or_else(|| anyhow!("Rekor v1 entry has no inclusion promise"))?
                .signed_entry_timestamp,
        )
        .context("base64-decode Rekor SET")?;
    let signature =
        p256::ecdsa::Signature::from_der(&signature_bytes).context("parse Rekor SET signature")?;
    key.verify(payload.as_bytes(), &signature)
        .context("verify Rekor Signed Entry Timestamp")
}

fn verify_rekor_v1_checkpoint_and_inclusion(
    entry: &TransparencyLogEntry,
    canonicalized_body: &[u8],
    key: &p256::ecdsa::VerifyingKey,
    log: &TrustedRekorLog,
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

    verify_rekor_checkpoint(&proof.checkpoint.envelope, tree_size, &root_hash, key, log)?;
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
    log: &TrustedRekorLog,
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
    let expected_origin_prefix = format!("{} - ", log.checkpoint_origin);
    if !origin_line.starts_with(&expected_origin_prefix) {
        bail!("checkpoint origin is not trusted");
    }
    if tree_size != expected_tree_size {
        bail!("checkpoint tree size does not match inclusion proof");
    }
    if decode_hash("checkpoint root hash", root_hash)? != *expected_root_hash {
        bail!("checkpoint root hash does not match inclusion proof");
    }

    let signature_prefix = format!("— {} ", log.checkpoint_origin);
    let encoded_signature = signatures
        .lines()
        .find_map(|line| line.strip_prefix(&signature_prefix))
        .ok_or_else(|| anyhow!("checkpoint has no signature from trusted origin"))?;
    let signature_with_hint = b64_std()
        .decode(encoded_signature)
        .context("base64-decode checkpoint signature")?;
    if signature_with_hint.len() <= 4 || signature_with_hint[..4] != log.log_id[..4] {
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

fn p256_verifying_key(key_der: &[u8]) -> Result<p256::ecdsa::VerifyingKey> {
    use p256::pkcs8::DecodePublicKey;
    p256::ecdsa::VerifyingKey::from_public_key_der(key_der)
        .context("parse trusted Rekor P-256 public key")
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
