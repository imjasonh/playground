//! Converts a Sigstore bundle (JSON, v0.3) into the device's bundle
//! container.

use base64::Engine;
use base64::engine::general_purpose::STANDARD;
use serde_json::Value;

fn b64(v: &Value, what: &str) -> Result<Vec<u8>, String> {
    let text = v.as_str().ok_or_else(|| format!("missing {what}"))?;
    let compact: String = text.chars().filter(|c| !c.is_ascii_whitespace()).collect();
    STANDARD.decode(compact).map_err(|e| format!("{what}: {e}"))
}

/// Builds the container from `bundle_json`. Fails if the bundle isn't in
/// the c3-boot profile: a v0.3 bundle with a message signature, a leaf
/// certificate, exactly one Rekor v2 `hashedrekord` entry with an inclusion
/// proof, and exactly one RFC 3161 timestamp. When `image_digest` is given,
/// the bundle's message digest must equal it.
pub fn from_bundle_json(
    bundle_json: &str,
    image_digest: Option<&[u8; 32]>,
) -> Result<Vec<u8>, String> {
    let b: Value = serde_json::from_str(bundle_json).map_err(|e| e.to_string())?;
    let media = b["mediaType"].as_str().unwrap_or("");
    if !media.starts_with("application/vnd.dev.sigstore.bundle") || !media.contains("0.3") {
        return Err(format!("unsupported bundle media type {media:?}"));
    }
    let sig = &b["messageSignature"];
    if sig.is_null() {
        return Err("bundle has no messageSignature".into());
    }
    if sig["messageDigest"]["algorithm"].as_str() != Some("SHA2_256") {
        return Err("message digest isn't SHA-256".into());
    }
    let digest = b64(&sig["messageDigest"]["digest"], "messageDigest")?;
    if let Some(expected) = image_digest
        && digest.as_slice() != expected
    {
        return Err("bundle signs a different image".into());
    }
    let vm = &b["verificationMaterial"];
    let cert = b64(&vm["certificate"]["rawBytes"], "certificate")?;
    let entries = vm["tlogEntries"].as_array().ok_or("missing tlogEntries")?;
    let [entry] = entries.as_slice() else {
        return Err("need exactly one tlog entry".into());
    };
    if entry["kindVersion"]["kind"] != "hashedrekord" || entry["kindVersion"]["version"] != "0.0.2"
    {
        return Err("entry isn't hashedrekord 0.0.2".into());
    }
    let proof = &entry["inclusionProof"];
    let index: u64 = proof["logIndex"]
        .as_str()
        .ok_or("missing logIndex")?
        .parse()
        .map_err(|_| "bad logIndex")?;
    let mut hashes = Vec::new();
    for h in proof["hashes"].as_array().into_iter().flatten() {
        hashes.extend_from_slice(&b64(h, "proof hash")?);
    }
    let checkpoint = proof["checkpoint"]["envelope"]
        .as_str()
        .ok_or("missing checkpoint")?;
    let stamps = vm["timestampVerificationData"]["rfc3161Timestamps"]
        .as_array()
        .ok_or("missing timestamp")?;
    let [stamp] = stamps.as_slice() else {
        return Err("need exactly one RFC 3161 timestamp".into());
    };
    let timestamp = b64(&stamp["signedTimestamp"], "signedTimestamp")?;
    let signature = b64(&sig["signature"], "signature")?;

    let mut out = b"C3BN".to_vec();
    out.extend_from_slice(&1u16.to_le_bytes());
    for field in [
        cert.as_slice(),
        &signature,
        &index.to_le_bytes(),
        &hashes,
        checkpoint.as_bytes(),
        &timestamp,
    ] {
        out.extend_from_slice(
            &u32::try_from(field.len())
                .map_err(|e| e.to_string())?
                .to_le_bytes(),
        );
        out.extend_from_slice(field);
    }
    Ok(out)
}
