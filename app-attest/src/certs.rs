//! X.509 chain checks for Apple App Attest certificates.
//!
//! The leaf (`credCert`) plus one Apple intermediate arrive in `attStmt.x5c`.
//! This module verifies that chain against the official Apple App Attestation
//! Root CA (embedded) or a test root, then reads the nonce extension
//! `1.2.840.113635.100.8.2`.

use der_parser::parse_der;
use p256::ecdsa::signature::Verifier as _;
use sha2::{Digest, Sha256};
use x509_parser::prelude::*;

use crate::error::Error;

/// Official Apple App Attestation Root CA (PEM).
pub const APPLE_APP_ATTEST_ROOT_PEM: &str = include_str!("apple_root.pem");

/// OID 1.2.840.113635.100.8.2 — App Attest nonce in `credCert`.
const NONCE_OID: &[u64] = &[1, 2, 840, 113635, 100, 8, 2];

const OID_ECDSA_SHA256: &[u64] = &[1, 2, 840, 10045, 4, 3, 2];
const OID_ECDSA_SHA384: &[u64] = &[1, 2, 840, 10045, 4, 3, 3];

/// Decode a single PEM certificate to DER.
pub fn pem_to_der(pem: &str) -> Result<Vec<u8>, Error> {
    let b64: String = pem
        .lines()
        .filter(|line| !line.starts_with("-----"))
        .collect();
    crate::b64::decode(&b64)
}

/// Apple's production App Attestation Root CA, as DER.
pub fn apple_root_der() -> Result<Vec<u8>, Error> {
    pem_to_der(APPLE_APP_ATTEST_ROOT_PEM)
}

/// Fields extracted from a verified leaf certificate.
pub struct VerifiedLeaf {
    /// Uncompressed SEC1 public key from `credCert` (65 bytes for P-256).
    pub public_key: Vec<u8>,
    /// 32-byte nonce from the Apple extension.
    pub nonce: [u8; 32],
}

/// Verify `x5c` (leaf, then intermediates) anchors at one of `roots`.
pub fn verify_chain(
    x5c: &[Vec<u8>],
    roots: &[Vec<u8>],
    now_unix: u64,
) -> Result<VerifiedLeaf, Error> {
    if x5c.is_empty() {
        return Err(Error::Certificate("x5c is empty"));
    }
    let leaf_der = &x5c[0];
    let leaf = parse_cert(leaf_der)?;
    check_time(&leaf, now_unix)?;

    let mut issuer_der = leaf_der.clone();
    for next in x5c.iter().skip(1) {
        let issuer = parse_cert(next)?;
        check_time(&issuer, now_unix)?;
        verify_signed_by(&parse_cert(&issuer_der)?, &issuer)?;
        issuer_der = next.clone();
    }

    let last = parse_cert(&issuer_der)?;
    let mut anchored = false;
    for root_der in roots {
        let root = parse_cert(root_der)?;
        check_time(&root, now_unix)?;
        if verify_signed_by(&last, &root).is_ok() {
            anchored = true;
            break;
        }
        // The last x5c entry may itself be the root (unusual) or the
        // intermediate. Also accept a direct match of the last cert to a root.
        if last.tbs_certificate.as_ref() == root.tbs_certificate.as_ref() {
            anchored = true;
            break;
        }
    }
    if !anchored {
        return Err(Error::Certificate(
            "chain does not anchor at a trusted root",
        ));
    }

    let public_key = leaf.public_key().subject_public_key.data.to_vec();
    if public_key.is_empty() {
        return Err(Error::Certificate("leaf public key missing"));
    }
    let nonce = extract_nonce(&leaf)?;
    Ok(VerifiedLeaf { public_key, nonce })
}

/// SHA-256 of the leaf public key; this is Apple's `keyId` preimage.
pub fn key_id_bytes(public_key: &[u8]) -> [u8; 32] {
    Sha256::digest(public_key).into()
}

fn parse_cert(der: &[u8]) -> Result<X509Certificate<'_>, Error> {
    let (_, cert) = X509Certificate::from_der(der)
        .map_err(|_| Error::Certificate("certificate is not valid DER"))?;
    Ok(cert)
}

fn check_time(cert: &X509Certificate<'_>, now_unix: u64) -> Result<(), Error> {
    let start = cert.validity().not_before.timestamp();
    let end = cert.validity().not_after.timestamp();
    if (now_unix as i64) < start || (now_unix as i64) > end {
        return Err(Error::Certificate("certificate is not valid at this time"));
    }
    Ok(())
}

fn verify_signed_by(cert: &X509Certificate<'_>, issuer: &X509Certificate<'_>) -> Result<(), Error> {
    let tbs = cert.tbs_certificate.as_ref();
    let sig = cert.signature_value.data.as_ref();
    let algo = cert
        .signature_algorithm
        .algorithm
        .iter()
        .ok_or(Error::Certificate("signature oid"))?;
    let oid: Vec<u64> = algo.collect();
    let issuer_pk = issuer.public_key().subject_public_key.data.as_ref();

    if oid == OID_ECDSA_SHA256 {
        verify_p256(issuer_pk, tbs, sig)
    } else if oid == OID_ECDSA_SHA384 {
        verify_p384(issuer_pk, tbs, sig)
    } else {
        Err(Error::Certificate(
            "unsupported certificate signature algorithm",
        ))
    }
}

fn verify_p256(public_key: &[u8], tbs: &[u8], sig: &[u8]) -> Result<(), Error> {
    let vk = p256::ecdsa::VerifyingKey::from_sec1_bytes(public_key)
        .map_err(|_| Error::Certificate("issuer P-256 key"))?;
    let signature = p256::ecdsa::Signature::from_der(sig)
        .or_else(|_| p256::ecdsa::Signature::from_slice(sig))
        .map_err(|_| Error::Certificate("P-256 signature encoding"))?;
    vk.verify(tbs, &signature)
        .map_err(|_| Error::Certificate("P-256 signature"))
}

fn verify_p384(public_key: &[u8], tbs: &[u8], sig: &[u8]) -> Result<(), Error> {
    let vk = p384::ecdsa::VerifyingKey::from_sec1_bytes(public_key)
        .map_err(|_| Error::Certificate("issuer P-384 key"))?;
    let signature = p384::ecdsa::Signature::from_der(sig)
        .or_else(|_| p384::ecdsa::Signature::from_slice(sig))
        .map_err(|_| Error::Certificate("P-384 signature encoding"))?;
    vk.verify(tbs, &signature)
        .map_err(|_| Error::Certificate("P-384 signature"))
}

fn extract_nonce(cert: &X509Certificate<'_>) -> Result<[u8; 32], Error> {
    let oid = der_parser::oid::Oid::from(NONCE_OID).map_err(|_| Error::Certificate("nonce oid"))?;
    let ext = cert
        .get_extension_unique(&oid)
        .map_err(|_| Error::Certificate("nonce extension"))?
        .ok_or(Error::Certificate("nonce extension missing"))?;
    parse_nonce_value(ext.value)
}

fn parse_nonce_value(value: &[u8]) -> Result<[u8; 32], Error> {
    let (_, obj) =
        parse_der(value).map_err(|_| Error::Certificate("nonce extension is not DER"))?;
    find_32(&obj).ok_or(Error::Certificate("nonce extension missing 32-byte value"))
}

fn find_32(obj: &der_parser::der::DerObject<'_>) -> Option<[u8; 32]> {
    use der_parser::ber::BerObjectContent;
    match &obj.content {
        BerObjectContent::OctetString(bytes) if bytes.len() == 32 => {
            let mut out = [0u8; 32];
            out.copy_from_slice(bytes);
            Some(out)
        }
        BerObjectContent::Sequence(seq) | BerObjectContent::Set(seq) => {
            seq.iter().find_map(find_32)
        }
        BerObjectContent::Tagged(_, _, inner) => find_32(inner),
        BerObjectContent::Optional(Some(inner)) => find_32(inner),
        BerObjectContent::Unknown(any) => {
            let data = any.data;
            if data.len() == 32 {
                let mut out = [0u8; 32];
                out.copy_from_slice(data);
                return Some(out);
            }
            parse_der(data).ok().and_then(|(_, inner)| find_32(&inner))
        }
        _ => {
            if let Ok(bytes) = obj.as_slice() {
                if bytes.len() == 32 {
                    let mut out = [0u8; 32];
                    out.copy_from_slice(bytes);
                    return Some(out);
                }
                if let Ok((_, inner)) = parse_der(bytes) {
                    return find_32(&inner);
                }
            }
            None
        }
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn apple_root_parses() {
        let der = apple_root_der().unwrap();
        let cert = parse_cert(&der).unwrap();
        assert!(cert
            .subject()
            .to_string()
            .contains("Apple App Attestation Root CA"));
    }

    #[test]
    fn nonce_sequence_with_context_tag() {
        // SEQUENCE { [1] OCTET STRING <32 0xab> }
        let mut der = vec![0x30, 0x24, 0xa1, 0x22, 0x04, 0x20];
        der.extend(std::iter::repeat_n(0xab, 32));
        let nonce = parse_nonce_value(&der).unwrap();
        assert_eq!(nonce, [0xab; 32]);
    }
}
