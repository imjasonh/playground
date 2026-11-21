//! Builds and signs key-set chain links and trust-root blobs.

use base64::Engine;
use base64::engine::general_purpose::STANDARD;
use c3_verify::chain::LINK_DOMAIN;
use c3_verify::trustroot::BLOB_DOMAIN;
use ed25519_dalek::Signer;
use ed25519_dalek::SigningKey;
use serde_json::Value;
use std::fmt::Write;

use x509_cert::Certificate;
use x509_cert::der::Decode;
use x509_cert::der::Encode;
use x509_cert::der::Reader;
use x509_cert::der::SliceReader;
use x509_cert::name::Name;
use x509_cert::serial_number::SerialNumber;

/// An inclusive validity window in Unix seconds.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub struct Window(pub u64, pub u64);

impl Window {
    fn intersect(self, other: Window) -> Window {
        Window(self.0.max(other.0), self.1.min(other.1))
    }
}

/// The values of a trust-root blob before signing.
#[derive(Clone, Debug, Default)]
pub struct TrustRootSpec {
    /// The blob's level.
    pub level: u8,
    /// An audit sequence number the device ignores.
    pub sequence: u32,
    /// Fulcio intermediates: subject DER, P-384 point, window.
    pub fulcio: Vec<(Vec<u8>, [u8; 97], Window)>,
    /// Log keys: origin, Ed25519 key, window.
    pub logs: Vec<(String, [u8; 32], Window)>,
    /// TSA signers: `SignerIdentifier` DER, P-384 point, window.
    pub tsas: Vec<(Vec<u8>, [u8; 97], Window)>,
    /// Issuer, Build Signer URI, repository ID, owner ID, and trigger.
    pub policy: [String; 5],
}

fn cert_window(cert: &Certificate) -> Window {
    let v = &cert.tbs_certificate.validity;
    Window(
        v.not_before.to_unix_duration().as_secs(),
        v.not_after.to_unix_duration().as_secs(),
    )
}

fn valid_for(v: &Value) -> Result<Window, String> {
    let start = v["start"].as_str().ok_or("validFor needs a start")?;
    let end = match v["end"].as_str() {
        Some(e) => crate::time::rfc3339(e)?,
        None => u64::MAX,
    };
    Ok(Window(crate::time::rfc3339(start)?, end))
}

fn chain_certs(v: &Value) -> Result<Vec<Certificate>, String> {
    let list = v["certChain"]["certificates"]
        .as_array()
        .ok_or("missing certChain")?;
    list.iter()
        .map(|c| {
            let der = STANDARD
                .decode(c["rawBytes"].as_str().ok_or("missing rawBytes")?)
                .map_err(|e| e.to_string())?;
            Certificate::from_der(&der).map_err(|e| e.to_string())
        })
        .collect()
}

fn p384_point(cert: &Certificate) -> Result<[u8; 97], String> {
    let bits = cert
        .tbs_certificate
        .subject_public_key_info
        .subject_public_key
        .raw_bytes();
    bits.try_into()
        .map_err(|_| "certificate key isn't an uncompressed P-384 point".into())
}

fn chain_window(certs: &[Certificate], base: Window) -> Window {
    certs.iter().fold(base, |w, c| w.intersect(cert_window(c)))
}

impl TrustRootSpec {
    /// Reads the Fulcio intermediates, Ed25519 Rekor logs, and TSAs from a
    /// Sigstore `trusted_root.json`. Each window is the trusted root's
    /// `validFor` intersected with the validity of every certificate in
    /// that entry's chain. Logs with non-Ed25519 keys are skipped, because
    /// the device verifies only Rekor v2 checkpoints.
    pub fn from_trusted_root(json: &str, level: u8, policy: [String; 5]) -> Result<Self, String> {
        let root: Value = serde_json::from_str(json).map_err(|e| e.to_string())?;
        let mut spec = TrustRootSpec {
            level,
            policy,
            ..Default::default()
        };
        for ca in root["certificateAuthorities"]
            .as_array()
            .into_iter()
            .flatten()
        {
            let certs = chain_certs(ca)?;
            let first = certs.first().ok_or("empty Fulcio chain")?;
            let subject = first
                .tbs_certificate
                .subject
                .to_der()
                .map_err(|e| e.to_string())?;
            let window = chain_window(&certs, valid_for(&ca["validFor"])?);
            spec.fulcio.push((subject, p384_point(first)?, window));
        }
        for tlog in root["tlogs"].as_array().into_iter().flatten() {
            let key = &tlog["publicKey"];
            if key["keyDetails"].as_str() != Some("PKIX_ED25519") {
                continue;
            }
            let spki = STANDARD
                .decode(key["rawBytes"].as_str().ok_or("missing log key")?)
                .map_err(|e| e.to_string())?;
            const PREFIX: [u8; 12] = [
                0x30, 0x2a, 0x30, 0x05, 0x06, 0x03, 0x2b, 0x65, 0x70, 0x03, 0x21, 0x00,
            ];
            let raw = spki
                .strip_prefix(&PREFIX)
                .ok_or("log key isn't an Ed25519 SPKI")?;
            let raw: [u8; 32] = raw.try_into().map_err(|_| "bad Ed25519 key length")?;
            let url = tlog["baseUrl"].as_str().ok_or("missing baseUrl")?;
            let origin = url
                .strip_prefix("https://")
                .unwrap_or(url)
                .trim_end_matches('/')
                .to_string();
            spec.logs.push((origin, raw, valid_for(&key["validFor"])?));
        }
        for tsa in root["timestampAuthorities"]
            .as_array()
            .into_iter()
            .flatten()
        {
            let certs = chain_certs(tsa)?;
            let leaf = certs.first().ok_or("empty TSA chain")?;
            let issuer = leaf
                .tbs_certificate
                .issuer
                .to_der()
                .map_err(|e| e.to_string())?;
            let serial = leaf
                .tbs_certificate
                .serial_number
                .to_der()
                .map_err(|e| e.to_string())?;
            let mut body = issuer;
            body.extend_from_slice(&serial);
            let window = chain_window(&certs, valid_for(&tsa["validFor"])?);
            spec.tsas
                .push((der_sequence(&body), p384_point(leaf)?, window));
        }
        Ok(spec)
    }

    /// Describes the entries a device would trust, as Markdown, for people
    /// who review a trust root before they sign its blob.
    pub fn describe(&self) -> Result<String, String> {
        let window = |w: &Window| {
            let end = if w.1 == u64::MAX {
                "no end".to_string()
            } else {
                crate::time::format(w.1)
            };
            format!("{} to {end}", crate::time::format(w.0))
        };
        let key_digest = |k: &[u8]| hex(&c3_crypto::sha256(k));
        let mut out = String::from("### Fulcio certificate authorities\n\n");
        for (subject, key, w) in &self.fulcio {
            let name = Name::from_der(subject).map_err(|e| e.to_string())?;
            let _ = writeln!(
                out,
                "- `{name}`, P-384 key SHA-256 `{}`, valid {}",
                key_digest(key),
                window(w)
            );
        }
        out.push_str("\n### Logs with Ed25519 keys\n\n");
        for (origin, key, w) in &self.logs {
            let _ = writeln!(
                out,
                "- `{origin}`, Ed25519 key `{}`, valid {}",
                hex(key),
                window(w)
            );
        }
        out.push_str("\n### Timestamp authorities\n\n");
        for (signer, key, w) in &self.tsas {
            let (issuer, serial) = signer_parts(signer)?;
            let _ = writeln!(
                out,
                "- issuer `{issuer}`, serial `{}`, P-384 key SHA-256 `{}`, valid {}",
                hex(serial.as_bytes()),
                key_digest(key),
                window(w)
            );
        }
        Ok(out)
    }

    /// The blob without signatures, as `docs/formats.md` lays it out.
    pub fn encode_body(&self) -> Result<Vec<u8>, String> {
        let mut out = b"C3TR".to_vec();
        out.extend_from_slice(&1u16.to_le_bytes());
        out.extend_from_slice(&self.sequence.to_le_bytes());
        out.push(self.level);
        out.push(0);
        out.push(count(self.fulcio.len(), 4)?);
        for (subject, key, w) in &self.fulcio {
            push_u16_string(&mut out, subject)?;
            out.extend_from_slice(key);
            push_window(&mut out, *w);
        }
        out.push(count(self.logs.len(), 8)?);
        for (origin, key, w) in &self.logs {
            out.push(u8::try_from(origin.len()).map_err(|_| "origin too long")?);
            out.extend_from_slice(origin.as_bytes());
            out.extend_from_slice(key);
            push_window(&mut out, *w);
        }
        out.push(count(self.tsas.len(), 4)?);
        for (signer_id, key, w) in &self.tsas {
            push_u16_string(&mut out, signer_id)?;
            out.extend_from_slice(key);
            push_window(&mut out, *w);
        }
        for s in &self.policy {
            push_u16_string(&mut out, s.as_bytes())?;
        }
        Ok(out)
    }
}

fn count(n: usize, max: usize) -> Result<u8, String> {
    if n == 0 || n > max {
        return Err(format!("need 1 through {max} entries, have {n}"));
    }
    u8::try_from(n).map_err(|e| e.to_string())
}

fn push_u16_string(out: &mut Vec<u8>, s: &[u8]) -> Result<(), String> {
    out.extend_from_slice(
        &u16::try_from(s.len())
            .map_err(|_| "string too long")?
            .to_le_bytes(),
    );
    out.extend_from_slice(s);
    Ok(())
}

fn push_window(out: &mut Vec<u8>, w: Window) {
    out.extend_from_slice(&w.0.to_le_bytes());
    out.extend_from_slice(&w.1.to_le_bytes());
}

/// Wraps `body` in a DER `SEQUENCE`.
fn hex(bytes: &[u8]) -> String {
    bytes.iter().map(|b| format!("{b:02x}")).collect()
}

/// Splits a `SignerIdentifier` into its issuer and serial number.
fn signer_parts(der: &[u8]) -> Result<(Name, SerialNumber), String> {
    let mut reader = SliceReader::new(der).map_err(|e| e.to_string())?;
    reader
        .sequence(|r| Ok((Name::decode(r)?, SerialNumber::decode(r)?)))
        .map_err(|e| e.to_string())
}

fn der_sequence(body: &[u8]) -> Vec<u8> {
    let mut out = vec![0x30];
    let n = body.len();
    if n < 128 {
        out.push(n as u8);
    } else if n < 256 {
        out.extend_from_slice(&[0x81, n as u8]);
    } else {
        out.extend_from_slice(&[0x82, (n >> 8) as u8, n as u8]);
    }
    out.extend_from_slice(body);
    out
}

/// Appends the signature list for `body` under `domain`: a count, then each
/// signer's key index and signature. `signers` must be in increasing index
/// order.
pub fn sign(body: &[u8], domain: &[u8], signers: &[(u8, &SigningKey)]) -> Result<Vec<u8>, String> {
    if !(2..=4).contains(&signers.len()) || signers.windows(2).any(|w| w[0].0 >= w[1].0) {
        return Err("need two to four signers in increasing index order".into());
    }
    let mut message = domain.to_vec();
    message.push(0);
    message.extend_from_slice(body);
    let mut out = body.to_vec();
    out.push(signers.len() as u8);
    for (index, key) in signers {
        out.push(*index);
        out.extend_from_slice(&key.sign(&message).to_bytes());
    }
    Ok(out)
}

/// Builds and signs a trust-root blob.
pub fn signed_blob(spec: &TrustRootSpec, signers: &[(u8, &SigningKey)]) -> Result<Vec<u8>, String> {
    sign(&spec.encode_body()?, BLOB_DOMAIN, signers)
}

/// Builds and signs one chain link that names `keys` at `level`.
pub fn signed_link(
    level: u8,
    keys: &[[u8; 32]],
    signers: &[(u8, &SigningKey)],
) -> Result<Vec<u8>, String> {
    let mut body = vec![level, count(keys.len(), 4)?];
    for k in keys {
        body.extend_from_slice(k);
    }
    sign(&body, LINK_DOMAIN, signers)
}

/// Builds a chain from already signed links.
pub fn chain(links: &[Vec<u8>]) -> Result<Vec<u8>, String> {
    let mut out = b"C3KC".to_vec();
    out.extend_from_slice(&1u16.to_le_bytes());
    out.push(u8::try_from(links.len()).map_err(|_| "too many links")?);
    out.push(0);
    for l in links {
        out.extend_from_slice(l);
    }
    Ok(out)
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn describes_the_production_trusted_root() {
        let json = include_str!("../../release/trusted_root.json");
        let spec = TrustRootSpec::from_trusted_root(json, 0, Default::default()).unwrap();
        let text = spec.describe().unwrap();
        assert!(text.contains("- `CN=sigstore-intermediate,O=sigstore.dev`, P-384 key SHA-256 `"));
        assert!(text.contains("- `log2025-1.rekor.sigstore.dev`, Ed25519 key `"));
        assert!(text.contains("valid 2025-09-23T00:00:00Z to no end"));
        assert!(text.contains("- issuer `CN=sigstore-tsa-selfsigned,O=sigstore.dev`, serial `"));
        assert_eq!(
            spec.logs.len(),
            1,
            "only the Rekor v2 log has an Ed25519 key"
        );
    }
}
