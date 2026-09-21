//! Parse and verify an Apple App Attest `attestationObject`.

use ciborium::value::Value;
use sha2::{Digest, Sha256};

use crate::b64;
use crate::certs::{self, VerifiedLeaf};
use crate::error::Error;

/// Production AAGUID: `appattest` plus seven zero bytes.
pub const AAGUID_PRODUCTION: &[u8; 16] = b"appattest\x00\x00\x00\x00\x00\x00\x00";
/// Development / Xcode AAGUID.
pub const AAGUID_DEVELOPMENT: &[u8; 16] = b"appattestdevelop";

const MAX_ATTESTATION_BYTES: usize = 16 * 1024;
const FLAG_AT: u8 = 0x40;

/// Inputs required to verify one attestation.
pub struct VerifyInput<'a> {
    pub app_id: &'a str,
    pub key_id: &'a str,
    pub attestation_object: &'a [u8],
    pub client_data_hash: &'a [u8; 32],
    pub roots: &'a [Vec<u8>],
    pub now_unix: u64,
}

/// Successful verification: the leaf public key is bound to `key_id`.
#[derive(Debug)]
pub struct VerifiedAttestation {
    pub public_key: Vec<u8>,
    /// Raw `attStmt.receipt` bytes (may be empty on a malformed object).
    pub receipt: Vec<u8>,
    pub development: bool,
}

/// Verify Apple's attestation object against `input`.
pub fn verify(input: &VerifyInput<'_>) -> Result<VerifiedAttestation, Error> {
    if input.attestation_object.len() > MAX_ATTESTATION_BYTES {
        return Err(Error::Attestation("attestationObject too large"));
    }
    let parsed = parse_attestation(input.attestation_object)?;
    let leaf = certs::verify_chain(&parsed.x5c, input.roots, input.now_unix)?;
    check_nonce(&parsed.auth_data, input.client_data_hash, &leaf)?;
    check_key_id(input.key_id, &leaf)?;
    let development = check_auth_data(&parsed.auth_data, input.app_id, input.key_id)?;
    Ok(VerifiedAttestation {
        public_key: leaf.public_key,
        receipt: parsed.receipt,
        development,
    })
}

struct ParsedAttestation {
    auth_data: Vec<u8>,
    x5c: Vec<Vec<u8>>,
    receipt: Vec<u8>,
}

fn parse_attestation(bytes: &[u8]) -> Result<ParsedAttestation, Error> {
    let value: Value = ciborium::from_reader(bytes)
        .map_err(|_| Error::Attestation("attestationObject is not CBOR"))?;
    let map = value
        .as_map()
        .ok_or(Error::Attestation("attestationObject is not a map"))?;
    let fmt = map_get(map, "fmt")
        .and_then(Value::as_text)
        .ok_or(Error::Attestation("fmt missing"))?;
    if fmt != "apple-appattest" {
        return Err(Error::Attestation("fmt must be apple-appattest"));
    }
    let auth_data = map_get(map, "authData")
        .and_then(Value::as_bytes)
        .ok_or(Error::Attestation("authData missing"))?
        .clone();
    let stmt = map_get(map, "attStmt")
        .and_then(Value::as_map)
        .ok_or(Error::Attestation("attStmt missing"))?;
    let x5c_val = map_get(stmt, "x5c").ok_or(Error::Attestation("x5c missing"))?;
    let x5c_arr = x5c_val
        .as_array()
        .ok_or(Error::Attestation("x5c is not an array"))?;
    let mut x5c = Vec::with_capacity(x5c_arr.len());
    for cert in x5c_arr {
        let der = cert
            .as_bytes()
            .ok_or(Error::Attestation("x5c entry is not a bstr"))?;
        x5c.push(der.clone());
    }
    if x5c.is_empty() {
        return Err(Error::Attestation("x5c is empty"));
    }
    let receipt = map_get(stmt, "receipt")
        .and_then(Value::as_bytes)
        .cloned()
        .unwrap_or_default();
    Ok(ParsedAttestation {
        auth_data,
        x5c,
        receipt,
    })
}

fn map_get<'a>(map: &'a [(Value, Value)], key: &str) -> Option<&'a Value> {
    map.iter()
        .find(|(k, _)| k.as_text() == Some(key))
        .map(|(_, v)| v)
}

fn check_nonce(
    auth_data: &[u8],
    client_data_hash: &[u8; 32],
    leaf: &VerifiedLeaf,
) -> Result<(), Error> {
    let mut composite = Vec::with_capacity(auth_data.len() + 32);
    composite.extend_from_slice(auth_data);
    composite.extend_from_slice(client_data_hash);
    let nonce: [u8; 32] = Sha256::digest(&composite).into();
    if nonce != leaf.nonce {
        return Err(Error::Binding(
            "certificate nonce does not match clientData",
        ));
    }
    Ok(())
}

fn check_key_id(key_id: &str, leaf: &VerifiedLeaf) -> Result<(), Error> {
    let want = certs::key_id_bytes(&leaf.public_key);
    let got = b64::decode(key_id).map_err(|_| Error::Binding("keyId is not base64"))?;
    if got.as_slice() != want {
        return Err(Error::Binding("keyId does not match credCert public key"));
    }
    Ok(())
}

fn check_auth_data(auth_data: &[u8], app_id: &str, key_id: &str) -> Result<bool, Error> {
    if auth_data.len() < 55 {
        return Err(Error::Attestation("authenticatorData too short"));
    }
    let rp_id_hash = &auth_data[..32];
    let want_rp: [u8; 32] = Sha256::digest(app_id.as_bytes()).into();
    if rp_id_hash != want_rp {
        return Err(Error::Binding("rpIdHash does not match APP_ID"));
    }
    let flags = auth_data[32];
    if flags & FLAG_AT == 0 {
        return Err(Error::Attestation("attested credential data missing"));
    }
    let counter = u32::from_be_bytes(
        auth_data[33..37]
            .try_into()
            .map_err(|_| Error::Attestation("counter truncated"))?,
    );
    if counter != 0 {
        return Err(Error::Attestation("attestation counter must be 0"));
    }
    let aaguid: [u8; 16] = auth_data[37..53]
        .try_into()
        .map_err(|_| Error::Attestation("aaguid truncated"))?;
    if aaguid != *AAGUID_PRODUCTION && aaguid != *AAGUID_DEVELOPMENT {
        return Err(Error::Attestation("unexpected aaguid"));
    }
    let cred_len = u16::from_be_bytes(
        auth_data[53..55]
            .try_into()
            .map_err(|_| Error::Attestation("credential id length truncated"))?,
    ) as usize;
    let cred_end = 55usize.saturating_add(cred_len);
    if auth_data.len() < cred_end {
        return Err(Error::Attestation("credential id truncated"));
    }
    let cred_id = &auth_data[55..cred_end];
    let key_id_raw = b64::decode(key_id).map_err(|_| Error::Binding("keyId is not base64"))?;
    if cred_id != key_id_raw {
        return Err(Error::Binding("credential id does not match keyId"));
    }
    Ok(aaguid == *AAGUID_DEVELOPMENT)
}

/// Encode an `apple-appattest` attestation object (tests and fixtures).
pub fn encode_attestation_object(auth_data: &[u8], x5c: Vec<Vec<u8>>) -> Vec<u8> {
    encode_attestation_object_with_receipt(auth_data, x5c, &[0])
}

/// Encode an attestation object with an explicit `attStmt.receipt`.
pub fn encode_attestation_object_with_receipt(
    auth_data: &[u8],
    x5c: Vec<Vec<u8>>,
    receipt: &[u8],
) -> Vec<u8> {
    let x5c_values: Vec<Value> = x5c.into_iter().map(Value::Bytes).collect();
    let stmt = vec![
        (Value::Text("x5c".into()), Value::Array(x5c_values)),
        (
            Value::Text("receipt".into()),
            Value::Bytes(receipt.to_vec()),
        ),
    ];
    let map = vec![
        (
            Value::Text("fmt".into()),
            Value::Text("apple-appattest".into()),
        ),
        (Value::Text("attStmt".into()), Value::Map(stmt)),
        (
            Value::Text("authData".into()),
            Value::Bytes(auth_data.to_vec()),
        ),
    ];
    let mut buf = Vec::new();
    ciborium::into_writer(&Value::Map(map), &mut buf).expect("attestation object encodes");
    buf
}

/// Build authenticator data for tests (and the fixture generator).
pub fn encode_auth_data(app_id: &str, key_id: &[u8], development: bool) -> Vec<u8> {
    let rp: [u8; 32] = Sha256::digest(app_id.as_bytes()).into();
    let mut out = Vec::with_capacity(55 + key_id.len());
    out.extend_from_slice(&rp);
    out.push(FLAG_AT | 0x01); // AT + UP
    out.extend_from_slice(&0u32.to_be_bytes());
    if development {
        out.extend_from_slice(AAGUID_DEVELOPMENT);
    } else {
        out.extend_from_slice(AAGUID_PRODUCTION);
    }
    let cred_len = u16::try_from(key_id.len()).expect("key id fits u16");
    out.extend_from_slice(&cred_len.to_be_bytes());
    out.extend_from_slice(key_id);
    out
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn rejects_wrong_fmt() {
        let mut buf = Vec::new();
        let map = vec![(Value::Text("fmt".into()), Value::Text("none".into()))];
        ciborium::into_writer(&Value::Map(map), &mut buf).unwrap();
        assert!(parse_attestation(&buf).is_err());
    }

    #[test]
    fn rp_id_mismatch() {
        let key = [7u8; 32];
        let auth = encode_auth_data("AAAA.io.example.app", &key, true);
        let err = check_auth_data(&auth, "BBBB.io.example.app", &b64::encode_std(key)).unwrap_err();
        assert!(matches!(err, Error::Binding(_)));
    }
}
