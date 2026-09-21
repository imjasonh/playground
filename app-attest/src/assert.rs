//! Parse and verify an Apple App Attest assertion object.
//!
//! Apple's assertion is a CBOR map `{ signature, authenticatorData }`. The
//! signature is ECDSA P-256 over `SHA-256(authenticatorData || clientDataHash)`
//! using the public key stored at attestation time. `authenticatorData` is the
//! WebAuthn prefix: rpIdHash (32), flags (1), counter (4), plus optional
//! extensions the server ignores.

use ciborium::value::Value;
use sha2::{Digest, Sha256};

use crate::certs;
use crate::error::Error;

const MAX_ASSERTION_BYTES: usize = 8 * 1024;
const AUTH_DATA_MIN: usize = 37;

/// Inputs required to verify one assertion.
pub struct VerifyInput<'a> {
    pub app_id: &'a str,
    pub public_key: &'a [u8],
    pub assertion_object: &'a [u8],
    pub client_data_hash: &'a [u8; 32],
    pub previous_counter: u32,
}

/// Successful verification: the new counter to persist.
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct VerifiedAssertion {
    pub counter: u32,
}

/// Verify Apple's assertion object against `input`.
pub fn verify(input: &VerifyInput<'_>) -> Result<VerifiedAssertion, Error> {
    if input.assertion_object.len() > MAX_ASSERTION_BYTES {
        return Err(Error::Assertion("assertionObject too large"));
    }
    if input.public_key.is_empty() {
        return Err(Error::Assertion("public key missing"));
    }
    let parsed = parse_assertion(input.assertion_object)?;
    check_rp_id(&parsed.auth_data, input.app_id)?;
    let counter = read_counter(&parsed.auth_data)?;
    if counter <= input.previous_counter {
        return Err(Error::Assertion("counter must increase"));
    }
    verify_signature(
        input.public_key,
        &parsed.auth_data,
        input.client_data_hash,
        &parsed.signature,
    )?;
    Ok(VerifiedAssertion { counter })
}

struct ParsedAssertion {
    auth_data: Vec<u8>,
    signature: Vec<u8>,
}

fn parse_assertion(bytes: &[u8]) -> Result<ParsedAssertion, Error> {
    let value: Value = ciborium::from_reader(bytes)
        .map_err(|_| Error::Assertion("assertionObject is not CBOR"))?;
    let map = value
        .as_map()
        .ok_or(Error::Assertion("assertionObject is not a map"))?;
    let auth_data = map_get(map, "authenticatorData")
        .and_then(Value::as_bytes)
        .ok_or(Error::Assertion("authenticatorData missing"))?
        .clone();
    let signature = map_get(map, "signature")
        .and_then(Value::as_bytes)
        .ok_or(Error::Assertion("signature missing"))?
        .clone();
    if auth_data.len() < AUTH_DATA_MIN {
        return Err(Error::Assertion("authenticatorData too short"));
    }
    if signature.is_empty() {
        return Err(Error::Assertion("signature missing"));
    }
    Ok(ParsedAssertion {
        auth_data,
        signature,
    })
}

fn map_get<'a>(map: &'a [(Value, Value)], key: &str) -> Option<&'a Value> {
    map.iter()
        .find(|(k, _)| k.as_text() == Some(key))
        .map(|(_, v)| v)
}

fn check_rp_id(auth_data: &[u8], app_id: &str) -> Result<(), Error> {
    let rp_id_hash = &auth_data[..32];
    let want_rp: [u8; 32] = Sha256::digest(app_id.as_bytes()).into();
    if rp_id_hash != want_rp {
        return Err(Error::Binding("rpIdHash does not match APP_ID"));
    }
    Ok(())
}

fn read_counter(auth_data: &[u8]) -> Result<u32, Error> {
    let bytes: [u8; 4] = auth_data[33..37]
        .try_into()
        .map_err(|_| Error::Assertion("counter truncated"))?;
    Ok(u32::from_be_bytes(bytes))
}

fn verify_signature(
    public_key: &[u8],
    auth_data: &[u8],
    client_data_hash: &[u8; 32],
    signature: &[u8],
) -> Result<(), Error> {
    let mut nonce_input = Vec::with_capacity(auth_data.len() + 32);
    nonce_input.extend_from_slice(auth_data);
    nonce_input.extend_from_slice(client_data_hash);
    certs::verify_p256_message(public_key, &nonce_input, signature)
        .map_err(|_| Error::Assertion("signature"))
}

/// Encode an assertion object (tests and fixtures).
pub fn encode_assertion_object(auth_data: &[u8], signature: &[u8]) -> Vec<u8> {
    let map = vec![
        (
            Value::Text("authenticatorData".into()),
            Value::Bytes(auth_data.to_vec()),
        ),
        (
            Value::Text("signature".into()),
            Value::Bytes(signature.to_vec()),
        ),
    ];
    let mut buf = Vec::new();
    ciborium::into_writer(&Value::Map(map), &mut buf).expect("assertion object encodes");
    buf
}

/// Build assertion authenticator data: rpIdHash || flags || counter.
pub fn encode_auth_data(app_id: &str, counter: u32) -> Vec<u8> {
    let rp: [u8; 32] = Sha256::digest(app_id.as_bytes()).into();
    let mut out = Vec::with_capacity(AUTH_DATA_MIN);
    out.extend_from_slice(&rp);
    out.push(0x01); // UP
    out.extend_from_slice(&counter.to_be_bytes());
    out
}

#[cfg(test)]
mod tests {
    use super::*;
    use p256::ecdsa::{signature::Signer, Signature, SigningKey};
    use rand_core::OsRng;

    const APP_ID: &str = "TEAMIDTEST.io.github.imjasonh.playground";

    fn sign_assertion(app_id: &str, counter: u32, client_hash: &[u8; 32]) -> (Vec<u8>, Vec<u8>) {
        let signing = SigningKey::random(&mut OsRng);
        let vk = signing.verifying_key();
        let public_key = vk.to_encoded_point(false).as_bytes().to_vec();
        let auth = encode_auth_data(app_id, counter);
        let mut msg = auth.clone();
        msg.extend_from_slice(client_hash);
        let sig: Signature = signing.sign(&msg);
        (
            public_key,
            encode_assertion_object(&auth, sig.to_der().as_bytes()),
        )
    }

    #[test]
    fn accepts_increasing_counter() {
        let hash = [9u8; 32];
        let (pk, obj) = sign_assertion(APP_ID, 3, &hash);
        let verified = verify(&VerifyInput {
            app_id: APP_ID,
            public_key: &pk,
            assertion_object: &obj,
            client_data_hash: &hash,
            previous_counter: 2,
        })
        .unwrap();
        assert_eq!(verified.counter, 3);
    }

    #[test]
    fn rejects_stale_counter() {
        let hash = [9u8; 32];
        let (pk, obj) = sign_assertion(APP_ID, 2, &hash);
        let err = verify(&VerifyInput {
            app_id: APP_ID,
            public_key: &pk,
            assertion_object: &obj,
            client_data_hash: &hash,
            previous_counter: 2,
        })
        .unwrap_err();
        assert!(matches!(err, Error::Assertion("counter must increase")));
    }

    #[test]
    fn rejects_wrong_app_id() {
        let hash = [9u8; 32];
        let (pk, obj) = sign_assertion(APP_ID, 1, &hash);
        let err = verify(&VerifyInput {
            app_id: "OTHER.io.example.app",
            public_key: &pk,
            assertion_object: &obj,
            client_data_hash: &hash,
            previous_counter: 0,
        })
        .unwrap_err();
        assert!(matches!(err, Error::Binding(_)));
    }

    #[test]
    fn rejects_wrong_signature() {
        let hash = [9u8; 32];
        let (_pk, obj) = sign_assertion(APP_ID, 1, &hash);
        let other = SigningKey::random(&mut OsRng);
        let other_pk = other
            .verifying_key()
            .to_encoded_point(false)
            .as_bytes()
            .to_vec();
        let err = verify(&VerifyInput {
            app_id: APP_ID,
            public_key: &other_pk,
            assertion_object: &obj,
            client_data_hash: &hash,
            previous_counter: 0,
        })
        .unwrap_err();
        assert!(matches!(err, Error::Assertion("signature")));
    }
}
