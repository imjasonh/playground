//! Client data JSON that the iOS app hashes and sends to `attestKey`.
//!
//! The hash is over the raw JSON bytes the client posts. The server never
//! re-serializes that block before hashing.

use serde::Deserialize;
use sha2::{Digest, Sha256};

use crate::error::Error;

const MAX_CLIENT_DATA_BYTES: usize = 2 * 1024;
const MAX_FIELD_CHARS: usize = 128;

/// Fields the iOS app binds into the attestation.
#[derive(Debug, Clone, PartialEq, Eq, Deserialize)]
pub struct ClientData {
    pub challenge: String,
    #[serde(rename = "userId")]
    pub user_id: String,
    #[serde(rename = "deviceId")]
    pub device_id: String,
}

impl ClientData {
    /// Parse raw JSON bytes and reject empty or oversized fields.
    pub fn parse(raw: &[u8]) -> Result<Self, Error> {
        if raw.is_empty() || raw.len() > MAX_CLIENT_DATA_BYTES {
            return Err(Error::BadRequest(
                "clientData is missing or too large".into(),
            ));
        }
        let data: Self = serde_json::from_slice(raw)
            .map_err(|_| Error::BadRequest("clientData is not JSON".into()))?;
        data.check_fields()?;
        Ok(data)
    }

    fn check_fields(&self) -> Result<(), Error> {
        for (name, value) in [
            ("challenge", self.challenge.as_str()),
            ("userId", self.user_id.as_str()),
            ("deviceId", self.device_id.as_str()),
        ] {
            if value.is_empty() || value.len() > MAX_FIELD_CHARS {
                return Err(Error::BadRequest(format!("{name} is empty or too long")));
            }
        }
        Ok(())
    }
}

/// SHA-256 of the exact client JSON bytes passed to `attestKey`.
pub fn hash(raw: &[u8]) -> [u8; 32] {
    Sha256::digest(raw).into()
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn parse_camel_case() {
        let raw = br#"{"challenge":"abc","userId":"u1","deviceId":"d1"}"#;
        let data = ClientData::parse(raw).unwrap();
        assert_eq!(data.user_id, "u1");
        assert_eq!(data.device_id, "d1");
        assert_eq!(data.challenge, "abc");
    }

    #[test]
    fn reject_empty_user() {
        let raw = br#"{"challenge":"abc","userId":"","deviceId":"d1"}"#;
        assert!(ClientData::parse(raw).is_err());
    }

    #[test]
    fn hash_is_stable() {
        let raw = br#"{"challenge":"abc","userId":"u1","deviceId":"d1"}"#;
        assert_eq!(hash(raw), hash(raw));
        assert_ne!(
            hash(raw),
            hash(br#"{"challenge":"abc","userId":"u2","deviceId":"d1"}"#)
        );
    }
}
