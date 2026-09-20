//! HS256 JWT used as the short-lived access token after a successful attest.

use hmac::{Hmac, Mac};
use serde::{Deserialize, Serialize};
use sha2::Sha256;

use crate::b64;
use crate::error::Error;

type HmacSha256 = Hmac<Sha256>;

const HEADER_JSON: &[u8] = br#"{"alg":"HS256","typ":"JWT"}"#;

/// Claims bound into the access token.
#[derive(Debug, Clone, PartialEq, Eq, Serialize, Deserialize)]
pub struct Claims {
    pub iss: String,
    pub sub: String,
    pub device_id: String,
    pub key_id: String,
    pub iat: u64,
    pub exp: u64,
    #[serde(default, skip_serializing_if = "std::ops::Not::not")]
    pub unattested: bool,
}

/// Mint a compact HS256 JWT.
pub fn mint(secret: &str, claims: &Claims) -> Result<String, Error> {
    if secret.is_empty() {
        return Err(Error::Token("secret missing"));
    }
    let header = b64::encode_url(HEADER_JSON);
    let payload = serde_json::to_vec(claims).map_err(|_| Error::Token("claims"))?;
    let signing_input = format!("{header}.{}", b64::encode_url(payload));
    let sig = hmac_bytes(secret, signing_input.as_bytes())?;
    Ok(format!("{signing_input}.{}", b64::encode_url(sig)))
}

/// Verify signature and expiry. `now_unix` must be strictly less than `exp`.
pub fn verify(secret: &str, token: &str, now_unix: u64) -> Result<Claims, Error> {
    let token = token.trim();
    if token.is_empty() {
        return Err(Error::Token("missing"));
    }
    let mut parts = token.split('.');
    let header = parts.next().ok_or(Error::Token("invalid"))?;
    let payload = parts.next().ok_or(Error::Token("invalid"))?;
    let sig = parts.next().ok_or(Error::Token("invalid"))?;
    if parts.next().is_some() {
        return Err(Error::Token("invalid"));
    }
    let signing_input = format!("{header}.{payload}");
    let want = hmac_bytes(secret, signing_input.as_bytes())?;
    let got = b64::decode(sig).map_err(|_| Error::Token("invalid"))?;
    if !ct_eq(&want, &got) {
        return Err(Error::Token("invalid"));
    }
    let claims_raw = b64::decode(payload).map_err(|_| Error::Token("invalid"))?;
    let claims: Claims =
        serde_json::from_slice(&claims_raw).map_err(|_| Error::Token("invalid"))?;
    if claims.exp <= now_unix {
        return Err(Error::Token("expired"));
    }
    if claims.sub.is_empty() || claims.device_id.is_empty() {
        return Err(Error::Token("invalid"));
    }
    Ok(claims)
}

fn hmac_bytes(secret: &str, message: &[u8]) -> Result<Vec<u8>, Error> {
    let mut mac = HmacSha256::new_from_slice(secret.as_bytes())
        .map_err(|_| Error::Token("secret missing"))?;
    mac.update(message);
    Ok(mac.finalize().into_bytes().to_vec())
}

fn ct_eq(a: &[u8], b: &[u8]) -> bool {
    if a.len() != b.len() {
        return false;
    }
    let mut diff = 0u8;
    for (x, y) in a.iter().zip(b.iter()) {
        diff |= x ^ y;
    }
    diff == 0
}

#[cfg(test)]
mod tests {
    use super::*;

    fn sample(now: u64) -> Claims {
        Claims {
            iss: "app-attest".into(),
            sub: "user-1".into(),
            device_id: "dev-1".into(),
            key_id: "key-1".into(),
            iat: now,
            exp: now + 60,
            unattested: false,
        }
    }

    #[test]
    fn round_trip() {
        let claims = sample(1_700_000_000);
        let token = mint("secret", &claims).unwrap();
        let got = verify("secret", &token, 1_700_000_000).unwrap();
        assert_eq!(got, claims);
    }

    #[test]
    fn reject_wrong_secret() {
        let token = mint("secret", &sample(10)).unwrap();
        assert!(verify("other", &token, 10).is_err());
    }

    #[test]
    fn reject_expired() {
        let token = mint("secret", &sample(10)).unwrap();
        assert!(matches!(
            verify("secret", &token, 70),
            Err(Error::Token("expired"))
        ));
    }

    #[test]
    fn reject_tampered_payload() {
        let token = mint("secret", &sample(10)).unwrap();
        let mut parts: Vec<&str> = token.split('.').collect();
        parts[1] = "aaaa";
        let bad = parts.join(".");
        assert!(verify("secret", &bad, 10).is_err());
    }
}
