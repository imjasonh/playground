//! VAPID — Voluntary Application Server Identification (RFC 8292).
//!
//! The application server proves its identity to the push service with a signed
//! JWT (ES256 = ECDSA over P-256 with SHA-256). The same key pair's public key
//! is what a browser passes as `applicationServerKey` when subscribing.

use p256::ecdsa::signature::Signer;
use p256::ecdsa::{Signature, SigningKey, VerifyingKey};
use p256::SecretKey;
use rand_core::OsRng;
use serde_json::json;

use crate::b64;
use crate::error::Error;

/// The fixed ES256 JWT header, `{"typ":"JWT","alg":"ES256"}`.
const JWT_HEADER: &[u8] = br#"{"typ":"JWT","alg":"ES256"}"#;

/// A VAPID signing key (a P-256 private key).
#[derive(Clone)]
pub struct VapidKey {
    signing: SigningKey,
}

impl VapidKey {
    /// Build from the raw 32-byte private scalar.
    pub fn from_secret_bytes(bytes: &[u8]) -> Result<Self, Error> {
        let signing = SigningKey::from_slice(bytes).map_err(|_| Error::InvalidPrivateKey)?;
        Ok(Self { signing })
    }

    /// Build from a base64url-encoded 32-byte private scalar.
    pub fn from_base64url(s: &str) -> Result<Self, Error> {
        Self::from_secret_bytes(&b64::decode(s)?)
    }

    /// Generate a fresh random VAPID key (used by tooling and tests).
    pub fn generate() -> Self {
        let secret = SecretKey::random(&mut OsRng);
        Self {
            signing: SigningKey::from(secret),
        }
    }

    /// The verifying (public) key.
    pub fn verifying_key(&self) -> VerifyingKey {
        *self.signing.verifying_key()
    }

    /// The public key as a 65-byte uncompressed SEC1 point.
    pub fn public_key_bytes(&self) -> [u8; 65] {
        let encoded = self.signing.verifying_key().to_encoded_point(false);
        let mut out = [0u8; 65];
        out.copy_from_slice(encoded.as_bytes());
        out
    }

    /// The public key as base64url — what the browser uses as
    /// `applicationServerKey` and what appears in the `k=` auth parameter.
    pub fn public_key_base64url(&self) -> String {
        b64::encode(self.public_key_bytes())
    }

    /// The private scalar as base64url (for emitting freshly generated keys).
    pub fn private_key_base64url(&self) -> String {
        b64::encode(self.signing.to_bytes())
    }

    /// Sign a VAPID JWT for the given audience (push service origin), `sub`
    /// contact, and absolute expiry (seconds since the Unix epoch).
    pub fn sign_jwt(&self, audience: &str, subject: &str, exp_unix: u64) -> String {
        let claims = json!({ "aud": audience, "exp": exp_unix, "sub": subject });
        // serde_json on an object of strings/numbers cannot fail to serialize.
        let claims_bytes = serde_json::to_vec(&claims).expect("serialize JWT claims");

        let signing_input = format!("{}.{}", b64::encode(JWT_HEADER), b64::encode(&claims_bytes));
        let signature: Signature = self.signing.sign(signing_input.as_bytes());
        format!("{signing_input}.{}", b64::encode(signature.to_bytes()))
    }

    /// The `Authorization` header value for the aes128gcm scheme
    /// (RFC 8292 §4): `vapid t=<jwt>, k=<public-key>`.
    pub fn authorization_header(&self, audience: &str, subject: &str, exp_unix: u64) -> String {
        format!(
            "vapid t={}, k={}",
            self.sign_jwt(audience, subject, exp_unix),
            self.public_key_base64url()
        )
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use p256::ecdsa::signature::Verifier;

    /// Decode the three dot-separated JWT segments.
    fn split_jwt(token: &str) -> (Vec<u8>, Vec<u8>, Vec<u8>) {
        let parts: Vec<&str> = token.split('.').collect();
        assert_eq!(parts.len(), 3, "JWT must have three segments");
        (
            b64::decode(parts[0]).unwrap(),
            b64::decode(parts[1]).unwrap(),
            b64::decode(parts[2]).unwrap(),
        )
    }

    #[test]
    fn jwt_header_and_claims_are_correct() {
        let key = VapidKey::generate();
        let token = key.sign_jwt(
            "https://push.example.net",
            "mailto:a@example.com",
            1_700_000_000,
        );
        let (header, claims, sig) = split_jwt(&token);

        assert_eq!(header, JWT_HEADER);
        let claims: serde_json::Value = serde_json::from_slice(&claims).unwrap();
        assert_eq!(claims["aud"], "https://push.example.net");
        assert_eq!(claims["sub"], "mailto:a@example.com");
        assert_eq!(claims["exp"], 1_700_000_000u64);
        assert_eq!(sig.len(), 64, "ES256 signature is r||s = 64 bytes");
    }

    #[test]
    fn jwt_signature_verifies_with_public_key() {
        let key = VapidKey::generate();
        let token = key.sign_jwt(
            "https://push.example.net",
            "mailto:a@example.com",
            1_700_000_000,
        );
        let dot = token.rfind('.').unwrap();
        let signing_input = &token[..dot];
        let (_, _, sig_bytes) = split_jwt(&token);

        let signature = Signature::from_slice(&sig_bytes).unwrap();
        key.verifying_key()
            .verify(signing_input.as_bytes(), &signature)
            .expect("signature must verify against the VAPID public key");
    }

    #[test]
    fn round_trips_private_key_encoding() {
        let key = VapidKey::generate();
        let restored = VapidKey::from_base64url(&key.private_key_base64url()).unwrap();
        assert_eq!(key.public_key_bytes(), restored.public_key_bytes());
    }

    #[test]
    fn authorization_header_has_t_and_k_params() {
        let key = VapidKey::generate();
        let header = key.authorization_header("https://push.example.net", "mailto:a@b.com", 1);
        assert!(header.starts_with("vapid t="));
        assert!(header.contains(", k="));
        assert!(header.contains(&key.public_key_base64url()));
    }
}
