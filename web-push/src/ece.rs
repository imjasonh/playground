//! Encrypted Content-Encoding for HTTP (aes128gcm), RFC 8188, plus the Web Push
//! message-encryption key derivation of RFC 8291.
//!
//! Layout of an aes128gcm body (single record, as used by Web Push):
//!
//! ```text
//! +----------+--------+--------+-------------------+------------------------+
//! | salt(16) | rs(4)  | idlen  | keyid (= as_pub)  | ciphertext + GCM tag   |
//! +----------+--------+--------+-------------------+------------------------+
//! ```
//!
//! For Web Push the `keyid` is the application server's *ephemeral* P-256
//! public key (65-byte uncompressed point).

// aes-gcm 0.10 depends on generic-array 0.14, which the upstream maintainers
// blanket-deprecated in favor of 1.x. We must still name `GenericArray` to pass
// keys/nonces to the AEAD, so silence that deprecation in this module only.
#![allow(deprecated)]

use aes_gcm::aead::generic_array::GenericArray;
use aes_gcm::aead::Aead;
use aes_gcm::{Aes128Gcm, KeyInit};
use hkdf::Hkdf;
use p256::elliptic_curve::sec1::ToEncodedPoint;
use p256::{PublicKey, SecretKey};
use sha2::Sha256;

use crate::error::Error;

/// Default record size advertised in the aes128gcm header.
pub const DEFAULT_RECORD_SIZE: u32 = 4096;

const CEK_INFO: &[u8] = b"Content-Encoding: aes128gcm\0";
const NONCE_INFO: &[u8] = b"Content-Encoding: nonce\0";
const WEBPUSH_INFO_PREFIX: &[u8] = b"WebPush: info\0";

/// Per-record overhead: one padding-delimiter octet plus the 16-byte GCM tag.
const RECORD_OVERHEAD: usize = 1 + 16;

/// Serialize a P-256 public key as a 65-byte uncompressed SEC1 point.
pub fn public_key_bytes(pk: &PublicKey) -> [u8; 65] {
    let encoded = pk.to_encoded_point(false);
    let mut out = [0u8; 65];
    out.copy_from_slice(encoded.as_bytes());
    out
}

/// HKDF-SHA256 (Extract then Expand) into an `N`-byte output.
fn hkdf(salt: &[u8], ikm: &[u8], info: &[u8]) -> [u8; 32] {
    let hk = Hkdf::<Sha256>::new(Some(salt), ikm);
    let mut okm = [0u8; 32];
    // Expanding 32 bytes from HKDF-SHA256 never fails.
    hk.expand(info, &mut okm).expect("hkdf expand <= 255*32");
    okm
}

/// RFC 8291 §3.4 step 1: combine the ECDH secret with the subscription `auth`
/// secret to derive the input keying material (IKM) for the content encoding.
fn webpush_ikm(
    ecdh_secret: &[u8],
    auth_secret: &[u8; 16],
    ua_public: &[u8; 65],
    as_public: &[u8; 65],
) -> [u8; 32] {
    let mut info = Vec::with_capacity(WEBPUSH_INFO_PREFIX.len() + 130);
    info.extend_from_slice(WEBPUSH_INFO_PREFIX);
    info.extend_from_slice(ua_public);
    info.extend_from_slice(as_public);
    hkdf(auth_secret, ecdh_secret, &info)
}

/// Derive the content-encryption key (16 bytes) and base nonce (12 bytes) from
/// the random salt and the input keying material (RFC 8188 §2.2/§2.3).
fn derive_cek_nonce(salt: &[u8; 16], ikm: &[u8]) -> ([u8; 16], [u8; 12]) {
    let cek_full = hkdf(salt, ikm, CEK_INFO);
    let nonce_full = hkdf(salt, ikm, NONCE_INFO);
    let mut cek = [0u8; 16];
    cek.copy_from_slice(&cek_full[..16]);
    let mut nonce = [0u8; 12];
    nonce.copy_from_slice(&nonce_full[..12]);
    (cek, nonce)
}

/// Encrypt a single aes128gcm record given input keying material directly.
///
/// This is the pure RFC 8188 layer (no ECDH); it is exercised directly by the
/// RFC 8188 Appendix A.1 known-answer test.
pub fn content_encrypt(
    ikm: &[u8],
    salt: &[u8; 16],
    keyid: &[u8],
    plaintext: &[u8],
    record_size: u32,
) -> Result<Vec<u8>, Error> {
    let rs = record_size as usize;
    let max_plaintext = rs.saturating_sub(RECORD_OVERHEAD);
    if plaintext.len() > max_plaintext {
        return Err(Error::PayloadTooLarge { max: max_plaintext });
    }
    if keyid.len() > u8::MAX as usize {
        return Err(Error::Crypto("keyid too long"));
    }

    let (cek, nonce) = derive_cek_nonce(salt, ikm);

    // Single, final record: data || 0x02 delimiter (no extra zero padding).
    let mut record = Vec::with_capacity(plaintext.len() + 1);
    record.extend_from_slice(plaintext);
    record.push(0x02);

    let cipher = Aes128Gcm::new_from_slice(&cek).map_err(|_| Error::Crypto("bad key length"))?;
    let ciphertext = cipher
        .encrypt(&GenericArray::from(nonce), record.as_slice())
        .map_err(|_| Error::Crypto("aes128gcm encrypt"))?;

    let mut body = Vec::with_capacity(16 + 4 + 1 + keyid.len() + ciphertext.len());
    body.extend_from_slice(salt);
    body.extend_from_slice(&record_size.to_be_bytes());
    body.push(keyid.len() as u8);
    body.extend_from_slice(keyid);
    body.extend_from_slice(&ciphertext);
    Ok(body)
}

/// Decrypt an aes128gcm body's single record given the input keying material.
fn content_decrypt(ikm: &[u8], salt: &[u8; 16], ciphertext: &[u8]) -> Result<Vec<u8>, Error> {
    let (cek, nonce) = derive_cek_nonce(salt, ikm);
    let cipher = Aes128Gcm::new_from_slice(&cek).map_err(|_| Error::Crypto("bad key length"))?;
    let mut plaintext = cipher
        .decrypt(&GenericArray::from(nonce), ciphertext)
        .map_err(|_| Error::Crypto("aes128gcm decrypt"))?;

    // Strip trailing zero padding, then the delimiter octet (0x02 last / 0x01).
    while matches!(plaintext.last(), Some(0u8)) {
        plaintext.pop();
    }
    match plaintext.pop() {
        Some(0x01) | Some(0x02) => Ok(plaintext),
        _ => Err(Error::MalformedBody("missing padding delimiter")),
    }
}

/// The receiver (user agent) keys taken from a PushSubscription.
#[derive(Clone)]
pub struct ReceiverKeys {
    /// The subscription's P-256 public key (`keys.p256dh`).
    pub p256dh: PublicKey,
    /// The subscription's 16-byte authentication secret (`keys.auth`).
    pub auth: [u8; 16],
}

/// Encrypt `plaintext` for a subscription using a caller-supplied ephemeral key
/// and salt (RFC 8291). Deterministic: used both at runtime (with random
/// inputs) and in tests (with fixed inputs).
pub fn encrypt(
    receiver: &ReceiverKeys,
    as_secret: &SecretKey,
    salt: &[u8; 16],
    plaintext: &[u8],
    record_size: u32,
) -> Result<Vec<u8>, Error> {
    let as_public = as_secret.public_key();
    let as_public_bytes = public_key_bytes(&as_public);
    let ua_public_bytes = public_key_bytes(&receiver.p256dh);

    let shared =
        p256::ecdh::diffie_hellman(as_secret.to_nonzero_scalar(), receiver.p256dh.as_affine());
    let ecdh_secret = shared.raw_secret_bytes();
    let ikm = webpush_ikm(
        ecdh_secret.as_ref(),
        &receiver.auth,
        &ua_public_bytes,
        &as_public_bytes,
    );

    content_encrypt(&ikm, salt, &as_public_bytes, plaintext, record_size)
}

/// Decrypt an aes128gcm Web Push body using the subscription's private key.
///
/// This is the user-agent side of RFC 8291; it exists so the full encrypt path
/// can be verified by round-trip in tests.
pub fn decrypt(
    ua_secret: &SecretKey,
    auth_secret: &[u8; 16],
    body: &[u8],
) -> Result<Vec<u8>, Error> {
    if body.len() < 21 {
        return Err(Error::MalformedBody("truncated header"));
    }
    let salt: [u8; 16] = body[0..16].try_into().unwrap();
    let idlen = body[20] as usize;
    let header_end = 21 + idlen;
    if body.len() < header_end {
        return Err(Error::MalformedBody("truncated keyid"));
    }
    let keyid = &body[21..header_end];
    let ciphertext = &body[header_end..];

    let as_public = PublicKey::from_sec1_bytes(keyid).map_err(|_| Error::InvalidPublicKey)?;
    let as_public_bytes = public_key_bytes(&as_public);
    let ua_public_bytes = public_key_bytes(&ua_secret.public_key());

    let shared = p256::ecdh::diffie_hellman(ua_secret.to_nonzero_scalar(), as_public.as_affine());
    let ecdh_secret = shared.raw_secret_bytes();
    let ikm = webpush_ikm(
        ecdh_secret.as_ref(),
        auth_secret,
        &ua_public_bytes,
        &as_public_bytes,
    );

    content_decrypt(&ikm, &salt, ciphertext)
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::b64;
    use rand_core::OsRng;

    /// RFC 8188 Appendix A.1: a single-record aes128gcm known-answer test with
    /// the input keying material supplied directly (no ECDH involved). This
    /// pins the HKDF derivation, record framing, and AES-128-GCM together.
    #[test]
    fn rfc8188_a1_known_answer() {
        let ikm = b64::decode("yqdlZ-tYemfogSmv7Ws5PQ").unwrap();
        let salt = b64::decode_array::<16>("I1BsxtFttlv3u_Oo94xnmw").unwrap();
        let body = content_encrypt(&ikm, &salt, b"", b"I am the walrus", 4096).unwrap();
        assert_eq!(
            b64::encode(&body),
            "I1BsxtFttlv3u_Oo94xnmwAAEAAA-NAVub2qFgBEuQKRapoZu-IxkIva3MEB1PD-ly8Thjg"
        );
    }

    #[test]
    fn webpush_round_trip() {
        let ua_secret = SecretKey::random(&mut OsRng);
        let receiver = ReceiverKeys {
            p256dh: ua_secret.public_key(),
            auth: [7u8; 16],
        };
        let as_secret = SecretKey::random(&mut OsRng);
        let salt = [9u8; 16];
        let plaintext = b"When I grow up, I want to be a watermelon";

        let body = encrypt(&receiver, &as_secret, &salt, plaintext, DEFAULT_RECORD_SIZE).unwrap();

        // The application-server public key must be embedded as the keyid.
        let idlen = body[20] as usize;
        assert_eq!(idlen, 65);
        assert_eq!(
            &body[21..21 + idlen],
            &public_key_bytes(&as_secret.public_key())
        );

        let decrypted = decrypt(&ua_secret, &receiver.auth, &body).unwrap();
        assert_eq!(decrypted, plaintext);
    }

    #[test]
    fn decrypt_rejects_tampered_ciphertext() {
        let ua_secret = SecretKey::random(&mut OsRng);
        let receiver = ReceiverKeys {
            p256dh: ua_secret.public_key(),
            auth: [3u8; 16],
        };
        let as_secret = SecretKey::random(&mut OsRng);
        let mut body = encrypt(
            &receiver,
            &as_secret,
            &[1u8; 16],
            b"secret",
            DEFAULT_RECORD_SIZE,
        )
        .unwrap();
        let last = body.len() - 1;
        body[last] ^= 0xff;
        assert!(decrypt(&ua_secret, &receiver.auth, &body).is_err());
    }

    #[test]
    fn payload_too_large_is_rejected() {
        let ikm = [0u8; 32];
        let salt = [0u8; 16];
        // record_size 50 leaves 33 plaintext bytes; 40 must be rejected.
        let err = content_encrypt(&ikm, &salt, b"", &[0u8; 40], 50).unwrap_err();
        assert!(matches!(err, Error::PayloadTooLarge { max: 33 }));
    }
}
