//! ECDSA verification over P-256 and P-384.
//!
//! The rules from `docs/formats.md` are enforced here explicitly: `r` and `s`
//! must be in 1 through n - 1, and the public key must be an uncompressed
//! point on the curve other than the point at infinity. `p256` and `p384` are
//! provisional backends until phase 0 picks the implementation phase 7
//! proves.

use p256::ecdsa::signature::hazmat::PrehashVerifier;

/// The P-256 group order, big-endian.
const P256_ORDER: [u8; 32] = [
    0xff, 0xff, 0xff, 0xff, 0x00, 0x00, 0x00, 0x00, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff,
    0xbc, 0xe6, 0xfa, 0xad, 0xa7, 0x17, 0x9e, 0x84, 0xf3, 0xb9, 0xca, 0xc2, 0xfc, 0x63, 0x25, 0x51,
];

/// The P-384 group order, big-endian.
const P384_ORDER: [u8; 48] = [
    0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff,
    0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xc7, 0x63, 0x4d, 0x81, 0xf4, 0x37, 0x2d, 0xdf,
    0x58, 0x1a, 0x0d, 0xb2, 0x48, 0xb0, 0xa7, 0x7a, 0xec, 0xec, 0x19, 0x6a, 0xcc, 0xc5, 0x29, 0x73,
];

/// Reports whether the big-endian number `x` is in 1 through `order - 1`.
fn in_scalar_range(x: &[u8], order: &[u8]) -> bool {
    if x.len() != order.len() || x.iter().all(|&b| b == 0) {
        return false;
    }
    for (a, b) in x.iter().zip(order) {
        if a != b {
            return a < b;
        }
    }
    false
}

/// Reports whether `point` is an uncompressed P-256 point on the curve.
pub fn p256_public_key_ok(point: &[u8; 65]) -> bool {
    point.first() == Some(&0x04) && p256::ecdsa::VerifyingKey::from_sec1_bytes(point).is_ok()
}

/// Reports whether `point` is an uncompressed P-384 point on the curve.
pub fn p384_public_key_ok(point: &[u8; 97]) -> bool {
    point.first() == Some(&0x04) && p384::ecdsa::VerifyingKey::from_sec1_bytes(point).is_ok()
}

/// Verifies an ECDSA P-256 signature `(r, s)` over the digest `prehash`.
///
/// `prehash` is the message digest, used as FIPS 186-5 describes.
pub fn p256_verify_prehash(point: &[u8; 65], prehash: &[u8], r: &[u8; 32], s: &[u8; 32]) -> bool {
    if !in_scalar_range(r, &P256_ORDER) || !in_scalar_range(s, &P256_ORDER) {
        return false;
    }
    if point.first() != Some(&0x04) {
        return false;
    }
    let Ok(key) = p256::ecdsa::VerifyingKey::from_sec1_bytes(point) else {
        return false;
    };
    let Ok(sig) = p256::ecdsa::Signature::from_scalars(*r, *s) else {
        return false;
    };
    key.verify_prehash(prehash, &sig).is_ok()
}

/// Verifies an ECDSA P-384 signature `(r, s)` over the digest `prehash`.
///
/// `prehash` may be a SHA-256 or SHA-384 digest. A digest shorter than the
/// group order is used as FIPS 186-5 describes, without padding.
pub fn p384_verify_prehash(point: &[u8; 97], prehash: &[u8], r: &[u8; 48], s: &[u8; 48]) -> bool {
    if !in_scalar_range(r, &P384_ORDER) || !in_scalar_range(s, &P384_ORDER) {
        return false;
    }
    if point.first() != Some(&0x04) {
        return false;
    }
    let Ok(key) = p384::ecdsa::VerifyingKey::from_sec1_bytes(point) else {
        return false;
    };
    let Ok(sig) = p384::ecdsa::Signature::from_scalars(*r, *s) else {
        return false;
    };
    key.verify_prehash(prehash, &sig).is_ok()
}

#[cfg(test)]
#[allow(clippy::indexing_slicing, clippy::arithmetic_side_effects)]
mod tests {
    use super::*;
    use p256::ecdsa::signature::hazmat::PrehashSigner;

    fn p256_key() -> p256::ecdsa::SigningKey {
        p256::ecdsa::SigningKey::from_slice(&[7u8; 32]).unwrap()
    }

    fn p384_key() -> p384::ecdsa::SigningKey {
        p384::ecdsa::SigningKey::from_slice(&[9u8; 48]).unwrap()
    }

    fn point256(k: &p256::ecdsa::SigningKey) -> [u8; 65] {
        k.verifying_key()
            .to_sec1_point(false)
            .as_bytes()
            .try_into()
            .unwrap()
    }

    fn point384(k: &p384::ecdsa::SigningKey) -> [u8; 97] {
        k.verifying_key()
            .to_sec1_point(false)
            .as_bytes()
            .try_into()
            .unwrap()
    }

    #[test]
    fn p256_round_trip() {
        let k = p256_key();
        let digest = crate::sha::sha256(b"image");
        let sig: p256::ecdsa::Signature = k.sign_prehash(&digest).unwrap();
        let (r, s) = sig.split_bytes();
        let (r, s): ([u8; 32], [u8; 32]) = (r.into(), s.into());
        let pt = point256(&k);
        assert!(p256_public_key_ok(&pt));
        assert!(p256_verify_prehash(&pt, &digest, &r, &s));
        assert!(!p256_verify_prehash(
            &pt,
            &crate::sha::sha256(b"other"),
            &r,
            &s
        ));
        assert!(!p256_verify_prehash(&pt, &digest, &[0u8; 32], &s));
        assert!(!p256_verify_prehash(&pt, &digest, &r, &P256_ORDER));
    }

    #[test]
    fn p384_over_sha256_round_trip() {
        let k = p384_key();
        let digest = crate::sha::sha256(b"attrs");
        let sig: p384::ecdsa::Signature = k.sign_prehash(&digest).unwrap();
        let (r, s) = sig.split_bytes();
        let (r, s): ([u8; 48], [u8; 48]) = (r.into(), s.into());
        let pt = point384(&k);
        assert!(p384_public_key_ok(&pt));
        assert!(p384_verify_prehash(&pt, &digest, &r, &s));
        let mut bad = pt;
        bad[96] ^= 1;
        assert!(!p384_public_key_ok(&bad));
        assert!(!p384_verify_prehash(&bad, &digest, &r, &s));
    }

    #[test]
    fn scalar_range() {
        let mut one = [0u8; 32];
        one[31] = 1;
        assert!(in_scalar_range(&one, &P256_ORDER));
        assert!(!in_scalar_range(&[0u8; 32], &P256_ORDER));
        assert!(!in_scalar_range(&P256_ORDER, &P256_ORDER));
        let mut below = P256_ORDER;
        below[31] -= 1;
        assert!(in_scalar_range(&below, &P256_ORDER));
    }
}
