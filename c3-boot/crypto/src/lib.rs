//! Signature checks for the c3-boot bootloader.
//!
//! Each function returns `true` only if the signature is valid under the rules
//! in `docs/esp32c3-verified-ota-plan.md`. Ed25519 uses `ed25519-dalek` as a
//! provisional backend until phase 0 chooses the implementation that phase 7
//! proves. The rules below are enforced here explicitly, so they don't depend
//! on the backend's defaults.

#![cfg_attr(not(test), no_std)]

use ed25519_dalek::Signature;
use ed25519_dalek::VerifyingKey;

/// The field prime 2^255 - 19, little-endian.
const FIELD_PRIME: [u8; 32] = [
    0xed, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff,
    0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0x7f,
];

/// The field element p - 1, little-endian.
const FIELD_PRIME_MINUS_ONE: [u8; 32] = [
    0xec, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff,
    0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0x7f,
];

/// The field element 1, little-endian.
const FIELD_ONE: [u8; 32] = [
    0x01, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00,
    0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00,
];

/// The order L of the Ed25519 base point, little-endian.
const GROUP_ORDER: [u8; 32] = [
    0xed, 0xd3, 0xf5, 0x5c, 0x1a, 0x63, 0x12, 0x58, 0xd6, 0x9c, 0xf7, 0xa2, 0xde, 0xf9, 0xde, 0x14,
    0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x10,
];

/// Reports whether the little-endian number `a` is less than `b`.
fn less_than_le(a: &[u8; 32], b: &[u8; 32]) -> bool {
    for (x, y) in a.iter().rev().zip(b.iter().rev()) {
        if x != y {
            return x < y;
        }
    }
    false
}

/// Reports whether `encoding` is the canonical encoding of a field element y
/// and a sign bit.
///
/// The y-coordinate must be below p. The sign bit must be clear when x is 0,
/// which happens exactly when y is 1 or p - 1.
fn is_canonical_point(encoding: &[u8; 32]) -> bool {
    let mut y = *encoding;
    let Some(top) = y.last_mut() else {
        return false;
    };
    let sign = *top & 0x80 != 0;
    *top &= 0x7f;
    if !less_than_le(&y, &FIELD_PRIME) {
        return false;
    }
    !(sign && (y == FIELD_ONE || y == FIELD_PRIME_MINUS_ONE))
}

/// Reports whether `public_key` can ever verify a signature under
/// [`ed25519_verify`]: a canonical encoding of a point on the curve that
/// doesn't have small order.
pub fn ed25519_public_key_ok(public_key: &[u8; 32]) -> bool {
    if !is_canonical_point(public_key) {
        return false;
    }
    match VerifyingKey::from_bytes(public_key) {
        Ok(key) => !key.is_weak(),
        Err(_) => false,
    }
}

/// Verifies an Ed25519 signature with the strict rules from the plan.
///
/// Rejects `S` at or above the group order, a non-canonical encoding of `A`
/// or `R`, and `A` or `R` of small order. Accepts only if `[S]B - [k]A`
/// equals `R` without multiplying by the cofactor.
pub fn ed25519_verify(public_key: &[u8; 32], message: &[u8], signature: &[u8; 64]) -> bool {
    let Some((r, s)) = signature.split_first_chunk::<32>() else {
        return false;
    };
    let Ok(s) = <&[u8; 32]>::try_from(s) else {
        return false;
    };
    if !less_than_le(s, &GROUP_ORDER) {
        return false;
    }
    if !ed25519_public_key_ok(public_key) || !is_canonical_point(r) {
        return false;
    }
    let Ok(key) = VerifyingKey::from_bytes(public_key) else {
        return false;
    };
    key.verify_strict(message, &Signature::from_bytes(signature))
        .is_ok()
}

#[cfg(test)]
#[allow(clippy::indexing_slicing, clippy::arithmetic_side_effects)]
mod tests {
    use super::*;
    use ed25519_dalek::Signer;
    use ed25519_dalek::SigningKey;

    fn key(seed: u8) -> SigningKey {
        SigningKey::from_bytes(&[seed; 32])
    }

    #[test]
    fn accepts_valid_signature() {
        let k = key(1);
        let sig = k.sign(b"message").to_bytes();
        assert!(ed25519_verify(
            &k.verifying_key().to_bytes(),
            b"message",
            &sig
        ));
    }

    #[test]
    fn rejects_wrong_message_or_key() {
        let k = key(1);
        let sig = k.sign(b"message").to_bytes();
        assert!(!ed25519_verify(
            &k.verifying_key().to_bytes(),
            b"messagf",
            &sig
        ));
        assert!(!ed25519_verify(
            &key(2).verifying_key().to_bytes(),
            b"message",
            &sig
        ));
    }

    #[test]
    fn rejects_s_plus_group_order() {
        let k = key(3);
        let mut sig = k.sign(b"m").to_bytes();
        let mut carry = 0u16;
        for i in 0..32 {
            let sum = u16::from(sig[32 + i]) + u16::from(GROUP_ORDER[i]) + carry;
            sig[32 + i] = sum as u8;
            carry = sum >> 8;
        }
        assert_eq!(carry, 0, "S + L fits in 32 bytes for this key");
        assert!(!ed25519_verify(&k.verifying_key().to_bytes(), b"m", &sig));
    }

    #[test]
    fn rejects_non_canonical_y() {
        let mut y = FIELD_PRIME;
        y[0] = y[0].wrapping_add(1);
        assert!(!is_canonical_point(&y));
        assert!(!is_canonical_point(&FIELD_PRIME));
        assert!(is_canonical_point(&FIELD_PRIME_MINUS_ONE));
    }

    #[test]
    fn rejects_negative_zero_x() {
        let mut one = FIELD_ONE;
        one[31] |= 0x80;
        assert!(!is_canonical_point(&one));
        let mut minus_one = FIELD_PRIME_MINUS_ONE;
        minus_one[31] |= 0x80;
        assert!(!is_canonical_point(&minus_one));
    }

    #[test]
    fn rejects_small_order_key() {
        let k = key(4);
        let sig = k.sign(b"m").to_bytes();
        // The identity point, y = 1, is canonical but has order 1.
        assert!(!ed25519_verify(&FIELD_ONE, b"m", &sig));
    }

    #[test]
    fn checks_public_keys() {
        assert!(ed25519_public_key_ok(&key(5).verifying_key().to_bytes()));
        assert!(!ed25519_public_key_ok(&FIELD_ONE));
        assert!(!ed25519_public_key_ok(&FIELD_PRIME));
    }

    #[test]
    fn compares_little_endian() {
        let mut a = [0u8; 32];
        let mut b = [0u8; 32];
        a[0] = 2;
        b[31] = 1;
        assert!(less_than_le(&a, &b));
        assert!(!less_than_le(&b, &a));
        assert!(!less_than_le(&a, &a));
    }
}
