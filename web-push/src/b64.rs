//! base64url helpers.
//!
//! Web Push uses unpadded base64url (RFC 7515 §2) everywhere: subscription
//! keys, VAPID keys, and JWT segments. Encoding always emits unpadded
//! base64url; decoding is tolerant of padding and of the standard alphabet so
//! that subscriptions produced by any browser are accepted.

use base64::engine::general_purpose::{STANDARD, STANDARD_NO_PAD, URL_SAFE, URL_SAFE_NO_PAD};
use base64::Engine;

use crate::error::Error;

/// Encode bytes as unpadded base64url.
pub fn encode(bytes: impl AsRef<[u8]>) -> String {
    URL_SAFE_NO_PAD.encode(bytes)
}

/// Decode base64url (or base64) text, tolerating optional padding.
pub fn decode(s: &str) -> Result<Vec<u8>, Error> {
    let s = s.trim();
    let has_pad = s.ends_with('=');
    let url_safe = s.contains('-') || s.contains('_');

    let attempt = match (url_safe, has_pad) {
        (true, true) => URL_SAFE.decode(s),
        (true, false) => URL_SAFE_NO_PAD.decode(s),
        (false, true) => STANDARD.decode(s),
        (false, false) => STANDARD_NO_PAD.decode(s),
    };
    attempt.map_err(|_| Error::Base64)
}

/// Decode into a fixed-size array, erroring if the length is wrong.
pub fn decode_array<const N: usize>(s: &str) -> Result<[u8; N], Error> {
    let v = decode(s)?;
    if v.len() != N {
        return Err(Error::Base64);
    }
    let mut out = [0u8; N];
    out.copy_from_slice(&v);
    Ok(out)
}
