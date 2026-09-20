//! Base64 helpers.
//!
//! Apple's `keyId` is standard base64. Client payloads and JWT segments use
//! unpadded base64url. Decoding accepts either alphabet and optional padding.

use base64::engine::general_purpose::{STANDARD, STANDARD_NO_PAD, URL_SAFE, URL_SAFE_NO_PAD};
use base64::Engine;

use crate::error::Error;

/// Encode bytes as unpadded base64url.
pub fn encode_url(bytes: impl AsRef<[u8]>) -> String {
    URL_SAFE_NO_PAD.encode(bytes)
}

/// Encode bytes as standard base64 (with padding), matching `DCAppAttestService`.
pub fn encode_std(bytes: impl AsRef<[u8]>) -> String {
    STANDARD.encode(bytes)
}

/// Decode base64 or base64url text, tolerating optional padding.
pub fn decode(s: &str) -> Result<Vec<u8>, Error> {
    let s = s.trim();
    if s.is_empty() {
        return Err(Error::Base64);
    }
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

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn round_trip_url() {
        let raw = b"hello world";
        let enc = encode_url(raw);
        assert_eq!(decode(&enc).unwrap(), raw);
    }

    #[test]
    fn decode_std_padded() {
        let raw = b"\x01\x02\x03\x04";
        let enc = encode_std(raw);
        assert_eq!(decode(&enc).unwrap(), raw);
    }
}
