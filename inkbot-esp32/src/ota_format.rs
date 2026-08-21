//! Host-testable encoding helpers shared with on-device OTA verify.

/// DSSE Pre-Authentication Encoding (https://github.com/secure-systems-lab/dsse).
///
/// `PAE("DSSEv1", payloadType, payload)` is
/// `"DSSEv1 <len(type)> <type> <len(payload)> <payload>"`.
pub fn pae_dsse_v1(payload_type: &str, payload: &[u8]) -> Vec<u8> {
    let mut out = Vec::with_capacity(64 + payload_type.len() + payload.len());
    out.extend_from_slice(b"DSSEv1 ");
    out.extend_from_slice(payload_type.len().to_string().as_bytes());
    out.push(b' ');
    out.extend_from_slice(payload_type.as_bytes());
    out.push(b' ');
    out.extend_from_slice(payload.len().to_string().as_bytes());
    out.push(b' ');
    out.extend_from_slice(payload);
    out
}

/// Base64url without padding (RFC 4648 §5).
pub fn b64url(input: &[u8]) -> String {
    const TABLE: &[u8; 64] = b"ABCDEFGHIJKLMNOPQRSTUVWXYZabcdefghijklmnopqrstuvwxyz0123456789-_";
    let mut out = String::with_capacity((input.len() * 4).div_ceil(3));
    let mut i = 0;
    while i < input.len() {
        let b0 = input[i];
        let b1 = if i + 1 < input.len() { input[i + 1] } else { 0 };
        let b2 = if i + 2 < input.len() { input[i + 2] } else { 0 };
        let n = ((b0 as u32) << 16) | ((b1 as u32) << 8) | (b2 as u32);
        out.push(TABLE[((n >> 18) & 63) as usize] as char);
        out.push(TABLE[((n >> 12) & 63) as usize] as char);
        if i + 1 < input.len() {
            out.push(TABLE[((n >> 6) & 63) as usize] as char);
        }
        if i + 2 < input.len() {
            out.push(TABLE[(n & 63) as usize] as char);
        }
        i += 3;
    }
    out
}

#[cfg(test)]
mod tests {
    use super::{b64url, pae_dsse_v1};

    #[test]
    fn pae_matches_dsse_spec_example_shape() {
        let pae = pae_dsse_v1("application/vnd.in-toto+json", b"{}");
        assert_eq!(pae, b"DSSEv1 28 application/vnd.in-toto+json 2 {}".to_vec());
    }

    #[test]
    fn b64url_no_pad_is_rfc4648() {
        assert_eq!(b64url(b""), "");
        assert_eq!(b64url(b"f"), "Zg");
        assert_eq!(b64url(b"fo"), "Zm8");
        assert_eq!(b64url(b"foo"), "Zm9v");
        assert_eq!(b64url(&[0xfb, 0xff]), "-_8");
    }
}
