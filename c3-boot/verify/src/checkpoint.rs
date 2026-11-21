//! The signed checkpoint note that commits a Rekor log to a tree.

use crate::error::Error;
use crate::trustroot::LogKey;
use crate::trustroot::TrustRoot;

/// The em dash and space that start every signature line.
const SIGNATURE_PREFIX: &[u8] = "\u{2014} ".as_bytes();

/// A checkpoint whose signature by a trusted log key has been verified.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub struct Checkpoint<'a> {
    /// The log key that signed it.
    pub log: LogKey<'a>,
    /// The tree size.
    pub size: u64,
    /// The root hash.
    pub root: [u8; 32],
}

/// Splits off the line that ends at the first newline, without the newline.
fn line(text: &[u8]) -> Result<(&[u8], &[u8]), Error> {
    let end = text
        .iter()
        .position(|&b| b == b'\n')
        .ok_or(Error::BadCheckpoint)?;
    let line = text.get(..end).ok_or(Error::BadCheckpoint)?;
    let rest = text
        .get(end.saturating_add(1)..)
        .ok_or(Error::BadCheckpoint)?;
    Ok((line, rest))
}

/// Parses a decimal tree size with no sign and no leading zeros.
fn tree_size(text: &[u8]) -> Result<u64, Error> {
    if text.is_empty() || text.len() > 19 || (text.len() > 1 && text.first() == Some(&b'0')) {
        return Err(Error::BadCheckpoint);
    }
    let mut n = 0u64;
    for &c in text {
        if !c.is_ascii_digit() {
            return Err(Error::BadCheckpoint);
        }
        n = n
            .checked_mul(10)
            .and_then(|n| n.checked_add(u64::from(c.wrapping_sub(b'0'))))
            .ok_or(Error::BadCheckpoint)?;
    }
    if n > i64::MAX as u64 {
        return Err(Error::BadCheckpoint);
    }
    Ok(n)
}

/// The C2SP key ID of an Ed25519 key: the first four bytes of
/// `SHA-256(name || 0x0A || 0x01 || key)`.
pub fn key_id(name: &[u8], key: &[u8; 32]) -> [u8; 4] {
    let h = c3_crypto::sha256_parts(&[name, b"\n", &[0x01], key]);
    let mut id = [0u8; 4];
    if let Some(prefix) = h.first_chunk::<4>() {
        id = *prefix;
    }
    id
}

/// Parses `text` as a checkpoint signed by a log key in `root`, and verifies
/// that key's signature.
///
/// Accepts only the shape in `docs/formats.md`: three body lines, a blank
/// line, and one or more well-formed signature lines, of which exactly one
/// is from the log whose origin is the first line.
pub fn verify<'a>(text: &[u8], root: &TrustRoot<'a>) -> Result<Checkpoint<'a>, Error> {
    let (origin, rest) = line(text)?;
    let (size_text, rest) = line(rest)?;
    let (root_text, rest) = line(rest)?;
    let (blank, mut signatures) = line(rest)?;
    if !blank.is_empty() || signatures.is_empty() {
        return Err(Error::BadCheckpoint);
    }
    let body_len = text
        .len()
        .checked_sub(signatures.len())
        .and_then(|n| n.checked_sub(1))
        .ok_or(Error::BadCheckpoint)?;
    let body = text.get(..body_len).ok_or(Error::BadCheckpoint)?;

    let size = tree_size(size_text)?;
    let root_hash =
        crate::base64::decode_array::<32>(root_text).map_err(|_| Error::BadCheckpoint)?;
    let log = *root
        .logs()
        .find(|l| l.origin == origin)
        .ok_or(Error::NoMatchingKey)?;
    let id = key_id(origin, log.public_key);

    let mut matched: Option<[u8; 64]> = None;
    while !signatures.is_empty() {
        let (sig_line, rest) = line(signatures)?;
        signatures = rest;
        let after_dash = sig_line
            .strip_prefix(SIGNATURE_PREFIX)
            .ok_or(Error::BadCheckpoint)?;
        let space = after_dash
            .iter()
            .position(|&b| b == b' ')
            .ok_or(Error::BadCheckpoint)?;
        let name = after_dash.get(..space).ok_or(Error::BadCheckpoint)?;
        let encoded = after_dash
            .get(space.saturating_add(1)..)
            .ok_or(Error::BadCheckpoint)?;
        if name.is_empty() || !crate::base64::is_canonical(encoded) || encoded.is_empty() {
            return Err(Error::BadCheckpoint);
        }
        if name != origin {
            continue;
        }
        let mut decoded = [0u8; 96];
        let n =
            crate::base64::decode_into(encoded, &mut decoded).map_err(|_| Error::BadCheckpoint)?;
        let value = decoded.get(..n).ok_or(Error::BadCheckpoint)?;
        let Some((hint, sig)) = value.split_first_chunk::<4>() else {
            continue;
        };
        if *hint != id {
            continue;
        }
        let sig: [u8; 64] = sig.try_into().map_err(|_| Error::BadCheckpoint)?;
        if matched.replace(sig).is_some() {
            return Err(Error::BadCheckpoint);
        }
    }
    let sig = matched.ok_or(Error::NoMatchingKey)?;
    if !c3_crypto::ed25519_verify(log.public_key, body, &sig) {
        return Err(Error::BadSignature);
    }
    Ok(Checkpoint {
        log,
        size,
        root: root_hash,
    })
}

#[cfg(test)]
#[allow(clippy::arithmetic_side_effects, clippy::indexing_slicing)]
mod tests {
    use super::*;

    #[test]
    fn parses_tree_sizes() {
        assert_eq!(tree_size(b"0"), Ok(0));
        assert_eq!(tree_size(b"736"), Ok(736));
        assert_eq!(tree_size(b"9223372036854775807"), Ok(i64::MAX as u64));
        for bad in [&b""[..], b"01", b"-1", b"+1", b"9223372036854775808", b"1 "] {
            assert_eq!(tree_size(bad), Err(Error::BadCheckpoint), "{bad:?}");
        }
    }

    #[test]
    fn splits_lines() {
        assert_eq!(line(b"a\nb"), Ok((&b"a"[..], &b"b"[..])));
        assert_eq!(line(b"a"), Err(Error::BadCheckpoint));
    }
}
