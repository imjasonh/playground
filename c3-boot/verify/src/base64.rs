//! Standard base64 with padding, as RFC 4648 section 4 defines it.

use crate::error::Error;

const ALPHABET: &[u8; 64] = b"ABCDEFGHIJKLMNOPQRSTUVWXYZabcdefghijklmnopqrstuvwxyz0123456789+/";

fn value(c: u8) -> Option<u8> {
    match c {
        b'A'..=b'Z' => c.checked_sub(b'A'),
        b'a'..=b'z' => c.checked_sub(b'a').and_then(|v| v.checked_add(26)),
        b'0'..=b'9' => c.checked_sub(b'0').and_then(|v| v.checked_add(52)),
        b'+' => Some(62),
        b'/' => Some(63),
        _ => None,
    }
}

/// Decodes `text` into `out` and returns the number of bytes written.
///
/// `text` must be canonical: a multiple of four characters, padding only at
/// the end, and zero bits in the unused low bits of the last character.
pub fn decode_into(text: &[u8], out: &mut [u8]) -> Result<usize, Error> {
    let (groups, rest) = text.as_chunks::<4>();
    if !rest.is_empty() {
        return Err(Error::BadBase64);
    }
    let mut written = 0usize;
    let last = groups.len().checked_sub(1);
    for (i, group) in groups.iter().enumerate() {
        let is_last = Some(i) == last;
        let pad = match group {
            [_, _, b'=', b'='] if is_last => 2usize,
            [_, _, _, b'='] if is_last => 1,
            _ => 0,
        };
        let mut bits = 0u32;
        for (j, &c) in group.iter().enumerate() {
            let v = if j >= 4usize.saturating_sub(pad) {
                0
            } else {
                value(c).ok_or(Error::BadBase64)?
            };
            bits = (bits << 6) | u32::from(v);
        }
        let bytes = bits.to_be_bytes();
        let (_, triple) = bytes.split_first_chunk::<1>().ok_or(Error::BadBase64)?;
        let keep = 3usize.saturating_sub(pad);
        let dropped = triple.get(keep..).ok_or(Error::BadBase64)?;
        if dropped.iter().any(|&b| b != 0) {
            return Err(Error::BadBase64);
        }
        let end = written.checked_add(keep).ok_or(Error::Overflow)?;
        let dst = out.get_mut(written..end).ok_or(Error::ScratchTooSmall)?;
        dst.copy_from_slice(triple.get(..keep).ok_or(Error::BadBase64)?);
        written = end;
    }
    Ok(written)
}

/// Decodes `text` into exactly `N` bytes.
pub fn decode_array<const N: usize>(text: &[u8]) -> Result<[u8; N], Error> {
    let mut out = [0u8; N];
    let mut buf = [0u8; 96];
    let n = decode_into(text, &mut buf)?;
    if n != N {
        return Err(Error::BadBase64);
    }
    out.copy_from_slice(buf.get(..N).ok_or(Error::BadBase64)?);
    Ok(out)
}

/// Reports whether `text` is canonical base64 of any length, without
/// decoding it.
pub fn is_canonical(text: &[u8]) -> bool {
    let mut scratch = [0u8; 3];
    let (groups, rest) = text.as_chunks::<4>();
    rest.is_empty()
        && groups.iter().enumerate().all(|(i, g)| {
            let mut text_g = [0u8; 4];
            text_g.copy_from_slice(g);
            let is_last = i.checked_add(1) == Some(groups.len());
            let padded = g.contains(&b'=');
            (!padded || is_last) && decode_into(&text_g, &mut scratch).is_ok()
        })
}

/// A destination for encoded text.
pub trait Sink {
    /// Appends `bytes`.
    fn write(&mut self, bytes: &[u8]);
}

impl Sink for c3_crypto::Sha256 {
    fn write(&mut self, bytes: &[u8]) {
        self.update(bytes);
    }
}

/// Writes the standard padded base64 encoding of `data` to `sink`.
pub fn encode_to<S: Sink>(data: &[u8], sink: &mut S) {
    let alphabet = |v: u32| -> u8 {
        ALPHABET
            .get(usize::try_from(v & 63).unwrap_or(0))
            .copied()
            .unwrap_or(b'A')
    };
    let (groups, rest) = data.as_chunks::<3>();
    for g in groups {
        let [a, b, c] = *g;
        let bits = (u32::from(a) << 16) | (u32::from(b) << 8) | u32::from(c);
        sink.write(&[
            alphabet(bits >> 18),
            alphabet(bits >> 12),
            alphabet(bits >> 6),
            alphabet(bits),
        ]);
    }
    match *rest {
        [a] => {
            let bits = u32::from(a) << 16;
            sink.write(&[alphabet(bits >> 18), alphabet(bits >> 12), b'=', b'=']);
        }
        [a, b] => {
            let bits = (u32::from(a) << 16) | (u32::from(b) << 8);
            sink.write(&[
                alphabet(bits >> 18),
                alphabet(bits >> 12),
                alphabet(bits >> 6),
                b'=',
            ]);
        }
        _ => {}
    }
}

#[cfg(test)]
#[allow(clippy::arithmetic_side_effects, clippy::indexing_slicing)]
pub(crate) mod tests {
    use super::*;

    impl Sink for Vec<u8> {
        fn write(&mut self, bytes: &[u8]) {
            self.extend_from_slice(bytes);
        }
    }

    fn enc(data: &[u8]) -> Vec<u8> {
        let mut v = Vec::new();
        encode_to(data, &mut v);
        v
    }

    #[test]
    fn rfc4648_vectors() {
        for (plain, text) in [
            (&b""[..], &b""[..]),
            (b"f", b"Zg=="),
            (b"fo", b"Zm8="),
            (b"foo", b"Zm9v"),
            (b"foob", b"Zm9vYg=="),
            (b"fooba", b"Zm9vYmE="),
            (b"foobar", b"Zm9vYmFy"),
        ] {
            assert_eq!(enc(plain), text);
            let mut out = [0u8; 8];
            let n = decode_into(text, &mut out).unwrap();
            assert_eq!(&out[..n], plain);
            assert!(is_canonical(text));
        }
    }

    #[test]
    fn rejects_non_canonical() {
        let mut out = [0u8; 8];
        for bad in [
            &b"Zg="[..],
            b"Zh==",
            b"Zm9=",
            b"Z===",
            b"Zg==Zg==",
            b"Zm9v\n",
            b"Zm-v",
            b"=Zm9",
        ] {
            assert!(decode_into(bad, &mut out).is_err(), "{:?}", bad);
            assert!(!is_canonical(bad));
        }
    }

    #[test]
    fn decodes_fixed_arrays() {
        assert_eq!(decode_array::<3>(b"Zm9v"), Ok(*b"foo"));
        assert_eq!(decode_array::<2>(b"Zm9v"), Err(Error::BadBase64));
    }
}
