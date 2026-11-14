//! The slot manifest, which locates the signed parts of a slot.

use crate::error::Error;
use crate::layout::IMAGE_OFFSET;
use crate::layout::SLOT_SIZE;
use crate::reader::Reader;

/// The length of a slot manifest in bytes.
pub const MANIFEST_LEN: usize = 40;

/// A region inside a slot, as an offset and a length.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub struct Part {
    /// The part's offset from the start of the slot.
    pub offset: u32,
    /// The part's length in bytes.
    pub length: u32,
}

impl Part {
    /// The offset one past the part's last byte.
    ///
    /// Fails if the end overflows.
    pub fn end(&self) -> Result<u32, Error> {
        self.offset.checked_add(self.length).ok_or(Error::Overflow)
    }
}

/// Where a slot's signed image, bundle, chain, and blob are.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub struct Manifest {
    /// The signed image.
    pub image: Part,
    /// The bundle container.
    pub bundle: Part,
    /// The key-set chain.
    pub chain: Part,
    /// The trust-root blob.
    pub blob: Part,
}

/// The smallest image: a header with one segment table entry and one byte of
/// segment data.
const MIN_IMAGE_LEN: u32 = 37;
/// The largest image: the slot after the manifest page.
const MAX_IMAGE_LEN: u32 = 0x1D_0000;
/// The smallest bundle container: the header, six length prefixes, and the
/// minimum length of each field.
const MIN_BUNDLE_LEN: u32 = 49;
/// The smallest chain: the header with no links.
const MIN_CHAIN_LEN: u32 = 8;
/// The smallest blob: one entry of each kind, one-byte strings, and two
/// signatures.
const MIN_BLOB_LEN: u32 = 443;

fn part(r: &mut Reader<'_>, min: u32, max: u32) -> Result<Part, Error> {
    let offset = r.u32()?;
    let length = r.u32()?;
    if length < min || length > max {
        return Err(Error::OutOfRange);
    }
    Ok(Part { offset, length })
}

/// Parses and checks a slot manifest.
///
/// `bytes` must be exactly [`MANIFEST_LEN`] bytes. The parts must lie inside
/// the slot, in the order image, bundle, chain, blob, without overlapping, and
/// the image must start at [`IMAGE_OFFSET`].
// c3-boot-proofs proves this function as compiled, so it needs its own symbol.
#[inline(never)]
pub fn parse(bytes: &[u8]) -> Result<Manifest, Error> {
    let mut r = Reader::new(bytes);
    r.magic(b"C3SL")?;
    r.version_1()?;
    r.reserved(2)?;
    let image = part(&mut r, MIN_IMAGE_LEN, MAX_IMAGE_LEN)?;
    let bundle = part(&mut r, MIN_BUNDLE_LEN, 16_384)?;
    let chain = part(&mut r, MIN_CHAIN_LEN, 2_048)?;
    let blob = part(&mut r, MIN_BLOB_LEN, 4_096)?;
    r.finish()?;

    if image.offset != IMAGE_OFFSET {
        return Err(Error::BadLayout);
    }
    let image_end = image.end()?;
    let bundle_end = bundle.end()?;
    let chain_end = chain.end()?;
    let blob_end = blob.end()?;
    let ordered = image_end <= bundle.offset
        && bundle_end <= chain.offset
        && chain_end <= blob.offset
        && blob_end <= SLOT_SIZE;
    if !ordered {
        return Err(Error::BadLayout);
    }
    Ok(Manifest {
        image,
        bundle,
        chain,
        blob,
    })
}

#[cfg(test)]
#[allow(clippy::arithmetic_side_effects, clippy::indexing_slicing)]
mod tests {
    use super::*;

    fn encode(parts: [(u32, u32); 4]) -> [u8; MANIFEST_LEN] {
        let mut out = [0u8; MANIFEST_LEN];
        out[0..4].copy_from_slice(b"C3SL");
        out[4..6].copy_from_slice(&1u16.to_le_bytes());
        for (i, (offset, length)) in parts.iter().enumerate() {
            let at = 8 + i * 8;
            out[at..at + 4].copy_from_slice(&offset.to_le_bytes());
            out[at + 4..at + 8].copy_from_slice(&length.to_le_bytes());
        }
        out
    }

    fn good() -> [(u32, u32); 4] {
        [
            (0x1_0000, 0x2_0000),
            (0x3_0000, 0x1000),
            (0x3_1000, 0x100),
            (0x3_1100, 0x400),
        ]
    }

    #[test]
    fn chain_minimum_is_the_empty_chain_header() {
        let mut p = good();
        p[2].1 = 7;
        assert_eq!(parse(&encode(p)), Err(Error::OutOfRange));
        p[2].1 = 8;
        assert!(parse(&encode(p)).is_ok());
    }

    #[test]
    fn accepts_ordered_parts() {
        let m = parse(&encode(good())).unwrap();
        assert_eq!(
            m.blob,
            Part {
                offset: 0x3_1100,
                length: 0x400
            }
        );
    }

    #[test]
    fn rejects_overlap_and_misplaced_image() {
        let mut p = good();
        p[1].0 = 0x2_FFFF;
        assert_eq!(parse(&encode(p)), Err(Error::BadLayout));
        let mut p = good();
        p[0].0 = 0x2_0000;
        p[1].0 = 0x4_0000;
        p[2].0 = 0x4_1000;
        p[3].0 = 0x4_1100;
        assert_eq!(parse(&encode(p)), Err(Error::BadLayout));
    }

    #[test]
    fn rejects_overflow_and_slot_overrun() {
        let mut p = good();
        p[3] = (u32::MAX - 10, 0x400);
        assert_eq!(parse(&encode(p)), Err(Error::Overflow));
        let mut p = good();
        p[3] = (SLOT_SIZE - 0x100, 0x400);
        assert_eq!(parse(&encode(p)), Err(Error::BadLayout));
    }

    #[test]
    fn rejects_bad_lengths_and_header() {
        let mut p = good();
        p[2].1 = 3;
        assert_eq!(parse(&encode(p)), Err(Error::OutOfRange));
        let mut bytes = encode(good());
        bytes[6] = 1;
        assert_eq!(parse(&bytes), Err(Error::NonzeroReserved));
        bytes[6] = 0;
        bytes[0] = b'X';
        assert_eq!(parse(&bytes), Err(Error::BadMagic));
        assert_eq!(parse(&encode(good())[..39]), Err(Error::Truncated));
    }
}
