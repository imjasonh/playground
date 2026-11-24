//! The slot manifest, which locates the signed parts of a slot.

use crate::error::Error;
use crate::layout::IMAGE_OFFSET;
use crate::layout::SLOT_SIZE;
use crate::reader::Reader;

/// The length of a slot manifest in bytes.
pub const MANIFEST_LEN: usize = 32;
/// The manifest format version.
pub const VERSION: u16 = 2;
/// The longest TUF part the bootloader reads.
pub const MAX_TUF_LEN: u32 = 24_576;

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

/// Where a slot's signed image, bundle, and TUF part are.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub struct Manifest {
    /// The signed image.
    pub image: Part,
    /// The bundle container.
    pub bundle: Part,
    /// The TUF part: new roots, `targets.json`, and `trusted_root.json`.
    pub tuf: Part,
}

/// The smallest image: a header with one segment table entry and one byte of
/// segment data.
const MIN_IMAGE_LEN: u32 = 37;
/// The largest image: the slot after the manifest page.
const MAX_IMAGE_LEN: u32 = 0x1D_0000;
/// The smallest bundle container: the header, six length prefixes, and the
/// minimum length of each field.
const MIN_BUNDLE_LEN: u32 = 49;
/// The smallest TUF part: the header with no roots and two one-byte
/// documents.
const MIN_TUF_LEN: u32 = 18;

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
/// the slot, in the order image, bundle, TUF part, without overlapping, and
/// the image must start at [`IMAGE_OFFSET`].
// c3-boot-proofs proves this function as compiled, so it needs its own symbol.
#[inline(never)]
pub fn parse(bytes: &[u8]) -> Result<Manifest, Error> {
    let mut r = Reader::new(bytes);
    r.magic(b"C3SL")?;
    if r.u16()? != VERSION {
        return Err(Error::BadVersion);
    }
    r.reserved(2)?;
    let image = part(&mut r, MIN_IMAGE_LEN, MAX_IMAGE_LEN)?;
    let bundle = part(&mut r, MIN_BUNDLE_LEN, 16_384)?;
    let tuf = part(&mut r, MIN_TUF_LEN, MAX_TUF_LEN)?;
    r.finish()?;

    if image.offset != IMAGE_OFFSET {
        return Err(Error::BadLayout);
    }
    let image_end = image.end()?;
    let bundle_end = bundle.end()?;
    let tuf_end = tuf.end()?;
    let ordered = image_end <= bundle.offset && bundle_end <= tuf.offset && tuf_end <= SLOT_SIZE;
    if !ordered {
        return Err(Error::BadLayout);
    }
    Ok(Manifest { image, bundle, tuf })
}

#[cfg(test)]
#[allow(clippy::arithmetic_side_effects, clippy::indexing_slicing)]
mod tests {
    use super::*;

    fn encode(parts: [(u32, u32); 3]) -> [u8; MANIFEST_LEN] {
        let mut out = [0u8; MANIFEST_LEN];
        out[0..4].copy_from_slice(b"C3SL");
        out[4..6].copy_from_slice(&VERSION.to_le_bytes());
        for (i, (offset, length)) in parts.iter().enumerate() {
            let at = 8 + i * 8;
            out[at..at + 4].copy_from_slice(&offset.to_le_bytes());
            out[at + 4..at + 8].copy_from_slice(&length.to_le_bytes());
        }
        out
    }

    fn good() -> [(u32, u32); 3] {
        [(0x1_0000, 0x2_0000), (0x3_0000, 0x1000), (0x3_1000, 0x2800)]
    }

    #[test]
    fn tuf_part_length_limits() {
        let mut p = good();
        p[2].1 = MIN_TUF_LEN - 1;
        assert_eq!(parse(&encode(p)), Err(Error::OutOfRange));
        p[2].1 = MIN_TUF_LEN;
        assert!(parse(&encode(p)).is_ok());
        p[2].1 = MAX_TUF_LEN;
        assert!(parse(&encode(p)).is_ok());
        p[2].1 = MAX_TUF_LEN + 1;
        assert_eq!(parse(&encode(p)), Err(Error::OutOfRange));
    }

    #[test]
    fn accepts_ordered_parts() {
        let m = parse(&encode(good())).unwrap();
        assert_eq!(
            m.tuf,
            Part {
                offset: 0x3_1000,
                length: 0x2800
            }
        );
    }

    #[test]
    fn rejects_overlap_and_misplaced_image() {
        let mut p = good();
        p[1].0 = 0x2_FFFF;
        assert_eq!(parse(&encode(p)), Err(Error::BadLayout));
        let mut p = good();
        p[2].0 = 0x3_0FFF;
        assert_eq!(parse(&encode(p)), Err(Error::BadLayout));
        let mut p = good();
        p[0].0 = 0x2_0000;
        p[1].0 = 0x4_0000;
        p[2].0 = 0x4_1000;
        assert_eq!(parse(&encode(p)), Err(Error::BadLayout));
    }

    #[test]
    fn rejects_overflow_and_slot_overrun() {
        let mut p = good();
        p[2] = (u32::MAX - 10, 0x400);
        assert_eq!(parse(&encode(p)), Err(Error::Overflow));
        let mut p = good();
        p[2] = (SLOT_SIZE - 0x100, 0x400);
        assert_eq!(parse(&encode(p)), Err(Error::BadLayout));
    }

    #[test]
    fn rejects_bad_header() {
        let mut bytes = encode(good());
        bytes[6] = 1;
        assert_eq!(parse(&bytes), Err(Error::NonzeroReserved));
        bytes[6] = 0;
        bytes[4] = 1;
        assert_eq!(parse(&bytes), Err(Error::BadVersion));
        bytes[4] = 2;
        bytes[0] = b'X';
        assert_eq!(parse(&bytes), Err(Error::BadMagic));
        assert_eq!(parse(&encode(good())[..31]), Err(Error::Truncated));
    }
}
