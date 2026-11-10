//! The signed image's header and segment table.

use crate::error::Error;
use crate::layout::FLASH_CODE;
use crate::layout::FLASH_DATA;
use crate::layout::FLASH_PAGE;
use crate::layout::IRAM_TO_DRAM;
use crate::layout::RAM_CODE;
use crate::layout::RAM_DATA;
use crate::layout::Region;
use crate::layout::ranges_overlap;
use crate::reader::Reader;

/// The most segments an image can have.
pub const MAX_SEGMENTS: usize = 16;
/// The highest security version an image can carry.
pub const MAX_SECURITY_VERSION: u8 = 16;
/// ESP-IDF's chip ID for the ESP32-C3.
pub const CHIP_ID_ESP32C3: u16 = 5;
/// The length of the fixed part of the image header.
const FIXED_HEADER_LEN: u32 = 20;
/// The length of one segment table entry.
const SEGMENT_ENTRY_LEN: u32 = 16;

/// What a segment holds and how the bootloader places it.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum SegmentKind {
    /// Code that the instruction cache maps from flash.
    FlashCode,
    /// Data that the data cache maps from flash.
    FlashData,
    /// Code that the bootloader copies into RAM.
    RamCode,
    /// Data that the bootloader copies into RAM.
    RamData,
}

impl SegmentKind {
    fn from_byte(b: u8) -> Result<Self, Error> {
        match b {
            1 => Ok(SegmentKind::FlashCode),
            2 => Ok(SegmentKind::FlashData),
            3 => Ok(SegmentKind::RamCode),
            4 => Ok(SegmentKind::RamData),
            _ => Err(Error::BadSegment),
        }
    }

    /// The addresses a segment of this kind may occupy.
    fn region(self) -> Region {
        match self {
            SegmentKind::FlashCode => FLASH_CODE,
            SegmentKind::FlashData => FLASH_DATA,
            SegmentKind::RamCode => RAM_CODE,
            SegmentKind::RamData => RAM_DATA,
        }
    }

    fn is_flash(self) -> bool {
        matches!(self, SegmentKind::FlashCode | SegmentKind::FlashData)
    }

    fn is_executable(self) -> bool {
        matches!(self, SegmentKind::FlashCode | SegmentKind::RamCode)
    }
}

/// One entry of the segment table.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub struct Segment {
    /// What the segment holds.
    pub kind: SegmentKind,
    /// The virtual address of the segment's first byte.
    pub address: u32,
    /// The offset of the segment's data from the start of the image.
    pub offset: u32,
    /// The segment's length in bytes.
    pub length: u32,
}

/// The address space a segment occupies, for overlap checks.
#[derive(Clone, Copy, PartialEq, Eq)]
enum Space {
    FlashCode,
    FlashData,
    Sram,
}

impl Segment {
    /// The segment's address space, and its start address in that space.
    ///
    /// RAM code and RAM data share SRAM, so RAM code addresses become their
    /// data-bus alias. Callers have already checked that the address is in
    /// the segment's region, so the subtraction can't underflow.
    fn physical(&self) -> Result<(Space, u32), Error> {
        match self.kind {
            SegmentKind::FlashCode => Ok((Space::FlashCode, self.address)),
            SegmentKind::FlashData => Ok((Space::FlashData, self.address)),
            SegmentKind::RamData => Ok((Space::Sram, self.address)),
            SegmentKind::RamCode => self
                .address
                .checked_sub(IRAM_TO_DRAM)
                .map(|a| (Space::Sram, a))
                .ok_or(Error::BadSegment),
        }
    }
}

/// A checked image header.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub struct Header {
    /// The image's security version, 0 through 16.
    pub security_version: u8,
    /// The address the bootloader jumps to.
    pub entry_point: u32,
    /// The total length of the signed image.
    pub image_length: u32,
    segments: [Segment; MAX_SEGMENTS],
    segment_count: usize,
}

impl Header {
    /// The image's segments, in table order.
    pub fn segments(&self) -> &[Segment] {
        self.segments.get(..self.segment_count).unwrap_or(&[])
    }

    /// The length of the header and segment table.
    pub fn header_len(&self) -> Result<u32, Error> {
        header_len(self.segment_count)
    }
}

fn header_len(segment_count: usize) -> Result<u32, Error> {
    let count = u32::try_from(segment_count).map_err(|_| Error::OutOfRange)?;
    count
        .checked_mul(SEGMENT_ENTRY_LEN)
        .and_then(|t| t.checked_add(FIXED_HEADER_LEN))
        .ok_or(Error::Overflow)
}

fn read_segment(r: &mut Reader<'_>) -> Result<Segment, Error> {
    let kind = SegmentKind::from_byte(r.u8()?)?;
    r.reserved(3)?;
    let address = r.u32()?;
    let offset = r.u32()?;
    let length = r.u32()?;
    Ok(Segment {
        kind,
        address,
        offset,
        length,
    })
}

/// Checks the rules that apply to one segment on its own.
fn check_segment(s: &Segment, image_length: u32) -> Result<(), Error> {
    if s.length == 0 {
        return Err(Error::BadSegment);
    }
    let end = s.offset.checked_add(s.length).ok_or(Error::Overflow)?;
    if end > image_length {
        return Err(Error::BadSegment);
    }
    if !s.kind.region().contains_range(s.address, s.length) {
        return Err(Error::BadSegment);
    }
    if s.kind.is_flash()
        && !(s.offset.is_multiple_of(FLASH_PAGE) && s.address.is_multiple_of(FLASH_PAGE))
    {
        return Err(Error::BadSegment);
    }
    Ok(())
}

/// Parses and checks an image header and segment table.
///
/// `bytes` holds at least the header and segment table, starting at the
/// first byte of the image. Bytes after the table are ignored. `image_length`
/// is the manifest's image length, which the header must repeat.
pub fn parse(bytes: &[u8], image_length: u32) -> Result<Header, Error> {
    let mut r = Reader::new(bytes);
    r.magic(b"C3IM")?;
    r.version_1()?;
    if r.u16()? != CHIP_ID_ESP32C3 {
        return Err(Error::WrongChip);
    }
    let security_version = r.u8()?;
    if security_version > MAX_SECURITY_VERSION {
        return Err(Error::OutOfRange);
    }
    let segment_count = usize::from(r.u8()?);
    if segment_count == 0 || segment_count > MAX_SEGMENTS {
        return Err(Error::OutOfRange);
    }
    r.reserved(2)?;
    let entry_point = r.u32()?;
    if r.u32()? != image_length {
        return Err(Error::BadLayout);
    }

    let table_end = header_len(segment_count)?;
    let empty = Segment {
        kind: SegmentKind::FlashCode,
        address: 0,
        offset: 0,
        length: 0,
    };
    let mut segments = [empty; MAX_SEGMENTS];
    let mut previous_end = table_end;
    for slot in segments.iter_mut().take(segment_count) {
        let s = read_segment(&mut r)?;
        check_segment(&s, image_length)?;
        if s.offset < previous_end {
            return Err(Error::BadSegment);
        }
        previous_end = s.offset.checked_add(s.length).ok_or(Error::Overflow)?;
        *slot = s;
    }
    if previous_end != image_length {
        return Err(Error::BadSegment);
    }

    let listed = segments.get(..segment_count).ok_or(Error::OutOfRange)?;
    for (i, a) in listed.iter().enumerate() {
        let (space_a, start_a) = a.physical()?;
        for b in listed.iter().skip(i.checked_add(1).ok_or(Error::Overflow)?) {
            let (space_b, start_b) = b.physical()?;
            if space_a == space_b && ranges_overlap(start_a, a.length, start_b, b.length) {
                return Err(Error::SegmentOverlap);
            }
        }
    }

    let entry_ok = entry_point.is_multiple_of(2)
        && listed.iter().any(|s| {
            s.kind.is_executable()
                && entry_point >= s.address
                && entry_point
                    .checked_sub(s.address)
                    .is_some_and(|d| d < s.length)
        });
    if !entry_ok {
        return Err(Error::BadEntryPoint);
    }

    Ok(Header {
        security_version,
        entry_point,
        image_length,
        segments,
        segment_count,
    })
}

#[cfg(test)]
#[allow(clippy::arithmetic_side_effects, clippy::indexing_slicing)]
mod tests {
    use super::*;

    struct Seg(u8, u32, u32, u32);

    fn encode(sv: u8, entry: u32, image_length: u32, segs: &[Seg]) -> Vec<u8> {
        let mut out = Vec::new();
        out.extend_from_slice(b"C3IM");
        out.extend_from_slice(&1u16.to_le_bytes());
        out.extend_from_slice(&CHIP_ID_ESP32C3.to_le_bytes());
        out.push(sv);
        out.push(segs.len() as u8);
        out.extend_from_slice(&[0, 0]);
        out.extend_from_slice(&entry.to_le_bytes());
        out.extend_from_slice(&image_length.to_le_bytes());
        for s in segs {
            out.push(s.0);
            out.extend_from_slice(&[0, 0, 0]);
            out.extend_from_slice(&s.1.to_le_bytes());
            out.extend_from_slice(&s.2.to_le_bytes());
            out.extend_from_slice(&s.3.to_le_bytes());
        }
        out
    }

    fn good_segments() -> Vec<Seg> {
        vec![
            Seg(4, 0x3FC8_0000, 0x100, 0x200),
            Seg(1, 0x4200_0000, 0x1_0000, 0x8000),
            Seg(2, 0x3C00_0000, 0x2_0000, 0x4000),
        ]
    }

    const GOOD_LEN: u32 = 0x2_4000;

    #[test]
    fn accepts_good_image() {
        let h = parse(
            &encode(3, 0x4200_0100, GOOD_LEN, &good_segments()),
            GOOD_LEN,
        )
        .unwrap();
        assert_eq!(h.security_version, 3);
        assert_eq!(h.segments().len(), 3);
        assert_eq!(h.header_len(), Ok(68));
    }

    #[test]
    fn rejects_header_fields() {
        let segs = good_segments();
        assert_eq!(
            parse(&encode(17, 0x4200_0100, GOOD_LEN, &segs), GOOD_LEN),
            Err(Error::OutOfRange)
        );
        assert_eq!(
            parse(&encode(3, 0x4200_0100, GOOD_LEN, &segs), GOOD_LEN + 1),
            Err(Error::BadLayout)
        );
        let mut bytes = encode(3, 0x4200_0100, GOOD_LEN, &segs);
        bytes[6] = 9;
        assert_eq!(parse(&bytes, GOOD_LEN), Err(Error::WrongChip));
        assert_eq!(
            parse(&encode(3, 0x4200_0100, GOOD_LEN, &[]), GOOD_LEN),
            Err(Error::OutOfRange)
        );
    }

    #[test]
    fn rejects_segment_into_bootloader_ram() {
        let mut segs = good_segments();
        segs[0] = Seg(4, 0x3FCA_0000 - 0x100, 0x100, 0x200);
        assert_eq!(
            parse(&encode(3, 0x4200_0100, GOOD_LEN, &segs), GOOD_LEN),
            Err(Error::BadSegment)
        );
    }

    #[test]
    fn rejects_ram_code_aliasing_ram_data() {
        let segs = vec![
            Seg(4, 0x3FC8_0000, 0x100, 0x200),
            Seg(3, 0x4038_0100, 0x300, 0x100),
        ];
        assert_eq!(
            parse(&encode(0, 0x4038_0100, 0x400, &segs), 0x400),
            Err(Error::SegmentOverlap)
        );
    }

    #[test]
    fn rejects_unaligned_flash_and_overlapping_data() {
        let mut segs = good_segments();
        segs[1] = Seg(1, 0x4200_0100, 0x1_0000, 0x8000);
        assert_eq!(
            parse(&encode(3, 0x4200_0100, GOOD_LEN, &segs), GOOD_LEN),
            Err(Error::BadSegment)
        );
        let mut segs = good_segments();
        segs[0] = Seg(4, 0x3FC8_0000, 0x40, 0x200);
        assert_eq!(
            parse(&encode(3, 0x4200_0100, GOOD_LEN, &segs), GOOD_LEN),
            Err(Error::BadSegment)
        );
    }

    #[test]
    fn rejects_trailing_bytes_and_bad_entry() {
        let segs = good_segments();
        assert_eq!(
            parse(&encode(3, 0x4200_0100, GOOD_LEN + 1, &segs), GOOD_LEN + 1),
            Err(Error::BadSegment)
        );
        assert_eq!(
            parse(&encode(3, 0x3C00_0000, GOOD_LEN, &segs), GOOD_LEN),
            Err(Error::BadEntryPoint)
        );
        assert_eq!(
            parse(&encode(3, 0x4200_0101, GOOD_LEN, &segs), GOOD_LEN),
            Err(Error::BadEntryPoint)
        );
        assert_eq!(
            parse(&encode(3, 0x4200_8000, GOOD_LEN, &segs), GOOD_LEN),
            Err(Error::BadEntryPoint)
        );
    }

    #[test]
    fn rejects_overflowing_segment() {
        let segs = vec![Seg(4, 0x3FC8_0000, u32::MAX - 4, 0x10)];
        assert_eq!(
            parse(&encode(0, 0x4200_0000, 0x400, &segs), 0x400),
            Err(Error::Overflow)
        );
    }
}
