//! Power-fail-safe metadata for the wear-leveled internal-flash frame slots.
//!
//! Write a candidate into the next wear-level slot, read it back, verify its payload
//! CRC, and only then append its metadata record. The previous record and frame
//! remain valid until the new record is durable.
//!
//! Each slot always holds a complete controller-native framebuffer. For a
//! partial transfer, copy the active image into RAM, apply the patch, and write
//! the merged 48 KiB image to the inactive slot. `image_crc` covers that merged
//! image; `frame.crc` still covers the transfer payload.

use crate::memory::FLASH_PAGE_BYTES;
use crate::panel::{Window, FRAME_BYTES};
use crate::protocol::{CommittedFrame, Crc32};

const MAGIC: [u8; 4] = *b"IMGF";
const FORMAT_VERSION: u8 = 1;

/// Encoded length of one frame metadata record.
pub const METADATA_RECORD_BYTES: usize = 40;
pub const METADATA_PAGE_BYTES: usize = FLASH_PAGE_BYTES as usize;
pub const METADATA_PAGE_COUNT: usize = 2;
pub const METADATA_JOURNAL_BYTES: usize = METADATA_PAGE_BYTES * METADATA_PAGE_COUNT;
pub const METADATA_RECORDS_PER_PAGE: usize = METADATA_PAGE_BYTES / METADATA_RECORD_BYTES;
pub const FRAME_SLOT_COUNT: usize = 5;
pub const MIN_FLASH_ERASE_CYCLES: u32 = 10_000;
pub const EXPECTED_DURABLE_FRAMES_PER_DAY: u32 = 24;
pub const MIN_FRAME_STORAGE_LIFETIME_DAYS: u32 =
    MIN_FLASH_ERASE_CYCLES * FRAME_SLOT_COUNT as u32 / EXPECTED_DURABLE_FRAMES_PER_DAY;
const _: () = assert!(MIN_FRAME_STORAGE_LIFETIME_DAYS >= 5 * 365);

#[derive(Clone, Copy, PartialEq, Eq, Debug)]
#[repr(u8)]
pub enum FrameSlot {
    A = 0,
    B = 1,
    C = 2,
    D = 3,
    E = 4,
}

impl FrameSlot {
    pub const fn index(self) -> usize {
        self as usize
    }

    pub const fn next(self) -> Self {
        match self {
            Self::A => Self::B,
            Self::B => Self::C,
            Self::C => Self::D,
            Self::D => Self::E,
            Self::E => Self::A,
        }
    }
}

/// A durable frame pointer stored after its payload passes readback and CRC.
#[derive(Clone, Copy, PartialEq, Eq, Debug)]
pub struct FrameRecord {
    pub generation: u32,
    pub slot: FrameSlot,
    /// CRC of the complete canonical 48 KiB image in `slot`.
    pub image_crc: u32,
    /// Transfer metadata, which can describe a partial patch.
    pub frame: CommittedFrame,
}

#[derive(Clone, Copy, PartialEq, Eq, Debug)]
pub enum RecordDecodeError {
    InvalidLength,
    InvalidMagic,
    UnsupportedVersion,
    ReservedBytes,
    InvalidSlot,
    InvalidFrame,
    CrcMismatch,
}

#[derive(Clone, Copy, PartialEq, Eq, Debug)]
pub enum JournalScanError {
    InvalidLength,
}

/// The safe next metadata write after scanning both flash pages.
#[derive(Clone, Copy, PartialEq, Eq, Debug)]
pub struct JournalWritePlan {
    pub offset: usize,
    /// Page to erase before writing, or `None` when the slot is already erased.
    pub erase_page: Option<u8>,
}

#[derive(Clone, Copy, PartialEq, Eq, Debug)]
pub struct JournalScan {
    pub latest: Option<FrameRecord>,
    pub latest_by_slot: [Option<FrameRecord>; FRAME_SLOT_COUNT],
    pub next_write: JournalWritePlan,
    pub invalid_records: u16,
}

impl FrameRecord {
    pub fn to_bytes(self) -> [u8; METADATA_RECORD_BYTES] {
        let mut bytes = [0xff; METADATA_RECORD_BYTES];
        bytes[0..4].copy_from_slice(&MAGIC);
        bytes[4] = FORMAT_VERSION;
        bytes[5] = self.slot as u8;
        bytes[6..8].fill(0);
        bytes[8..12].copy_from_slice(&self.generation.to_le_bytes());
        bytes[12..16].copy_from_slice(&self.frame.id.to_le_bytes());
        bytes[16..20].copy_from_slice(&self.frame.len.to_le_bytes());
        bytes[20..24].copy_from_slice(&self.frame.crc.to_le_bytes());
        bytes[24..26].copy_from_slice(&self.frame.window.x.to_le_bytes());
        bytes[26..28].copy_from_slice(&self.frame.window.y.to_le_bytes());
        bytes[28..30].copy_from_slice(&self.frame.window.w.to_le_bytes());
        bytes[30..32].copy_from_slice(&self.frame.window.h.to_le_bytes());
        bytes[32..36].copy_from_slice(&self.image_crc.to_le_bytes());
        let record_crc = crc32(&bytes[..36]);
        bytes[36..40].copy_from_slice(&record_crc.to_le_bytes());
        bytes
    }

    pub fn from_bytes(bytes: &[u8]) -> Result<Self, RecordDecodeError> {
        if bytes.len() != METADATA_RECORD_BYTES {
            return Err(RecordDecodeError::InvalidLength);
        }
        if bytes[0..4] != MAGIC {
            return Err(RecordDecodeError::InvalidMagic);
        }
        if bytes[4] != FORMAT_VERSION {
            return Err(RecordDecodeError::UnsupportedVersion);
        }
        if bytes[6..8] != [0, 0] {
            return Err(RecordDecodeError::ReservedBytes);
        }
        let slot = match bytes[5] {
            0 => FrameSlot::A,
            1 => FrameSlot::B,
            2 => FrameSlot::C,
            3 => FrameSlot::D,
            4 => FrameSlot::E,
            _ => return Err(RecordDecodeError::InvalidSlot),
        };
        let expected_record_crc = word(bytes, 36);
        if crc32(&bytes[..36]) != expected_record_crc {
            return Err(RecordDecodeError::CrcMismatch);
        }
        let frame = CommittedFrame {
            id: word(bytes, 12),
            len: word(bytes, 16),
            crc: word(bytes, 20),
            window: Window {
                x: half(bytes, 24),
                y: half(bytes, 26),
                w: half(bytes, 28),
                h: half(bytes, 30),
            },
        };
        if !frame.window.is_valid() || frame.len != frame.window.packed_bytes() as u32 {
            return Err(RecordDecodeError::InvalidFrame);
        }
        Ok(Self {
            generation: word(bytes, 8),
            slot,
            image_crc: word(bytes, 32),
            frame,
        })
    }

    /// Verify the complete framebuffer before selecting or painting this slot.
    pub fn verifies_image(self, image: &[u8]) -> bool {
        image.len() == FRAME_BYTES && crc32(image) == self.image_crc
    }
}

/// Select the latest valid record from the two metadata journal heads.
pub const fn select_latest(a: Option<FrameRecord>, b: Option<FrameRecord>) -> Option<FrameRecord> {
    match (a, b) {
        (None, None) => None,
        (Some(record), None) | (None, Some(record)) => Some(record),
        (Some(a), Some(b)) => {
            if sequence_is_newer(b.generation, a.generation) {
                Some(b)
            } else {
                Some(a)
            }
        }
    }
}

/// Select the newest record whose complete frame slot still matches its CRC.
pub fn select_latest_verified(
    candidates: &[(FrameRecord, &[u8])],
) -> Option<FrameRecord> {
    let mut latest: Option<FrameRecord> = None;
    for &(record, image) in candidates {
        if record.verifies_image(image)
            && latest.is_none_or(|previous| {
                sequence_is_newer(record.generation, previous.generation)
            })
        {
            latest = Some(record);
        }
    }
    latest
}

/// Scan the two-page append journal without trusting torn or corrupt records.
pub fn scan_metadata_journal(bytes: &[u8]) -> Result<JournalScan, JournalScanError> {
    if bytes.len() != METADATA_JOURNAL_BYTES {
        return Err(JournalScanError::InvalidLength);
    }

    let mut latest: Option<(FrameRecord, usize)> = None;
    let mut latest_by_slot = [None; FRAME_SLOT_COUNT];
    let mut last_programmed = [None; METADATA_PAGE_COUNT];
    let mut invalid_records = 0_u16;
    for page in 0..METADATA_PAGE_COUNT {
        let page_start = page * METADATA_PAGE_BYTES;
        for index in 0..METADATA_RECORDS_PER_PAGE {
            let offset = page_start + index * METADATA_RECORD_BYTES;
            let encoded = &bytes[offset..offset + METADATA_RECORD_BYTES];
            if encoded.iter().all(|byte| *byte == 0xff) {
                continue;
            }
            last_programmed[page] = Some(index);
            let Ok(record) = FrameRecord::from_bytes(encoded) else {
                invalid_records = invalid_records.saturating_add(1);
                continue;
            };
            let slot_record = &mut latest_by_slot[record.slot.index()];
            if slot_record.is_none_or(|previous| {
                sequence_is_newer(record.generation, previous.generation)
            }) {
                *slot_record = Some(record);
            }
            if latest
                .is_none_or(|(previous, _)| sequence_is_newer(record.generation, previous.generation))
            {
                latest = Some((record, page));
            }
        }
    }

    let next_write = if let Some((_, latest_page)) = latest {
        if let Some(next_index) = last_programmed[latest_page]
            .map(|index| index + 1)
            .filter(|index| *index < METADATA_RECORDS_PER_PAGE)
        {
            JournalWritePlan {
                offset: latest_page * METADATA_PAGE_BYTES
                    + next_index * METADATA_RECORD_BYTES,
                erase_page: None,
            }
        } else {
            let target_page = 1 - latest_page;
            JournalWritePlan {
                offset: target_page * METADATA_PAGE_BYTES,
                erase_page: last_programmed[target_page].map(|_| target_page as u8),
            }
        }
    } else {
        JournalWritePlan {
            offset: 0,
            erase_page: last_programmed[0].map(|_| 0),
        }
    };

    Ok(JournalScan {
        latest: latest.map(|(record, _)| record),
        latest_by_slot,
        next_write,
        invalid_records,
    })
}

fn crc32(bytes: &[u8]) -> u32 {
    let mut crc = Crc32::new();
    crc.update(bytes);
    crc.finalize()
}

fn word(bytes: &[u8], offset: usize) -> u32 {
    u32::from_le_bytes([
        bytes[offset],
        bytes[offset + 1],
        bytes[offset + 2],
        bytes[offset + 3],
    ])
}

fn half(bytes: &[u8], offset: usize) -> u16 {
    u16::from_le_bytes([bytes[offset], bytes[offset + 1]])
}

const fn sequence_is_newer(candidate: u32, previous: u32) -> bool {
    let distance = candidate.wrapping_sub(previous);
    distance != 0 && distance < (1 << 31)
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::panel;

    #[derive(Clone)]
    struct FakeNor {
        bytes: [u8; METADATA_JOURNAL_BYTES],
    }

    impl FakeNor {
        fn erased() -> Self {
            Self {
                bytes: [0xff; METADATA_JOURNAL_BYTES],
            }
        }

        fn program_prefix(&mut self, offset: usize, data: &[u8], length: usize) {
            for (destination, source) in self.bytes[offset..offset + length]
                .iter_mut()
                .zip(&data[..length])
            {
                assert_eq!(*destination & *source, *source);
                *destination &= *source;
            }
        }

        fn erase_prefix(&mut self, page: usize, length: usize) {
            let start = page * METADATA_PAGE_BYTES;
            self.bytes[start..start + length].fill(0xff);
        }

        fn scan(&self) -> JournalScan {
            scan_metadata_journal(&self.bytes).unwrap()
        }
    }

    fn record(generation: u32, slot: FrameSlot) -> FrameRecord {
        FrameRecord {
            generation,
            slot,
            image_crc: 0x89ab_cdef,
            frame: CommittedFrame {
                id: 42,
                len: panel::FRAME_BYTES as u32,
                crc: 0x1234_5678,
                window: Window::FULL,
            },
        }
    }

    #[test]
    fn record_round_trips() {
        let expected = record(7, FrameSlot::B);
        assert_eq!(FrameRecord::from_bytes(&expected.to_bytes()), Ok(expected));
    }

    #[test]
    fn image_crc_covers_the_complete_frame_slot() {
        let image = [0xa5; FRAME_BYTES];
        let mut expected = record(7, FrameSlot::B);
        expected.image_crc = crc32(&image);
        assert!(expected.verifies_image(&image));

        let mut corrupted = image;
        corrupted[FRAME_BYTES / 2] ^= 1;
        assert!(!expected.verifies_image(&corrupted));
        assert!(!expected.verifies_image(&image[..FRAME_BYTES - 1]));
    }

    #[test]
    fn selection_falls_back_when_the_newest_frame_slot_is_corrupt() {
        let old_image = [0x55; FRAME_BYTES];
        let new_image = [0xaa; FRAME_BYTES];
        let mut old = record(7, FrameSlot::A);
        old.image_crc = crc32(&old_image);
        let mut new = record(8, FrameSlot::B);
        new.image_crc = crc32(&new_image);

        assert_eq!(
            select_latest_verified(&[(old, &old_image), (new, &new_image)]),
            Some(new)
        );
        let mut corrupted = new_image;
        corrupted[0] ^= 1;
        assert_eq!(
            select_latest_verified(&[(old, &old_image), (new, &corrupted)]),
            Some(old)
        );
        corrupted = old_image;
        corrupted[0] ^= 1;
        assert_eq!(
            select_latest_verified(&[(old, &corrupted), (new, &corrupted)]),
            None
        );
    }

    #[test]
    fn corruption_and_torn_records_are_rejected() {
        let mut bytes = record(7, FrameSlot::A).to_bytes();
        bytes[20] ^= 1;
        assert_eq!(
            FrameRecord::from_bytes(&bytes),
            Err(RecordDecodeError::CrcMismatch)
        );
        assert_eq!(
            FrameRecord::from_bytes(&bytes[..20]),
            Err(RecordDecodeError::InvalidLength)
        );
    }

    #[test]
    fn every_truncation_and_single_bit_corruption_is_rejected() {
        let valid = record(7, FrameSlot::A).to_bytes();
        for length in 0..METADATA_RECORD_BYTES {
            assert_eq!(
                FrameRecord::from_bytes(&valid[..length]),
                Err(RecordDecodeError::InvalidLength)
            );
        }
        for index in 0..METADATA_RECORD_BYTES {
            for bit in 0..8 {
                let mut corrupted = valid;
                corrupted[index] ^= 1 << bit;
                assert!(
                    FrameRecord::from_bytes(&corrupted).is_err(),
                    "accepted corruption at byte {index}, bit {bit}"
                );
            }
        }
    }

    #[test]
    fn reserved_and_invalid_fields_are_rejected_after_valid_crc() {
        let mut reserved = record(7, FrameSlot::A).to_bytes();
        reserved[6] = 1;
        let record_crc = crc32(&reserved[..36]);
        reserved[36..40].copy_from_slice(&record_crc.to_le_bytes());
        assert_eq!(
            FrameRecord::from_bytes(&reserved),
            Err(RecordDecodeError::ReservedBytes)
        );

        let mut invalid_frame = record(7, FrameSlot::A).to_bytes();
        invalid_frame[28..30].copy_from_slice(&7_u16.to_le_bytes());
        let record_crc = crc32(&invalid_frame[..36]);
        invalid_frame[36..40].copy_from_slice(&record_crc.to_le_bytes());
        assert_eq!(
            FrameRecord::from_bytes(&invalid_frame),
            Err(RecordDecodeError::InvalidFrame)
        );
    }

    #[test]
    fn latest_record_selection_handles_generation_wrap() {
        let old = record(u32::MAX, FrameSlot::A);
        let new = record(0, FrameSlot::B);
        assert_eq!(select_latest(Some(old), Some(new)), Some(new));
        assert_eq!(select_latest(Some(new), Some(old)), Some(new));
        assert_eq!(select_latest(Some(old), None), Some(old));
        assert_eq!(select_latest(None, None), None);
    }

    #[test]
    fn successful_commits_rotate_across_every_frame_slot() {
        let mut previous = record(12, FrameSlot::A);
        for expected_slot in [
            FrameSlot::B,
            FrameSlot::C,
            FrameSlot::D,
            FrameSlot::E,
            FrameSlot::A,
        ] {
            let next = FrameRecord {
                generation: previous.generation.wrapping_add(1),
                slot: previous.slot.next(),
                image_crc: previous.image_crc,
                frame: previous.frame,
            };
            assert_eq!(next.slot, expected_slot);
            assert_eq!(select_latest(Some(previous), Some(next)), Some(next));
            previous = next;
        }
        assert_eq!(FRAME_SLOT_COUNT, 5);
        assert!(MIN_FRAME_STORAGE_LIFETIME_DAYS >= 5 * 365);
    }

    #[test]
    fn fresh_journal_starts_at_the_first_erased_slot() {
        assert_eq!(
            crate::memory::FRAME_METADATA.len() as usize,
            METADATA_JOURNAL_BYTES
        );
        assert_eq!(
            scan_metadata_journal(&[]),
            Err(JournalScanError::InvalidLength)
        );
        let scan = FakeNor::erased().scan();
        assert_eq!(scan.latest, None);
        assert_eq!(
            scan.next_write,
            JournalWritePlan {
                offset: 0,
                erase_page: None
            }
        );
        assert_eq!(scan.invalid_records, 0);
    }

    #[test]
    fn every_torn_metadata_word_preserves_the_previous_record() {
        let old = record(7, FrameSlot::A);
        let new = record(8, FrameSlot::B);
        let mut committed = FakeNor::erased();
        committed.program_prefix(0, &old.to_bytes(), METADATA_RECORD_BYTES);

        for written_words in 0..=METADATA_RECORD_BYTES / 4 {
            let mut interrupted = committed.clone();
            interrupted.program_prefix(
                METADATA_RECORD_BYTES,
                &new.to_bytes(),
                written_words * 4,
            );
            let scan = interrupted.scan();
            let expected = if written_words == METADATA_RECORD_BYTES / 4 {
                new
            } else {
                old
            };
            assert_eq!(scan.latest, Some(expected));
        }
    }

    #[test]
    fn interrupted_page_recycling_never_erases_the_latest_record() {
        let mut full = FakeNor::erased();
        for index in 0..METADATA_RECORDS_PER_PAGE {
            let entry = record(index as u32, FrameSlot::A);
            full.program_prefix(
                index * METADATA_RECORD_BYTES,
                &entry.to_bytes(),
                METADATA_RECORD_BYTES,
            );
        }
        let stale = record(0, FrameSlot::B);
        full.program_prefix(
            METADATA_PAGE_BYTES,
            &stale.to_bytes(),
            METADATA_RECORD_BYTES,
        );

        let latest = record((METADATA_RECORDS_PER_PAGE - 1) as u32, FrameSlot::A);
        let scan = full.scan();
        assert_eq!(scan.latest, Some(latest));
        assert_eq!(scan.latest_by_slot[FrameSlot::A.index()], Some(latest));
        assert_eq!(scan.latest_by_slot[FrameSlot::B.index()], Some(stale));
        assert_eq!(
            scan.next_write,
            JournalWritePlan {
                offset: METADATA_PAGE_BYTES,
                erase_page: Some(1)
            }
        );

        for erased in [0, 1, 20, 39, 40, METADATA_PAGE_BYTES - 1, METADATA_PAGE_BYTES] {
            let mut interrupted = full.clone();
            interrupted.erase_prefix(1, erased);
            assert_eq!(interrupted.scan().latest, Some(latest));
        }

        let next = record(METADATA_RECORDS_PER_PAGE as u32, FrameSlot::B);
        let mut erased = full;
        erased.erase_prefix(1, METADATA_PAGE_BYTES);
        for written_words in 0..=METADATA_RECORD_BYTES / 4 {
            let mut interrupted = erased.clone();
            interrupted.program_prefix(
                METADATA_PAGE_BYTES,
                &next.to_bytes(),
                written_words * 4,
            );
            let expected = if written_words == METADATA_RECORD_BYTES / 4 {
                next
            } else {
                latest
            };
            assert_eq!(interrupted.scan().latest, Some(expected));
        }
    }
}
