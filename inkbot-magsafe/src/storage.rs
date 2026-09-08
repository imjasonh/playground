//! Power-fail-safe metadata for the two internal-flash frame slots.
//!
//! Write a candidate into the inactive slot, read it back, verify its payload
//! CRC, and only then append its metadata record. The previous record and frame
//! remain valid until the new record is durable.
//!
//! Each slot always holds a complete controller-native framebuffer. For a
//! partial transfer, copy the active image into RAM, apply the patch, and write
//! the merged 48 KiB image to the inactive slot. `image_crc` covers that merged
//! image; `frame.crc` still covers the transfer payload.

use crate::panel::{Window, FRAME_BYTES};
use crate::protocol::{CommittedFrame, Crc32};

const MAGIC: [u8; 4] = *b"IMGF";
const FORMAT_VERSION: u8 = 1;

/// Encoded length of one frame metadata record.
pub const METADATA_RECORD_BYTES: usize = 40;

#[derive(Clone, Copy, PartialEq, Eq, Debug)]
#[repr(u8)]
pub enum FrameSlot {
    A = 0,
    B = 1,
}

impl FrameSlot {
    pub const fn other(self) -> Self {
        match self {
            Self::A => Self::B,
            Self::B => Self::A,
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
    fn successful_commit_alternates_slots() {
        let previous = record(12, FrameSlot::A);
        let next = FrameRecord {
            generation: previous.generation.wrapping_add(1),
            slot: previous.slot.other(),
            image_crc: previous.image_crc,
            frame: previous.frame,
        };
        assert_eq!(next.slot, FrameSlot::B);
        assert_eq!(select_latest(Some(previous), Some(next)), Some(next));
    }
}
