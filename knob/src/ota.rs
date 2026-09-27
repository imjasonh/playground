//! BLE firmware update session.
//!
//! The iOS app writes a begin command, then ordered data packets, then
//! finish. This type checks the sequence, the size, and the CRC-32. The
//! device writes each accepted chunk into the inactive OTA slot. An image
//! aimed at the companion is relayed over the UART link instead.

use crate::board::{APP_SLOT_ESP32, APP_SLOT_S3};
use crate::crc::Crc32;

/// Which chip the image is for.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum OtaTarget {
    S3 = 0,
    Esp32 = 1,
}

impl OtaTarget {
    pub fn from_u8(v: u8) -> Option<Self> {
        match v {
            0 => Some(Self::S3),
            1 => Some(Self::Esp32),
            _ => None,
        }
    }

    pub fn slot_limit(self) -> u32 {
        match self {
            Self::S3 => APP_SLOT_S3,
            Self::Esp32 => APP_SLOT_ESP32,
        }
    }
}

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum OtaState {
    Idle,
    Receiving,
    Complete,
    Failed,
}

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum OtaError {
    Busy,
    Idle,
    BadTarget,
    TooLarge,
    Empty,
    Seq,
    Overflow,
    Crc,
    State,
}

#[derive(Clone, Debug)]
pub struct OtaSession {
    state: OtaState,
    target: Option<OtaTarget>,
    size: u32,
    expect_crc: u32,
    written: u32,
    next_seq: u16,
    crc: Crc32,
    error: Option<OtaError>,
}

impl Default for OtaSession {
    fn default() -> Self {
        Self::new()
    }
}

impl OtaSession {
    pub fn new() -> Self {
        Self {
            state: OtaState::Idle,
            target: None,
            size: 0,
            expect_crc: 0,
            written: 0,
            next_seq: 0,
            crc: Crc32::new(),
            error: None,
        }
    }

    pub fn state(&self) -> OtaState {
        self.state
    }

    pub fn written(&self) -> u32 {
        self.written
    }

    pub fn target(&self) -> Option<OtaTarget> {
        self.target
    }

    pub fn error(&self) -> Option<OtaError> {
        self.error
    }

    pub fn begin(&mut self, target: OtaTarget, size: u32, crc: u32) -> Result<(), OtaError> {
        if self.state == OtaState::Receiving {
            return Err(OtaError::Busy);
        }
        if size == 0 {
            return self.fail(OtaError::Empty);
        }
        if size > target.slot_limit() {
            return self.fail(OtaError::TooLarge);
        }
        *self = Self::new();
        self.state = OtaState::Receiving;
        self.target = Some(target);
        self.size = size;
        self.expect_crc = crc;
        Ok(())
    }

    /// Accept the next chunk. `seq` starts at 0 and increases by 1.
    pub fn push(&mut self, seq: u16, data: &[u8]) -> Result<(), OtaError> {
        if self.state != OtaState::Receiving {
            return Err(OtaError::Idle);
        }
        if seq != self.next_seq {
            return self.fail(OtaError::Seq);
        }
        if data.is_empty() {
            return self.fail(OtaError::Empty);
        }
        let next = self.written.saturating_add(data.len() as u32);
        if next > self.size {
            return self.fail(OtaError::Overflow);
        }
        self.crc.update(data);
        self.written = next;
        self.next_seq = self.next_seq.wrapping_add(1);
        Ok(())
    }

    pub fn finish(&mut self) -> Result<OtaTarget, OtaError> {
        if self.state != OtaState::Receiving {
            return Err(OtaError::State);
        }
        if self.written != self.size {
            return self.fail(OtaError::State);
        }
        if self.crc.finish() != self.expect_crc {
            return self.fail(OtaError::Crc);
        }
        self.state = OtaState::Complete;
        self.target.ok_or(OtaError::BadTarget)
    }

    pub fn abort(&mut self) {
        *self = Self::new();
    }

    /// Record a device-side failure (flash write, link, or CRC) and stop the session.
    pub fn note_error(&mut self, err: OtaError) {
        let _ = self.fail::<()>(err);
    }

    fn fail<T>(&mut self, err: OtaError) -> Result<T, OtaError> {
        self.state = OtaState::Failed;
        self.error = Some(err);
        Err(err)
    }
}

/// Control characteristic opcodes.
pub mod opcode {
    pub const BEGIN: u8 = 0x01;
    pub const ABORT: u8 = 0x02;
    pub const FINISH: u8 = 0x03;
    pub const REBOOT: u8 = 0x04;
    pub const MARK_VALID: u8 = 0x05;
}

/// Begin payload: target u8, size u32 le, crc u32 le.
pub fn encode_begin(target: OtaTarget, size: u32, crc: u32) -> [u8; 10] {
    let mut out = [0u8; 10];
    out[0] = opcode::BEGIN;
    out[1] = target as u8;
    out[2..6].copy_from_slice(&size.to_le_bytes());
    out[6..10].copy_from_slice(&crc.to_le_bytes());
    out
}

pub fn parse_begin(data: &[u8]) -> Result<(OtaTarget, u32, u32), OtaError> {
    if data.len() != 10 || data[0] != opcode::BEGIN {
        return Err(OtaError::State);
    }
    let target = OtaTarget::from_u8(data[1]).ok_or(OtaError::BadTarget)?;
    let size = u32::from_le_bytes(data[2..6].try_into().unwrap());
    let crc = u32::from_le_bytes(data[6..10].try_into().unwrap());
    Ok((target, size, crc))
}

/// Data packet: seq u16 le, then bytes.
pub fn encode_chunk(seq: u16, data: &[u8]) -> Vec<u8> {
    let mut out = Vec::with_capacity(2 + data.len());
    out.extend_from_slice(&seq.to_le_bytes());
    out.extend_from_slice(data);
    out
}

pub fn parse_chunk(data: &[u8]) -> Result<(u16, &[u8]), OtaError> {
    if data.len() < 3 {
        return Err(OtaError::Empty);
    }
    let seq = u16::from_le_bytes(data[0..2].try_into().unwrap());
    Ok((seq, &data[2..]))
}

/// Status notify: state, target, written u32 le, error.
pub fn encode_status(session: &OtaSession) -> [u8; 7] {
    let mut out = [0u8; 7];
    out[0] = match session.state() {
        OtaState::Idle => 0,
        OtaState::Receiving => 1,
        OtaState::Complete => 2,
        OtaState::Failed => 3,
    };
    out[1] = session.target().map(|t| t as u8).unwrap_or(0xFF);
    out[2..6].copy_from_slice(&session.written().to_le_bytes());
    out[6] = session.error().map(error_code).unwrap_or(0);
    out
}

pub fn error_code(err: OtaError) -> u8 {
    match err {
        OtaError::Busy => 1,
        OtaError::Idle => 2,
        OtaError::BadTarget => 3,
        OtaError::TooLarge => 4,
        OtaError::Empty => 5,
        OtaError::Seq => 6,
        OtaError::Overflow => 7,
        OtaError::Crc => 8,
        OtaError::State => 9,
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::crc::crc32;

    #[test]
    fn accepts_ordered_chunks_and_checks_crc() {
        let image = b"firmware-bytes-for-the-s3";
        let sum = crc32(image);
        let mut s = OtaSession::new();
        s.begin(OtaTarget::S3, image.len() as u32, sum).unwrap();
        let frame = encode_chunk(0, &image[..10]);
        let (seq, chunk) = parse_chunk(&frame).unwrap();
        s.push(seq, chunk).unwrap();
        s.push(1, &image[10..]).unwrap();
        assert_eq!(s.finish().unwrap(), OtaTarget::S3);
        assert_eq!(s.state(), OtaState::Complete);
    }

    #[test]
    fn rejects_a_gap_and_an_oversized_image() {
        let mut s = OtaSession::new();
        s.begin(OtaTarget::Esp32, 4, crc32(b"abcd")).unwrap();
        assert_eq!(s.push(1, b"ab"), Err(OtaError::Seq));
        assert_eq!(s.state(), OtaState::Failed);

        let mut s = OtaSession::new();
        let too_big = OtaTarget::Esp32.slot_limit() + 1;
        assert_eq!(
            s.begin(OtaTarget::Esp32, too_big, 0),
            Err(OtaError::TooLarge)
        );
    }

    #[test]
    fn begin_bytes_round_trip() {
        let raw = encode_begin(OtaTarget::Esp32, 32, 0xAABB_CCDD);
        assert_eq!(
            parse_begin(&raw).unwrap(),
            (OtaTarget::Esp32, 32, 0xAABB_CCDD)
        );
    }
}
