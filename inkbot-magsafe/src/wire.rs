//! Versioned BLE control, status, capability, and GATT fallback wire formats.

use crate::protocol::{FrameHeader, HeaderDecodeError, HEADER_LEN, PROTOCOL_VERSION};

pub const SERVICE_UUID: [u8; 16] = [
    0xad, 0x1e, 0x04, 0x0b, 0x23, 0x85, 0x58, 0x8b, 0xa9, 0xf3, 0x5c, 0x11, 0xb3, 0x60, 0xb3, 0x5c,
];
pub const CONTROL_UUID: [u8; 16] = [
    0xc2, 0xc9, 0xd6, 0x10, 0xbf, 0x0a, 0x51, 0xbc, 0xb3, 0xde, 0xac, 0xf5, 0x75, 0xf0, 0x21, 0xc3,
];
pub const CAPABILITIES_UUID: [u8; 16] = [
    0xda, 0xd1, 0xd5, 0x26, 0xcb, 0x2b, 0x54, 0x66, 0x9a, 0x57, 0xf9, 0x8d, 0x52, 0x90, 0x2a, 0xb5,
];
pub const STATUS_UUID: [u8; 16] = [
    0xec, 0x99, 0x95, 0x86, 0x41, 0x4b, 0x5a, 0x08, 0x9a, 0x1a, 0x28, 0x75, 0x70, 0x68, 0x47, 0xfa,
];
pub const FRAME_UUID: [u8; 16] = [
    0x61, 0x9d, 0x0f, 0xc7, 0x76, 0x4a, 0x53, 0xc9, 0x8f, 0x25, 0xbd, 0xba, 0x65, 0x5b, 0xeb, 0x92,
];

pub const CONTROL_BEGIN: u8 = 0x01;
pub const CONTROL_COMMIT: u8 = 0x02;
pub const CONTROL_CANCEL: u8 = 0x03;
pub const CONTROL_QUERY_STATUS: u8 = 0x04;
pub const CONTROL_PREFIX_LEN: usize = 2;
pub const CHUNK_HEADER_LEN: usize = 9;
pub const STATUS_LEN: usize = 16;
pub const CAPABILITIES_LEN: usize = 8;
pub const TRANSFER_IDLE_TIMEOUT_MS: u32 = 30_000;

#[derive(Clone, Copy, PartialEq, Eq, Debug)]
pub enum WireDecodeError {
    InvalidLength,
    UnsupportedVersion,
    UnknownOpcode,
    ReservedBytes,
    InvalidPhase,
    InvalidStatus,
    InvalidCapabilities,
    EmptyChunk,
    Header(HeaderDecodeError),
}

#[derive(Clone, Copy, PartialEq, Eq, Debug)]
pub enum WireEncodeError {
    BufferTooSmall,
}

#[derive(Clone, Copy, PartialEq, Eq, Debug)]
pub enum ControlRequest {
    Begin(FrameHeader),
    Commit { frame_id: u32 },
    Cancel { frame_id: u32 },
    QueryStatus,
}

impl ControlRequest {
    pub const fn encoded_len(self) -> usize {
        match self {
            Self::Begin(_) => CONTROL_PREFIX_LEN + HEADER_LEN,
            Self::Commit { .. } | Self::Cancel { .. } => CONTROL_PREFIX_LEN + 4,
            Self::QueryStatus => CONTROL_PREFIX_LEN,
        }
    }

    pub fn encode(self, output: &mut [u8]) -> Result<usize, WireEncodeError> {
        let length = self.encoded_len();
        if output.len() < length {
            return Err(WireEncodeError::BufferTooSmall);
        }
        output[0] = PROTOCOL_VERSION;
        match self {
            Self::Begin(header) => {
                output[1] = CONTROL_BEGIN;
                output[CONTROL_PREFIX_LEN..length].copy_from_slice(&header.to_bytes());
            }
            Self::Commit { frame_id } => {
                output[1] = CONTROL_COMMIT;
                output[CONTROL_PREFIX_LEN..length].copy_from_slice(&frame_id.to_le_bytes());
            }
            Self::Cancel { frame_id } => {
                output[1] = CONTROL_CANCEL;
                output[CONTROL_PREFIX_LEN..length].copy_from_slice(&frame_id.to_le_bytes());
            }
            Self::QueryStatus => {
                output[1] = CONTROL_QUERY_STATUS;
            }
        }
        Ok(length)
    }

    pub fn decode(bytes: &[u8]) -> Result<Self, WireDecodeError> {
        if bytes.len() < CONTROL_PREFIX_LEN {
            return Err(WireDecodeError::InvalidLength);
        }
        if bytes[0] != PROTOCOL_VERSION {
            return Err(WireDecodeError::UnsupportedVersion);
        }
        match bytes[1] {
            CONTROL_BEGIN if bytes.len() == CONTROL_PREFIX_LEN + HEADER_LEN => {
                FrameHeader::from_bytes(&bytes[CONTROL_PREFIX_LEN..])
                    .map(Self::Begin)
                    .map_err(WireDecodeError::Header)
            }
            CONTROL_COMMIT if bytes.len() == CONTROL_PREFIX_LEN + 4 => Ok(Self::Commit {
                frame_id: word(bytes, CONTROL_PREFIX_LEN),
            }),
            CONTROL_CANCEL if bytes.len() == CONTROL_PREFIX_LEN + 4 => Ok(Self::Cancel {
                frame_id: word(bytes, CONTROL_PREFIX_LEN),
            }),
            CONTROL_QUERY_STATUS if bytes.len() == CONTROL_PREFIX_LEN => Ok(Self::QueryStatus),
            CONTROL_BEGIN | CONTROL_COMMIT | CONTROL_CANCEL | CONTROL_QUERY_STATUS => {
                Err(WireDecodeError::InvalidLength)
            }
            _ => Err(WireDecodeError::UnknownOpcode),
        }
    }
}

#[derive(Clone, Copy, PartialEq, Eq, Debug)]
pub struct FrameChunk<'a> {
    pub frame_id: u32,
    pub offset: u32,
    pub payload: &'a [u8],
}

impl<'a> FrameChunk<'a> {
    pub fn decode(bytes: &'a [u8]) -> Result<Self, WireDecodeError> {
        if bytes.len() <= CHUNK_HEADER_LEN {
            return if bytes.len() == CHUNK_HEADER_LEN {
                Err(WireDecodeError::EmptyChunk)
            } else {
                Err(WireDecodeError::InvalidLength)
            };
        }
        if bytes[0] != PROTOCOL_VERSION {
            return Err(WireDecodeError::UnsupportedVersion);
        }
        Ok(Self {
            frame_id: word(bytes, 1),
            offset: word(bytes, 5),
            payload: &bytes[CHUNK_HEADER_LEN..],
        })
    }

    pub fn encode(self, output: &mut [u8]) -> Result<usize, WireEncodeError> {
        let length = CHUNK_HEADER_LEN + self.payload.len();
        if output.len() < length {
            return Err(WireEncodeError::BufferTooSmall);
        }
        output[0] = PROTOCOL_VERSION;
        output[1..5].copy_from_slice(&self.frame_id.to_le_bytes());
        output[5..9].copy_from_slice(&self.offset.to_le_bytes());
        output[CHUNK_HEADER_LEN..length].copy_from_slice(self.payload);
        Ok(length)
    }
}

#[derive(Clone, Copy, PartialEq, Eq, Debug)]
#[repr(u8)]
pub enum TransferPhase {
    Idle = 0,
    Receiving = 1,
    Verified = 2,
    Committed = 3,
}

impl TransferPhase {
    const fn decode(value: u8) -> Option<Self> {
        match value {
            0 => Some(Self::Idle),
            1 => Some(Self::Receiving),
            2 => Some(Self::Verified),
            3 => Some(Self::Committed),
            _ => None,
        }
    }
}

#[derive(Clone, Copy, PartialEq, Eq, Debug)]
#[repr(u8)]
pub enum StatusCode {
    Ok = 0,
    InvalidRequest = 1,
    StaleFrame = 2,
    WrongOffset = 3,
    CrcMismatch = 4,
    StorageFailure = 5,
    PowerInhibited = 6,
    PanelFailure = 7,
}

impl StatusCode {
    const fn decode(value: u8) -> Option<Self> {
        match value {
            0 => Some(Self::Ok),
            1 => Some(Self::InvalidRequest),
            2 => Some(Self::StaleFrame),
            3 => Some(Self::WrongOffset),
            4 => Some(Self::CrcMismatch),
            5 => Some(Self::StorageFailure),
            6 => Some(Self::PowerInhibited),
            7 => Some(Self::PanelFailure),
            _ => None,
        }
    }
}

#[derive(Clone, Copy, PartialEq, Eq, Debug)]
pub struct TransferStatus {
    pub phase: TransferPhase,
    pub code: StatusCode,
    pub frame_id: u32,
    pub next_offset: u32,
    pub committed_id: u32,
}

impl TransferStatus {
    pub fn to_bytes(self) -> [u8; STATUS_LEN] {
        let mut bytes = [0; STATUS_LEN];
        bytes[0] = PROTOCOL_VERSION;
        bytes[1] = self.phase as u8;
        bytes[2] = self.code as u8;
        bytes[4..8].copy_from_slice(&self.frame_id.to_le_bytes());
        bytes[8..12].copy_from_slice(&self.next_offset.to_le_bytes());
        bytes[12..16].copy_from_slice(&self.committed_id.to_le_bytes());
        bytes
    }

    pub fn from_bytes(bytes: &[u8]) -> Result<Self, WireDecodeError> {
        if bytes.len() != STATUS_LEN {
            return Err(WireDecodeError::InvalidLength);
        }
        if bytes[0] != PROTOCOL_VERSION {
            return Err(WireDecodeError::UnsupportedVersion);
        }
        if bytes[3] != 0 {
            return Err(WireDecodeError::ReservedBytes);
        }
        Ok(Self {
            phase: TransferPhase::decode(bytes[1]).ok_or(WireDecodeError::InvalidPhase)?,
            code: StatusCode::decode(bytes[2]).ok_or(WireDecodeError::InvalidStatus)?,
            frame_id: word(bytes, 4),
            next_offset: word(bytes, 8),
            committed_id: word(bytes, 12),
        })
    }
}

#[derive(Clone, Copy, PartialEq, Eq, Debug)]
pub struct Capabilities {
    pub max_gatt_chunk: u16,
    pub l2cap_psm: Option<u16>,
    pub max_l2cap_chunk: u16,
}

impl Capabilities {
    pub const fn is_valid(self) -> bool {
        self.max_gatt_chunk > 0
            && match self.l2cap_psm {
                Some(psm) => psm >= 0x0080 && psm <= 0x00ff && self.max_l2cap_chunk > 0,
                None => self.max_l2cap_chunk == 0,
            }
    }

    pub fn to_bytes(self) -> Result<[u8; CAPABILITIES_LEN], WireDecodeError> {
        if !self.is_valid() {
            return Err(WireDecodeError::InvalidCapabilities);
        }
        let mut bytes = [0; CAPABILITIES_LEN];
        bytes[0] = PROTOCOL_VERSION;
        if let Some(psm) = self.l2cap_psm {
            bytes[1] = 1;
            bytes[2..4].copy_from_slice(&psm.to_le_bytes());
        }
        bytes[4..6].copy_from_slice(&self.max_gatt_chunk.to_le_bytes());
        bytes[6..8].copy_from_slice(&self.max_l2cap_chunk.to_le_bytes());
        Ok(bytes)
    }

    pub fn from_bytes(bytes: &[u8]) -> Result<Self, WireDecodeError> {
        if bytes.len() != CAPABILITIES_LEN {
            return Err(WireDecodeError::InvalidLength);
        }
        if bytes[0] != PROTOCOL_VERSION {
            return Err(WireDecodeError::UnsupportedVersion);
        }
        if bytes[1] & !1 != 0 {
            return Err(WireDecodeError::ReservedBytes);
        }
        let has_l2cap = bytes[1] & 1 != 0;
        let psm = half(bytes, 2);
        let capabilities = Self {
            max_gatt_chunk: half(bytes, 4),
            l2cap_psm: has_l2cap.then_some(psm),
            max_l2cap_chunk: half(bytes, 6),
        };
        if (!has_l2cap && psm != 0) || !capabilities.is_valid() {
            return Err(WireDecodeError::InvalidCapabilities);
        }
        Ok(capabilities)
    }
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

#[cfg(test)]
mod tests {
    use super::*;
    use crate::panel::Window;

    fn header() -> FrameHeader {
        FrameHeader {
            id: 0x1122_3344,
            len: 1,
            crc: 0xaabb_ccdd,
            window: Window {
                x: 8,
                y: 2,
                w: 8,
                h: 1,
            },
        }
    }

    fn round_trip(request: ControlRequest) {
        let mut encoded = [0; CONTROL_PREFIX_LEN + HEADER_LEN];
        let length = request.encode(&mut encoded).unwrap();
        assert_eq!(ControlRequest::decode(&encoded[..length]), Ok(request));
        assert_eq!(
            request.encode(&mut encoded[..length - 1]),
            Err(WireEncodeError::BufferTooSmall)
        );
    }

    #[test]
    fn stable_uuid_and_control_vectors() {
        assert_eq!(
            SERVICE_UUID,
            [
                0xad, 0x1e, 0x04, 0x0b, 0x23, 0x85, 0x58, 0x8b, 0xa9, 0xf3, 0x5c, 0x11, 0xb3, 0x60,
                0xb3, 0x5c,
            ]
        );
        let begin = ControlRequest::Begin(header());
        let mut encoded = [0; CONTROL_PREFIX_LEN + HEADER_LEN];
        begin.encode(&mut encoded).unwrap();
        assert_eq!(
            encoded,
            [
                1, 1, 1, 0, 0, 0, 0x44, 0x33, 0x22, 0x11, 1, 0, 0, 0, 0xdd, 0xcc, 0xbb, 0xaa, 8, 0,
                2, 0, 8, 0, 1, 0,
            ]
        );
        round_trip(begin);
        round_trip(ControlRequest::Commit {
            frame_id: 0x1122_3344,
        });
        round_trip(ControlRequest::Cancel {
            frame_id: 0x1122_3344,
        });
        round_trip(ControlRequest::QueryStatus);
    }

    #[test]
    fn malformed_control_messages_are_rejected() {
        let request = ControlRequest::Begin(header());
        let mut encoded = [0; CONTROL_PREFIX_LEN + HEADER_LEN];
        let length = request.encode(&mut encoded).unwrap();
        for truncated in 0..length {
            assert!(ControlRequest::decode(&encoded[..truncated]).is_err());
        }
        encoded[0] = 2;
        assert_eq!(
            ControlRequest::decode(&encoded),
            Err(WireDecodeError::UnsupportedVersion)
        );
        encoded[0] = PROTOCOL_VERSION;
        encoded[1] = 0xff;
        assert_eq!(
            ControlRequest::decode(&encoded),
            Err(WireDecodeError::UnknownOpcode)
        );
    }

    #[test]
    fn gatt_chunk_envelope_round_trips_without_copying_payload() {
        let chunk = FrameChunk {
            frame_id: 0x1122_3344,
            offset: 0x5566_7788,
            payload: &[0xaa, 0xbb, 0xcc],
        };
        let mut encoded = [0; 12];
        assert_eq!(chunk.encode(&mut encoded), Ok(12));
        assert_eq!(
            encoded,
            [1, 0x44, 0x33, 0x22, 0x11, 0x88, 0x77, 0x66, 0x55, 0xaa, 0xbb, 0xcc]
        );
        assert_eq!(FrameChunk::decode(&encoded), Ok(chunk));
        assert_eq!(
            FrameChunk::decode(&encoded[..CHUNK_HEADER_LEN]),
            Err(WireDecodeError::EmptyChunk)
        );
    }

    #[test]
    fn status_vector_round_trips_and_rejects_reserved_bytes() {
        let status = TransferStatus {
            phase: TransferPhase::Receiving,
            code: StatusCode::WrongOffset,
            frame_id: 0x1122_3344,
            next_offset: 0x5566_7788,
            committed_id: 9,
        };
        let mut encoded = status.to_bytes();
        assert_eq!(
            encoded,
            [1, 1, 3, 0, 0x44, 0x33, 0x22, 0x11, 0x88, 0x77, 0x66, 0x55, 9, 0, 0, 0]
        );
        assert_eq!(TransferStatus::from_bytes(&encoded), Ok(status));
        encoded[3] = 1;
        assert_eq!(
            TransferStatus::from_bytes(&encoded),
            Err(WireDecodeError::ReservedBytes)
        );
    }

    #[test]
    fn capabilities_publish_transport_limits_and_dynamic_psm() {
        let expected = Capabilities {
            max_gatt_chunk: 234,
            l2cap_psm: Some(0x0081),
            max_l2cap_chunk: 1024,
        };
        let encoded = expected.to_bytes().unwrap();
        assert_eq!(Capabilities::from_bytes(&encoded), Ok(expected));

        let gatt_only = Capabilities {
            max_gatt_chunk: 234,
            l2cap_psm: None,
            max_l2cap_chunk: 0,
        };
        assert_eq!(
            Capabilities::from_bytes(&gatt_only.to_bytes().unwrap()),
            Ok(gatt_only)
        );

        let invalid_psm = Capabilities {
            l2cap_psm: Some(0x0100),
            ..expected
        };
        assert_eq!(
            invalid_psm.to_bytes(),
            Err(WireDecodeError::InvalidCapabilities)
        );
    }
}
