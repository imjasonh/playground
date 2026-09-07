//! The BLE frame-transfer protocol between the iOS app (sender) and the tile
//! (receiver).
//!
//! The link is lossy and background windows are short, so a transfer must be
//! resumable and idempotent. The sender announces a frame with a
//! versioned [`FrameHeader`] (id, length, CRC-32, target window), then streams
//! the pixel bytes in order. The receiver tracks how much it has and a running
//! CRC, so it never has to buffer the whole frame in RAM and can report an
//! offset to resume from after a dropped connection.

use crate::panel::{Window, FRAME_BYTES};

/// Streaming CRC-32 (IEEE 802.3, reflected), computed without a lookup table to
/// keep the code and RAM footprint small.
#[derive(Clone, Copy)]
pub struct Crc32 {
    state: u32,
}

impl Crc32 {
    /// A fresh CRC accumulator.
    pub const fn new() -> Self {
        Crc32 { state: 0xFFFF_FFFF }
    }

    /// Fold more bytes into the running value.
    pub fn update(&mut self, bytes: &[u8]) {
        for &byte in bytes {
            self.state ^= u32::from(byte);
            for _ in 0..8 {
                if self.state & 1 != 0 {
                    self.state = (self.state >> 1) ^ 0xEDB8_8320;
                } else {
                    self.state >>= 1;
                }
            }
        }
    }

    /// The final CRC value for everything folded in so far.
    pub fn finalize(self) -> u32 {
        !self.state
    }
}

impl Default for Crc32 {
    fn default() -> Self {
        Self::new()
    }
}

/// Frame-header wire version accepted by this firmware.
pub const PROTOCOL_VERSION: u8 = 1;

/// Wire length of an encoded [`FrameHeader`].
pub const HEADER_LEN: usize = 24;

/// Why a frame header could not be decoded.
#[derive(Clone, Copy, PartialEq, Eq, Debug)]
pub enum HeaderDecodeError {
    /// The input does not contain one complete header.
    InvalidLength,
    /// The sender uses a wire version this firmware does not implement.
    UnsupportedVersion,
    /// Reserved bytes are nonzero.
    ReservedBytes,
}

/// The announcement that opens (or re-opens) a frame transfer.
#[derive(Clone, Copy, PartialEq, Eq, Debug)]
pub struct FrameHeader {
    /// Monotonic frame id, so a repeated announcement is recognized.
    pub id: u32,
    /// Total pixel-data length in bytes.
    pub len: u32,
    /// CRC-32 of the whole pixel payload.
    pub crc: u32,
    /// The panel region this frame paints.
    pub window: Window,
}

impl FrameHeader {
    /// Encode to the fixed 24-byte little-endian wire form.
    pub fn to_bytes(self) -> [u8; HEADER_LEN] {
        let mut b = [0u8; HEADER_LEN];
        b[0] = PROTOCOL_VERSION;
        b[4..8].copy_from_slice(&self.id.to_le_bytes());
        b[8..12].copy_from_slice(&self.len.to_le_bytes());
        b[12..16].copy_from_slice(&self.crc.to_le_bytes());
        b[16..18].copy_from_slice(&self.window.x.to_le_bytes());
        b[18..20].copy_from_slice(&self.window.y.to_le_bytes());
        b[20..22].copy_from_slice(&self.window.w.to_le_bytes());
        b[22..24].copy_from_slice(&self.window.h.to_le_bytes());
        b
    }

    /// Decode the exact wire form.
    pub fn from_bytes(b: &[u8]) -> Result<Self, HeaderDecodeError> {
        if b.len() != HEADER_LEN {
            return Err(HeaderDecodeError::InvalidLength);
        }
        if b[0] != PROTOCOL_VERSION {
            return Err(HeaderDecodeError::UnsupportedVersion);
        }
        if b[1..4] != [0, 0, 0] {
            return Err(HeaderDecodeError::ReservedBytes);
        }
        let word = |o: usize| u32::from_le_bytes([b[o], b[o + 1], b[o + 2], b[o + 3]]);
        let half = |o: usize| u16::from_le_bytes([b[o], b[o + 1]]);
        Ok(FrameHeader {
            id: word(4),
            len: word(8),
            crc: word(12),
            window: Window {
                x: half(16),
                y: half(18),
                w: half(20),
                h: half(22),
            },
        })
    }

    /// Validate panel bounds, byte alignment, and payload length.
    pub fn validate(self) -> Result<(), BeginError> {
        if !self.window.is_valid() {
            return Err(BeginError::InvalidWindow);
        }
        let expected = self.window.packed_bytes();
        if expected > FRAME_BYTES || self.len != expected as u32 {
            return Err(BeginError::InvalidLength);
        }
        Ok(())
    }
}

/// The outcome of announcing a frame transfer.
#[derive(Clone, Copy, PartialEq, Eq, Debug)]
pub enum Begin {
    /// A new frame replaced any incomplete transfer.
    Started,
    /// The same frame was announced again. The sender can resume at this offset.
    Resumed(u32),
    /// The same frame already passed its length and CRC checks.
    Verified,
    /// The same canonical frame was already committed.
    AlreadyCommitted,
}

/// Why a frame announcement was rejected.
#[derive(Clone, Copy, PartialEq, Eq, Debug)]
pub enum BeginError {
    /// The panel window is empty, out of bounds, or not byte-aligned.
    InvalidWindow,
    /// The payload length does not exactly match the panel window.
    InvalidLength,
    /// The frame id matches an active transfer but describes different data.
    ConflictingId,
    /// Another verified frame must be committed or discarded first.
    UncommittedFrame,
    /// The frame id is not newer than the active or most recently committed frame.
    StaleId,
}

/// Why a frame chunk was rejected.
#[derive(Clone, Copy, PartialEq, Eq, Debug)]
pub enum AcceptError {
    /// No transfer is accepting bytes.
    NoActiveTransfer,
    /// The chunk does not begin at the receiver's requested offset.
    WrongOffset,
    /// Empty chunks cannot advance a transfer.
    EmptyChunk,
    /// The chunk extends past the announced payload length.
    ChunkTooLong,
    /// The completed payload does not match the announced CRC.
    CrcMismatch,
    /// Internal transfer counters became inconsistent.
    InvalidState,
}

/// Storage target that acknowledges a chunk only after retaining its bytes.
pub trait FrameSink {
    type Error;

    fn write(&mut self, offset: u32, bytes: &[u8]) -> Result<(), Self::Error>;
}

#[derive(Clone, Copy, PartialEq, Eq, Debug)]
pub enum IngestError<E> {
    Sink(E),
}

/// The outcome of offering a chunk to the [`Receiver`].
#[derive(Clone, Copy, PartialEq, Eq, Debug)]
pub enum Accept {
    /// Chunk taken; the value is the new total received so far.
    Progress(u32),
    /// All bytes are in and the CRC matched; the frame is ready to paint.
    Complete,
    /// The chunk was rejected.
    Rejected(AcceptError),
}

/// A frame that the caller has made durable.
#[derive(Clone, Copy, PartialEq, Eq, Debug)]
pub struct CommittedFrame {
    pub id: u32,
    pub len: u32,
    pub crc: u32,
    pub window: Window,
}

impl CommittedFrame {
    const fn matches(self, header: FrameHeader) -> bool {
        self.id == header.id
            && self.len == header.len
            && self.crc == header.crc
            && self.window.x == header.window.x
            && self.window.y == header.window.y
            && self.window.w == header.window.w
            && self.window.h == header.window.h
    }
}

/// Tracks one in-flight frame transfer.
pub struct Receiver {
    id: u32,
    len: u32,
    crc: u32,
    window: Window,
    received: u32,
    running: Crc32,
    active: bool,
    verified: bool,
    last_completed: Option<CommittedFrame>,
}

impl Receiver {
    /// An idle receiver with no active transfer.
    pub const fn new() -> Self {
        Receiver {
            id: 0,
            len: 0,
            crc: 0,
            window: Window::FULL,
            received: 0,
            running: Crc32::new(),
            active: false,
            verified: false,
            last_completed: None,
        }
    }

    /// Restore the replay boundary after loading a committed frame record.
    pub const fn with_last_completed(committed: CommittedFrame) -> Self {
        let mut receiver = Self::new();
        receiver.last_completed = Some(committed);
        receiver
    }

    /// Start a transfer. Re-announcing the same frame keeps existing progress,
    /// so a dropped-and-retried header does not restart the download.
    pub fn begin(&mut self, header: FrameHeader) -> Result<Begin, BeginError> {
        header.validate()?;
        if (self.active || self.verified) && self.id == header.id {
            if self.len == header.len && self.crc == header.crc && self.window == header.window {
                return if self.verified {
                    Ok(Begin::Verified)
                } else {
                    Ok(Begin::Resumed(self.received))
                };
            }
            return Err(BeginError::ConflictingId);
        }
        if self.verified {
            return Err(BeginError::UncommittedFrame);
        }
        if self.active && !sequence_is_newer(header.id, self.id) {
            return Err(BeginError::StaleId);
        }
        if let Some(committed) = self.last_completed {
            if header.id == committed.id {
                return if committed.matches(header) {
                    Ok(Begin::AlreadyCommitted)
                } else {
                    Err(BeginError::ConflictingId)
                };
            }
            if !sequence_is_newer(header.id, committed.id) {
                return Err(BeginError::StaleId);
            }
        }
        self.id = header.id;
        self.len = header.len;
        self.crc = header.crc;
        self.window = header.window;
        self.received = 0;
        self.running = Crc32::new();
        self.active = true;
        self.verified = false;
        Ok(Begin::Started)
    }

    /// Byte offset the next chunk must start at.
    pub fn offset(&self) -> u32 {
        self.received
    }

    /// Whether a transfer is in progress.
    pub fn is_active(&self) -> bool {
        self.active
    }

    /// Whether the received frame is waiting for a durable commit.
    pub fn is_verified(&self) -> bool {
        self.verified
    }

    /// The last frame that the caller committed to durable storage.
    pub fn last_completed(&self) -> Option<CommittedFrame> {
        self.last_completed
    }

    /// Record a verified frame after its pixels and metadata are durable.
    pub fn commit(&mut self) -> Option<CommittedFrame> {
        if !self.verified {
            return None;
        }
        let committed = CommittedFrame {
            id: self.id,
            len: self.len,
            crc: self.crc,
            window: self.window,
        };
        self.last_completed = Some(committed);
        self.verified = false;
        self.received = 0;
        self.running = Crc32::new();
        Some(committed)
    }

    /// Discard the active or verified transfer without moving the replay boundary.
    pub fn cancel(&mut self) {
        self.active = false;
        self.verified = false;
        self.received = 0;
        self.running = Crc32::new();
    }

    /// Retain a chunk, then advance the acknowledged transfer offset.
    pub fn ingest<S: FrameSink>(
        &mut self,
        at: u32,
        chunk: &[u8],
        sink: &mut S,
    ) -> Result<Accept, IngestError<S::Error>> {
        let Ok(chunk_len) = u32::try_from(chunk.len()) else {
            return Ok(Accept::Rejected(AcceptError::ChunkTooLong));
        };
        if !self.active {
            return Ok(Accept::Rejected(AcceptError::NoActiveTransfer));
        }
        if at != self.received {
            return Ok(Accept::Rejected(AcceptError::WrongOffset));
        }
        if chunk_len == 0 {
            return Ok(Accept::Rejected(AcceptError::EmptyChunk));
        }
        let Some(remaining) = self.len.checked_sub(self.received) else {
            self.cancel();
            return Ok(Accept::Rejected(AcceptError::InvalidState));
        };
        if chunk_len > remaining {
            return Ok(Accept::Rejected(AcceptError::ChunkTooLong));
        }
        sink.write(at, chunk).map_err(IngestError::Sink)?;
        Ok(self.accept_retained(at, chunk))
    }

    fn accept_retained(&mut self, at: u32, chunk: &[u8]) -> Accept {
        let Ok(chunk_len) = u32::try_from(chunk.len()) else {
            return Accept::Rejected(AcceptError::ChunkTooLong);
        };
        if !self.active {
            return Accept::Rejected(AcceptError::NoActiveTransfer);
        }
        if at != self.received {
            return Accept::Rejected(AcceptError::WrongOffset);
        }
        if chunk_len == 0 {
            return Accept::Rejected(AcceptError::EmptyChunk);
        }
        let Some(remaining) = self.len.checked_sub(self.received) else {
            self.cancel();
            return Accept::Rejected(AcceptError::InvalidState);
        };
        if chunk_len > remaining {
            return Accept::Rejected(AcceptError::ChunkTooLong);
        }
        self.running.update(chunk);
        self.received += chunk_len;
        if self.received != self.len {
            return Accept::Progress(self.received);
        }
        let matched = self.running.finalize() == self.crc;
        self.active = false;
        if matched {
            self.verified = true;
            Accept::Complete
        } else {
            self.cancel();
            Accept::Rejected(AcceptError::CrcMismatch)
        }
    }

    #[cfg(test)]
    fn accept(&mut self, at: u32, chunk: &[u8]) -> Accept {
        let mut sink = TestSink;
        self.ingest(at, chunk, &mut sink).unwrap()
    }
}

/// Compare wrapping sequence numbers while rejecting duplicates.
const fn sequence_is_newer(candidate: u32, previous: u32) -> bool {
    let distance = candidate.wrapping_sub(previous);
    distance != 0 && distance < (1 << 31)
}

impl Default for Receiver {
    fn default() -> Self {
        Self::new()
    }
}

#[cfg(test)]
struct TestSink;

#[cfg(test)]
impl FrameSink for TestSink {
    type Error = ();

    fn write(&mut self, _offset: u32, _bytes: &[u8]) -> Result<(), Self::Error> {
        Ok(())
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    // Reference CRC-32 of "123456789" is 0xCBF43926.
    #[test]
    fn crc32_matches_reference_vector() {
        let mut crc = Crc32::new();
        crc.update(b"123456789");
        assert_eq!(crc.finalize(), 0xCBF4_3926);
    }

    #[test]
    fn crc32_is_order_independent_across_updates() {
        let mut a = Crc32::new();
        a.update(b"12345");
        a.update(b"6789");
        assert_eq!(a.finalize(), 0xCBF4_3926);
    }

    fn header_for(data: &[u8], id: u32) -> FrameHeader {
        let mut crc = Crc32::new();
        crc.update(data);
        FrameHeader {
            id,
            len: data.len() as u32,
            crc: crc.finalize(),
            window: Window::FULL,
        }
    }

    #[test]
    fn header_round_trips() {
        let h = header_for(b"pixels", 7);
        let decoded = FrameHeader::from_bytes(&h.to_bytes()).unwrap();
        assert_eq!(h, decoded);
        assert_eq!(
            FrameHeader::from_bytes(&[0u8; 4]),
            Err(HeaderDecodeError::InvalidLength)
        );
        assert_eq!(
            FrameHeader::from_bytes(&[0u8; HEADER_LEN + 1]),
            Err(HeaderDecodeError::InvalidLength)
        );

        let mut unsupported = h.to_bytes();
        unsupported[0] = PROTOCOL_VERSION + 1;
        assert_eq!(
            FrameHeader::from_bytes(&unsupported),
            Err(HeaderDecodeError::UnsupportedVersion)
        );

        let mut reserved = h.to_bytes();
        reserved[2] = 1;
        assert_eq!(
            FrameHeader::from_bytes(&reserved),
            Err(HeaderDecodeError::ReservedBytes)
        );
    }

    #[test]
    fn streamed_chunks_complete_and_verify() {
        let data = b"the quick brown fox";
        let mut rx = Receiver::new();
        let mut header = header_for(data, 1);
        header.window = Window {
            x: 0,
            y: 0,
            w: 152,
            h: 1,
        };
        assert_eq!(header.len, header.window.packed_bytes() as u32);
        assert_eq!(rx.begin(header), Ok(Begin::Started));
        assert_eq!(rx.accept(0, &data[0..4]), Accept::Progress(4));
        assert_eq!(rx.offset(), 4);
        assert_eq!(rx.accept(4, &data[4..]), Accept::Complete);
        assert!(!rx.is_active());
        assert!(rx.is_verified());
        assert_eq!(rx.last_completed(), None);
        let committed = CommittedFrame {
            id: 1,
            len: header.len,
            crc: header.crc,
            window: header.window,
        };
        assert_eq!(rx.commit(), Some(committed));
        assert_eq!(rx.last_completed(), Some(committed));
    }

    #[test]
    fn out_of_order_chunk_is_rejected_and_offset_holds() {
        let data = b"abcdefgh";
        let mut rx = Receiver::new();
        let h = FrameHeader {
            window: Window {
                x: 0,
                y: 0,
                w: 64,
                h: 1,
            },
            ..header_for(data, 1)
        };
        rx.begin(h).unwrap();
        assert_eq!(rx.accept(0, &data[0..4]), Accept::Progress(4));
        // Sender jumps ahead; receiver rejects and keeps its offset for resume.
        assert_eq!(
            rx.accept(6, &data[6..]),
            Accept::Rejected(AcceptError::WrongOffset)
        );
        assert_eq!(rx.offset(), 4);
        assert_eq!(rx.accept(4, &data[4..]), Accept::Complete);
    }

    #[test]
    fn corrupt_payload_fails_crc() {
        let data = b"abcdefgh";
        let mut header = header_for(data, 1);
        header.window = Window {
            x: 0,
            y: 0,
            w: 64,
            h: 1,
        };
        header.crc ^= 0x1; // wrong CRC
        let mut rx = Receiver::new();
        rx.begin(header).unwrap();
        assert_eq!(
            rx.accept(0, data),
            Accept::Rejected(AcceptError::CrcMismatch)
        );
        assert_eq!(rx.offset(), 0);
        assert!(!rx.is_active());
        assert!(!rx.is_verified());
        assert_eq!(rx.commit(), None);
    }

    #[test]
    fn re_announcing_same_frame_keeps_progress() {
        let data = b"abcdefgh";
        let h = FrameHeader {
            window: Window {
                x: 0,
                y: 0,
                w: 64,
                h: 1,
            },
            ..header_for(data, 1)
        };
        let mut rx = Receiver::new();
        rx.begin(h).unwrap();
        assert_eq!(rx.accept(0, &data[0..4]), Accept::Progress(4));
        assert_eq!(rx.begin(h), Ok(Begin::Resumed(4)));
        assert_eq!(rx.offset(), 4);
        assert_eq!(rx.accept(4, &data[4..]), Accept::Complete);
        assert_eq!(rx.begin(h), Ok(Begin::Verified));
    }

    #[test]
    fn a_new_frame_id_resets_progress() {
        let first = b"abcdefgh";
        let first_header = FrameHeader {
            window: Window {
                x: 0,
                y: 0,
                w: 64,
                h: 1,
            },
            ..header_for(first, 1)
        };
        let mut rx = Receiver::new();
        rx.begin(first_header).unwrap();
        assert_eq!(rx.accept(0, &first[0..4]), Accept::Progress(4));
        let second = b"zyxw";
        let second_header = FrameHeader {
            window: Window {
                x: 0,
                y: 0,
                w: 32,
                h: 1,
            },
            ..header_for(second, 2)
        };
        rx.begin(second_header).unwrap();
        assert_eq!(rx.offset(), 0);
        assert_eq!(rx.accept(0, second), Accept::Complete);
    }

    #[test]
    fn header_must_match_an_aligned_panel_window() {
        let mut h = header_for(&[0; 8], 1);
        h.window = Window {
            x: 1,
            y: 0,
            w: 64,
            h: 1,
        };
        assert_eq!(h.validate(), Err(BeginError::InvalidWindow));

        h.window.x = 0;
        h.len = 7;
        assert_eq!(h.validate(), Err(BeginError::InvalidLength));
    }

    #[test]
    fn conflicting_and_stale_frame_ids_are_rejected() {
        let data = b"abcdefgh";
        let h = FrameHeader {
            window: Window {
                x: 0,
                y: 0,
                w: 64,
                h: 1,
            },
            ..header_for(data, 7)
        };
        let mut rx = Receiver::new();
        rx.begin(h).unwrap();

        let mut conflict = h;
        conflict.crc ^= 1;
        assert_eq!(rx.begin(conflict), Err(BeginError::ConflictingId));
        assert_eq!(rx.accept(0, data), Accept::Complete);
        assert_eq!(rx.begin(h), Ok(Begin::Verified));
        assert_eq!(rx.commit().unwrap().id, 7);
        assert_eq!(rx.begin(h), Ok(Begin::AlreadyCommitted));

        let mut committed_conflict = h;
        committed_conflict.crc ^= 1;
        assert_eq!(rx.begin(committed_conflict), Err(BeginError::ConflictingId));

        let mut older = h;
        older.id = 6;
        assert_eq!(rx.begin(older), Err(BeginError::StaleId));
    }

    #[test]
    fn empty_and_oversized_chunks_do_not_advance() {
        let data = b"abcdefgh";
        let h = FrameHeader {
            window: Window {
                x: 0,
                y: 0,
                w: 64,
                h: 1,
            },
            ..header_for(data, 1)
        };
        let mut rx = Receiver::new();
        rx.begin(h).unwrap();
        assert_eq!(rx.accept(0, &[]), Accept::Rejected(AcceptError::EmptyChunk));
        assert_eq!(
            rx.accept(0, b"123456789"),
            Accept::Rejected(AcceptError::ChunkTooLong)
        );
        assert_eq!(rx.offset(), 0);
    }

    #[test]
    fn sink_failure_does_not_acknowledge_bytes() {
        struct FailingSink;

        impl FrameSink for FailingSink {
            type Error = u8;

            fn write(&mut self, _offset: u32, _bytes: &[u8]) -> Result<(), Self::Error> {
                Err(7)
            }
        }

        let data = b"abcdefgh";
        let header = FrameHeader {
            window: Window {
                x: 0,
                y: 0,
                w: 64,
                h: 1,
            },
            ..header_for(data, 1)
        };
        let mut receiver = Receiver::new();
        receiver.begin(header).unwrap();
        assert_eq!(
            receiver.ingest(0, data, &mut FailingSink),
            Err(IngestError::Sink(7))
        );
        assert_eq!(receiver.offset(), 0);
        assert!(receiver.is_active());
    }

    #[test]
    fn active_transfer_rejects_an_older_replacement() {
        let data = b"abcdefgh";
        let active = FrameHeader {
            window: Window {
                x: 0,
                y: 0,
                w: 64,
                h: 1,
            },
            ..header_for(data, 10)
        };
        let mut rx = Receiver::new();
        rx.begin(active).unwrap();
        let mut older = active;
        older.id = 9;
        assert_eq!(rx.begin(older), Err(BeginError::StaleId));
        assert_eq!(rx.begin(active), Ok(Begin::Resumed(0)));
    }

    #[test]
    fn verified_frame_blocks_replacement_until_commit_or_cancel() {
        let data = b"abcdefgh";
        let first = FrameHeader {
            window: Window {
                x: 0,
                y: 0,
                w: 64,
                h: 1,
            },
            ..header_for(data, 1)
        };
        let mut rx = Receiver::new();
        rx.begin(first).unwrap();
        assert_eq!(rx.accept(0, data), Accept::Complete);

        let mut next = first;
        next.id = 2;
        assert_eq!(rx.begin(next), Err(BeginError::UncommittedFrame));
        rx.cancel();
        assert_eq!(rx.begin(next), Ok(Begin::Started));
    }

    #[test]
    fn restored_replay_boundary_survives_a_restart() {
        let data = b"abcdefgh";
        let old = FrameHeader {
            window: Window {
                x: 0,
                y: 0,
                w: 64,
                h: 1,
            },
            ..header_for(data, 41)
        };
        let committed = CommittedFrame {
            id: old.id,
            len: old.len,
            crc: old.crc,
            window: old.window,
        };
        let mut rx = Receiver::with_last_completed(committed);
        assert_eq!(rx.begin(old), Ok(Begin::AlreadyCommitted));

        let mut next = old;
        next.id = 42;
        assert_eq!(rx.begin(next), Ok(Begin::Started));
    }
}
