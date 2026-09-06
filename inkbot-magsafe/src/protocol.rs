//! The BLE frame-transfer protocol between the iOS app (sender) and the tile
//! (receiver).
//!
//! The link is lossy and background windows are short, so a transfer must be
//! resumable and idempotent. The sender announces a frame with a
//! [`FrameHeader`] (id, length, CRC-32, target window), then streams the pixel
//! bytes in order. The receiver tracks how much it has and a running CRC, so it
//! never has to buffer the whole frame in RAM and can report an offset to
//! resume from after a dropped connection.

use crate::panel::Window;

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

/// Wire length of an encoded [`FrameHeader`].
pub const HEADER_LEN: usize = 20;

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
    /// Encode to the fixed 20-byte little-endian wire form.
    pub fn to_bytes(self) -> [u8; HEADER_LEN] {
        let mut b = [0u8; HEADER_LEN];
        b[0..4].copy_from_slice(&self.id.to_le_bytes());
        b[4..8].copy_from_slice(&self.len.to_le_bytes());
        b[8..12].copy_from_slice(&self.crc.to_le_bytes());
        b[12..14].copy_from_slice(&self.window.x.to_le_bytes());
        b[14..16].copy_from_slice(&self.window.y.to_le_bytes());
        b[16..18].copy_from_slice(&self.window.w.to_le_bytes());
        b[18..20].copy_from_slice(&self.window.h.to_le_bytes());
        b
    }

    /// Decode from the wire form, or `None` if the buffer is too short.
    pub fn from_bytes(b: &[u8]) -> Option<Self> {
        if b.len() < HEADER_LEN {
            return None;
        }
        let word = |o: usize| u32::from_le_bytes([b[o], b[o + 1], b[o + 2], b[o + 3]]);
        let half = |o: usize| u16::from_le_bytes([b[o], b[o + 1]]);
        Some(FrameHeader {
            id: word(0),
            len: word(4),
            crc: word(8),
            window: Window {
                x: half(12),
                y: half(14),
                w: half(16),
                h: half(18),
            },
        })
    }
}

/// The outcome of offering a chunk to the [`Receiver`].
#[derive(Clone, Copy, PartialEq, Eq, Debug)]
pub enum Accept {
    /// Chunk taken; the value is the new total received so far.
    Progress(u32),
    /// All bytes are in and the CRC matched; the frame is ready to paint.
    Complete,
    /// The chunk did not fit the active transfer. The sender should resume
    /// from [`Receiver::offset`].
    Rejected,
}

/// Tracks one in-flight frame transfer.
pub struct Receiver {
    id: u32,
    len: u32,
    crc: u32,
    received: u32,
    running: Crc32,
    active: bool,
}

impl Receiver {
    /// An idle receiver with no active transfer.
    pub const fn new() -> Self {
        Receiver {
            id: 0,
            len: 0,
            crc: 0,
            received: 0,
            running: Crc32::new(),
            active: false,
        }
    }

    /// Start a transfer. Re-announcing the same frame keeps existing progress,
    /// so a dropped-and-retried header does not restart the download.
    pub fn begin(&mut self, header: FrameHeader) {
        let same =
            self.active && self.id == header.id && self.len == header.len && self.crc == header.crc;
        if same {
            return;
        }
        self.id = header.id;
        self.len = header.len;
        self.crc = header.crc;
        self.received = 0;
        self.running = Crc32::new();
        self.active = true;
    }

    /// Byte offset the next chunk must start at.
    pub fn offset(&self) -> u32 {
        self.received
    }

    /// Whether a transfer is in progress.
    pub fn is_active(&self) -> bool {
        self.active
    }

    /// Offer a chunk that the sender says begins at `at`.
    pub fn accept(&mut self, at: u32, chunk: &[u8]) -> Accept {
        if !self.active || at != self.received {
            return Accept::Rejected;
        }
        let remaining = self.len - self.received;
        if chunk.len() as u32 > remaining {
            return Accept::Rejected;
        }
        self.running.update(chunk);
        self.received += chunk.len() as u32;
        if self.received != self.len {
            return Accept::Progress(self.received);
        }
        let matched = self.running.finalize() == self.crc;
        self.active = false;
        if matched {
            Accept::Complete
        } else {
            Accept::Rejected
        }
    }
}

impl Default for Receiver {
    fn default() -> Self {
        Self::new()
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
        assert!(FrameHeader::from_bytes(&[0u8; 4]).is_none());
    }

    #[test]
    fn streamed_chunks_complete_and_verify() {
        let data = b"the quick brown fox";
        let mut rx = Receiver::new();
        rx.begin(header_for(data, 1));
        assert_eq!(rx.accept(0, &data[0..4]), Accept::Progress(4));
        assert_eq!(rx.offset(), 4);
        assert_eq!(rx.accept(4, &data[4..]), Accept::Complete);
        assert!(!rx.is_active());
    }

    #[test]
    fn out_of_order_chunk_is_rejected_and_offset_holds() {
        let data = b"abcdefgh";
        let mut rx = Receiver::new();
        rx.begin(header_for(data, 1));
        assert_eq!(rx.accept(0, &data[0..4]), Accept::Progress(4));
        // Sender jumps ahead; receiver rejects and keeps its offset for resume.
        assert_eq!(rx.accept(6, &data[6..]), Accept::Rejected);
        assert_eq!(rx.offset(), 4);
        assert_eq!(rx.accept(4, &data[4..]), Accept::Complete);
    }

    #[test]
    fn corrupt_payload_fails_crc() {
        let data = b"abcdefgh";
        let mut header = header_for(data, 1);
        header.crc ^= 0x1; // wrong CRC
        let mut rx = Receiver::new();
        rx.begin(header);
        assert_eq!(rx.accept(0, data), Accept::Rejected);
    }

    #[test]
    fn re_announcing_same_frame_keeps_progress() {
        let data = b"abcdefgh";
        let h = header_for(data, 1);
        let mut rx = Receiver::new();
        rx.begin(h);
        assert_eq!(rx.accept(0, &data[0..4]), Accept::Progress(4));
        rx.begin(h); // dropped connection, sender re-announces
        assert_eq!(rx.offset(), 4);
        assert_eq!(rx.accept(4, &data[4..]), Accept::Complete);
    }

    #[test]
    fn a_new_frame_id_resets_progress() {
        let first = b"abcdefgh";
        let mut rx = Receiver::new();
        rx.begin(header_for(first, 1));
        assert_eq!(rx.accept(0, &first[0..4]), Accept::Progress(4));
        let second = b"zyxw";
        rx.begin(header_for(second, 2));
        assert_eq!(rx.offset(), 0);
        assert_eq!(rx.accept(0, second), Accept::Complete);
    }
}
