//! Host-testable photo album wire format, 4-gray bitplane packing, and empty-state
//! placeholder renderer for the Waveshare 7.5″ 800×480 photo frame app.
//!
//! Albums are stored in the inactive OTA flash partition (`esp_ota_get_next_update_partition`)
//! with a 20-byte `MCUP` header followed by `count` fixed-size raw display frames:
//!
//! | Offset | Size | Field           | Description |
//! |--------|------|-----------------|-------------|
//! | `0..4` | 4    | `magic`         | `b"MCUP"` (distinct from ESP-IDF `0xE9` image magic) |
//! | `4`    | 1    | `version`       | Format version (`1`) |
//! | `5`    | 1    | `mode`          | `0` = 1-bit B&W (48,000 B/frame), `1` = 4-gray 2-plane (96,000 B/frame) |
//! | `6..8` | 2    | `count`         | Number of photos (`u16` LE, `>= 1`) |
//! | `8..12`| 4    | `interval_secs` | Auto-rotation interval in seconds (`u32` LE; `0` = manual only) |
//! | `12..16`| 4   | `payload_crc32` | IEEE CRC32 over all frame bytes |
//! | `16..20`| 4   | `header_crc32`  | IEEE CRC32 over header bytes `0..16` |
//!
//! For `PhotoMode::Gray4`, each 96,000-byte frame consists of two contiguous
//! 48,000-byte bitplanes matching the UC8179 `display_4Gray` polarity:
//! - Plane 0 (`DTM1`, `0x10`): 48,000 bytes (MSB-first, 8 pixels per byte)
//! - Plane 1 (`DTM2`, `0x13`): 48,000 bytes (MSB-first, 8 pixels per byte)
//!
//! Pixel level mapping (`0 = black, 1 = dark gray, 2 = light gray, 3 = white`):
//! - `0` (Black):      `DTM1 = 1, DTM2 = 1`
//! - `1` (Dark Gray):  `DTM1 = 0, DTM2 = 1`
//! - `2` (Light Gray): `DTM1 = 1, DTM2 = 0`
//! - `3` (White):      `DTM1 = 0, DTM2 = 0`

use crate::panel::{FRAME_BYTES, PANEL_HEIGHT, PANEL_WIDTH};
use crate::protocol::{crc32, OTA_SLOT_BYTES};

/// On-wire / log identifier for the Waveshare 7.5″ photo frame app.
pub const PHOTO_FIRMWARE_ID: &str = "waveshare-epd75-photo/0.1";

/// 4-byte magic prefix for a photo album blob in flash (distinct from ESP `0xE9`).
pub const PHOTO_ALBUM_MAGIC: [u8; 4] = *b"MCUP";

/// Current photo album binary format version.
pub const PHOTO_ALBUM_VERSION: u8 = 1;

/// Fixed byte length of the serialized [`PhotoAlbumHeader`].
pub const PHOTO_HEADER_LEN: usize = 20;

/// Default slideshow rotation interval (10 minutes).
pub const DEFAULT_ROTATE_INTERVAL_SECS: u32 = 600;

/// Bytes per 4-gray (2-bit, two-plane) 800×480 frame.
pub const GRAY4_FRAME_BYTES: usize = FRAME_BYTES * 2;

/// Maximum number of 1-bit B&W photos that fit in one OTA slot.
pub const MAX_BW_PHOTOS: u16 = ((OTA_SLOT_BYTES as usize - PHOTO_HEADER_LEN) / FRAME_BYTES) as u16;

/// Maximum number of 4-gray photos that fit in one OTA slot.
pub const MAX_GRAY4_PHOTOS: u16 =
    ((OTA_SLOT_BYTES as usize - PHOTO_HEADER_LEN) / GRAY4_FRAME_BYTES) as u16;

/// Display pixel format for all frames in a [`PhotoAlbumHeader`].
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
#[repr(u8)]
pub enum PhotoMode {
    /// Packed 1-bit B&W framebuffer (48,000 bytes/frame, MSB-first, 1 = white).
    Bw1Bit = 0,
    /// Two-plane 4-level grayscale framebuffer (96,000 bytes/frame: DTM1 + DTM2).
    Gray4 = 1,
}

impl PhotoMode {
    pub fn from_byte(b: u8) -> Option<Self> {
        match b {
            0 => Some(Self::Bw1Bit),
            1 => Some(Self::Gray4),
            _ => None,
        }
    }

    pub const fn frame_bytes(self) -> usize {
        match self {
            Self::Bw1Bit => FRAME_BYTES,
            Self::Gray4 => GRAY4_FRAME_BYTES,
        }
    }

    pub const fn max_photos(self) -> u16 {
        match self {
            Self::Bw1Bit => MAX_BW_PHOTOS,
            Self::Gray4 => MAX_GRAY4_PHOTOS,
        }
    }

    pub const fn as_str(self) -> &'static str {
        match self {
            Self::Bw1Bit => "bw1",
            Self::Gray4 => "gray4",
        }
    }
}

/// 20-byte header stored at offset 0 of the inactive OTA partition.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub struct PhotoAlbumHeader {
    pub mode: PhotoMode,
    pub count: u16,
    pub interval_secs: u32,
    pub payload_crc32: u32,
}

impl PhotoAlbumHeader {
    /// Serialize the header with its trailing IEEE CRC32 over bytes `0..16`.
    pub fn encode(&self) -> [u8; PHOTO_HEADER_LEN] {
        let mut out = [0u8; PHOTO_HEADER_LEN];
        out[0..4].copy_from_slice(&PHOTO_ALBUM_MAGIC);
        out[4] = PHOTO_ALBUM_VERSION;
        out[5] = self.mode as u8;
        out[6..8].copy_from_slice(&self.count.to_le_bytes());
        out[8..12].copy_from_slice(&self.interval_secs.to_le_bytes());
        out[12..16].copy_from_slice(&self.payload_crc32.to_le_bytes());
        let hdr_crc = crc32(&out[0..16]);
        out[16..20].copy_from_slice(&hdr_crc.to_le_bytes());
        out
    }

    /// Parse and validate a 20-byte [`PhotoAlbumHeader`].
    pub fn parse(bytes: &[u8]) -> Result<Self, String> {
        if bytes.len() < PHOTO_HEADER_LEN {
            return Err(format!(
                "photo header too short: {} < {PHOTO_HEADER_LEN}",
                bytes.len()
            ));
        }
        if bytes[0..4] != PHOTO_ALBUM_MAGIC {
            return Err("invalid photo album magic".to_string());
        }
        let version = bytes[4];
        if version != PHOTO_ALBUM_VERSION {
            return Err(format!("unsupported photo album version {version}"));
        }
        let expected_hdr_crc = u32::from_le_bytes([bytes[16], bytes[17], bytes[18], bytes[19]]);
        let actual_hdr_crc = crc32(&bytes[0..16]);
        if actual_hdr_crc != expected_hdr_crc {
            return Err(format!(
                "photo header crc32 mismatch: got {actual_hdr_crc:#010x}, want {expected_hdr_crc:#010x}"
            ));
        }
        let mode = PhotoMode::from_byte(bytes[5])
            .ok_or_else(|| format!("unknown photo mode {}", bytes[5]))?;
        let count = u16::from_le_bytes([bytes[6], bytes[7]]);
        if count == 0 || count > mode.max_photos() {
            return Err(format!(
                "photo count {count} out of range 1..={}",
                mode.max_photos()
            ));
        }
        let interval_secs = u32::from_le_bytes([bytes[8], bytes[9], bytes[10], bytes[11]]);
        let payload_crc32 = u32::from_le_bytes([bytes[12], bytes[13], bytes[14], bytes[15]]);
        let header = Self {
            mode,
            count,
            interval_secs,
            payload_crc32,
        };
        if header.total_bytes() > OTA_SLOT_BYTES as usize {
            return Err(format!(
                "photo album {}B exceeds OTA slot {}B",
                header.total_bytes(),
                OTA_SLOT_BYTES
            ));
        }
        Ok(header)
    }

    /// Total payload bytes across all frames (excluding the 20-byte header).
    pub const fn payload_bytes(&self) -> usize {
        self.count as usize * self.mode.frame_bytes()
    }

    /// Total serialized album size in bytes (header + payload).
    pub const fn total_bytes(&self) -> usize {
        PHOTO_HEADER_LEN + self.payload_bytes()
    }

    /// Byte offset from start of the album to frame `index`.
    pub fn frame_offset(&self, index: u16) -> Option<usize> {
        if index >= self.count {
            return None;
        }
        Some(PHOTO_HEADER_LEN + index as usize * self.mode.frame_bytes())
    }
}

/// Validate the first 4 bytes of an incoming `BEGIN_DATA` transfer before writing flash.
pub fn validate_photo_album_magic(prefix: &[u8]) -> Result<(), String> {
    if prefix.is_empty() {
        return Err("empty data blob".to_string());
    }
    let check_len = prefix.len().min(PHOTO_ALBUM_MAGIC.len());
    if prefix[..check_len] != PHOTO_ALBUM_MAGIC[..check_len] {
        return Err(format!(
            "invalid data blob magic: expected MCUP, got {:02x?}",
            &prefix[..check_len]
        ));
    }
    Ok(())
}

/// Encode a complete `MCUP` photo album blob from pre-packed frame slices.
pub fn encode_photo_album(
    mode: PhotoMode,
    interval_secs: u32,
    frames: &[&[u8]],
) -> Result<Vec<u8>, String> {
    let count = u16::try_from(frames.len()).map_err(|_| "too many photos".to_string())?;
    if count == 0 || count > mode.max_photos() {
        return Err(format!(
            "photo count {count} out of range 1..={}",
            mode.max_photos()
        ));
    }
    let expected_frame_len = mode.frame_bytes();
    let mut payload = Vec::with_capacity(count as usize * expected_frame_len);
    for (i, frame) in frames.iter().enumerate() {
        if frame.len() != expected_frame_len {
            return Err(format!(
                "frame {i} length {} != expected {expected_frame_len}",
                frame.len()
            ));
        }
        payload.extend_from_slice(frame);
    }
    let header = PhotoAlbumHeader {
        mode,
        count,
        interval_secs,
        payload_crc32: crc32(&payload),
    };
    let mut out = Vec::with_capacity(PHOTO_HEADER_LEN + payload.len());
    out.extend_from_slice(&header.encode());
    out.extend_from_slice(&payload);
    Ok(out)
}

/// Streaming IEEE CRC32 state (bitwise-identical to [`crate::protocol::crc32`])
/// so firmware can verify a multi-hundred-KiB album in flash using a 4 KiB buffer.
#[derive(Clone, Copy, Debug)]
pub struct Crc32Hasher {
    state: u32,
}

impl Crc32Hasher {
    pub const fn new() -> Self {
        Self { state: 0xFFFF_FFFF }
    }

    pub fn update(&mut self, bytes: &[u8]) {
        for &b in bytes {
            self.state ^= u32::from(b);
            for _ in 0..8 {
                let mask = (self.state & 1).wrapping_neg();
                self.state = (self.state >> 1) ^ (0xEDB8_8320 & mask);
            }
        }
    }

    pub const fn finalize(self) -> u32 {
        !self.state
    }
}

impl Default for Crc32Hasher {
    fn default() -> Self {
        Self::new()
    }
}

/// Pack 800×480 2-bit gray levels (`0 = black, 1 = dark gray, 2 = light gray, 3 = white`)
/// into the `(dtm1, dtm2)` 48,000-byte UC8179 bitplanes.
pub fn pack_4gray_planes(levels: &[u8]) -> Result<(Vec<u8>, Vec<u8>), String> {
    let expected_pixels = (PANEL_WIDTH as usize) * (PANEL_HEIGHT as usize);
    if levels.len() != expected_pixels {
        return Err(format!(
            "expected {expected_pixels} pixels, got {}",
            levels.len()
        ));
    }
    let mut dtm1 = vec![0u8; FRAME_BYTES];
    let mut dtm2 = vec![0u8; FRAME_BYTES];
    for byte_idx in 0..FRAME_BYTES {
        let base = byte_idx * 8;
        let mut b1 = 0u8;
        let mut b2 = 0u8;
        for bit in 0..8 {
            let lvl = levels[base + bit];
            let shift = 7 - bit;
            // Waveshare UC8179 4-gray polarity:
            // 0 (black)      -> DTM1=1, DTM2=1
            // 1 (dark gray)  -> DTM1=0, DTM2=1
            // 2 (light gray) -> DTM1=1, DTM2=0
            // 3 (white)      -> DTM1=0, DTM2=0
            let (p1, p2) = match lvl & 0x03 {
                0 => (1u8, 1u8),
                1 => (0u8, 1u8),
                2 => (1u8, 0u8),
                _ => (0u8, 0u8),
            };
            b1 |= p1 << shift;
            b2 |= p2 << shift;
        }
        dtm1[byte_idx] = b1;
        dtm2[byte_idx] = b2;
    }
    Ok((dtm1, dtm2))
}

/// Render a clean 1-bit B&W placeholder frame (48,000 bytes, 1 = white) shown on
/// freshly flashed boards before any photos have been uploaded from iOS.
pub fn render_empty_placeholder() -> Vec<u8> {
    let mut frame = vec![0xFFu8; FRAME_BYTES];
    let w = PANEL_WIDTH as usize;
    let h = PANEL_HEIGHT as usize;

    // Outer gallery frame border (double hairline).
    draw_rect(&mut frame, 24, 24, w - 48, h - 48, 4);
    draw_rect(&mut frame, 38, 38, w - 76, h - 76, 2);

    // Simple centered camera/frame icon above the title.
    let icon_w = 120;
    let icon_h = 84;
    let icon_x = (w - icon_w) / 2;
    let icon_y = 126;
    draw_rect(&mut frame, icon_x, icon_y, icon_w, icon_h, 4);
    // Sun circle (small filled square) + mountain peaks inside the frame icon.
    fill_rect(&mut frame, icon_x + 22, icon_y + 18, 14, 14);
    for i in 0..34 {
        let y = icon_y + icon_h - 8 - i;
        let left = icon_x + 14 + i;
        let right = icon_x + 82 - i;
        if left <= right {
            for x in left..=right {
                set_black(&mut frame, x, y);
            }
        }
    }
    for i in 0..24 {
        let y = icon_y + icon_h - 8 - i;
        let left = icon_x + 58 + i;
        let right = icon_x + 106 - i;
        if left <= right {
            for x in left..=right {
                set_black(&mut frame, x, y);
            }
        }
    }

    draw_centered_text(&mut frame, 248, "MCU LAB PHOTO FRAME", 4);
    draw_centered_text(&mut frame, 300, "SEND PHOTOS FROM PLAYGROUND IOS", 2);
    draw_centered_text(&mut frame, 336, "WAVESHARE 7.5 INCH 800X480", 2);

    frame
}

fn set_black(frame: &mut [u8], x: usize, y: usize) {
    if x >= PANEL_WIDTH as usize || y >= PANEL_HEIGHT as usize {
        return;
    }
    let idx = y * (PANEL_WIDTH as usize / 8) + (x / 8);
    let mask = 1u8 << (7 - (x & 7));
    frame[idx] &= !mask;
}

fn fill_rect(frame: &mut [u8], x: usize, y: usize, w: usize, h: usize) {
    for yy in y..y.saturating_add(h) {
        for xx in x..x.saturating_add(w) {
            set_black(frame, xx, yy);
        }
    }
}

fn draw_rect(frame: &mut [u8], x: usize, y: usize, w: usize, h: usize, thickness: usize) {
    fill_rect(frame, x, y, w, thickness);
    fill_rect(frame, x, y + h.saturating_sub(thickness), w, thickness);
    fill_rect(frame, x, y, thickness, h);
    fill_rect(frame, x + w.saturating_sub(thickness), y, thickness, h);
}

fn draw_centered_text(frame: &mut [u8], y: usize, text: &str, scale: usize) {
    let glyph_w = 5 * scale;
    let advance = 6 * scale;
    let total_w = if text.is_empty() {
        0
    } else {
        text.len() * advance - scale
    };
    let start_x = (PANEL_WIDTH as usize).saturating_sub(total_w) / 2;
    for (idx, ch) in text.chars().enumerate() {
        let gx = start_x + idx * advance;
        if gx + glyph_w > PANEL_WIDTH as usize {
            break;
        }
        let rows = glyph_5x7(ch);
        for (ry, &bits) in rows.iter().enumerate() {
            for rx in 0..5 {
                if (bits & (1 << (4 - rx))) != 0 {
                    fill_rect(frame, gx + rx * scale, y + ry * scale, scale, scale);
                }
            }
        }
    }
}

/// Minimal 5×7 uppercase bitmap font for the empty-state placeholder screen.
fn glyph_5x7(ch: char) -> [u8; 7] {
    match ch.to_ascii_uppercase() {
        'A' => [0x0E, 0x11, 0x11, 0x1F, 0x11, 0x11, 0x11],
        'B' => [0x1E, 0x11, 0x11, 0x1E, 0x11, 0x11, 0x1E],
        'C' => [0x0E, 0x11, 0x10, 0x10, 0x10, 0x11, 0x0E],
        'D' => [0x1C, 0x12, 0x11, 0x11, 0x11, 0x12, 0x1C],
        'E' => [0x1F, 0x10, 0x10, 0x1E, 0x10, 0x10, 0x1F],
        'F' => [0x1F, 0x10, 0x10, 0x1E, 0x10, 0x10, 0x10],
        'G' => [0x0E, 0x11, 0x10, 0x17, 0x11, 0x11, 0x0F],
        'H' => [0x11, 0x11, 0x11, 0x1F, 0x11, 0x11, 0x11],
        'I' => [0x0E, 0x04, 0x04, 0x04, 0x04, 0x04, 0x0E],
        'L' => [0x10, 0x10, 0x10, 0x10, 0x10, 0x10, 0x1F],
        'M' => [0x11, 0x1B, 0x15, 0x15, 0x11, 0x11, 0x11],
        'N' => [0x11, 0x19, 0x15, 0x13, 0x11, 0x11, 0x11],
        'O' => [0x0E, 0x11, 0x11, 0x11, 0x11, 0x11, 0x0E],
        'P' => [0x1E, 0x11, 0x11, 0x1E, 0x10, 0x10, 0x10],
        'R' => [0x1E, 0x11, 0x11, 0x1E, 0x14, 0x12, 0x11],
        'S' => [0x0F, 0x10, 0x10, 0x0E, 0x01, 0x01, 0x1E],
        'T' => [0x1F, 0x04, 0x04, 0x04, 0x04, 0x04, 0x04],
        'U' => [0x11, 0x11, 0x11, 0x11, 0x11, 0x11, 0x0E],
        'V' => [0x11, 0x11, 0x11, 0x11, 0x11, 0x0A, 0x04],
        'W' => [0x11, 0x11, 0x11, 0x15, 0x15, 0x1B, 0x11],
        'X' => [0x11, 0x11, 0x0A, 0x04, 0x0A, 0x11, 0x11],
        'Y' => [0x11, 0x11, 0x0A, 0x04, 0x04, 0x04, 0x04],
        '0' => [0x0E, 0x11, 0x13, 0x15, 0x19, 0x11, 0x0E],
        '4' => [0x02, 0x06, 0x0A, 0x12, 0x1F, 0x02, 0x02],
        '5' => [0x1F, 0x10, 0x1E, 0x01, 0x01, 0x11, 0x0E],
        '7' => [0x1F, 0x01, 0x02, 0x04, 0x08, 0x08, 0x08],
        '8' => [0x0E, 0x11, 0x11, 0x0E, 0x11, 0x11, 0x0E],
        '.' => [0x00, 0x00, 0x00, 0x00, 0x00, 0x0C, 0x0C],
        _ => [0x00; 7],
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn album_header_round_trips_and_validates_crc() {
        let hdr = PhotoAlbumHeader {
            mode: PhotoMode::Gray4,
            count: 3,
            interval_secs: DEFAULT_ROTATE_INTERVAL_SECS,
            payload_crc32: 0xDEAD_BEEF,
        };
        let mut encoded = hdr.encode();
        let decoded = PhotoAlbumHeader::parse(&encoded).expect("valid header");
        assert_eq!(decoded, hdr);
        assert_eq!(decoded.frame_offset(0), Some(PHOTO_HEADER_LEN));
        assert_eq!(
            decoded.frame_offset(2),
            Some(PHOTO_HEADER_LEN + 2 * GRAY4_FRAME_BYTES)
        );
        assert_eq!(decoded.frame_offset(3), None);

        // Corrupt a byte and verify CRC rejection.
        encoded[8] ^= 0x01;
        assert!(PhotoAlbumHeader::parse(&encoded).is_err());
    }

    #[test]
    fn encode_photo_album_rejects_bad_counts_and_matches_streaming_crc() {
        let frame0 = vec![0xAAu8; FRAME_BYTES];
        let frame1 = vec![0x55u8; FRAME_BYTES];
        let blob = encode_photo_album(PhotoMode::Bw1Bit, 600, &[&frame0, &frame1])
            .expect("encode 2 bw frames");
        assert_eq!(blob.len(), PHOTO_HEADER_LEN + 2 * FRAME_BYTES);
        assert!(validate_photo_album_magic(&blob[..4]).is_ok());
        assert!(validate_photo_album_magic(&[0xE9, 0x00, 0x00, 0x00]).is_err());

        let hdr = PhotoAlbumHeader::parse(&blob).expect("parse header");
        assert_eq!(hdr.mode, PhotoMode::Bw1Bit);
        assert_eq!(hdr.count, 2);
        assert_eq!(hdr.interval_secs, 600);

        let mut hasher = Crc32Hasher::new();
        for chunk in blob[PHOTO_HEADER_LEN..].chunks(4096) {
            hasher.update(chunk);
        }
        assert_eq!(hasher.finalize(), hdr.payload_crc32);

        // Empty album rejected.
        assert!(encode_photo_album(PhotoMode::Bw1Bit, 600, &[]).is_err());
        // Wrong frame length rejected.
        assert!(encode_photo_album(PhotoMode::Gray4, 600, &[&frame0]).is_err());
    }

    #[test]
    fn pack_4gray_planes_matches_uc8179_polarity() {
        let mut levels = vec![3u8; (PANEL_WIDTH as usize) * (PANEL_HEIGHT as usize)];
        // First 8 pixels: [0, 1, 2, 3, 0, 1, 2, 3]
        // Expected DTM1 bits: 1, 0, 1, 0, 1, 0, 1, 0 = 0xAA
        // Expected DTM2 bits: 1, 1, 0, 0, 1, 1, 0, 0 = 0xCC
        levels[0..8].copy_from_slice(&[0, 1, 2, 3, 0, 1, 2, 3]);
        let (dtm1, dtm2) = pack_4gray_planes(&levels).expect("pack 4-gray");
        assert_eq!(dtm1.len(), FRAME_BYTES);
        assert_eq!(dtm2.len(), FRAME_BYTES);
        assert_eq!(dtm1[0], 0xAA);
        assert_eq!(dtm2[0], 0xCC);
        // Remaining pixels are all white (level 3 -> DTM1=0, DTM2=0).
        assert_eq!(dtm1[1], 0x00);
        assert_eq!(dtm2[1], 0x00);
    }

    #[test]
    fn empty_placeholder_is_full_panel_with_visible_ink() {
        let frame = render_empty_placeholder();
        assert_eq!(frame.len(), FRAME_BYTES);
        let black_bytes = frame.iter().filter(|&&b| b != 0xFF).count();
        assert!(
            black_bytes > 500,
            "placeholder should draw visible border and text"
        );
    }
}
