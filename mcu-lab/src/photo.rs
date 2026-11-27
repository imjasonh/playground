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

/// Incremental white→black frame counts for the 3 stepped [`crate::grayscale::lut::DriveLuts`]
/// passes used to render 4-level grayscale after a factory full-white clear:
///
/// - Pass 0 (`level <= 2`, light gray + dark gray + black): 4 frames (total 4)
/// - Pass 1 (`level <= 1`, dark gray + black):              6 frames (total 10)
/// - Pass 2 (`level == 0`, black only):                    14 frames (total 24)
///
/// Every active pixel in every pass moves in the same polarity (white → black)
/// from a uniform white baseline, avoiding opposite-direction column crosstalk
/// and panel-batch OTP `0x5F` incompatibilities.
pub const GRAY4_STEP_FRAMES: [u8; 3] = [4, 6, 14];

/// Compute one byte of the `DTM2` new-plane mask for stepped 4-gray pass `pass` (`0..3`),
/// given the corresponding `dtm1` and `dtm2` bytes from a [`PhotoMode::Gray4`] frame.
///
/// With `DTM1` (old plane) held at `0xFF` (white) and `DDX[1:0] = 01`, a `0` bit in `DTM2`
/// selects `WK` (push black) and a `1` bit selects `WW` (hold):
/// - Pass 0 (`level <= 2`): `!(dtm1 | dtm2)`
/// - Pass 1 (`level <= 1`): `!dtm2`
/// - Pass 2 (`level == 0`): `!(dtm1 & dtm2)`
pub const fn gray4_step_new_byte(pass: usize, dtm1: u8, dtm2: u8) -> u8 {
    match pass {
        0 => !(dtm1 | dtm2),
        1 => !dtm2,
        2 => !(dtm1 & dtm2),
        _ => 0xFF,
    }
}

/// 4×4 Bayer ordered-dither threshold matrix (`0..16`) for the calibration gradient band.
const BAYER_4X4: [[u8; 4]; 4] = [[0, 8, 2, 10], [12, 4, 14, 6], [3, 11, 1, 9], [15, 7, 13, 5]];

/// Compute the 2-bit gray level (`0 = black, 1 = dark gray, 2 = light gray, 3 = white`)
/// for pixel `(x, y)` of the 800×480 4-gray calibration test pattern:
///
/// - `y = 0..280`: 4 vertical solid bars (White, Light Gray, Dark Gray, Black)
/// - `y = 280..360`: horizontal 4-level Bayer-dithered gradient (White → Black)
/// - `y = 360..480`: 4 full-width horizontal solid bars (White, Light Gray, Dark Gray, Black)
///   to inspect horizontal uniformity and column streaking across all 800 columns.
pub fn calibration_4gray_pixel(x: usize, y: usize) -> u8 {
    let w = PANEL_WIDTH as usize;
    if y < 280 {
        let bar = (x * 4) / w;
        return 3u8.saturating_sub(bar as u8);
    }
    if y < 360 {
        // Map x in 0..800 to 0.0..3.0 darkness (0 = white, 3 = black) with 4×4 Bayer dithering.
        let scaled = (x * 3 * 16) / (w - 1);
        let base = scaled / 16;
        let rem = (scaled % 16) as u8;
        let threshold = BAYER_4X4[y & 3][x & 3];
        let darkness = (base + usize::from(rem > threshold)).min(3);
        return (3 - darkness) as u8;
    }
    let band = ((y - 360) * 4) / (PANEL_HEIGHT as usize - 360);
    3u8.saturating_sub(band as u8)
}

/// Stream bytes of the 96,000-byte 4-gray calibration pattern (`DTM1` at `0..48_000`,
/// `DTM2` at `48_000..96_000`) into `dst` starting at `offset`, without heap allocation.
pub fn fill_calibration_4gray_chunk(offset: usize, dst: &mut [u8]) {
    let row_bytes = PANEL_WIDTH as usize / 8;
    for (i, out) in dst.iter_mut().enumerate() {
        let pos = offset + i;
        if pos >= GRAY4_FRAME_BYTES {
            *out = 0;
            continue;
        }
        let is_dtm2 = pos >= FRAME_BYTES;
        let byte_idx = if is_dtm2 { pos - FRAME_BYTES } else { pos };
        let y = byte_idx / row_bytes;
        let x0 = (byte_idx % row_bytes) * 8;
        let mut acc = 0u8;
        for bit in 0..8 {
            let lvl = calibration_4gray_pixel(x0 + bit, y) & 0x03;
            let bit_val = if is_dtm2 {
                u8::from(lvl == 0 || lvl == 1)
            } else {
                u8::from(lvl == 0 || lvl == 2)
            };
            acc |= bit_val << (7 - bit);
        }
        *out = acc;
    }
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

    #[test]
    fn gray4_step_passes_deliver_monotonic_cumulative_frames() {
        let mut levels = vec![3u8; (PANEL_WIDTH as usize) * (PANEL_HEIGHT as usize)];
        levels[0..8].copy_from_slice(&[0, 1, 2, 3, 3, 2, 1, 0]);
        let (dtm1, dtm2) = pack_4gray_planes(&levels).expect("pack 4-gray");

        let mut cumulative = [0u16; 8];
        for (pass, &frames) in GRAY4_STEP_FRAMES.iter().enumerate() {
            let new_byte = gray4_step_new_byte(pass, dtm1[0], dtm2[0]);
            for (bit, total) in cumulative.iter_mut().enumerate() {
                // DTM1 is 1 (white); a 0 bit in DTM2 selects WK (push black).
                if (new_byte & (1 << (7 - bit))) == 0 {
                    *total += u16::from(frames);
                }
            }
        }
        let expected_black = u16::from(GRAY4_STEP_FRAMES[0])
            + u16::from(GRAY4_STEP_FRAMES[1])
            + u16::from(GRAY4_STEP_FRAMES[2]);
        let expected_dark = u16::from(GRAY4_STEP_FRAMES[0]) + u16::from(GRAY4_STEP_FRAMES[1]);
        let expected_light = u16::from(GRAY4_STEP_FRAMES[0]);
        assert_eq!(
            cumulative,
            [
                expected_black,
                expected_dark,
                expected_light,
                0,
                0,
                expected_light,
                expected_dark,
                expected_black,
            ]
        );
    }

    #[test]
    fn calibration_4gray_chunk_matches_pack_4gray_planes() {
        let w = PANEL_WIDTH as usize;
        let h = PANEL_HEIGHT as usize;
        let mut levels = vec![0u8; w * h];
        for y in 0..h {
            for x in 0..w {
                levels[y * w + x] = calibration_4gray_pixel(x, y);
            }
        }
        // Verify the 4 vertical bars span white -> black left-to-right.
        assert_eq!(calibration_4gray_pixel(50, 100), 3);
        assert_eq!(calibration_4gray_pixel(250, 100), 2);
        assert_eq!(calibration_4gray_pixel(450, 100), 1);
        assert_eq!(calibration_4gray_pixel(650, 100), 0);
        // Verify the 4 horizontal bars span white -> black top-to-bottom.
        assert_eq!(calibration_4gray_pixel(400, 370), 3);
        assert_eq!(calibration_4gray_pixel(400, 400), 2);
        assert_eq!(calibration_4gray_pixel(400, 430), 1);
        assert_eq!(calibration_4gray_pixel(400, 460), 0);

        let (dtm1, dtm2) = pack_4gray_planes(&levels).expect("pack calibration");
        let mut expected = Vec::with_capacity(GRAY4_FRAME_BYTES);
        expected.extend_from_slice(&dtm1);
        expected.extend_from_slice(&dtm2);

        let mut streamed = vec![0u8; GRAY4_FRAME_BYTES];
        for (idx, chunk) in streamed.chunks_mut(1024).enumerate() {
            fill_calibration_4gray_chunk(idx * 1024, chunk);
        }
        assert_eq!(streamed, expected);
    }
}
