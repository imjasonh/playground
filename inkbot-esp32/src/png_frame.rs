//! Decode a packed 1-bit (or strict B/W) PNG into the panel framebuffer.
//!
//! The inkbot Worker always serves a grayscale BitDepth::One PNG. We also
//! accept 8-bit gray / RGB(A) where every pixel is pure black or white so a
//! hand-made PNG still works during bring-up.

use crate::panel::{FRAME_BYTES, PANEL_HEIGHT, PANEL_WIDTH};
use png::{BitDepth, ColorType, Decoder, Transformations};
use std::io::Cursor;

#[derive(Debug, PartialEq, Eq)]
pub enum PngFrameError {
    Decode(String),
    WrongSize { got_w: u32, got_h: u32 },
    UnsupportedColor,
    NotBlackAndWhite,
    BadLength,
}

impl std::fmt::Display for PngFrameError {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self {
            PngFrameError::Decode(m) => write!(f, "png decode failed: {m}"),
            PngFrameError::WrongSize { got_w, got_h } => {
                write!(
                    f,
                    "expected {PANEL_WIDTH}x{PANEL_HEIGHT}, got {got_w}x{got_h}"
                )
            }
            PngFrameError::UnsupportedColor => write!(f, "unsupported png color type"),
            PngFrameError::NotBlackAndWhite => write!(f, "image is not strictly black-and-white"),
            PngFrameError::BadLength => write!(f, "decoded buffer length mismatch"),
        }
    }
}

impl std::error::Error for PngFrameError {}

/// Decode `bytes` into a packed 1-bit framebuffer (MSB first, 1 = white).
pub fn decode_bw_png(bytes: &[u8]) -> Result<Vec<u8>, PngFrameError> {
    let mut decoder = Decoder::new(Cursor::new(bytes));
    // Keep packed 1-bit rows when the source is already BitDepth::One.
    decoder.set_transformations(Transformations::IDENTITY);
    let mut reader = decoder
        .read_info()
        .map_err(|e| PngFrameError::Decode(e.to_string()))?;
    let info = reader.info();
    let width = info.width;
    let height = info.height;
    let color_type = info.color_type;
    let bit_depth = info.bit_depth;
    if width != PANEL_WIDTH || height != PANEL_HEIGHT {
        return Err(PngFrameError::WrongSize {
            got_w: width,
            got_h: height,
        });
    }

    let mut raw = vec![0u8; reader.output_buffer_size()];
    let frame_info = reader
        .next_frame(&mut raw)
        .map_err(|e| PngFrameError::Decode(e.to_string()))?;
    raw.truncate(frame_info.buffer_size());

    match (color_type, bit_depth) {
        (ColorType::Grayscale, BitDepth::One) => {
            if raw.len() != FRAME_BYTES {
                return Err(PngFrameError::BadLength);
            }
            Ok(raw)
        }
        (ColorType::Grayscale, BitDepth::Eight) => pack_gray8(&raw),
        (ColorType::Rgb, BitDepth::Eight) => pack_rgb8(&raw, false),
        (ColorType::Rgba, BitDepth::Eight) => pack_rgb8(&raw, true),
        _ => Err(PngFrameError::UnsupportedColor),
    }
}

fn pack_gray8(raw: &[u8]) -> Result<Vec<u8>, PngFrameError> {
    if raw.len() != (PANEL_WIDTH * PANEL_HEIGHT) as usize {
        return Err(PngFrameError::BadLength);
    }
    let mut out = vec![0u8; FRAME_BYTES];
    for (i, &lum) in raw.iter().enumerate() {
        if lum != 0 && lum != 255 {
            return Err(PngFrameError::NotBlackAndWhite);
        }
        if lum >= 128 {
            out[i / 8] |= 0x80 >> (i % 8);
        }
    }
    Ok(out)
}

fn pack_rgb8(raw: &[u8], alpha: bool) -> Result<Vec<u8>, PngFrameError> {
    let stride = if alpha { 4 } else { 3 };
    let pixels = (PANEL_WIDTH * PANEL_HEIGHT) as usize;
    if raw.len() != pixels * stride {
        return Err(PngFrameError::BadLength);
    }
    let mut out = vec![0u8; FRAME_BYTES];
    for i in 0..pixels {
        let o = i * stride;
        let (r, g, b) = (raw[o], raw[o + 1], raw[o + 2]);
        let a = if alpha { raw[o + 3] } else { 255 };
        if a == 0 {
            out[i / 8] |= 0x80 >> (i % 8); // transparent → white
            continue;
        }
        let is_black = r == 0 && g == 0 && b == 0;
        let is_white = r == 255 && g == 255 && b == 255;
        if !is_black && !is_white {
            return Err(PngFrameError::NotBlackAndWhite);
        }
        if is_white {
            out[i / 8] |= 0x80 >> (i % 8);
        }
    }
    Ok(out)
}

#[cfg(test)]
mod tests {
    use super::*;
    use png::{BitDepth, ColorType, Encoder};
    use std::io::Cursor;

    fn encode_one_bit(packed: &[u8]) -> Vec<u8> {
        assert_eq!(packed.len(), FRAME_BYTES);
        let mut out = Vec::new();
        let mut enc = Encoder::new(Cursor::new(&mut out), PANEL_WIDTH, PANEL_HEIGHT);
        enc.set_color(ColorType::Grayscale);
        enc.set_depth(BitDepth::One);
        let mut writer = enc.write_header().unwrap();
        writer.write_image_data(packed).unwrap();
        drop(writer);
        out
    }

    #[test]
    fn round_trip_one_bit() {
        let mut packed = vec![0u8; FRAME_BYTES];
        // Checkerboard-ish: first row half black / half white.
        for x in 400..800 {
            packed[x / 8] |= 0x80 >> (x % 8);
        }
        let png = encode_one_bit(&packed);
        let decoded = decode_bw_png(&png).unwrap();
        assert_eq!(decoded, packed);
    }

    #[test]
    fn reject_wrong_size() {
        let mut out = Vec::new();
        let mut enc = Encoder::new(Cursor::new(&mut out), 16, 16);
        enc.set_color(ColorType::Grayscale);
        enc.set_depth(BitDepth::Eight);
        let mut writer = enc.write_header().unwrap();
        writer.write_image_data(&[0u8; 16 * 16]).unwrap();
        drop(writer);
        assert!(matches!(
            decode_bw_png(&out),
            Err(PngFrameError::WrongSize { .. })
        ));
    }

    #[test]
    fn pack_gray8_requires_strict_bw() {
        let mut raw = vec![0u8; (PANEL_WIDTH * PANEL_HEIGHT) as usize];
        raw[0] = 128;
        // Build via the private helper through a tiny PNG would need gray8
        // encode — call the helper path via a gray8 PNG.
        let mut out = Vec::new();
        let mut enc = Encoder::new(Cursor::new(&mut out), PANEL_WIDTH, PANEL_HEIGHT);
        enc.set_color(ColorType::Grayscale);
        enc.set_depth(BitDepth::Eight);
        let mut writer = enc.write_header().unwrap();
        writer.write_image_data(&raw).unwrap();
        drop(writer);
        assert_eq!(decode_bw_png(&out), Err(PngFrameError::NotBlackAndWhite));
    }
}
