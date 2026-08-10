//! Panel image validation and Slack→e-ink transforms.
//!
//! The Waveshare 7.5″ V2 monochrome panel is 800×480. Direct uploads must
//! already be that size and strictly black-and-white. Slack attachments are
//! cover-cropped, Floyd–Steinberg dithered to 1-bit, and re-encoded as a
//! compact packed PNG plus a raw framebuffer the ESP32 can display.

use image::imageops::{self, FilterType};
use image::{DynamicImage, GenericImageView, GrayImage, Luma, RgbaImage};
use sha2::{Digest, Sha256};
use std::io::Cursor;

/// Default Waveshare 7.5″ V2 resolution.
pub const DEFAULT_WIDTH: u32 = 800;
pub const DEFAULT_HEIGHT: u32 = 480;

/// Target panel geometry.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub struct PanelSpec {
    pub width: u32,
    pub height: u32,
}

impl Default for PanelSpec {
    fn default() -> Self {
        Self {
            width: DEFAULT_WIDTH,
            height: DEFAULT_HEIGHT,
        }
    }
}

impl PanelSpec {
    pub fn new(width: u32, height: u32) -> Result<Self, PanelError> {
        if width == 0 || height == 0 || width % 8 != 0 {
            return Err(PanelError::BadSpec);
        }
        Ok(Self { width, height })
    }

    pub fn frame_bytes(self) -> usize {
        (self.width as usize / 8) * self.height as usize
    }
}

#[derive(Debug, PartialEq, Eq)]
pub enum PanelError {
    BadSpec,
    Decode(String),
    WrongSize { got_w: u32, got_h: u32 },
    NotBlackAndWhite,
    Encode(String),
}

impl std::fmt::Display for PanelError {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self {
            PanelError::BadSpec => write!(f, "invalid panel spec"),
            PanelError::Decode(m) => write!(f, "image decode failed: {m}"),
            PanelError::WrongSize { got_w, got_h } => {
                write!(f, "image must be panel-sized; got {got_w}x{got_h}")
            }
            PanelError::NotBlackAndWhite => {
                write!(f, "image must be strictly black-and-white")
            }
            PanelError::Encode(m) => write!(f, "png encode failed: {m}"),
        }
    }
}

impl std::error::Error for PanelError {}

/// Validated panel image: browser-friendly PNG plus the packed 1-bit
/// framebuffer the ESP32 can display without a zlib inflate.
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct PanelImage {
    pub png: Vec<u8>,
    /// `width/8 * height` bytes, MSB-first, 1 = white.
    pub packed: Vec<u8>,
    pub etag: String,
}

impl PanelImage {
    pub fn from_encoded(png: Vec<u8>, packed: Vec<u8>) -> Self {
        let etag = etag_for(&png);
        Self { png, packed, etag }
    }
}

pub fn etag_for(bytes: &[u8]) -> String {
    let digest = Sha256::digest(bytes);
    format!("\"{}\"", hex::encode(digest))
}

/// Accept a direct upload: decode, require exact panel size + B/W, re-encode
/// as a packed 1-bit PNG (so clients always see a canonical form).
pub fn accept_upload(bytes: &[u8], spec: PanelSpec) -> Result<PanelImage, PanelError> {
    let img = image::load_from_memory(bytes).map_err(|e| PanelError::Decode(e.to_string()))?;
    let (w, h) = img.dimensions();
    if w != spec.width || h != spec.height {
        return Err(PanelError::WrongSize { got_w: w, got_h: h });
    }
    let gray = to_strict_bw_gray(&img)?;
    let (png, packed) = encode_bw_png(&gray, spec)?;
    Ok(PanelImage::from_encoded(png, packed))
}

/// Transform an arbitrary photo (from Slack) into a panel-ready B/W PNG:
/// cover-crop to the panel aspect ratio, resize, Floyd–Steinberg dither.
pub fn transform_for_panel(bytes: &[u8], spec: PanelSpec) -> Result<PanelImage, PanelError> {
    let img = image::load_from_memory(bytes).map_err(|e| PanelError::Decode(e.to_string()))?;
    let fitted = cover_crop_resize(&img, spec);
    let dithered = floyd_steinberg_bw(&fitted);
    let (png, packed) = encode_bw_png(&dithered, spec)?;
    Ok(PanelImage::from_encoded(png, packed))
}

/// Cover-crop then resize so the full panel is filled with no letterboxing.
pub fn cover_crop_resize(img: &DynamicImage, spec: PanelSpec) -> GrayImage {
    let (src_w, src_h) = img.dimensions();
    let src_w = src_w.max(1) as f64;
    let src_h = src_h.max(1) as f64;
    let target_w = spec.width as f64;
    let target_h = spec.height as f64;

    let scale = (target_w / src_w).max(target_h / src_h);
    let scaled_w = (src_w * scale).round().max(1.0) as u32;
    let scaled_h = (src_h * scale).round().max(1.0) as u32;

    let rgba: RgbaImage = img
        .resize_exact(scaled_w, scaled_h, FilterType::Triangle)
        .to_rgba8();

    let x0 = scaled_w.saturating_sub(spec.width) / 2;
    let y0 = scaled_h.saturating_sub(spec.height) / 2;
    let cropped = imageops::crop_imm(&rgba, x0, y0, spec.width, spec.height).to_image();
    DynamicImage::ImageRgba8(cropped).to_luma8()
}

/// Floyd–Steinberg error diffusion to pure black/white.
pub fn floyd_steinberg_bw(gray: &GrayImage) -> GrayImage {
    let w = gray.width() as usize;
    let h = gray.height() as usize;
    let mut buf: Vec<f32> = gray.pixels().map(|p| f32::from(p.0[0])).collect();
    let mut out = GrayImage::new(gray.width(), gray.height());

    for y in 0..h {
        for x in 0..w {
            let i = y * w + x;
            let old = buf[i].clamp(0.0, 255.0);
            let new = if old >= 128.0 { 255.0 } else { 0.0 };
            let err = old - new;
            out.put_pixel(x as u32, y as u32, Luma([new as u8]));

            if x + 1 < w {
                buf[i + 1] += err * 7.0 / 16.0;
            }
            if y + 1 < h {
                if x > 0 {
                    buf[i + w - 1] += err * 3.0 / 16.0;
                }
                buf[i + w] += err * 5.0 / 16.0;
                if x + 1 < w {
                    buf[i + w + 1] += err * 1.0 / 16.0;
                }
            }
        }
    }
    out
}

fn to_strict_bw_gray(img: &DynamicImage) -> Result<GrayImage, PanelError> {
    let rgba = img.to_rgba8();
    let mut gray = GrayImage::new(rgba.width(), rgba.height());
    for (x, y, px) in rgba.enumerate_pixels() {
        let [r, g, b, a] = px.0;
        // Treat fully transparent as white (paper).
        if a == 0 {
            gray.put_pixel(x, y, Luma([255]));
            continue;
        }
        let is_black = r == 0 && g == 0 && b == 0;
        let is_white = r == 255 && g == 255 && b == 255;
        if !is_black && !is_white {
            return Err(PanelError::NotBlackAndWhite);
        }
        gray.put_pixel(x, y, Luma([if is_black { 0 } else { 255 }]));
    }
    Ok(gray)
}

/// Encode a B/W gray image as a packed 1-bit PNG (0 = black, 1 = white).
///
/// Returns `(png_bytes, packed_framebuffer)`.
pub fn encode_bw_png(gray: &GrayImage, spec: PanelSpec) -> Result<(Vec<u8>, Vec<u8>), PanelError> {
    if gray.width() != spec.width || gray.height() != spec.height {
        return Err(PanelError::WrongSize {
            got_w: gray.width(),
            got_h: gray.height(),
        });
    }
    let row_bytes = (spec.width as usize).div_ceil(8);
    let mut packed = vec![0u8; row_bytes * spec.height as usize];
    for y in 0..spec.height {
        for x in 0..spec.width {
            let lum = gray.get_pixel(x, y).0[0];
            if lum >= 128 {
                let i = y as usize * row_bytes + (x as usize / 8);
                packed[i] |= 0x80 >> (x % 8);
            }
        }
    }

    let mut out = Vec::new();
    {
        let mut encoder = png::Encoder::new(Cursor::new(&mut out), spec.width, spec.height);
        encoder.set_color(png::ColorType::Grayscale);
        encoder.set_depth(png::BitDepth::One);
        encoder.set_compression(png::Compression::Default);
        let mut writer = encoder
            .write_header()
            .map_err(|e| PanelError::Encode(e.to_string()))?;
        writer
            .write_image_data(&packed)
            .map_err(|e| PanelError::Encode(e.to_string()))?;
    }
    Ok((out, packed))
}

/// Recover the packed framebuffer from a canonical 1-bit panel PNG (used when
/// loading legacy R2 objects that only stored the PNG).
pub fn packed_from_panel_png(png: &[u8], spec: PanelSpec) -> Result<Vec<u8>, PanelError> {
    let img = image::load_from_memory(png).map_err(|e| PanelError::Decode(e.to_string()))?;
    let (w, h) = img.dimensions();
    if w != spec.width || h != spec.height {
        return Err(PanelError::WrongSize { got_w: w, got_h: h });
    }
    let gray = to_strict_bw_gray(&img)?;
    let (_png, packed) = encode_bw_png(&gray, spec)?;
    Ok(packed)
}

#[cfg(test)]
mod tests {
    use super::*;
    use image::RgbImage;

    fn solid_bw_png(w: u32, h: u32, black: bool) -> Vec<u8> {
        let lum = if black { 0 } else { 255 };
        let img = GrayImage::from_pixel(w, h, Luma([lum]));
        encode_bw_png(&img, PanelSpec::new(w, h).unwrap())
            .unwrap()
            .0
    }

    #[test]
    fn accept_upload_round_trips_panel_png() {
        let spec = PanelSpec::default();
        let png = solid_bw_png(spec.width, spec.height, false);
        let accepted = accept_upload(&png, spec).unwrap();
        assert!(accepted.png.starts_with(&[0x89, b'P', b'N', b'G']));
        assert!(accepted.etag.len() > 4);

        // Re-accepting the canonical form still works.
        let again = accept_upload(&accepted.png, spec).unwrap();
        assert_eq!(again.etag, accepted.etag);
    }

    #[test]
    fn reject_wrong_size() {
        let png = solid_bw_png(16, 16, true);
        let err = accept_upload(&png, PanelSpec::default()).unwrap_err();
        assert!(matches!(err, PanelError::WrongSize { .. }));
    }

    #[test]
    fn reject_gray() {
        let mut img = RgbImage::new(800, 480);
        for p in img.pixels_mut() {
            p.0 = [128, 128, 128];
        }
        let mut bytes = Vec::new();
        DynamicImage::ImageRgb8(img)
            .write_to(&mut Cursor::new(&mut bytes), image::ImageFormat::Png)
            .unwrap();
        let err = accept_upload(&bytes, PanelSpec::default()).unwrap_err();
        assert_eq!(err, PanelError::NotBlackAndWhite);
    }

    #[test]
    fn transform_cover_crops_and_dithers() {
        // Tall red→white gradient; after cover-crop+dither we get panel size.
        let mut img = RgbImage::new(200, 400);
        for (x, y, p) in img.enumerate_pixels_mut() {
            let v = ((x + y) % 256) as u8;
            p.0 = [v, v / 2, 255 - v];
        }
        let mut bytes = Vec::new();
        DynamicImage::ImageRgb8(img)
            .write_to(&mut Cursor::new(&mut bytes), image::ImageFormat::Png)
            .unwrap();

        let panel = transform_for_panel(&bytes, PanelSpec::default()).unwrap();
        let decoded = image::load_from_memory(&panel.png).unwrap();
        assert_eq!(decoded.dimensions(), (800, 480));
        // Every pixel must be 0 or 255 after dither.
        for px in decoded.to_luma8().pixels() {
            assert!(px.0[0] == 0 || px.0[0] == 255);
        }
    }

    #[test]
    fn floyd_steinberg_preserves_size() {
        let gray = GrayImage::from_fn(32, 16, |x, y| Luma([((x * 7 + y * 13) % 256) as u8]));
        let out = floyd_steinberg_bw(&gray);
        assert_eq!(out.dimensions(), (32, 16));
        assert!(out.pixels().all(|p| p.0[0] == 0 || p.0[0] == 255));
    }
}
