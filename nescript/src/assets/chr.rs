use image::GenericImageView;

/// Output of [`png_to_nametable_with_chr`]. Bundles the three
/// outputs into a named struct so the function signature stays
/// readable and clippy's `type_complexity` lint stays quiet.
#[derive(Debug, Clone)]
pub struct PngNametable {
    /// 960-byte tile-index table (32 cols × 30 rows). Each entry
    /// is offset by `chr_base_tile` so it points at the actual
    /// physical CHR-ROM tile the linker will assign.
    pub tiles: [u8; 960],
    /// 64-byte attribute table (8 × 8, each covering 32×32 px).
    pub attrs: [u8; 64],
    /// Flat CHR data for the unique tiles, `unique * 16` bytes
    /// in plane-0-then-plane-1 layout. Linker copies this into
    /// CHR ROM at `chr_base_tile * 16`.
    pub chr_bytes: Vec<u8>,
}

/// Convert a PNG image to NES CHR tile data (2-bitplane format).
/// Each 8x8 tile = 16 bytes (8 bytes plane 0, 8 bytes plane 1).
pub fn png_to_chr(path: &std::path::Path) -> Result<Vec<u8>, String> {
    let img = image::open(path).map_err(|e| format!("failed to open {}: {e}", path.display()))?;
    let (w, h) = img.dimensions();

    if w % 8 != 0 || h % 8 != 0 {
        return Err(format!("image dimensions {w}x{h} must be multiples of 8"));
    }

    let mut chr_data = Vec::new();
    let tiles_x = w / 8;
    let tiles_y = h / 8;

    for ty in 0..tiles_y {
        for tx in 0..tiles_x {
            let tile = encode_tile(&img, tx * 8, ty * 8);
            chr_data.extend_from_slice(&tile);
        }
    }

    Ok(chr_data)
}

/// Convert a 256×240 PNG into a nametable (`tiles`, `attrs`) pair.
///
/// Thin wrapper around [`png_to_nametable_with_chr`] for callers
/// that don't need the CHR data — e.g. the analyzer test fixtures
/// and the existing background tests. Production callers should
/// prefer the full triple form so the auto-generated CHR data
/// gets spliced into PRG.
pub fn png_to_nametable(path: &std::path::Path) -> Result<([u8; 960], [u8; 64]), String> {
    let nt = png_to_nametable_with_chr(path, 0)?;
    Ok((nt.tiles, nt.attrs))
}

/// Convert a 256×240 PNG into a nametable plus the per-tile CHR
/// data needed to render it on real hardware.
///
/// Returns a 4-tuple unpacked into 3 values: the 960-byte tile-
/// index table, the 64-byte attribute table, and a flat CHR blob
/// (`unique_tile_count * 16` bytes, plane-0 then plane-1 per row,
/// ready to splice into PRG/CHR ROM).
///
/// `chr_base_tile` shifts every entry in the tile-index table by
/// that constant so the output references the actual physical
/// tile indices the linker will assign — the asset pipeline
/// reserves tile 0 for the runtime smiley and tiles 1..N for
/// user sprites, so the resolver passes
/// `chr_base_tile = next_sprite_tile` to slot the auto-generated
/// background tiles right after the sprite range.
///
/// The image is sliced into 32×30 8×8 cells. Each cell's raw RGB
/// bytes are hashed; the first occurrence of a given hash becomes
/// a fresh tile index. A maximum of 256 unique tiles fit in a
/// single pattern table — anything beyond that is rejected. The
/// 64-byte attribute table is filled by computing, for each
/// 16×16 quadrant of a 32×32 meta-cell, the dominant brightness
/// bucket (0-3) and packing the four buckets into a single byte.
pub fn png_to_nametable_with_chr(
    path: &std::path::Path,
    chr_base_tile: u8,
) -> Result<PngNametable, String> {
    let img = image::open(path).map_err(|e| format!("failed to open {}: {e}", path.display()))?;
    let (w, h) = img.dimensions();
    if w != 256 || h != 240 {
        return Err(format!(
            "nametable PNG {} must be 256×240 (got {w}×{h})",
            path.display()
        ));
    }

    // 32×30 tile grid. For each tile we serialise its 64 pixels into
    // a 192-byte RGB blob, then use that blob as the dedup key via a
    // small hand-rolled table rather than pulling a hash crate in.
    // Keys are kept in a Vec<Vec<u8>> with the index as the tile id
    // — O(N²) in unique tiles, but N ≤ 256 so it's fine.
    //
    // Once the dedup decides a tile is new, we *also* immediately
    // encode it into 16 bytes of CHR data (plane 0 then plane 1)
    // and append it to `chr_bytes`. The two streams stay in sync:
    // tile index `i` in `unique_tiles` corresponds to the 16-byte
    // window starting at `i * 16` in `chr_bytes`.
    let rgb = img.to_rgb8();
    let mut unique_tiles: Vec<Vec<u8>> = Vec::new();
    let mut chr_bytes: Vec<u8> = Vec::new();
    let mut tiles = [0u8; 960];

    // Maximum unique tiles must leave room for the existing CHR
    // contents the linker has already promised — `chr_base_tile`
    // is the first index this background can claim, so the
    // top of the range is 256 - chr_base_tile.
    let max_unique = 256usize - chr_base_tile as usize;

    for ty in 0..30u32 {
        for tx in 0..32u32 {
            let mut key = Vec::with_capacity(8 * 8 * 3);
            for row in 0..8u32 {
                for col in 0..8u32 {
                    let p = rgb.get_pixel(tx * 8 + col, ty * 8 + row);
                    key.push(p[0]);
                    key.push(p[1]);
                    key.push(p[2]);
                }
            }
            let idx = if let Some(pos) = unique_tiles.iter().position(|t| t == &key) {
                pos
            } else {
                if unique_tiles.len() >= max_unique {
                    return Err(format!(
                        "nametable PNG {} needs more than {max_unique} unique 8×8 \
                         tiles after reserving {chr_base_tile} for sprites; \
                         simplify the image, split it into multiple backgrounds, \
                         or reduce the sprite count",
                        path.display()
                    ));
                }
                let new_idx = unique_tiles.len();
                let encoded = encode_tile_from_rgb(&rgb, tx * 8, ty * 8);
                chr_bytes.extend_from_slice(&encoded);
                unique_tiles.push(key);
                new_idx
            };
            // Add the per-background offset so the result references
            // physical CHR-ROM tile indices, not local 0..N.
            tiles[(ty * 32 + tx) as usize] = (idx as u8).wrapping_add(chr_base_tile);
        }
    }

    // Attribute table: 8×8 bytes, each covering a 32×32 region made
    // up of four 16×16 quadrants. Each quadrant gets 2 bits
    // (0..=3) packed into the byte as `BR<<6 | BL<<4 | TR<<2 | TL`
    // per the PPU's documented layout. The 15-row nametable only
    // half-fills the last attribute byte-row (rows 8..10 of the
    // bottom attribute byte are unused and stay at 0, matching the
    // hand-packed form the parser already emits).
    //
    // For each 16×16 quadrant we bucket the average brightness of
    // its 256 pixels into 0..=3. That's a crude approximation but
    // it's deterministic and maps "darker" regions to sub-palette 0
    // and "brighter" regions to sub-palette 3 — a reasonable default
    // until per-quadrant palette selection is exposed in the source.
    let mut attrs = [0u8; 64];
    for aty in 0..8u32 {
        for atx in 0..8u32 {
            let quadrant = |qx: u32, qy: u32| -> u8 {
                // qx/qy are 0 or 1 → top-left/top-right/bottom-left/
                // bottom-right of the 32×32 attribute cell.
                let base_x = atx * 32 + qx * 16;
                let base_y = aty * 32 + qy * 16;
                if base_x >= 256 || base_y >= 240 {
                    return 0;
                }
                let mut total: u32 = 0;
                let mut count: u32 = 0;
                let y_end = (base_y + 16).min(240);
                let x_end = (base_x + 16).min(256);
                for y in base_y..y_end {
                    for x in base_x..x_end {
                        let p = rgb.get_pixel(x, y);
                        total += u32::from(p[0]) + u32::from(p[1]) + u32::from(p[2]);
                        count += 1;
                    }
                }
                if count == 0 {
                    return 0;
                }
                let avg = total / (count * 3);
                match avg {
                    0..=63 => 0,
                    64..=127 => 1,
                    128..=191 => 2,
                    _ => 3,
                }
            };
            let tl = quadrant(0, 0);
            let tr = quadrant(1, 0);
            let bl = quadrant(0, 1);
            let br = quadrant(1, 1);
            let byte = (br << 6) | (bl << 4) | (tr << 2) | tl;
            attrs[(aty * 8 + atx) as usize] = byte;
        }
    }

    Ok(PngNametable {
        tiles,
        attrs,
        chr_bytes,
    })
}

/// Encode an 8×8 region of an `RgbImage` into the NES 2-bitplane
/// CHR format. Mirrors [`encode_tile`] but operates on the
/// already-extracted RGB buffer used by the nametable resolver,
/// which avoids re-opening the image and keeps the per-tile cost
/// to a single rectangle scan.
fn encode_tile_from_rgb(rgb: &image::RgbImage, x: u32, y: u32) -> [u8; 16] {
    let mut tile = [0u8; 16];
    for row in 0..8u32 {
        let mut plane0 = 0u8;
        let mut plane1 = 0u8;
        for col in 0..8u32 {
            let pixel = rgb.get_pixel(x + col, y + row);
            let brightness = (u16::from(pixel[0]) + u16::from(pixel[1]) + u16::from(pixel[2])) / 3;
            let index = match brightness {
                0..=63 => 0u8,
                64..=127 => 1,
                128..=191 => 2,
                _ => 3,
            };
            if index & 1 != 0 {
                plane0 |= 0x80 >> col;
            }
            if index & 2 != 0 {
                plane1 |= 0x80 >> col;
            }
        }
        tile[row as usize] = plane0;
        tile[row as usize + 8] = plane1;
    }
    tile
}

fn encode_tile(img: &image::DynamicImage, x: u32, y: u32) -> [u8; 16] {
    let mut tile = [0u8; 16];

    for row in 0..8u32 {
        let mut plane0 = 0u8;
        let mut plane1 = 0u8;
        for col in 0..8u32 {
            let pixel = img.get_pixel(x + col, y + row);
            // Map to 2-bit palette index based on brightness
            let brightness = (u16::from(pixel[0]) + u16::from(pixel[1]) + u16::from(pixel[2])) / 3;
            let index = match brightness {
                0..=63 => 0u8,
                64..=127 => 1,
                128..=191 => 2,
                _ => 3,
            };
            if index & 1 != 0 {
                plane0 |= 0x80 >> col;
            }
            if index & 2 != 0 {
                plane1 |= 0x80 >> col;
            }
        }
        tile[row as usize] = plane0;
        tile[row as usize + 8] = plane1;
    }

    tile
}

#[cfg(test)]
mod tests {
    use super::*;
    use image::{Rgb, RgbImage};

    #[test]
    fn png_to_nametable_dedupes_tiles() {
        // A 256×240 image split into 8×8 tiles: the top half is all
        // black and the bottom half is all white. We expect the
        // deduplicator to find exactly two unique tiles and to emit
        // a 960-byte tile map where rows 0..14 reference tile 0 and
        // rows 15..29 reference tile 1.
        let dir = std::env::temp_dir();
        let path = dir.join("nescript_png_to_nametable_dedupe.png");
        let mut img = RgbImage::new(256, 240);
        for y in 0..240u32 {
            let c = if y < 120 { 0u8 } else { 255u8 };
            for x in 0..256u32 {
                img.put_pixel(x, y, Rgb([c, c, c]));
            }
        }
        img.save(&path).unwrap();
        let (tiles, attrs) = png_to_nametable(&path).unwrap();
        let _ = std::fs::remove_file(&path);

        // Top 15 rows should be uniformly tile 0; bottom 15 rows
        // should be uniformly tile 1.
        for row in 0..15usize {
            for col in 0..32usize {
                assert_eq!(tiles[row * 32 + col], 0);
            }
        }
        for row in 15..30usize {
            for col in 0..32usize {
                assert_eq!(tiles[row * 32 + col], 1);
            }
        }
        // Attributes: top half dark → sub-palette 0; bottom half
        // bright → sub-palette 3. Each attribute byte covers 32×32
        // so row 0..3 of the attribute table is "top half" and
        // row 4..7 is "bottom half"; row 3 straddles the 120-pixel
        // seam so we only check rows that are cleanly on one side.
        for row in 0..3usize {
            for col in 0..8usize {
                assert_eq!(
                    attrs[row * 8 + col],
                    0,
                    "attr row {row} col {col} should be dark"
                );
            }
        }
        for row in 4..7usize {
            for col in 0..8usize {
                // 3 packed into every 2-bit slot = 0xFF.
                assert_eq!(
                    attrs[row * 8 + col],
                    0xFF,
                    "attr row {row} col {col} should be bright"
                );
            }
        }
    }

    #[test]
    fn png_to_nametable_rejects_wrong_size() {
        let dir = std::env::temp_dir();
        let path = dir.join("nescript_png_nametable_wrong_size.png");
        let img = RgbImage::new(320, 240);
        img.save(&path).unwrap();
        let err = png_to_nametable(&path).unwrap_err();
        let _ = std::fs::remove_file(&path);
        assert!(err.contains("must be 256"), "unexpected error: {err}");
    }

    #[test]
    fn png_to_nametable_with_chr_emits_per_tile_data_and_offsets_indices() {
        // Two-tile gradient: the top half is uniformly mid-gray and
        // the bottom half is uniformly white. We feed in a sprite
        // base tile of 5 to exercise the offset path — the output
        // tile-index table must reference 5 and 6, and the chr_bytes
        // blob must be exactly 32 bytes (two 16-byte tiles).
        let dir = std::env::temp_dir();
        let path = dir.join("nescript_png_to_nametable_with_chr.png");
        let mut img = RgbImage::new(256, 240);
        for y in 0..240u32 {
            let c: u8 = if y < 120 { 96 } else { 255 };
            for x in 0..256u32 {
                img.put_pixel(x, y, Rgb([c, c, c]));
            }
        }
        img.save(&path).unwrap();
        let nt = png_to_nametable_with_chr(&path, 5).unwrap();
        let _ = std::fs::remove_file(&path);
        // The first tile (index 0 inside the dedupe table) becomes
        // physical tile 5; the second becomes physical tile 6.
        assert_eq!(nt.tiles[0], 5, "top-left tile should be at base + 0");
        assert_eq!(
            nt.tiles[20 * 32],
            6,
            "bottom-left tile should be at base + 1"
        );
        // Two unique tiles → 32 bytes of CHR data.
        assert_eq!(nt.chr_bytes.len(), 32, "should emit exactly 2 * 16 bytes");
        // The mid-gray tile should encode every pixel as palette
        // index 1 (brightness 96 buckets to 1) — that's plane0 = $FF
        // and plane1 = $00 for every row. The white tile encodes
        // every pixel as index 3, so plane0 = plane1 = $FF.
        for byte in &nt.chr_bytes[..8] {
            assert_eq!(*byte, 0xFF, "tile 0 plane 0 should be all 1s");
        }
        for byte in &nt.chr_bytes[8..16] {
            assert_eq!(*byte, 0x00, "tile 0 plane 1 should be all 0s");
        }
        for byte in &nt.chr_bytes[16..32] {
            assert_eq!(*byte, 0xFF, "tile 1 should be all 1s in both planes");
        }
    }

    #[test]
    fn png_to_nametable_with_chr_respects_sprite_base_for_max_unique() {
        // Reserving N tiles for sprites caps the background at
        // 256-N unique tiles. We exercise the bound by reserving
        // 250 sprite tiles and then asking the resolver to dedupe
        // an image with more than 6 distinct cells — it should
        // fail with a clear error pointing at both the cap and
        // the reservation.
        let dir = std::env::temp_dir();
        let path = dir.join("nescript_png_to_nametable_with_chr_cap.png");
        // 8 distinct horizontal stripes (one per row group), each
        // 30 pixels tall so the dedupe table sees 8 unique tiles.
        let mut img = RgbImage::new(256, 240);
        for y in 0..240u32 {
            let c: u8 = ((y / 30) * 32) as u8;
            for x in 0..256u32 {
                img.put_pixel(x, y, Rgb([c, c, c]));
            }
        }
        img.save(&path).unwrap();
        let err = png_to_nametable_with_chr(&path, 250).unwrap_err();
        let _ = std::fs::remove_file(&path);
        assert!(
            err.contains("more than 6"),
            "expected 'more than 6 unique' (256-250), got: {err}"
        );
        assert!(
            err.contains("reserving 250"),
            "expected the error to mention the sprite reservation, got: {err}"
        );
    }

    #[test]
    fn png_to_nametable_rejects_too_many_unique_tiles() {
        // A 256×240 image of unique gradient tiles — each 8×8 cell
        // has a distinct top-left pixel value. With 32×30 = 960
        // tiles but only 256 unique slots available, this must
        // fail with a clear error. We force uniqueness by tiling
        // monotonically increasing colours across the 32×30 grid.
        let dir = std::env::temp_dir();
        let path = dir.join("nescript_png_nametable_too_many.png");
        let mut img = RgbImage::new(256, 240);
        for ty in 0..30u32 {
            for tx in 0..32u32 {
                let idx = ty * 32 + tx;
                // 960 distinct (r, g, b) triplets. We use 10 bits
                // worth of variation so no two tiles collide.
                let r = (idx & 0xFF) as u8;
                let g = ((idx >> 2) & 0xFF) as u8;
                let b = ((idx >> 4) & 0xFF) as u8;
                for row in 0..8u32 {
                    for col in 0..8u32 {
                        img.put_pixel(tx * 8 + col, ty * 8 + row, Rgb([r, g, b]));
                    }
                }
            }
        }
        img.save(&path).unwrap();
        let err = png_to_nametable(&path).unwrap_err();
        let _ = std::fs::remove_file(&path);
        assert!(
            err.contains("more than 256 unique"),
            "unexpected error: {err}"
        );
    }
}
