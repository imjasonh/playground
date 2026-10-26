use std::path::Path;

use crate::linker::SpriteData;
use crate::parser::ast::{AssetSource, Program};

/// Resolved palette data, ready for the linker to splice into PRG
/// ROM as a 32-byte data blob at the label returned by [`Self::label`].
/// Declarations shorter than 32 bytes are zero-padded so the runtime
/// can always push exactly 32 bytes to `$3F00-$3F1F`.
#[derive(Debug, Clone)]
pub struct PaletteData {
    pub name: String,
    /// Exactly 32 bytes. Index `i` is the value written to PPU
    /// address `$3F00 + i`.
    pub colors: [u8; 32],
}

impl PaletteData {
    /// The ROM-level label under which the linker emits the 32-byte
    /// blob. The IR codegen references this label when lowering
    /// `set_palette Name`.
    #[must_use]
    pub fn label(&self) -> String {
        format!("__palette_{}", self.name)
    }
}

/// Resolved background data. `tiles` is the 960-byte nametable
/// (32 columns × 30 rows) and `attrs` is the 64-byte attribute
/// table. Both are zero-padded up from the declared sizes so the
/// runtime NMI helper can always push fixed-length data.
///
/// `chr_bytes` and `chr_base_tile` describe the per-background
/// CHR data the resolver auto-generates from a `@nametable(...)`
/// PNG source. `chr_bytes` is empty (and `chr_base_tile == 0`)
/// for inline `tiles:` / `attributes:` declarations — those still
/// reference whatever tiles the user supplied via separate
/// sprite / `@chr(...)` declarations, so the linker doesn't
/// touch the CHR ROM on their behalf. PNG-sourced backgrounds
/// instead emit a flat 16-byte-per-tile blob keyed by
/// `chr_base_tile`, which the linker copies into CHR ROM at
/// `chr_base_tile * 16`.
#[derive(Debug, Clone)]
pub struct BackgroundData {
    pub name: String,
    pub tiles: [u8; 960],
    pub attrs: [u8; 64],
    pub chr_bytes: Vec<u8>,
    pub chr_base_tile: u8,
}

impl BackgroundData {
    #[must_use]
    pub fn tiles_label(&self) -> String {
        format!("__bg_tiles_{}", self.name)
    }
    #[must_use]
    pub fn attrs_label(&self) -> String {
        format!("__bg_attrs_{}", self.name)
    }
}

/// Resolved level data for a `room Name { ... }` declaration. The
/// compiler expands each room (16×15 metatile grid) at compile time
/// into three fixed-size blobs that the linker embeds in PRG ROM:
///
/// - `tiles` (960 bytes): the 32×30 nametable the room paints into.
///   Each of the 240 metatile cells produces 2×2 CHR tile indices,
///   row-major.
/// - `attrs` (64 bytes): the 8×8 attribute table. v1 writes zeros
///   (sub-palette 0 for every quadrant); a future revision can
///   derive this from per-metatile palette hints.
/// - `collision` (240 bytes): one byte per metatile, mirroring the
///   `layout` array but carrying the metatileset's `collide` flag
///   instead of the metatile ID. `collides_at(x, y)` indexes into
///   this by `(y / 16) * 16 + (x / 16)`.
///
/// Labels used downstream: `__room_tiles_<name>`, `__room_attrs_<name>`,
/// `__room_col_<name>`. `paint_room <name>` queues the first two
/// through the same vblank-safe update machinery as `load_background`,
/// and installs the third's address into the room-pointer ZP slots
/// so subsequent `collides_at` queries read from this room's map.
#[derive(Debug, Clone)]
pub struct RoomData {
    pub name: String,
    pub tiles: [u8; 960],
    pub attrs: [u8; 64],
    pub collision: [u8; 240],
}

impl RoomData {
    #[must_use]
    pub fn tiles_label(&self) -> String {
        format!("__room_tiles_{}", self.name)
    }
    #[must_use]
    pub fn attrs_label(&self) -> String {
        format!("__room_attrs_{}", self.name)
    }
    #[must_use]
    pub fn collision_label(&self) -> String {
        format!("__room_col_{}", self.name)
    }
}

/// Resolve sprite declarations in a program into concrete CHR byte blobs and
/// assign each one a tile index in CHR ROM.
///
/// Tile index 0 is reserved for the built-in default smiley sprite, so user
/// sprites start at tile index 1. A single sprite declaration may occupy
/// multiple consecutive tiles if its CHR data is larger than 16 bytes.
///
/// `source_dir` is used as the base for `@binary` / `@chr` relative paths.
/// Missing files are silently skipped (not an error) so programs that
/// reference external assets for documentation purposes compile without
/// requiring the files to exist yet.
pub fn resolve_sprites(program: &Program, source_dir: &Path) -> Result<Vec<SpriteData>, String> {
    let mut sprites = Vec::new();
    // Tile index 0 is the built-in smiley; user sprites start at 1.
    let mut next_tile: u8 = 1;

    for sprite_decl in &program.sprites {
        let chr_bytes = match &sprite_decl.chr_source {
            AssetSource::Inline(bytes) => bytes.clone(),
            AssetSource::Binary(path) => {
                // Try to read raw bytes from the file. Missing files are
                // skipped silently so declarations can reference assets
                // that haven't been added yet.
                let full_path = source_dir.join(path);
                match std::fs::read(&full_path) {
                    Ok(bytes) => bytes,
                    Err(_) => continue,
                }
            }
            AssetSource::Chr(path) => {
                // PNG → CHR conversion. Missing files skipped silently.
                let full_path = source_dir.join(path);
                match crate::assets::png_to_chr(&full_path) {
                    Ok(bytes) => bytes,
                    Err(_) => continue,
                }
            }
        };

        // Each NES 8x8 tile is 16 bytes of 2-bitplane CHR data. A single
        // sprite declaration can span multiple tiles when its CHR blob is
        // longer than 16 bytes.
        let tile_count = chr_bytes.len().div_ceil(16);
        if tile_count == 0 {
            continue;
        }
        if next_tile as usize + tile_count > 256 {
            return Err(format!(
                "sprite '{}' would exceed CHR ROM tile limit",
                sprite_decl.name
            ));
        }

        sprites.push(SpriteData {
            name: sprite_decl.name.clone(),
            tile_index: next_tile,
            chr_bytes,
        });
        next_tile += tile_count as u8;
    }

    Ok(sprites)
}

/// Resolve all `palette Name { ... }` declarations in `program` into
/// 32-byte fixed-size blobs suitable for splicing into PRG ROM.
///
/// Each declaration can take one of three shapes:
/// - `colors: [...]` flat byte array — shorter than 32 is zero-padded.
/// - grouped `universal / bg0..sp3` form — already assembled into
///   `colors` by the parser.
/// - `@palette("file.png")` — decoded on the fly via
///   [`crate::assets::png_to_palette`], which maps RGB pixels to
///   nearest NES master-palette indices and enforces the universal
///   first-byte convention.
///
/// `source_dir` is the base for PNG-relative paths — callers typically
/// pass the source file's parent directory so `@palette("art/main.png")`
/// resolves next to the `.ne` file, the same convention the sprite
/// resolver uses.
pub fn resolve_palettes(program: &Program, source_dir: &Path) -> Result<Vec<PaletteData>, String> {
    let mut out = Vec::with_capacity(program.palettes.len());
    for p in &program.palettes {
        let colors = if let Some(png_path) = &p.png_source {
            let full_path = source_dir.join(png_path);
            crate::assets::png_to_palette(&full_path)
                .map_err(|e| format!("palette '{}' PNG source: {e}", p.name))?
        } else {
            let mut colors = [0u8; 32];
            for (i, c) in p.colors.iter().enumerate().take(32) {
                colors[i] = *c;
            }
            colors
        };
        out.push(PaletteData {
            name: p.name.clone(),
            colors,
        });
    }
    Ok(out)
}

/// Resolve all `background Name { ... }` declarations in `program`
/// into fixed-size 960-byte tile maps and 64-byte attribute tables.
/// Declarations shorter than the maximum are zero-padded.
///
/// When a declaration uses the PNG shortcut form
/// (`@nametable("file.png")`), the image is decoded via
/// [`crate::assets::png_to_nametable_with_chr`] into a 960-byte
/// tile index table + 64-byte attribute table + the CHR data for
/// the unique tiles. The auto-generated CHR is offset by
/// `next_sprite_tile` so it sits immediately after the user's
/// sprite tile range — the linker copies it into CHR ROM via
/// `BackgroundData::chr_bytes` and `chr_base_tile`. Inline
/// `tiles:` / `attributes:` declarations leave `chr_bytes`
/// empty; those still rely on the user supplying tiles via
/// separate sprite declarations.
pub fn resolve_backgrounds(
    program: &Program,
    source_dir: &Path,
    next_sprite_tile: u8,
) -> Result<Vec<BackgroundData>, String> {
    let mut out = Vec::with_capacity(program.backgrounds.len());
    let mut next_tile = next_sprite_tile;
    for b in &program.backgrounds {
        if let Some(png_path) = &b.png_source {
            let full_path = source_dir.join(png_path);
            let nt = crate::assets::png_to_nametable_with_chr(&full_path, next_tile)
                .map_err(|e| format!("background '{}' PNG source: {e}", b.name))?;
            // Each unique tile is exactly 16 bytes of CHR data;
            // `next_tile` advances past the new range so a second
            // PNG-sourced background lands its tiles after the
            // first one's.
            #[allow(clippy::cast_possible_truncation)]
            let tile_count: u8 = (nt.chr_bytes.len() / 16) as u8;
            let chr_base_tile = next_tile;
            next_tile = next_tile.saturating_add(tile_count);
            out.push(BackgroundData {
                name: b.name.clone(),
                tiles: nt.tiles,
                attrs: nt.attrs,
                chr_bytes: nt.chr_bytes,
                chr_base_tile,
            });
        } else {
            let mut tiles = [0u8; 960];
            for (i, t) in b.tiles.iter().enumerate().take(960) {
                tiles[i] = *t;
            }
            let mut attrs = [0u8; 64];
            for (i, a) in b.attributes.iter().enumerate().take(64) {
                attrs[i] = *a;
            }
            out.push(BackgroundData {
                name: b.name.clone(),
                tiles,
                attrs,
                chr_bytes: Vec::new(),
                chr_base_tile: 0,
            });
        }
    }
    Ok(out)
}

/// Resolve every `room Name { ... }` declaration in `program` into
/// expanded [`RoomData`] blobs. The analyzer has already validated
/// layout length, metatile IDs, and metatileset references, so this
/// is a straightforward 16×15 → 32×30 unpack plus a parallel
/// collision-byte copy.
pub fn resolve_rooms(program: &Program) -> Vec<RoomData> {
    let mut out = Vec::with_capacity(program.rooms.len());
    let mts_by_name: std::collections::HashMap<&str, &crate::parser::ast::MetatilesetDecl> =
        program
            .metatilesets
            .iter()
            .map(|m| (m.name.as_str(), m))
            .collect();
    for room in &program.rooms {
        let mut tiles = [0u8; 960];
        let mut collision = [0u8; 240];
        if let Some(mts) = mts_by_name.get(room.metatileset.as_str()) {
            for (cell_idx, &mt_id) in room.layout.iter().enumerate().take(240) {
                let mt_x = cell_idx % 16;
                let mt_y = cell_idx / 16;
                let entry = &mts.metatiles[usize::from(mt_id)];
                // Expand 2×2 metatile into its four nametable cells.
                // Each nametable row is 32 cells wide; each metatile
                // row is 15 metatiles tall × 2 = 30 rows (a full
                // playfield height).
                let tl_x = mt_x * 2;
                let tl_y = mt_y * 2;
                let tl_idx = tl_y * 32 + tl_x;
                tiles[tl_idx] = entry.tiles[0]; // TL
                tiles[tl_idx + 1] = entry.tiles[1]; // TR
                tiles[tl_idx + 32] = entry.tiles[2]; // BL
                tiles[tl_idx + 33] = entry.tiles[3]; // BR
                collision[cell_idx] = u8::from(entry.collide);
            }
        }
        out.push(RoomData {
            name: room.name.clone(),
            tiles,
            attrs: [0u8; 64],
            collision,
        });
    }
    out
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::lexer::Span;
    use crate::parser::ast::{GameDecl, HeaderFormat, Mapper, Mirroring, SpriteDecl};

    fn make_program(sprite: SpriteDecl) -> Program {
        Program {
            game: GameDecl {
                name: "Test".to_string(),
                mapper: Mapper::NROM,
                mirroring: Mirroring::Horizontal,
                header: HeaderFormat::Ines1,
                debug_port: 0x4800,
                sprite_flicker: false,
                span: Span::dummy(),
            },
            globals: Vec::new(),
            saves: Vec::new(),
            constants: Vec::new(),
            enums: Vec::new(),
            structs: Vec::new(),
            functions: Vec::new(),
            states: Vec::new(),
            sprites: vec![sprite],
            palettes: Vec::new(),
            backgrounds: Vec::new(),
            metasprites: Vec::new(),
            metatilesets: Vec::new(),
            rooms: Vec::new(),
            sfx: Vec::new(),
            music: Vec::new(),
            banks: Vec::new(),
            start_state: "Main".to_string(),
            span: Span::dummy(),
        }
    }

    #[test]
    fn resolve_inline_sprite() {
        let sprite = SpriteDecl {
            name: "Player".to_string(),
            chr_source: AssetSource::Inline(vec![0u8; 16]),
            span: Span::dummy(),
        };
        let program = make_program(sprite);
        let sprites = resolve_sprites(&program, Path::new(".")).unwrap();
        assert_eq!(sprites.len(), 1);
        assert_eq!(sprites[0].name, "Player");
        assert_eq!(sprites[0].tile_index, 1);
        assert_eq!(sprites[0].chr_bytes.len(), 16);
    }

    #[test]
    fn resolve_binary_file_reads_bytes() {
        let dir = std::env::temp_dir();
        let file_path = dir.join("nescript_resolve_test.bin");
        let bytes: Vec<u8> = (0x40..0x50).collect();
        std::fs::write(&file_path, &bytes).unwrap();

        let sprite = SpriteDecl {
            name: "Tile".to_string(),
            chr_source: AssetSource::Binary(
                file_path.file_name().unwrap().to_string_lossy().to_string(),
            ),
            span: Span::dummy(),
        };
        let program = make_program(sprite);
        let sprites = resolve_sprites(&program, &dir).unwrap();
        assert_eq!(sprites.len(), 1);
        assert_eq!(sprites[0].chr_bytes, bytes);

        let _ = std::fs::remove_file(&file_path);
    }

    #[test]
    fn resolve_missing_binary_skipped() {
        let sprite = SpriteDecl {
            name: "Missing".to_string(),
            chr_source: AssetSource::Binary("nonexistent.bin".to_string()),
            span: Span::dummy(),
        };
        let program = make_program(sprite);
        let sprites = resolve_sprites(&program, Path::new(".")).unwrap();
        // Missing binary file → silently skipped
        assert!(sprites.is_empty());
    }

    use crate::parser::ast::{BackgroundDecl, PaletteDecl};

    fn blank_program() -> Program {
        Program {
            game: GameDecl {
                name: "Test".to_string(),
                mapper: Mapper::NROM,
                mirroring: Mirroring::Horizontal,
                header: HeaderFormat::Ines1,
                debug_port: 0x4800,
                sprite_flicker: false,
                span: Span::dummy(),
            },
            globals: Vec::new(),
            saves: Vec::new(),
            constants: Vec::new(),
            enums: Vec::new(),
            structs: Vec::new(),
            functions: Vec::new(),
            states: Vec::new(),
            sprites: Vec::new(),
            palettes: Vec::new(),
            backgrounds: Vec::new(),
            metasprites: Vec::new(),
            metatilesets: Vec::new(),
            rooms: Vec::new(),
            sfx: Vec::new(),
            music: Vec::new(),
            banks: Vec::new(),
            start_state: "Main".to_string(),
            span: Span::dummy(),
        }
    }

    #[test]
    fn resolve_palette_zero_pads_to_32_bytes() {
        let mut program = blank_program();
        program.palettes.push(PaletteDecl {
            name: "Cool".to_string(),
            colors: vec![0x0F, 0x01, 0x11, 0x21],
            png_source: None,
            span: Span::dummy(),
        });
        let resolved = resolve_palettes(&program, Path::new(".")).unwrap();
        assert_eq!(resolved.len(), 1);
        assert_eq!(resolved[0].name, "Cool");
        assert_eq!(resolved[0].colors.len(), 32);
        assert_eq!(&resolved[0].colors[..4], &[0x0F, 0x01, 0x11, 0x21]);
        // Remainder is zero-padded.
        assert!(resolved[0].colors[4..].iter().all(|&b| b == 0));
        assert_eq!(resolved[0].label(), "__palette_Cool");
    }

    #[test]
    fn resolve_palette_truncates_beyond_32_bytes() {
        // The analyzer rejects >32-byte palettes with E0201; at the
        // resolve level we defensively truncate so downstream code
        // always sees exactly 32 bytes. This lets bad input still
        // produce a valid ROM structure for diagnostic purposes.
        let mut program = blank_program();
        program.palettes.push(PaletteDecl {
            name: "Big".to_string(),
            colors: (0u8..40).collect(),
            png_source: None,
            span: Span::dummy(),
        });
        let resolved = resolve_palettes(&program, Path::new(".")).unwrap();
        assert_eq!(resolved[0].colors.len(), 32);
        assert_eq!(resolved[0].colors[0], 0);
        assert_eq!(resolved[0].colors[31], 31);
    }

    #[test]
    fn resolve_palette_from_png() {
        // A 2×1 PNG with pure black and pure red goes through the
        // PNG-sourced path. We write the fixture to a tempdir, point
        // the resolver at it, and verify the universal-byte rule
        // (every sub-palette's first byte = first unique colour).
        use image::{Rgb, RgbImage};

        let dir = std::env::temp_dir();
        let png_path = dir.join("nescript_resolve_palette_png.png");
        let mut img = RgbImage::new(2, 1);
        img.put_pixel(0, 0, Rgb([0, 0, 0]));
        img.put_pixel(1, 0, Rgb([248, 0, 0]));
        img.save(&png_path).unwrap();

        let mut program = blank_program();
        program.palettes.push(PaletteDecl {
            name: "Fromimg".to_string(),
            colors: Vec::new(),
            png_source: Some(png_path.file_name().unwrap().to_string_lossy().to_string()),
            span: Span::dummy(),
        });
        let resolved = resolve_palettes(&program, &dir).unwrap();
        let _ = std::fs::remove_file(&png_path);
        assert_eq!(resolved.len(), 1);
        assert_eq!(resolved[0].colors.len(), 32);
        // Every sub-palette slot's first byte is the universal.
        let universal = resolved[0].colors[0];
        for slot in 0..8 {
            assert_eq!(resolved[0].colors[slot * 4], universal);
        }
    }

    #[test]
    fn resolve_palette_missing_png_is_error() {
        // Unlike the sprite resolver (which silently skips missing
        // `@binary` / `@chr` files to keep documentation-only
        // declarations cheap), a missing PNG palette is a hard
        // failure — the declaration has no fallback bytes to fall
        // back on. The error bubbles up with the palette's name.
        let mut program = blank_program();
        program.palettes.push(PaletteDecl {
            name: "Missing".to_string(),
            colors: Vec::new(),
            png_source: Some("nonexistent_palette.png".to_string()),
            span: Span::dummy(),
        });
        let err = resolve_palettes(&program, Path::new(".")).unwrap_err();
        assert!(err.contains("palette 'Missing' PNG source"));
    }

    #[test]
    fn resolve_background_pads_tiles_and_attrs() {
        let mut program = blank_program();
        program.backgrounds.push(BackgroundDecl {
            name: "Stage".to_string(),
            tiles: vec![1, 2, 3],
            attributes: vec![0xFF],
            png_source: None,
            span: Span::dummy(),
        });
        let resolved = resolve_backgrounds(&program, Path::new("."), 1).unwrap();
        assert_eq!(resolved.len(), 1);
        assert_eq!(resolved[0].name, "Stage");
        assert_eq!(resolved[0].tiles.len(), 960);
        assert_eq!(resolved[0].tiles[0], 1);
        assert_eq!(resolved[0].tiles[2], 3);
        assert!(resolved[0].tiles[3..].iter().all(|&b| b == 0));
        assert_eq!(resolved[0].attrs.len(), 64);
        assert_eq!(resolved[0].attrs[0], 0xFF);
        assert!(resolved[0].attrs[1..].iter().all(|&b| b == 0));
        assert_eq!(resolved[0].tiles_label(), "__bg_tiles_Stage");
        assert_eq!(resolved[0].attrs_label(), "__bg_attrs_Stage");
    }

    #[test]
    fn resolve_background_from_png() {
        // A 256×240 PNG with a simple horizontal-stripe pattern so
        // the tile deduplicator produces a predictable number of
        // tiles. We flag the tile count rather than exact bytes
        // because the hashing is implementation-defined.
        use image::{Rgb, RgbImage};

        let dir = std::env::temp_dir();
        let png_path = dir.join("nescript_resolve_bg_png.png");
        let mut img = RgbImage::new(256, 240);
        for y in 0..240u32 {
            let band = (y / 16) as u8;
            for x in 0..256u32 {
                let c = band.wrapping_mul(30);
                img.put_pixel(x, y, Rgb([c, c, c]));
            }
        }
        img.save(&png_path).unwrap();

        let mut program = blank_program();
        program.backgrounds.push(BackgroundDecl {
            name: "Fromimg".to_string(),
            tiles: Vec::new(),
            attributes: Vec::new(),
            png_source: Some(png_path.file_name().unwrap().to_string_lossy().to_string()),
            span: Span::dummy(),
        });
        let resolved = resolve_backgrounds(&program, &dir, 1).unwrap();
        let _ = std::fs::remove_file(&png_path);
        assert_eq!(resolved.len(), 1);
        assert_eq!(resolved[0].tiles.len(), 960);
        assert_eq!(resolved[0].attrs.len(), 64);
        // Horizontal bands mean every column's tile in a given row
        // is the same — the 32 tiles of row 0 are all tile index 0.
        assert!(
            resolved[0].tiles[..32]
                .iter()
                .all(|&t| t == resolved[0].tiles[0]),
            "row 0 should be a single repeating tile"
        );
    }

    #[test]
    fn resolve_background_wrong_size_png_is_error() {
        // Nametable PNGs must be exactly 256×240. Any other size
        // is a hard failure with the background's name attached.
        use image::{Rgb, RgbImage};

        let dir = std::env::temp_dir();
        let png_path = dir.join("nescript_resolve_bg_wrong_size.png");
        let mut img = RgbImage::new(128, 128);
        for p in img.pixels_mut() {
            *p = Rgb([0, 0, 0]);
        }
        img.save(&png_path).unwrap();

        let mut program = blank_program();
        program.backgrounds.push(BackgroundDecl {
            name: "Oops".to_string(),
            tiles: Vec::new(),
            attributes: Vec::new(),
            png_source: Some(png_path.file_name().unwrap().to_string_lossy().to_string()),
            span: Span::dummy(),
        });
        let err = resolve_backgrounds(&program, &dir, 1).unwrap_err();
        let _ = std::fs::remove_file(&png_path);
        assert!(
            err.contains("background 'Oops' PNG source"),
            "unexpected error: {err}"
        );
        assert!(
            err.contains("256") || err.contains("240"),
            "unexpected error: {err}"
        );
    }
}
