//! One-shot generator for the CHR tiles and nametable used by
//! `examples/platformer.ne`.
//!
//! Run with `cargo run --bin gen_platformer_tiles`. The output is
//! intended to be pasted into `platformer.ne` under the
//! `sprite Tileset { pixels: [...] }` and
//! `background Level { legend { ... } map: [...] palette_map: [...] }`
//! blocks. Keeping the source of truth here (instead of
//! hand-maintained ASCII in the `.ne` file) ensures the tile art,
//! the nametable, and the named tile indices all stay in sync.
//!
//! Tiles are defined as 8×8 ASCII art where each character selects
//! one of 4 sub-palette slots:
//!     '.' = colour 0  (sky / transparent for sprites)
//!     'a' = colour 1
//!     'b' = colour 2
//!     'c' = colour 3
//!
//! Both the generator *and* the `NEScript` parser accept `.abc` as
//! aliases for `.#%@`, so the output is ready to paste directly
//! into a `pixels:` block without translation.

/// A single 8×8 tile description: name + ASCII art.
struct Tile {
    name: &'static str,
    art: &'static str,
}

/// All tiles referenced by the platformer example. Order matters —
/// tile 0 is the default smiley reserved by the linker, so entry 0
/// here lands at CHR index 1, entry 1 at index 2, and so on.
///
/// Colour conventions (must line up with the palette + attribute
/// layout in `examples/platformer.ne`):
///   sprite sub-palette 0 (player / enemy / coin):
///     a = red/cap, b = peach/skin, c = white/highlight
///   bg sub-palette 0 (sky row): a = white, b = light gray, c = black
///   bg sub-palette 1 (block row): a = red, b = peach, c = dark red
///   bg sub-palette 2 (ground row): a = light green, b = light brown,
///                                   c = dark brown
const TILES: &[Tile] = &[
    Tile {
        name: "Player head L",
        art: "\
..aaaaaa
.aaaaaaa
.aaabbbb
.aabbbbc
aabbcccc
aabbccbc
aabbbbbb
aabbbbbb",
    },
    Tile {
        name: "Player head R",
        art: "\
aaaaaa..
aaaaaaa.
bbbbaaa.
cbbbbbaa
cccccbbb
bcbbccbb
bbbbbbbb
bbbbbbbb",
    },
    Tile {
        name: "Player body L",
        art: "\
.aaaaaaa
aaacaaaa
aaaccaaa
aaaaaaaa
.bbbbbbb
.bbbbbbb
.bb..bbb
aaa..bbb",
    },
    Tile {
        name: "Player body R",
        art: "\
aaaaaaa.
aaaacaaa
aaaccaaa
aaaaaaaa
bbbbbbb.
bbbbbbb.
bbb..bb.
bbb..aaa",
    },
    Tile {
        name: "Enemy",
        art: "\
..aaaa..
.aaaaaa.
.aacbaa.
aacccaaa
abbccbba
.aaaaaa.
a.aaaa.a
a..aa..a",
    },
    Tile {
        name: "Coin",
        art: "\
...bb...
..bbbb..
.bbccbb.
.bcbbcb.
.bcbbcb.
.bbccbb.
..bbbb..
...bb...",
    },
    // Grass top (sub-palette 2: a=green, c=dark brown).
    Tile {
        name: "Grass top",
        art: "\
aaaaaaaa
a.aaa.aa
aaaaaaaa
accacaca
ccccaccc
cccccccc
cbccccbc
cccccccc",
    },
    // Dirt (sub-palette 2: c=dark brown bulk, b=light brown speckles).
    Tile {
        name: "Dirt",
        art: "\
cccccccc
cbccccbc
cccccccc
ccccbccc
cccccccc
cbccccbc
ccccbccc
cccccccc",
    },
    // Brick (sub-palette 1: a=red, c=dark red mortar).
    Tile {
        name: "Brick",
        art: "\
cccccccc
caaaaaca
caaaaaca
caaaaaca
cccccccc
aaacaaaa
aaacaaaa
aaacaaaa",
    },
    // Cloud left (sub-palette 0: a=white, b=light gray shade).
    Tile {
        name: "Cloud L",
        art: "\
........
...aaa..
..aaaaa.
.aaaaaaa
.aaaaaaa
.bbaaaaa
..bbbbba
.....bbb",
    },
    // Cloud right (sub-palette 0).
    Tile {
        name: "Cloud R",
        art: "\
........
.aaa....
aaaaa...
aaaaaaa.
aaaaaaa.
aaaaabb.
abbbbb..
bbb.....",
    },
    // Hill (sub-palette 2: a=green, b=light brown shade).
    Tile {
        name: "Hill",
        art: "\
........
....aa..
...aaaa.
..aaaaaa
..abaaaa
.abbabaa
.aaababa
aabbabba",
    },
    // Bush (sub-palette 2: a=green, c=dark brown outline).
    Tile {
        name: "Bush",
        art: "\
........
...aa...
..aaaa..
.aaaaac.
aaaaaaca
aaaaacca
aaaaacca
acacacac",
    },
    // Q Block (sub-palette 1: a=red frame, b=peach face, c=dark red).
    Tile {
        name: "Q Block",
        art: "\
cccccccc
caaaaaac
cabbbbac
cabccbac
cabcbbac
cabbbbac
caaaaaac
cccccccc",
    },
    // Sky (all transparent — renders as the universal bg colour).
    Tile {
        name: "Sky (blank)",
        art: "\
........
........
........
........
........
........
........
........",
    },
    // ── HUD glyphs (sprite-only; palette sp0: a=red, c=white) ──
    // Each digit is a 4-wide outline centred in an 8×8 cell and
    // drawn in white ('c') so it reads crisply over the sky
    // backdrop at the top of the playfield. The compiler treats
    // '.' as transparent for sprites, so the sky shows through.
    Tile {
        name: "Digit 0",
        art: "\
........
..cccc..
..c..c..
..c..c..
..c..c..
..c..c..
..cccc..
........",
    },
    Tile {
        name: "Digit 1",
        art: "\
........
...cc...
..ccc...
...cc...
...cc...
...cc...
..cccc..
........",
    },
    Tile {
        name: "Digit 2",
        art: "\
........
..cccc..
.....c..
....cc..
...cc...
..cc....
..cccc..
........",
    },
    Tile {
        name: "Digit 3",
        art: "\
........
..cccc..
.....c..
...ccc..
.....c..
.....c..
..cccc..
........",
    },
    Tile {
        name: "Digit 4",
        art: "\
........
..c..c..
..c..c..
..cccc..
.....c..
.....c..
.....c..
........",
    },
    Tile {
        name: "Digit 5",
        art: "\
........
..cccc..
..c.....
..cccc..
.....c..
..c..c..
..cccc..
........",
    },
    Tile {
        name: "Digit 6",
        art: "\
........
..cccc..
..c.....
..cccc..
..c..c..
..c..c..
..cccc..
........",
    },
    Tile {
        name: "Digit 7",
        art: "\
........
..cccc..
.....c..
....c...
...c....
..c.....
..c.....
........",
    },
    Tile {
        name: "Digit 8",
        art: "\
........
..cccc..
..c..c..
..cccc..
..c..c..
..c..c..
..cccc..
........",
    },
    Tile {
        name: "Digit 9",
        art: "\
........
..cccc..
..c..c..
..cccc..
.....c..
.....c..
..cccc..
........",
    },
    // Small red heart for the lives readout. Uses 'a' (red) so the
    // shape pops against the sky and matches the cap/brick red.
    Tile {
        name: "Heart",
        art: "\
........
.aa..aa.
aaaaaaaa
aaaaaaaa
.aaaaaa.
..aaaa..
...aa...
........",
    },
    // Sprite-0 hit pair — two single-pixel tiles whose one opaque
    // pixel sits at row 7 col 3 (sprite side) and row 0 col 3 (bg
    // side). OAM slot 0 gets `Sprite 0 anchor` at (248, 8) and NT
    // (col 31, row 2) gets `BG anchor`, so both opaque pixels
    // land at screen (251, 16) — the first scanline of the
    // playfield, one scanline below the HUD row. The PPU's
    // sprite-0 hit fires at dot 251 of scanline 16, `$2005`
    // writes from `sprite_0_split` land in HBLANK, and the
    // horizontal-scroll reload for scanline 17 latches the
    // playfield's `camera_x` without touching scanlines 8-15
    // (where the HUD glyphs live). A hit on scanline 15 itself
    // would smear the bottom row of every HUD glyph across the
    // split in jsnes. Both tiles are transparent everywhere
    // except that one pixel, so the only BG footprint is a
    // single dot at (251, 16) — inside jsnes's right-edge
    // overscan, invisible in the committed golden.
    Tile {
        name: "Sprite 0 anchor",
        art: "\
........
........
........
........
........
........
........
...c....",
    },
    Tile {
        name: "BG anchor",
        art: "\
...c....
........
........
........
........
........
........
........",
    },
];

// ── Named CHR tile indices used by the nametable layout below ──
// (Player/enemy/coin tile indices are referenced by name only in
// the .ne file's `draw` statements, not by the nametable here, so
// the nametable-only constants live here.)
const GRASS: u8 = 7;
const DIRT: u8 = 8;
const BRICK: u8 = 9;
const CLOUD_L: u8 = 10;
const CLOUD_R: u8 = 11;
const HILL: u8 = 12;
const BUSH: u8 = 13;
const QBLOCK: u8 = 14;
const SKY: u8 = 15;

/// Validate that a tile's ASCII art is well-formed (8 rows × 8 cols,
/// only the legal `.abc` characters). Pixel→CHR encoding now happens
/// inside the `NEScript` parser when it sees the `pixels:` block, so
/// this generator's job is just to make sure the strings we paste
/// are syntactically valid.
fn validate_tile_art(name: &str, art: &str) {
    let rows: Vec<&str> = art.lines().filter(|l| !l.is_empty()).collect();
    assert_eq!(
        rows.len(),
        8,
        "tile '{name}': expected 8 rows, got {}",
        rows.len()
    );
    for (y, row) in rows.iter().enumerate() {
        assert_eq!(
            row.len(),
            8,
            "tile '{name}' row {y}: expected 8 cols, got {row:?}"
        );
        for ch in row.chars() {
            assert!(
                matches!(ch, '.' | 'a' | 'b' | 'c'),
                "tile '{name}' row {y}: invalid character '{ch}'"
            );
        }
    }
}

/// Build a 32×30 nametable for a static Mario-ish level vista.
/// Horizontal scrolling pans this single nametable via `scroll()`,
/// so it only needs to look interesting at any X offset.
fn build_nametable() -> [u8; 960] {
    let mut nt = [SKY; 960];
    let set = |nt: &mut [u8; 960], y: usize, x: usize, t: u8| {
        nt[y * 32 + x] = t;
    };

    // Row 5 & 6: two clouds at different X positions for parallax feel.
    for &cx in &[4usize, 20] {
        set(&mut nt, 5, cx, CLOUD_L);
        set(&mut nt, 5, cx + 1, CLOUD_R);
    }
    set(&mut nt, 6, 12, CLOUD_L);
    set(&mut nt, 6, 13, CLOUD_R);

    // Row 15: a suspended brick platform with a Q-block in the middle.
    for x in 6..=9 {
        let t = if x == 8 { QBLOCK } else { BRICK };
        set(&mut nt, 15, x, t);
    }
    for x in 18..=20 {
        set(&mut nt, 15, x, BRICK);
    }

    // Row 20: hills sitting behind the grass line.
    for x in 2..=4 {
        set(&mut nt, 20, x, HILL);
    }
    for x in 22..=25 {
        set(&mut nt, 20, x, HILL);
    }

    // Row 21: bushes on top of the grass.
    for x in 10..=12 {
        set(&mut nt, 21, x, BUSH);
    }
    for x in 27..=28 {
        set(&mut nt, 21, x, BUSH);
    }

    // Row 22: grass top — a full horizontal line.
    for x in 0..32 {
        set(&mut nt, 22, x, GRASS);
    }

    // Row 23-29: dirt rows with a few buried bricks for texture.
    for y in 23..30 {
        for x in 0..32 {
            set(&mut nt, y, x, DIRT);
        }
    }
    for &(y, x) in &[(24usize, 5usize), (25, 11), (24, 18), (25, 24), (23, 30)] {
        set(&mut nt, y, x, BRICK);
    }

    nt
}

/// Build a 64-byte attribute table that pairs every 2×2 metatile
/// with a background sub-palette.
///
/// The attribute table covers a 16×15 grid of 16×16 metatiles. Each
/// byte encodes 4 quadrants (top-left, top-right, bottom-left,
/// bottom-right) of a 32×32-pixel "super-metatile" with 2 bits
/// apiece (palette index 0..3). For this demo we simply pick a
/// sub-palette per screen row region:
/// - top region (sky): sub-palette 0
/// - mid region (hills/blocks): sub-palette 1
/// - ground region (grass/dirt): sub-palette 2
fn build_attributes() -> [u8; 64] {
    let mut attr = [0u8; 64];
    // The attribute table is 8×8 bytes. Row `ay` covers nametable
    // rows 4*ay..4*ay+3. Palette layout:
    //   rows 0-11 (ay 0-2): sub-palette 0 (sky/clouds: whites)
    //   rows 12-15 (ay 3):  sub-palette 1 (brick/Q-block row)
    //   rows 16-19 (ay 4):  sub-palette 0 (more sky above the hills)
    //   rows 20-29 (ay 5-7): sub-palette 2 (grass/hills/bushes/dirt)
    for ay in 0..8 {
        let pal: u8 = match ay {
            0..=2 => 0,
            3 => 1,
            4 => 0,
            _ => 2, // 5, 6, 7
        };
        let quad = pal & 0b11;
        let byte = quad | (quad << 2) | (quad << 4) | (quad << 6);
        for ax in 0..8 {
            attr[ay * 8 + ax] = byte;
        }
    }
    attr
}

fn main() {
    // ── CHR tiles as pixel-art strings ──────────────────────────
    //
    // `NEScript`'s `sprite Name { pixels: [...] }` accepts one string
    // per pixel row; the parser splits the grid into 8×8 tiles in
    // row-major reading order, so emitting each 8-row tile
    // sequentially (stacked vertically, 1 tile wide × 15 tiles tall)
    // produces CHR tile indices 1..15 in the same order as the
    // TILES array.
    println!("// ── CHR tiles (paste into sprite Tileset {{ pixels: [...] }}) ──");
    println!("    pixels: [");
    for (i, tile) in TILES.iter().enumerate() {
        validate_tile_art(tile.name, tile.art);
        let tile_idx = i + 1;
        println!("        // tile {tile_idx}: {}", tile.name);
        for row in tile.art.lines().filter(|l| !l.is_empty()) {
            println!("        \"{row}\",");
        }
    }
    println!("    ]\n");

    // ── Background tilemap via legend + map form ────────────────
    //
    // Each distinct nametable tile gets one easy-to-read legend
    // character. `.` is the most common (sky), so use it for the
    // default fill to keep the `map:` strings tidy. The compiler
    // validates every character — any typo in the rows below is
    // caught by the parser rather than by a render bug at runtime.
    println!("// ── Nametable (paste into background Level {{ legend/map/palette_map }}) ──");
    println!("    legend {{");
    println!("        \".\": 15   // sky (blank)");
    println!("        \"<\": 10   // cloud left half");
    println!("        \">\": 11   // cloud right half");
    println!("        \"#\": 9    // brick");
    println!("        \"Q\": 14   // question block");
    println!("        \"^\": 12   // hill silhouette");
    println!("        \"*\": 13   // bush");
    println!("        \"=\": 7    // grass top");
    println!("        \"%\": 8    // dirt");
    println!("    }}");
    println!();
    println!("    map: [");
    let nt = build_nametable();
    assert_eq!(nt.len(), 960);
    let legend = legend_char_for;
    for row in 0..30 {
        let mut s = String::from("        \"");
        for col in 0..32 {
            s.push(legend(nt[row * 32 + col]));
        }
        s.push_str("\",");
        println!("{s}");
    }
    println!("    ]\n");

    // ── Palette map (auto-packs the 64-byte attribute table) ────
    //
    // `palette_map:` is a 16-wide grid of sub-palette digits (one
    // per 16×16 metatile). The parser packs pairs of rows into the
    // 8×8 attribute table automatically, so we emit the metatile
    // grid directly and skip the awkward `(br<<6)|(bl<<4)|(tr<<2)|tl`
    // bit-packing the old raw-bytes form demanded.
    //
    // The attribute table covers 16 metatile rows (8 attr rows ×
    // 2 each); the last row sits below the visible 240-scanline
    // screen but the PPU still reads it, so we emit all 16 rows to
    // match whatever the original hand-packed attribute byte was.
    println!("// ── Attributes (paste into background Level {{ palette_map: [...] }}) ──");
    println!("    palette_map: [");
    let attr = build_attributes();
    for my in 0..16 {
        let mut s = String::from("        \"");
        for mx in 0..16 {
            // Recover the sub-palette index for metatile (mx, my)
            // from the packed attribute table. Each byte covers a
            // 2×2 metatile block at attr[(my/2)*8 + mx/2], with
            // quadrants laid out as BR BL TR TL in the high bits.
            let byte = attr[(my / 2) * 8 + mx / 2];
            let quadrant = match (mx % 2, my % 2) {
                (0, 0) => byte & 0b11,
                (1, 0) => (byte >> 2) & 0b11,
                (0, 1) => (byte >> 4) & 0b11,
                _ => (byte >> 6) & 0b11,
            };
            s.push(char::from(b'0' + quadrant));
        }
        s.push_str("\",");
        println!("{s}");
    }
    println!("    ]");
}

/// Map a CHR tile index back to its legend character in the
/// generated `map:` block. Must stay in sync with the `legend { ... }`
/// block printed by `main()`.
fn legend_char_for(tile: u8) -> char {
    match tile {
        15 => '.',
        10 => '<',
        11 => '>',
        9 => '#',
        14 => 'Q',
        12 => '^',
        13 => '*',
        7 => '=',
        8 => '%',
        other => panic!("no legend char for tile {other}"),
    }
}
