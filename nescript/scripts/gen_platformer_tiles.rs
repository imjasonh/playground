//! Generator for the CHR tiles, tile-index constants, and nametable
//! used by `examples/platformer.ne`.
//!
//! Run with `cargo run --bin gen_platformer_tiles`. Paste the three
//! printed blocks into `platformer.ne`: the `pixels:` rows go in
//! `sprite Tileset`, the `const TILE_*` lines replace the tile index
//! constants, and the `legend` / `map:` / `palette_map:` blocks go in
//! `background Level`. A tile inside a `sprite` has no name, so this
//! program keeps the art, the indices, and the level map in one place.
//!
//! Art is ASCII where each character selects a sub-palette slot:
//!     '.' = colour 0  (universal background / transparent sprite pixel)
//!     'a' = colour 1
//!     'b' = colour 2
//!     'c' = colour 3
//!
//! A piece wider or taller than 8 pixels is split into 8×8 tiles in
//! row-major order, and each tile gets the matching entry of `names`.

/// One piece of art: `w` tiles wide, `names.len() / w` tiles tall.
struct Art {
    names: &'static [&'static str],
    w: usize,
    art: &'static str,
    /// Add a one-pixel drop shadow in colour 3 below and right of every
    /// colour-1 pixel. The font uses it so white text reads over sky.
    shadow: bool,
}

const fn art(names: &'static [&'static str], w: usize, art: &'static str) -> Art {
    Art {
        names,
        w,
        art,
        shadow: false,
    }
}

const fn font(names: &'static [&'static str], art: &'static str) -> Art {
    Art {
        names,
        w: 1,
        art,
        shadow: true,
    }
}

/// Every tile in CHR order. Tile 0 is the linker's built-in smiley,
/// so the first entry here lands at CHR index 1.
///
/// Sub-palettes (they must match `palette Main` in the example):
///   bg0 sky, clouds, text, HUD: a = white, b = light blue, c = black
///   bg1 bricks and ? blocks:    a = orange, b = black, c = dark orange
///   bg2 hills and bushes:       a = light green, b = green, c = dark green
///   bg3 grass and dirt:         a = light green, b = brown, c = dark orange
///   sp0 hero:   a = red, b = skin, c = brown
///   sp1 walker: a = dark orange, b = tan, c = black
///   sp2 coin:   a = yellow, b = dark orange, c = cream
///   sp3 text and heart: a = white, b = red, c = black
const ARTS: &[Art] = &[
    // ── Font: white glyphs with a black drop shadow ──
    font(
        &["DIGIT_0"],
        "\
..aaa...
.aa.aa..
aa...aa.
aa...aa.
aa...aa.
.aa.aa..
..aaa...
........",
    ),
    font(
        &["DIGIT_1"],
        "\
...aa...
..aaa...
...aa...
...aa...
...aa...
...aa...
.aaaaaa.
........",
    ),
    font(
        &["DIGIT_2"],
        "\
.aaaaa..
aa...aa.
.....aa.
...aaa..
.aaa....
aa......
aaaaaaa.
........",
    ),
    font(
        &["DIGIT_3"],
        "\
.aaaaaa.
....aa..
...aa...
....aa..
.....aa.
aa...aa.
.aaaaa..
........",
    ),
    font(
        &["DIGIT_4"],
        "\
...aaa..
..aaaa..
.aa.aa..
aa..aa..
aaaaaaa.
....aa..
....aa..
........",
    ),
    font(
        &["DIGIT_5"],
        "\
aaaaaa..
aa......
aaaaaa..
.....aa.
.....aa.
aa...aa.
.aaaaa..
........",
    ),
    font(
        &["DIGIT_6"],
        "\
..aaaa..
.aa.....
aa......
aaaaaa..
aa...aa.
aa...aa.
.aaaaa..
........",
    ),
    font(
        &["DIGIT_7"],
        "\
aaaaaaa.
aa...aa.
....aa..
...aa...
..aa....
..aa....
..aa....
........",
    ),
    font(
        &["DIGIT_8"],
        "\
.aaaaa..
aa...aa.
aa...aa.
.aaaaa..
aa...aa.
aa...aa.
.aaaaa..
........",
    ),
    font(
        &["DIGIT_9"],
        "\
.aaaaa..
aa...aa.
aa...aa.
.aaaaaa.
.....aa.
....aa..
.aaaa...
........",
    ),
    font(
        &["A"],
        "\
..aaa...
.aa.aa..
aa...aa.
aa...aa.
aaaaaaa.
aa...aa.
aa...aa.
........",
    ),
    font(
        &["E"],
        "\
aaaaaaa.
aa......
aa......
aaaaaa..
aa......
aa......
aaaaaaa.
........",
    ),
    font(
        &["F"],
        "\
aaaaaaa.
aa......
aa......
aaaaaa..
aa......
aa......
aa......
........",
    ),
    font(
        &["G"],
        "\
..aaaaa.
.aa.....
aa......
aa..aaa.
aa...aa.
.aa..aa.
..aaaaa.
........",
    ),
    font(
        &["L"],
        "\
aa......
aa......
aa......
aa......
aa......
aa......
aaaaaaa.
........",
    ),
    font(
        &["M"],
        "\
aa...aa.
aaa.aaa.
aaaaaaa.
aa.a.aa.
aa...aa.
aa...aa.
aa...aa.
........",
    ),
    font(
        &["P"],
        "\
aaaaaa..
aa...aa.
aa...aa.
aaaaaa..
aa......
aa......
aa......
........",
    ),
    font(
        &["R"],
        "\
aaaaaa..
aa...aa.
aa...aa.
aa..aaa.
aaaaa...
aa.aaa..
aa..aaa.
........",
    ),
    font(
        &["S"],
        "\
.aaaaa..
aa...aa.
aa......
.aaaaa..
.....aa.
aa...aa.
.aaaaa..
........",
    ),
    font(
        &["T"],
        "\
aaaaaa..
..aa....
..aa....
..aa....
..aa....
..aa....
..aa....
........",
    ),
    font(
        &["V"],
        "\
aa...aa.
aa...aa.
aa...aa.
aa...aa.
.aa.aa..
..aaa...
...a....
........",
    ),
    // ── Background (bg0): blank sky, a 3×2 cloud ──
    art(
        &["SKY"],
        1,
        "\
........
........
........
........
........
........
........
........",
    ),
    art(
        &[
            "CLOUD_TL", "CLOUD_TM", "CLOUD_TR", "CLOUD_BL", "CLOUD_BM", "CLOUD_BR",
        ],
        3,
        "\
.........aaaaa..........
.......aaaaaaaaa........
...aaa.aaaaaaaaaa.aaa...
..aaaaaaaaaaaaaaaaaaaa..
.aaaaaaaaaaaaaaaaaaaaaa.
.aaaaaaaaaaaaaaaaaaaaaa.
aaaaaaaaaaaaaaaaaaaaaaaa
aaaaaaaaaaaaaaaaaaaaaaaa
aaaaaaaaaaaaaaaaaaaaaaaa
aaaaaaaaaaaaaaaaaaaaaaab
.aaaaaaaaaaaaaaaaaaaaabb
.baaaaaaaaaaaaaaaaaaabb.
..bbaaaabbbaaaaaabbbbb..
...bbbbbb.bbbbbbbbbbb...
....bbbb...bbbb.bbbb....
........................",
    ),
    // ── Background (bg1): brick and ? block, one tile tall ──
    art(
        &["BRICK"],
        1,
        "\
aaaaaaab
cccccccb
cccccccb
bbbbbbbb
aaabaaaa
cccbcccc
cccbcccc
bbbbbbbb",
    ),
    art(
        &["QBLOCK"],
        1,
        "\
aaaaaaab
abaaaaba
aaabbaaa
aabaabaa
aaaabaaa
abaaaaba
aaaabaac
bbbbbbbb",
    ),
    // ── Background (bg2): hill pieces and a bush ──
    // A hill is a cap (HILL_TL, HILL_TR) over slopes (HILL_L, HILL_R)
    // around plain and spotted fill.
    art(
        &["HILL_TL", "HILL_TR"],
        2,
        "\
.....cccccc.....
...ccbbbbbbcc...
..cbbbbbbbbbbc..
.cbbbbbcbbbbbbc.
.cbbbbbbbbbbbbc.
cbbbbbbbbbbbbbbc
cbbbbbbbbbbbbbbc
bbbbbbbbbbbbbbbb",
    ),
    art(
        &["HILL_L", "HILL_FILL", "HILL_SPOT", "HILL_R"],
        4,
        "\
.......cbbbbbbbbbbbbbbbbc.......
......cbbbbbbbbbbbbbcbbbbc......
.....cbbbbbbbbbbbbbcccbbbbc.....
....cbbbbbbbbbbbbbbbcbbbbbbc....
...cbbbbbbbbbbbbbbbbbbbbbbbbc...
..cbbbbbbbbbbbbbbcbbbbbbbbbbbc..
.cbbbbbbbbbbbbbbcccbbbbbbbbbbbc.
cbbbbbbbbbbbbbbbbcbbbbbbbbbbbbbc",
    ),
    art(
        &["BUSH_L", "BUSH_M", "BUSH_R"],
        3,
        "\
.....cccc....cccc....ccc
...ccaaaacccaaaacc.ccaaa
..caaaaaaaaaaaaaaaccaaaa
.caaaabaaaaaaabaaaaaaaab
caaaabaaaaaaaabaaaaaaabb
caaaaaaaaabaaaaaaabaaabb
caabbaaaabbbaaaaabbbabbb
cabbbbbbbbbbbbbbbbbbbbbb",
    ),
    // ── Background (bg3): grass top and two kinds of dirt ──
    art(
        &["GRASS"],
        1,
        "\
a.aaa.aa
aaaaaaaa
aaaaaaaa
aaabaaaa
abbbbbab
bcbbcbbc
cccccccc
cccbcccc",
    ),
    art(
        &["DIRT"],
        1,
        "\
cccccccc
cbcccccc
cccccbcc
cccccccc
ccbccccc
cccccccb
cccccccc
cccbcccc",
    ),
    art(
        &["DIRT_ROCK"],
        1,
        "\
cccccccc
ccbbbccc
cbbabbcc
cbaabbbc
cbbbbbbc
ccbbbbcc
cccccccc
cccccbcc",
    ),
    // ── Sprite (sp0): the hero, facing right ──
    // One head over three bodies: standing, mid-step, and jumping.
    art(
        &["HERO_HL", "HERO_HR"],
        2,
        "\
......aaaaa.....
....aaaaaaaaa...
...aaaaaaaaaaa..
...aaaaaaaaaaaaa
...cccbbbbbb....
..ccbbbbcbbcb...
..ccbbbbcbbcb...
...cbbbbbbbbbb..",
    ),
    art(
        &["HERO_STAND_L", "HERO_STAND_R"],
        2,
        "\
....bbbbbbbb....
.....bbbbbb.....
....aaaaaaaa....
...aaaaaaaaab...
...baaaaaaaab...
....cccccccc....
....ccc..ccc....
...cccc..cccc...",
    ),
    art(
        &["HERO_STEP_L", "HERO_STEP_R"],
        2,
        "\
....bbbbbbbb....
.....bbbbbb.....
....aaaaaaaa....
...aaaaaaaaaab..
..baaaaaaaaa....
...cccccccccc...
..ccc......ccc..
.cccc......cccc.",
    ),
    art(
        &["HERO_JUMP_L", "HERO_JUMP_R"],
        2,
        "\
....bbbbbbbb..b.
.....bbbbbb..ab.
....aaaaaaaaaa..
..baaaaaaaaaa...
...aaaaaaaa.....
...ccccccccc....
..ccc....cccc...
.ccc.......ccc..",
    ),
    // ── Sprite (sp1): the walker. Its feet are lopsided, so drawing
    // it mirrored is the second walk frame. ──
    art(
        &["WALKER_TL", "WALKER_TR", "WALKER_BL", "WALKER_BR"],
        2,
        "\
......aaaa......
....aaaaaaaa....
...aaaaaaaaaa...
..acaaaaaaaaca..
.aaaccaaaaccaaa.
.aabbcbaabcbbaa.
aaabbcbaabcbbaaa
aaabbbbaabbbbaaa
aaaaaaaaaaaaaaaa
.aaaaaaaaaaaaaa.
...abbbbbbbba...
.....bbbbbb.....
....bbbbbbbbcc..
..cccbbbbbbcccc.
.ccccccbbbccccc.
.cccccc...cccc..",
    ),
    // The flattened walker is symmetric: draw SQUASH, then SQUASH
    // mirrored beside it.
    art(
        &["SQUASH"],
        1,
        "\
........
........
.....aaa
..aaaaaa
.aacccaa
aaaaaaaa
.ccccccb
cccccc..",
    ),
    // ── Sprite (sp2): an 8×16 coin in three turns of its spin,
    // and the small coin icon for the HUD ──
    art(
        &["COIN_FULL_T", "COIN_FULL_B"],
        1,
        "\
..bbbb..
.baaaab.
baacaaab
bacaaaab
bacaaaab
bacaaaab
bacaaaab
bacaaaab
bacaaaab
bacaaaab
bacaaaab
baaaaaab
baaaaaab
.baaaab.
..bbbb..
........",
    ),
    art(
        &["COIN_THIN_T", "COIN_THIN_B"],
        1,
        "\
...bb...
..baab..
..bcab..
..bcab..
..bcab..
..bcab..
..bcab..
..bcab..
..bcab..
..bcab..
..bcab..
..baab..
..baab..
..baab..
...bb...
........",
    ),
    art(
        &["COIN_EDGE_T", "COIN_EDGE_B"],
        1,
        "\
...bb...
...bb...
...bb...
...bb...
...bb...
...bb...
...bb...
...bb...
...bb...
...bb...
...bb...
...bb...
...bb...
...bb...
...bb...
........",
    ),
    art(
        &["COIN_ICON"],
        1,
        "\
..bbb...
.baaab..
bacaaab.
bacaaab.
bacaaab.
.baaab..
..bbb...
........",
    ),
    // ── Sprite (sp3): the lives heart ──
    art(
        &["HEART"],
        1,
        "\
.bb.bb..
bbbbbbb.
bbabbbbc
bbbbbbbc
.bbbbbc.
..bbbc..
...bc...
........",
    ),
    // ── Sprite-0 hit pair ──
    // OAM slot 0 holds SPRITE0_ANCHOR at (248, 15), so its one opaque
    // pixel draws at screen (251, 16). Map row 2 is a full row of
    // HUD_RULE, whose top pixel row is solid, so the hit fires on
    // scanline 16 whatever the camera. The scroll write lands partway
    // through that scanline, but every column of the rule looks the
    // same and the rest of row 2 is sky, so nothing visible moves.
    art(
        &["SPRITE0_ANCHOR"],
        1,
        "\
...c....
........
........
........
........
........
........
........",
    ),
    art(
        &["HUD_RULE"],
        1,
        "\
bbbbbbbb
........
........
........
........
........
........
........",
    ),
];

/// One 8×8 tile, as eight rows of eight `.abc` characters.
type TileRows = [[u8; 8]; 8];

/// Split every `Art` into named 8×8 tiles in CHR order.
fn tiles() -> Vec<(&'static str, TileRows)> {
    let mut out = Vec::new();
    for piece in ARTS {
        let rows: Vec<&[u8]> = piece.art.lines().map(str::as_bytes).collect();
        let h = piece.names.len() / piece.w;
        assert_eq!(piece.names.len(), piece.w * h, "{:?}", piece.names);
        assert_eq!(
            rows.len(),
            h * 8,
            "{:?}: expected {} rows",
            piece.names,
            h * 8
        );
        for (y, row) in rows.iter().enumerate() {
            assert_eq!(
                row.len(),
                piece.w * 8,
                "{:?} row {y}: expected {} cols",
                piece.names,
                piece.w * 8
            );
            for &ch in *row {
                assert!(
                    matches!(ch, b'.' | b'a' | b'b' | b'c'),
                    "{:?} row {y}: invalid character {:?}",
                    piece.names,
                    ch as char
                );
            }
        }
        for ty in 0..h {
            for tx in 0..piece.w {
                let mut tile = [[b'.'; 8]; 8];
                for (y, row) in tile.iter_mut().enumerate() {
                    row.copy_from_slice(&rows[ty * 8 + y][tx * 8..tx * 8 + 8]);
                }
                if piece.shadow {
                    let src = tile;
                    for y in 1..8 {
                        for x in 1..8 {
                            if src[y - 1][x - 1] == b'a' && src[y][x] == b'.' {
                                tile[y][x] = b'c';
                            }
                        }
                    }
                }
                out.push((piece.names[ty * piece.w + tx], tile));
            }
        }
    }
    out
}

/// The legend: one map character per background tile.
const LEGEND: &[(char, &str, &str)] = &[
    ('.', "SKY", "sky"),
    ('(', "CLOUD_TL", "cloud, top row"),
    ('-', "CLOUD_TM", ""),
    (')', "CLOUD_TR", ""),
    ('[', "CLOUD_BL", "cloud, bottom row"),
    ('_', "CLOUD_BM", ""),
    (']', "CLOUD_BR", ""),
    ('#', "BRICK", "brick (one-way platform)"),
    ('Q', "QBLOCK", "? block (one-way platform)"),
    ('{', "HILL_TL", "hill cap"),
    ('}', "HILL_TR", ""),
    ('/', "HILL_L", "hill slopes"),
    ('\\', "HILL_R", ""),
    ('^', "HILL_FILL", "hill fill"),
    ('o', "HILL_SPOT", "hill fill with spots"),
    ('<', "BUSH_L", "bush"),
    ('*', "BUSH_M", ""),
    ('>', "BUSH_R", ""),
    ('=', "GRASS", "grass top"),
    ('%', "DIRT", "dirt"),
    ('@', "DIRT_ROCK", "rock in the dirt"),
    ('0', "DIGIT_0", "HUD: score tens and ones"),
    ('3', "DIGIT_3", "HUD: lives"),
    ('~', "HUD_RULE", "HUD rule; the sprite-0 hit anchor"),
];

/// The 32×30 level. Horizontal mirroring repeats it as the camera
/// scrolls, so it loops every 256 pixels. Rows 8 and 11 stay sky: the
/// title screen writes its text there.
const MAP: [&str; 30] = [
    "................................",
    "....00....................3.....",
    "~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~",
    "..(-)..................(-)......",
    "..[_]........(-).......[_]......",
    ".............[_]................",
    "................................",
    "................................",
    "................................",
    "................................",
    "................................",
    "................................",
    "................................",
    "................................",
    "................................",
    "......##Q##........#Q#..........",
    "................................",
    "................................",
    "................................",
    "...{}...........................",
    "../^^\\..............{}..........",
    "./^o^^\\..<**>....../^o\\...<*>...",
    "================================",
    "%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%",
    "%%%%%@%%%%%%%%%%%%%@%%%%%%%%%%%%",
    "%%%%%%%%%%%%%@%%%%%%%%%%%%%%@%%%",
    "%%%@%%%%%%%%%%%%%%%%%%%@%%%%%%%%",
    "%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%",
    "%%%%%%%%%@%%%%%%%%%%%%%%%%%%%%%%",
    "%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%",
];

/// Sub-palette per 16×16 metatile row. The PPU reads all 16 attribute
/// rows, including the one below the visible screen.
const PALETTE_ROWS: [(u8, &str); 16] = [
    (0, "NT rows 0-1: HUD"),
    (0, "NT rows 2-11: sky, clouds, title text"),
    (0, ""),
    (0, ""),
    (0, ""),
    (0, ""),
    (0, "NT rows 12-13: sky"),
    (1, "NT rows 14-15: brick platforms"),
    (0, "NT rows 16-17: sky"),
    (2, "NT rows 18-21: hills and bushes"),
    (2, ""),
    (3, "NT rows 22-29: grass and dirt"),
    (3, ""),
    (3, ""),
    (3, ""),
    (3, "below the screen"),
];

fn main() {
    let tiles = tiles();
    let index_of = |name: &str| -> usize {
        1 + tiles
            .iter()
            .position(|(n, _)| *n == name)
            .unwrap_or_else(|| panic!("no tile named {name}"))
    };
    assert!(tiles.len() < 255, "too many tiles");

    println!("// ── CHR tiles (paste into sprite Tileset {{ pixels: [...] }}) ──");
    println!("    pixels: [");
    for (i, (name, rows)) in tiles.iter().enumerate() {
        println!("        // tile {}: {name}", i + 1);
        for (y, row) in rows.iter().enumerate() {
            let comma = if i + 1 == tiles.len() && y == 7 {
                ""
            } else {
                ","
            };
            println!("        \"{}\"{comma}", std::str::from_utf8(row).unwrap());
        }
    }
    println!("    ]\n");

    println!("// ── Tile indices (paste over the TILE_* constants) ──");
    for (i, (name, _)) in tiles.iter().enumerate() {
        println!("const TILE_{name}: u8 = {}", i + 1);
    }
    println!();

    println!("// ── Level (paste into background Level {{ legend / map / palette_map }}) ──");
    println!("    legend {{");
    for (ch, name, comment) in LEGEND {
        let key = if *ch == '\\' {
            "\\\\".to_string()
        } else {
            ch.to_string()
        };
        let idx = index_of(name);
        let comment = if comment.is_empty() {
            String::new()
        } else {
            format!("   // {comment}")
        };
        println!("        \"{key}\": {idx}{comment}");
    }
    println!("    }}\n");
    println!("    map: [");
    for (y, row) in MAP.iter().enumerate() {
        assert_eq!(row.chars().count(), 32, "map row {y}");
        for ch in row.chars() {
            assert!(
                LEGEND.iter().any(|(c, _, _)| *c == ch),
                "map row {y}: {ch:?} is not in the legend"
            );
        }
        let escaped = row.replace('\\', "\\\\");
        let comma = if y + 1 == MAP.len() { "" } else { "," };
        println!("        \"{escaped}\"{comma}");
    }
    println!("    ]\n");
    println!("    palette_map: [");
    for (y, (pal, comment)) in PALETTE_ROWS.iter().enumerate() {
        let row: String = std::iter::repeat_n(char::from(b'0' + pal), 16).collect();
        let comma = if y + 1 == PALETTE_ROWS.len() { "" } else { "," };
        let comment = if comment.is_empty() {
            String::new()
        } else {
            format!("   // {comment}")
        };
        println!("        \"{row}\"{comma}{comment}");
    }
    println!("    ]");
}
