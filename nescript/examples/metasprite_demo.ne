// Metasprite demo — declarative multi-tile sprite groups.
//
// The `metasprite` keyword bundles a list of (dx, dy, frame)
// offsets into one named entity. `draw Hero at: (x, y)` then
// expands to one OAM slot per tile, so user code stops having
// to hand-write the four `draw Tileset at: (x+8, y+8) frame:
// TILE_PLAYER_BR` calls that platformer.ne uses today. Each
// tile inherits the OAM-cursor allocator from the runtime, so
// metasprites compose with regular `draw` statements without
// any extra wiring.
//
// Build: cargo run -- build examples/metasprite_demo.ne

game "Metasprite Demo" {
    mapper: NROM
}

// 16×16 hero sprite drawn as ASCII pixel art. The parser splits
// it into four 8×8 tiles in row-major order: tile 0 = top-left,
// tile 1 = top-right, tile 2 = bottom-left, tile 3 = bottom-right.
// We refer to those four tiles by base offset below.
sprite Hero16 {
    pixels: [
        "..####....####..",
        ".######..######.",
        "###@##....##@###",
        "###@##....##@###",
        "################",
        "################",
        ".##############.",
        "..############..",
        "...##########...",
        "....########....",
        "....##....##....",
        "....##....##....",
        "....##....##....",
        "....##....##....",
        "...####..####...",
        "..######..######"
    ]
}

// Arrange Hero16's four tiles into a 16×16 metasprite. Each
// row in the metasprite block is logically one OAM slot; the
// `dx` / `dy` arrays carry the per-tile offset from the
// metasprite's anchor point and `frame` carries the tile index.
//
// `sprite: Hero16` resolves to the base tile index reserved by
// the asset resolver; the four entries below pick consecutive
// tiles starting at that base — i.e. the four 8×8 tiles the
// pixel-art block was sliced into.
metasprite Hero {
    sprite: Hero16
    dx:    [0, 8, 0, 8]
    dy:    [0, 0, 8, 8]
    frame: [0, 1, 2, 3]
}

var px: u8 = 120
var py: u8 = 96
var dir: u8 = 0  // 0 = right, 1 = left

on frame {
    // Bounce horizontally between two rails so the harness
    // captures movement at frame 180 regardless of which
    // direction we started in.
    if dir == 0 {
        px += 1
        if px == 200 {
            dir = 1
        }
    } else {
        px -= 1
        if px == 32 {
            dir = 0
        }
    }

    // One `draw Hero` expands to four `draw Hero16` calls under
    // the hood. Compare with the four-line sequence in
    // platformer.ne's `draw_player()` — same OAM layout, much
    // less typing.
    draw Hero at: (px, py)
}

start Main
