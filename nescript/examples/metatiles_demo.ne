// Metatiles + collision demo — shows the `metatileset` /
// `room` declarations, `paint_room` at reset, and
// `collides_at(x, y)` as a runtime query that actually
// changes observable behaviour.
//
// What the program does:
//
//   - Declares a `metatileset Blocks` with two 2×2 metatiles:
//     `id 0` = floor (CHR tile 0 everywhere, non-colliding)
//     `id 1` = wall  (CHR tile 0 everywhere, colliding)
//
//     Both metatiles use tile 0 in CHR (the built-in smiley) so
//     we don't need a sprite declaration just to author tile
//     data. The palette swap below is what visually distinguishes
//     floor from wall.
//
//   - Declares a `room Dungeon` whose 16×15 layout frames the
//     playfield with wall metatiles and leaves the interior as
//     floor. `paint_room Dungeon` at reset blits the expanded
//     32×30 nametable into NT 0 and installs the room's
//     collision bitmap pointer so `collides_at` can answer
//     queries against this room.
//
//   - A probe sprite marches right along row 9 starting at x=120.
//     Every frame the probe advances two pixels. Before drawing
//     the sprite we query `collides_at(probe_x + 8, probe_y)` —
//     the +8 puts the test point near the sprite's right edge.
//     When the query returns true (we've hit the right wall)
//     we flip `dx`, so the probe bounces back.
//
//     With dx=2 and start x=120, the right-edge hit fires around
//     frame 56 (probe_x reaches 232). The probe then bounces
//     back at -2 per frame, so by frame 180 (the harness golden
//     frame) it's well inside the playfield. A regression that
//     silently returned 0 from `collides_at` would leave the
//     probe stuck against the wall or wrapping the u8 x
//     coordinate — either way, the committed golden wouldn't
//     match.
//
// Build:  cargo run --release -- build examples/metatiles_demo.ne

game "Metatiles Demo" {
    mapper: NROM
}

metatileset Blocks {
    metatiles: [
        { id: 0, tiles: [0, 0, 0, 0], collide: false },
        { id: 1, tiles: [0, 0, 0, 0], collide: true  },
    ],
}

// 16×15 grid. `1` = wall (colliding), `0` = floor (free).
//
//     ┌────────────────┐  row 0
//     │wwwwwwwwwwwwwwww│  row 1-12 frame walls on the edges
//     │w..............w│  and leave the interior as floor
//     │w..............w│  tiles. Row 9 (the middle-ish)
//     │w..............w│  is where the probe walks.
//     │w..............w│
//     │w..............w│
//     │w..............w│
//     │w..............w│
//     │w..............w│
//     │w..............w│
//     │w..............w│
//     │wwwwwwwwwwwwwwww│
room Dungeon {
    metatileset: Blocks,
    layout: [
        // row 0 — top wall
        1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1,
        // rows 1..13 — side walls bracket 14 floor cells
        1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1,
        1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1,
        1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1,
        1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1,
        1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1,
        1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1,
        1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1,
        1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1,
        1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1,
        1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1,
        1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1,
        1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1,
        1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1,
        // row 14 — bottom wall
        1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1,
    ],
}

var probe_x: u8 = 120
var probe_y: u8 = 144   // roughly row 9 of the metatile grid
var dx: i8 = 2
var painted: u8 = 0

on frame {
    // Paint the room once on the first frame. Doing this inside
    // `on frame` (rather than an `on enter` handler) keeps the
    // example minimal and avoids a separate state.
    if painted == 0 {
        paint_room Dungeon
        painted = 1
    }

    // Move the probe two pixels per frame in whichever direction
    // `dx` points. Two explicit branches because i8 runtime
    // expressions don't compose directly with u8 assignment —
    // keeping the sign logic out of the IR is cleaner than
    // rigging up a cast chain.
    if dx == 2 {
        probe_x += 2
    }
    if dx == -2 {
        probe_x -= 2
    }

    // Check the pixel just ahead of the probe's facing side.
    // The probe is 8 pixels wide; testing at `probe_x + 8` is
    // the right-edge probe and at `probe_x - 1` is the
    // left-edge. Combined with the sprite width this means the
    // probe flips direction one pixel before it would visually
    // overlap the wall.
    if dx == 2 {
        if collides_at(probe_x + 8, probe_y) {
            dx = -2
        }
    }
    if dx == -2 {
        if collides_at(probe_x - 1, probe_y) {
            dx = 2
        }
    }

    draw Probe at: (probe_x, probe_y)
}

start Main
