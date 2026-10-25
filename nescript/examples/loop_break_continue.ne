// Loop / Break / Continue — demonstrates `loop`, `break`, and
// `continue` via a linear scan that finds the first "hazard" the
// player is overlapping.
//
// NEScript's sprite allocator assigns a static OAM slot per `draw`
// statement at compile time, so a `draw` inside a loop body would
// reuse the same slot on every iteration. We instead use the loop
// to COMPUTE state — "is the player touching a hazard, and which
// one?" — and then fold that result into how (and whether) the
// single player sprite is drawn. The hazards themselves get one
// unrolled `draw` per slot so each hazard gets its own OAM entry.
//
// Features shown:
//   - `loop { ... }` as an infinite loop
//   - `break` to exit on first match
//   - `continue` to skip inactive slots
//   - array indexing with a loop-carried variable
//
// Build: cargo run -- build examples/loop_break_continue.ne

game "Loop Demo" {
    mapper: NROM
}

const NUM_HAZARDS: u8 = 4
const HIT_RADIUS:  u8 = 12

// Four hazard slots. `active` is 1 if the slot is live.
var active:   u8[4] = [1, 1, 0, 1]
var hazard_x: u8[4] = [40, 96, 160, 200]
var hazard_y: u8[4] = [60, 140, 100, 180]

var px: u8 = 120
var py: u8 = 120

// Search results, written by the loop each frame.
var hit:     u8 = 0    // 1 if the player is touching any hazard
var hit_idx: u8 = 0    // which slot was hit (only meaningful if hit == 1)

// Small absolute-difference helper. Saves lines at each call site.
// Not marked `inline`: the conditional early return is one of
// the shapes the inliner declines (W0110).
fun abs_diff(a: u8, b: u8) -> u8 {
    if a > b {
        return a - b
    }
    return b - a
}

on frame {
    // Player movement.
    if button.right { px += 1 }
    if button.left  { px -= 1 }
    if button.down  { py += 1 }
    if button.up    { py -= 1 }

    // Linear scan for the first active hazard the player is
    // touching. The loop exits via `break` on the first hit, or
    // by running i past the end.
    hit = 0
    var i: u8 = 0
    loop {
        if i >= NUM_HAZARDS {
            break
        }
        if active[i] == 0 {
            // Skip inactive slots — this is where `continue`
            // shines: the increment and re-test happen at the top.
            i += 1
            continue
        }

        var dx: u8 = abs_diff(px, hazard_x[i])
        var dy: u8 = abs_diff(py, hazard_y[i])
        if dx < HIT_RADIUS {
            if dy < HIT_RADIUS {
                hit = 1
                hit_idx = i
                break
            }
        }
        i += 1
    }

    // One draw per hazard slot — unrolled so each sprite gets its
    // own static OAM entry. Inactive slots draw off-screen ($FE)
    // so they don't flicker the visible ones.
    if active[0] == 1 {
        draw Hazard at: (hazard_x[0], hazard_y[0])
    }
    if active[1] == 1 {
        draw Hazard at: (hazard_x[1], hazard_y[1])
    }
    if active[2] == 1 {
        draw Hazard at: (hazard_x[2], hazard_y[2])
    }
    if active[3] == 1 {
        draw Hazard at: (hazard_x[3], hazard_y[3])
    }

    // The player sprite reflects the collision state: when hit,
    // draw a "bang" marker above the player head. The `hit_idx`
    // is unused visually but proves the loop ran to completion.
    draw Player at: (px, py)
    if hit == 1 {
        draw Spark at: (px, py - 8)
    }
}

start Main
