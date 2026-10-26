// Function Chain — exercises a deep call graph with parameter
// passing and return values across multiple user functions.
//
// The analyzer caps call depth at 8 (hard NES stack limit for
// a cooperative compiler). This example chains five functions:
//
//   frame -> compute -> scale -> clamp -> fold -> taper
//
// Each function takes its argument through the calling
// convention and returns a value in A. The chained result is
// what drives the player sprite's X position on screen each
// frame.
//
// Parameters land at a non-uniform address set:
//   - The deepest callee (`taper`) is a leaf — it has no nested
//     `JSR` and can receive its arg in the `$04` transport slot
//     directly. Its body reads `$04` in place of a spill copy.
//   - Every other function (`compute`, `scale`, `clamp`, `fold`)
//     is non-leaf and uses the direct-write convention: each
//     caller stages the arg straight into the callee's
//     analyzer-allocated param slot before the `JSR`. No
//     transport, no prologue copy.
//
// What this exercises end-to-end:
//   - Five levels of nested `JSR` without stack corruption
//   - The hybrid leaf / non-leaf calling convention
//   - Return value propagation through A
//   - `fun ... -> u8 { return ... }` — the full typed-function
//     shape, including an early `return` inside an `if`
//   - Interaction of function calls with handler-local vars
//     (the `out` result ends up in a local that drives draw)
//
// Build: cargo run -- build examples/function_chain.ne

game "Fn Chain" {
    mapper: NROM
}

const SCREEN_MIN: u8 = 16
const SCREEN_MAX: u8 = 232

var tick: u8 = 0

// Level 5: final transform — fold the input by reflecting any
// overshoot back toward the middle. Pure function, returns u8.
fun taper(v: u8) -> u8 {
    if v > 200 {
        return 200
    }
    return v
}

// Level 4: fold — bias the input toward the screen center.
fun fold(v: u8) -> u8 {
    var biased: u8 = v
    if biased < SCREEN_MIN {
        biased = SCREEN_MIN
    }
    return taper(biased)
}

// Level 3: clamp to the visible screen band.
fun clamp(v: u8) -> u8 {
    if v > SCREEN_MAX {
        return fold(SCREEN_MAX)
    }
    return fold(v)
}

// Level 2: scale the tick into a pixel position. Uses a shift
// instead of multiply so we don't pull in the soft multiply.
fun scale(t: u8) -> u8 {
    return clamp(t << 1)
}

// Level 1: top of the call chain. Takes the raw frame counter,
// adds a small offset, and hands it to `scale`. The returned
// value is the player's X position.
fun compute(counter: u8) -> u8 {
    var shifted: u8 = counter
    shifted += 16
    return scale(shifted)
}

on frame {
    tick += 1

    // Single call site that triggers the whole chain. If any
    // link in the chain corrupts the param passing or stack,
    // the player sprite starts jittering or disappears.
    var x: u8 = compute(tick)

    // Player Y is fixed; X comes from the chain. Visually the
    // sprite sweeps across the screen as the chain holds.
    draw Player at: (x, 112)

    // Also draw a static reference marker so the smoke test
    // always has at least one visible sprite even if the chain
    // somehow returns 0.
    draw Marker at: (8, 8)
}

start Main
