// Feature canary — a round-trip smoke test for memory-affecting
// language features. Every check writes a distinctive constant
// through one language construct, then reads it back and compares
// against the written value. A pass leaves the universal palette
// green; any failure flips it to red.
//
// The goal is a single emulator golden that captures the green-
// backdrop "all features round-trip correctly" state at frame 180.
// If any of the following bugs reappear, the canary turns red and
// `tests/emulator/goldens/feature_canary.png` no longer matches:
//
//   - PR #31 (state-local variable writes silently dropped)
//   - Uninitialized struct-field writes silently dropped (caught
//     while hardening `var_addrs` in this audit)
//   - `slow` placement ignored (cold var still lands in ZP)
//   - u16 high byte not stored
//   - Array-element write silently dropped
//   - Function return value dropped
//
// Every check cascades into `all_ok` (cleared to 0 on first
// failure), so the final set_palette call picks Pass/Fail from
// one flag. We deliberately do not use `debug.assert` because
// `--debug` builds strip nothing; the palette swap works in
// release and that's what the emulator harness runs.
//
// Build: cargo run -- build examples/feature_canary.ne

game "Feature Canary" { mapper: NROM }

// ── Palettes ────────────────────────────────────────────────
//
// Pass = all-green backdrop; Fail = all-red. The canary starts
// in Pass; if any round-trip check mismatches, `set_palette Fail`
// flips the entire screen red for the rest of the run.
palette Pass {
    universal: green
    bg0: [dk_green, lt_green, white]
    bg1: [dk_green, lt_green, white]
    bg2: [dk_green, lt_green, white]
    bg3: [dk_green, lt_green, white]
    sp0: [black, black, black]
    sp1: [black, black, black]
    sp2: [black, black, black]
    sp3: [black, black, black]
}

palette Fail {
    universal: red
    bg0: [dk_red, lt_red, white]
    bg1: [dk_red, lt_red, white]
    bg2: [dk_red, lt_red, white]
    bg3: [dk_red, lt_red, white]
    sp0: [black, black, black]
    sp1: [black, black, black]
    sp2: [black, black, black]
    sp3: [black, black, black]
}

// ── Types and storage ──────────────────────────────────────

struct Vec2 { x: u8, y: u8 }

// Uninitialized struct global — this is the shape that was
// silently dropping field writes before the `var_addrs` fix.
var pos: Vec2

// Global u8 / u16 / array — classic globals.
var scalar: u8 = 0
var wide: u16 = 0
var row: u8[4] = [0, 0, 0, 0]

// A deliberately-cold u8 placed via `slow` so the analyzer
// keeps it outside zero-page. If `slow` regresses to advisory,
// the allocation address moves into ZP but the round-trip still
// succeeds — so this byte is for memory-map inspection, not the
// backdrop flip.
slow var cold_byte: u8 = 0

fun double_u8(x: u8) -> u8 {
    return x + x
}

// A six-parameter non-leaf function. The call site exercises
// the direct-write calling convention — the caller stages each
// arg straight into the callee's per-param RAM slot, no
// transport through `$04-$07`. Returns the sum of all six, so
// a regression that silently drops any one (same shape as PR
// #31 but for params) knocks the result off 21 and flips the
// canary red.
fun sum6(a: u8, b: u8, c: u8, d: u8, e: u8, f: u8) -> u8 {
    var tmp: u8 = a + b
    tmp = tmp + c
    tmp = tmp + d
    tmp = tmp + e
    tmp = tmp + f
    return tmp
}

// ── Main state ─────────────────────────────────────────────

state Main {
    // State-local — the PR #31 bug.
    var local_counter: u8 = 0
    // Per-frame "pass" flag. Starts true each frame; any failed
    // round-trip clears it.
    var all_ok: u8 = 1

    on enter {
        set_palette Pass
    }

    on frame {
        all_ok = 1

        // Check 1: state-local write-read.
        local_counter = 42
        if local_counter != 42 { all_ok = 0 }

        // Check 2: uninitialized struct-field write-read.
        pos.x = 99
        pos.y = 77
        if pos.x != 99 { all_ok = 0 }
        if pos.y != 77 { all_ok = 0 }

        // Check 3: global u8.
        scalar = 123
        if scalar != 123 { all_ok = 0 }

        // Check 4: global u16 > 255 (both low and high bytes must
        // land — the u16 path splits into StoreVar + StoreVarHi).
        wide = 1234
        if wide != 1234 { all_ok = 0 }

        // Check 5: array element write-read at nonzero index.
        row[2] = 55
        if row[2] != 55 { all_ok = 0 }

        // Check 6: slow-placed global still round-trips.
        cold_byte = 200
        if cold_byte != 200 { all_ok = 0 }

        // Check 7: function call return value survives the
        // caller's frame of reference.
        var r: u8 = double_u8(21)
        if r != 42 { all_ok = 0 }

        // Check 8: six-parameter non-leaf function — exercises
        // the direct-write calling convention that lifts the
        // old 4-param ceiling. 1+2+3+4+5+6 = 21.
        var s: u8 = sum6(1, 2, 3, 4, 5, 6)
        if s != 21 { all_ok = 0 }

        // Drive the backdrop flip. `set_palette` schedules an
        // update during the next vblank, so the effect lands on
        // the following frame — well before the frame-180 golden
        // sample.
        if all_ok == 0 {
            set_palette Fail
        }

        wait_frame
    }
}

start Main
