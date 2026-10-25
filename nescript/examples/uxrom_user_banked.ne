// UxROM User-Banked — first NEScript example to put real user code
// inside a switchable bank. The `bank Extras { fun ... }` block tells
// the linker that `step_animation` lives in the named PRG bank
// instead of the fixed bank; the IR codegen emits a
// `__tramp_step_animation` stub in the fixed bank, and every call
// from a state handler now goes through the trampoline (which
// selects bank 0 at $8000-$BFFF, JSRs the function, then restores
// the fixed bank before returning).
//
// UxROM is the friendliest mapper for this work because its
// `__bank_select` routine is a single bus-conflict-safe write to
// $FFF0; MMC1's serial shift register and MMC3's two-register dance
// would both work but add more moving parts to an already-large
// pipeline change.
//
// The example sweeps a smiley left-and-right entirely from inside
// the banked helper. The helper reads two globals (`px`, `dir`) and
// updates them in place — no parameters, no return value, so the
// fixed-bank call site is a single `JSR __tramp_step_animation`.
// The harness captures frame 180 somewhere along the sweep, so any
// regression in bank-switching, trampoline emission, or banked-stream
// assembly will flip the golden.
//
// Build: cargo run -- build examples/uxrom_user_banked.ne

game "UxROM User Banked" {
    mapper: UxROM
    mirroring: horizontal
}

// The banked helper drives `px` directly so the fixed-bank state
// handler is just `JSR __tramp_step_animation; draw Smiley`. `dir`
// is 0 while sweeping right and 1 while sweeping left.
var px: u8 = 110
var dir: u8 = 0

bank Extras {
    // Step the smiley one pixel each frame, bouncing off x = 110
    // and x = 150. The whole computation lives in the switchable
    // bank: nothing here references any fixed-bank function, so the
    // bank's instruction stream resolves cleanly during the linker's
    // two-pass assembly without needing a second trampoline.
    fun step_animation() {
        if dir == 0 {
            px = px + 1
            if px == 150 {
                dir = 1
            }
        } else {
            px = px - 1
            if px == 110 {
                dir = 0
            }
        }
    }
}

on frame {
    // Trampoline call: the codegen emits `JSR __tramp_step_animation`
    // because the function is tagged `bank: Some("Extras")`. The
    // trampoline lives in the fixed bank, switches to bank 0, JSRs
    // `__ir_fn_step_animation` at its $8000-window address, then
    // switches back before returning.
    step_animation()
    draw Smiley at: (px, 120)
}

start Main
