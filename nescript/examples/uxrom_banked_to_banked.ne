// UxROM Banked-to-Banked — first NEScript example to exercise a
// switchable-bank function calling *another* switchable-bank function.
//
// The previous user-banked example (`uxrom_user_banked.ne`) only put
// fixed → banked calls through the trampoline path; here `bank Logic`
// holds `step()` and `bank Helpers` holds `clamp()`, and `step` calls
// `clamp` once per frame. The codegen emits `JSR __tramp_clamp` from
// inside bank Logic, which lands in the fixed-bank trampoline that
// saves the current bank (Logic), switches to Helpers, runs the body,
// then restores Logic on the way out — see runtime/gen_bank_trampoline
// for the PHA/PLA implementation.
//
// The harness captures frame 180 somewhere along the sweep, so any
// regression in the trampoline's save/restore would either leave the
// wrong bank mapped at $8000 (subsequent sprite reads would corrupt)
// or crash before the OAM update happened.
//
// Build: cargo run -- build examples/uxrom_banked_to_banked.ne

game "UxROM Banked to Banked" {
    mapper: UxROM
    mirroring: horizontal
}

// Globals live in the fixed bank's RAM and are reachable from any
// bank via direct zero-page / absolute addressing — bank switching
// only affects the $8000-$BFFF code window.
var px: u8 = 80
var dir: u8 = 0  // 0 = sweep right, 1 = sweep left

bank Logic {
    // The "main" banked function. Lives in bank Logic and calls
    // into bank Helpers via the fixed-bank trampoline emitted
    // by the linker.
    fun step() {
        if dir == 0 {
            px = px + 1
        } else {
            px = px - 1
        }
        // Cross-bank call into Helpers. The codegen sees a
        // current_bank of "Logic" and a callee bank of "Helpers"
        // and emits `JSR __tramp_clamp` — the trampoline lives
        // in the fixed bank, saves the caller's bank
        // (ZP_BANK_CURRENT == Logic), switches to Helpers, runs
        // the body, then restores Logic before returning here.
        clamp()
    }
}

bank Helpers {
    // Bounce the sprite between two pixel rails. Self-contained
    // — only reads/writes the global zero-page slots, no calls
    // back out of the bank, so the trampoline never has to
    // recursively unwind a third level.
    fun clamp() {
        if px == 176 {
            dir = 1
        }
        if px == 80 {
            dir = 0
        }
    }
}

on frame {
    // Single fixed → banked trampoline call. Inside, `step` does a
    // banked → banked call into `clamp` — that second hop is the
    // path the new trampoline implementation enables.
    step()
    draw Smiley at: (px, 112)
}

start Main
