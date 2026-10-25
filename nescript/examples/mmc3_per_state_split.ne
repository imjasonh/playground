// MMC3 Per-State Scanline Split — proves the compiler's per-state
// IRQ dispatch and reload logic. Two states each own their own
// `on scanline(N)` handler at a different scanline; pressing START
// transitions between them. Because the MMC3 IRQ latch is
// reloaded from the *current* state's scanline each frame (via
// the `__ir_mmc3_reload` helper), the visible split line moves
// when the state changes.
//
// What this exercises end-to-end:
//   - MMC3 scanline IRQ firing at the latched line
//   - `__ir_mmc3_reload` walking the dispatch table to pick the
//     latch value for the new state after a transition
//   - `__irq_user` dispatching to the right per-state handler
//   - scroll writes from inside an IRQ handler landing before the
//     PPU renders the next visible scanline
//
// Controls:
//   START — toggle between Upper-split and Lower-split states
//
// Build: cargo run -- build examples/mmc3_per_state_split.ne

game "MMC3 Split" {
    mapper: MMC3
    mirroring: horizontal
}

// Scroll values for the two halves of the screen. `frame_scroll`
// drifts every frame so the split is easy to see in motion — the
// top half scrolls right, the bottom scrolls left.
var top_scroll:    u8 = 0
var bottom_scroll: u8 = 0

// Tiny debouncer so one press of START doesn't cycle through the
// states multiple times per frame.
var debounce: u8 = 0

// Shared drift counter — primarily for observability (the split
// animation works from `top_scroll` / `bottom_scroll` directly).
var _frame_counter: u8 = 0

state Upper {
    on enter {
        // When we arrive, reset the scroll so the split is easy
        // to see from the first frame onward.
        top_scroll = 0
        bottom_scroll = 0
    }

    on frame {
        _frame_counter += 1
        top_scroll += 1
        bottom_scroll -= 1

        // Initial scroll for the TOP half. The scanline handler
        // below will rewrite scroll midway through the frame.
        scroll(top_scroll, 0)

        // Draw a marker at the top half and a player sprite in
        // the bottom half so the split position is visually
        // obvious.
        draw Marker at: (40, 40)
        draw Player at: (120, 140)

        if debounce > 0 {
            debounce -= 1
        }
        if button.start and debounce == 0 {
            transition Lower
            debounce = 30
        }
    }

    // Split at line 80 — the top 80 rows use `top_scroll`, the
    // rest use `bottom_scroll`.
    on scanline(80) {
        scroll(bottom_scroll, 0)
    }
}

state Lower {
    on enter {
        top_scroll = 0
        bottom_scroll = 0
    }

    on frame {
        _frame_counter += 1
        top_scroll += 1
        bottom_scroll -= 1

        scroll(top_scroll, 0)

        draw Marker at: (40, 40)
        draw Player at: (120, 140)

        if debounce > 0 {
            debounce -= 1
        }
        if button.start and debounce == 0 {
            transition Upper
            debounce = 30
        }
    }

    // Split at line 160 — lower split, so the top 160 rows use
    // `top_scroll` and only the last ~80 rows use `bottom_scroll`.
    on scanline(160) {
        scroll(bottom_scroll, 0)
    }
}

start Upper
