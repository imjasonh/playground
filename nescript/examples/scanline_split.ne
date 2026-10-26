// Scanline Split — demonstrates MMC3's per-scanline IRQ via an
// `on scanline(N)` handler. The handler runs at PPU scanline 120,
// roughly mid-screen, and changes the horizontal scroll register
// so the top half and bottom half appear to scroll independently.
// This is the classic "status bar + parallax" trick used in many
// NES games.
//
// Build: cargo run -- build examples/scanline_split.ne

game "Scanline Split" {
    mapper: MMC3
    mirroring: horizontal
}

var top_scroll:    u8 = 0
var bottom_scroll: u8 = 0
var px:            u8 = 120
var py:            u8 = 160

state Main {
    on enter {
        top_scroll = 0
        bottom_scroll = 0
        px = 120
        py = 160
    }

    on frame {
        // Drift the top layer left and the bottom layer right so
        // the split is easy to see when the example runs.
        top_scroll += 1
        bottom_scroll -= 1

        // Player on the bottom half.
        if button.right { px += 2 }
        if button.left  { px -= 2 }
        if button.up    { py -= 2 }
        if button.down  { py += 2 }

        // Top-half banner.
        draw Banner at: (40, 24)

        // Bottom-half player.
        draw Player at: (px, py)

        // Set scroll for the TOP half. The scanline handler will
        // overwrite this partway through the frame for the bottom
        // half. Without a handler call the PPU would use this one
        // value for the entire visible screen.
        scroll(top_scroll, 0)
    }

    // Fires ~halfway down the visible screen. MMC3's scanline IRQ
    // counts rendered lines and fires when the reload value
    // elapses; the compiler emits the reload + acknowledge glue.
    on scanline(120) {
        scroll(bottom_scroll, 0)
    }
}

start Main
