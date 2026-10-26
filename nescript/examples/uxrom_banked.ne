// UxROM Banked — smallest possible UxROM game that exercises the
// bank-switching linker path. UxROM pins the last PRG bank at
// $C000-$FFFF and lets the $8000-$BFFF window hold any of the
// other 16 KB banks. NEScript currently places all user code in
// the fixed bank and leaves the declared banks as empty 16 KB
// payload slots, so this example serves as a smoke test for the
// linker layout + `__bank_select` subroutine emission rather than
// for cross-bank calls.
//
// Build: cargo run -- build examples/uxrom_banked.ne

game "UxROM Banked" {
    mapper: UxROM
    mirroring: horizontal
}

// Four declared PRG banks -> five-bank ROM (4 switchable + 1 fixed).
// The linker places each declared bank as a $FF-padded 16 KB slot
// in physical-order bank 0, 1, 2, 3, and emits the fixed bank last
// as bank 4.
bank World1: prg
bank World2: prg
bank World3: prg
bank World4: prg

var px: u8 = 120
var py: u8 = 112
var tick: u8 = 0

on frame {
    // Auto-animate so the golden comparison has a stable motion
    // pattern to match. Ticking px on every frame exercises the
    // main loop, and the wrap at 240 keeps the sprite on-screen.
    tick += 1
    if tick > 59 {
        tick = 0
    }

    if button.right { px += 1 }
    if button.left  {
        if px > 1 { px -= 1 }
    }
    if button.down  { py += 1 }
    if button.up    {
        if py > 1 { py -= 1 }
    }

    draw Smiley at: (px, py)
}

start Main
