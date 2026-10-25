// AxROM (mapper 7) demo — single 32 KB PRG with single-screen
// mirroring. Most homebrew AxROM games have multiple 32 KB pages;
// this minimal demo runs in bank 0 of a 32 KB-padded ROM to
// exercise the mapper's reset, bank-select register, and iNES
// header emission.

game "AxROM Demo" {
    mapper: AxROM
}

var px: u8 = 120
var dx: u8 = 1

on frame {
    if dx == 1 {
        px += 1
        if px >= 240 { dx = 0 }
    } else {
        px -= 1
        if px == 0 { dx = 1 }
    }
    draw Ball at: (px, 100)
}

start Main
