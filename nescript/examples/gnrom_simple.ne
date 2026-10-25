// GNROM (mapper 66) demo — 32 KB PRG page + 8 KB CHR bank in a
// single write to `$8000-$FFFF`. Bits 4-5 select the PRG page,
// bits 0-1 select the CHR bank. Single-page GNROM is functionally
// equivalent to AxROM at the PRG level; this example just exercises
// the reset-time init and iNES header emission.

game "GNROM Demo" {
    mapper: GNROM
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
