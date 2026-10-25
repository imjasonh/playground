// CNROM (mapper 3) demo — fixed 32 KB PRG, switchable 8 KB CHR.
// Single-bank CNROM exercises the mapper reset, header emission,
// and compatible runtime — functionally equivalent to NROM but
// with a different iNES mapper number.

game "CNROM Demo" {
    mapper: CNROM
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
