// PRNG demo — sprite positions driven by the runtime PRNG.
//
// Each frame draws four sprites at pseudorandom coordinates pulled
// from the Galois-LFSR `rand8()` intrinsic, plus one sprite whose
// (x, y) pair comes from a single `rand16()` draw. Exercises all
// three PRNG intrinsics (`rand8`, `rand16`, `seed_rand`) end-to-end.
// `seed_rand(0x1234)` on the first frame pins the sequence so the
// committed golden is deterministic.

game "PRNG Demo" {
    mapper: NROM
}

var seeded: u8 = 0

on frame {
    if seeded == 0 {
        // Pin the seed so the recording is deterministic. The
        // runtime forces bit 0 of the low byte high so a zero
        // seed doesn't stick the LFSR.
        seed_rand(0x1234)
        seeded = 1
    }

    // Four random sprites per frame. Each call pulls fresh
    // entropy from the shared PRNG state, so the positions
    // drift over time instead of staying fixed.
    var x1: u8 = rand8()
    var y1: u8 = rand8()
    draw Ball at: (x1, y1)

    var x2: u8 = rand8()
    var y2: u8 = rand8()
    draw Ball at: (x2, y2)

    // rand16() returns u16; truncate to u8 for the draw.
    var r: u16 = rand16()
    var x3: u8 = r as u8
    var y3: u8 = (r >> 8) as u8
    draw Ball at: (x3, y3)

    var x4: u8 = rand8()
    var y4: u8 = rand8()
    draw Ball at: (x4, y4)
}

start Main
