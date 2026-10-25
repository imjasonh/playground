// war/rng.ne — 8-bit Galois LFSR pseudo-random number generator.
//
// A classic taps = 0xB8 Galois LFSR: on every call, shift the
// state right by one and XOR with the taps polynomial if the old
// low bit was 1. The period is 255 (all non-zero states), which
// is plenty for a card shuffle.
//
// The state lives in the global `rng_state` byte declared in
// war/state.ne. Seeded from a running tick counter on title exit
// (so the jsnes golden harness gets a deterministic shuffle).

// Advance the LFSR one step and return the new state. Every caller
// treats the return value as the next random byte.
fun rand_u8() -> u8 {
    var s: u8 = rng_state
    var lsb: u8 = s & 1
    s = s >> 1
    if lsb != 0 {
        s = s ^ 0xB8
    }
    // Guard against the degenerate all-zero state: if we ever
    // roll into zero the LFSR is stuck, so reseed from a fixed
    // non-zero constant. In practice this only happens on a
    // bad initial seed — we start at 0xA7 so the cycle stays
    // healthy.
    if s == 0 {
        s = 0xA7
    }
    rng_state = s
    return s
}

// Seed the LFSR from an arbitrary byte. Zero is remapped to the
// same fallback constant rand_u8() uses so the period stays 255.
fun rng_seed(seed: u8) {
    if seed == 0 {
        rng_state = 0xA7
    } else {
        rng_state = seed
    }
}
