// pong/rng.ne — 8-bit Galois LFSR PRNG.
//
// Classic maximal-period 8-bit Galois LFSR: shift right and XOR in
// the tap mask 0xB8 whenever the LSB was 1. The sequence visits
// every non-zero 8-bit value exactly once over 255 calls, which
// is enough randomness for serve-direction jitter, powerup kind
// selection, and AI reaction noise.

// Advance the LFSR by one step and return the new byte.
fun rng_next() -> u8 {
    var s: u8 = rng_state
    var lsb: u8 = s & 1
    s = s >> 1
    if lsb == 1 {
        s = s ^ 0xB8
    }
    rng_state = s
    return s
}

// Seed the LFSR. 0 is a degenerate state (the LFSR stays at 0
// forever), so we coerce zero seeds to 1.
fun rng_seed(s: u8) {
    if s == 0 {
        rng_state = 1
    } else {
        rng_state = s
    }
}
