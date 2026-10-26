// sha256/sha_core.ne — SHA-256 block compression in NEScript.
//
// FIPS 180-4 §6.2 specifies a 256-bit hash computed over one or
// more 512-bit (= 64-byte) message blocks. The compression of a
// single block is the hot path; since our on-screen keyboard
// restricts the input to 16 characters, every message fits in
// one block after padding, so the driver below only needs to
// process one block per Enter press.
//
// Representation: every 32-bit word is held as four consecutive
// bytes, little-endian (LSB first). This choice lets the 6502
// do 32-bit arithmetic by chaining its native `ADC`, `EOR`,
// `AND`, `ROR`, and `LSR` instructions — each of which walks
// one byte per cycle group and pushes the carry into the next.
//
// Every primitive operates on byte offsets into one of three
// globally-visible byte arrays:
//     wk[64]  — scratch: a..h and T1/T2/Σ/tmp (see constants.ne)
//     w[256]  — 64 u32 message-schedule words, packed contig.
//     h_state[32] — 8 u32 persistent hash words
//
// K[i] and H_INIT[i] live in RAM as `var` arrays loaded from
// the init_array initialiser at reset time (see constants.ne).

// ── 32-bit byte primitives ──────────────────────────────────
//
// Every primitive reads its destination and source offsets
// via `{dst}` / `{src}` / `{w_ofs}` / … substitutions, which
// resolve to the analyzer's per-function local slots. The
// codegen's function prologue spills the `$04`/`$05` transport
// slots into those same addresses on entry, so the values are
// already live by the time the asm block runs.

// wk[dst..dst+4] = wk[src..src+4]
fun cp_wk(dst: u8, src: u8) {
    asm {
        LDX {dst}
        LDY {src}
        LDA {wk},Y
        STA {wk},X
        INX
        INY
        LDA {wk},Y
        STA {wk},X
        INX
        INY
        LDA {wk},Y
        STA {wk},X
        INX
        INY
        LDA {wk},Y
        STA {wk},X
    }
}

// wk[dst..dst+4] ^= wk[src..src+4]
fun xor_wk(dst: u8, src: u8) {
    asm {
        LDX {dst}
        LDY {src}
        LDA {wk},X
        EOR {wk},Y
        STA {wk},X
        INX
        INY
        LDA {wk},X
        EOR {wk},Y
        STA {wk},X
        INX
        INY
        LDA {wk},X
        EOR {wk},Y
        STA {wk},X
        INX
        INY
        LDA {wk},X
        EOR {wk},Y
        STA {wk},X
    }
}

// wk[dst..dst+4] &= wk[src..src+4]
fun and_wk(dst: u8, src: u8) {
    asm {
        LDX {dst}
        LDY {src}
        LDA {wk},X
        AND {wk},Y
        STA {wk},X
        INX
        INY
        LDA {wk},X
        AND {wk},Y
        STA {wk},X
        INX
        INY
        LDA {wk},X
        AND {wk},Y
        STA {wk},X
        INX
        INY
        LDA {wk},X
        AND {wk},Y
        STA {wk},X
    }
}

// wk[dst..dst+4] += wk[src..src+4]  (chained ADC for carry)
fun add_wk(dst: u8, src: u8) {
    asm {
        LDX {dst}
        LDY {src}
        CLC
        LDA {wk},X
        ADC {wk},Y
        STA {wk},X
        INX
        INY
        LDA {wk},X
        ADC {wk},Y
        STA {wk},X
        INX
        INY
        LDA {wk},X
        ADC {wk},Y
        STA {wk},X
        INX
        INY
        LDA {wk},X
        ADC {wk},Y
        STA {wk},X
    }
}

// wk[dst..dst+4] = ~wk[dst..dst+4]  (bitwise NOT, in place)
fun not_wk(dst: u8) {
    asm {
        LDX {dst}
        LDA {wk},X
        EOR #$FF
        STA {wk},X
        INX
        LDA {wk},X
        EOR #$FF
        STA {wk},X
        INX
        LDA {wk},X
        EOR #$FF
        STA {wk},X
        INX
        LDA {wk},X
        EOR #$FF
        STA {wk},X
    }
}

// Rotate wk[dst..dst+4] right by 1 bit, in place. Treat the
// 4-byte little-endian value as one 32-bit integer. A right-
// rotation pulls bit 0 of the LSB into bit 31 of the MSB. The
// ROR chain below first captures bit 0 of the LSB into the
// carry (via LSR A on a non-destructive copy), then runs ROR
// MSB, byte 2, byte 1, LSB in that order — each ROR pulls the
// previous byte's bit 0 into the next byte's bit 7.
fun rotr1_wk(dst: u8) {
    asm {
        LDX {dst}
        LDA {wk},X
        LSR A
        INX
        INX
        INX
        ROR {wk},X
        DEX
        ROR {wk},X
        DEX
        ROR {wk},X
        DEX
        ROR {wk},X
    }
}

// Rotate wk[dst..dst+4] right by 1 byte, in place.
//     new[0] = old[1], new[1] = old[2],
//     new[2] = old[3], new[3] = old[0]
fun byte_rotr_wk(dst: u8) {
    asm {
        LDX {dst}
        LDY {wk},X
        INX
        LDA {wk},X
        DEX
        STA {wk},X
        INX
        INX
        LDA {wk},X
        DEX
        STA {wk},X
        INX
        INX
        LDA {wk},X
        DEX
        STA {wk},X
        INX
        TYA
        STA {wk},X
    }
}

// Rotate wk[dst..dst+4] right by `n` bits.  Handles any n in
// 0..31 by first rotating whole bytes (each call is cheaper
// than 8 ROR chains) and then finishing with up to 7 single-
// bit ROR chains.
//
// The SHA-256 sigmas only need a fixed set of rotation amounts
// (2, 6, 7, 11, 13, 17, 18, 19, 22, 25), so the per-amount
// helpers below skip this loop's runtime byte/bit decomposition
// and unroll the right number of `byte_rotr_wk` / `rotr1_wk`
// calls. This `rotr_wk` wrapper stays available for the rare
// caller that needs a runtime amount.
fun rotr_wk(dst: u8, n: u8) {
    var rem: u8 = n
    while rem >= 8 {
        byte_rotr_wk(dst)
        rem -= 8
    }
    while rem > 0 {
        rotr1_wk(dst)
        rem -= 1
    }
}

// ── Per-amount rotate helpers ───────────────────────────────
//
// Each `rotr_wk_<N>` rotates wk[dst..dst+4] right by exactly N
// bits with no loop overhead. Calling these directly from the
// sigma helpers replaces ~80 cycles of `rem >= 8` / `rem > 0`
// loop bookkeeping with the bare sequence of byte + bit
// rotations the analyzer-level constant rotation always reduces
// to. Per SHA-256 block, ~45K cycles saved across 384 sigma
// rotations.

fun rotr_wk_2(dst: u8) {
    rotr1_wk(dst)
    rotr1_wk(dst)
}

fun rotr_wk_6(dst: u8) {
    rotr1_wk(dst)
    rotr1_wk(dst)
    rotr1_wk(dst)
    rotr1_wk(dst)
    rotr1_wk(dst)
    rotr1_wk(dst)
}

fun rotr_wk_7(dst: u8) {
    rotr1_wk(dst)
    rotr1_wk(dst)
    rotr1_wk(dst)
    rotr1_wk(dst)
    rotr1_wk(dst)
    rotr1_wk(dst)
    rotr1_wk(dst)
}

// 11 = 1 byte + 3 bits
fun rotr_wk_11(dst: u8) {
    byte_rotr_wk(dst)
    rotr1_wk(dst)
    rotr1_wk(dst)
    rotr1_wk(dst)
}

// 13 = 1 byte + 5 bits
fun rotr_wk_13(dst: u8) {
    byte_rotr_wk(dst)
    rotr1_wk(dst)
    rotr1_wk(dst)
    rotr1_wk(dst)
    rotr1_wk(dst)
    rotr1_wk(dst)
}

// 17 = 2 bytes + 1 bit
fun rotr_wk_17(dst: u8) {
    byte_rotr_wk(dst)
    byte_rotr_wk(dst)
    rotr1_wk(dst)
}

// 18 = 2 bytes + 2 bits
fun rotr_wk_18(dst: u8) {
    byte_rotr_wk(dst)
    byte_rotr_wk(dst)
    rotr1_wk(dst)
    rotr1_wk(dst)
}

// 19 = 2 bytes + 3 bits
fun rotr_wk_19(dst: u8) {
    byte_rotr_wk(dst)
    byte_rotr_wk(dst)
    rotr1_wk(dst)
    rotr1_wk(dst)
    rotr1_wk(dst)
}

// 22 = 2 bytes + 6 bits
fun rotr_wk_22(dst: u8) {
    byte_rotr_wk(dst)
    byte_rotr_wk(dst)
    rotr1_wk(dst)
    rotr1_wk(dst)
    rotr1_wk(dst)
    rotr1_wk(dst)
    rotr1_wk(dst)
    rotr1_wk(dst)
}

// 25 = 3 bytes + 1 bit
fun rotr_wk_25(dst: u8) {
    byte_rotr_wk(dst)
    byte_rotr_wk(dst)
    byte_rotr_wk(dst)
    rotr1_wk(dst)
}

// Shift wk[dst..dst+4] right by 1 bit (logical — top bit
// becomes 0).
fun shr1_wk(dst: u8) {
    asm {
        LDX {dst}
        INX
        INX
        INX
        LSR {wk},X
        DEX
        ROR {wk},X
        DEX
        ROR {wk},X
        DEX
        ROR {wk},X
    }
}

// Shift wk[dst..dst+4] right by 1 byte, in place.  The top
// byte becomes 0.
fun byte_shr_wk(dst: u8) {
    asm {
        LDX {dst}
        INX
        LDA {wk},X
        DEX
        STA {wk},X
        INX
        INX
        LDA {wk},X
        DEX
        STA {wk},X
        INX
        INX
        LDA {wk},X
        DEX
        STA {wk},X
        INX
        LDA #0
        STA {wk},X
    }
}

// Shift wk[dst..dst+4] right by `n` bits (logical). Generic
// runtime-amount form; the SHA-256 sigmas use the per-amount
// helpers below instead.
fun shr_wk(dst: u8, n: u8) {
    var rem: u8 = n
    while rem >= 8 {
        byte_shr_wk(dst)
        rem -= 8
    }
    while rem > 0 {
        shr1_wk(dst)
        rem -= 1
    }
}

// 3 bits — used by σ0(x) = ... ^ (x >> 3)
fun shr_wk_3(dst: u8) {
    shr1_wk(dst)
    shr1_wk(dst)
    shr1_wk(dst)
}

// 10 bits = 1 byte + 2 bits — used by σ1(x) = ... ^ (x >> 10)
fun shr_wk_10(dst: u8) {
    byte_shr_wk(dst)
    shr1_wk(dst)
    shr1_wk(dst)
}

// ── Cross-array primitives ──────────────────────────────────

// wk[dst..dst+4] = w[w_ofs..w_ofs+4]
fun cp_w_to_wk(dst: u8, w_ofs: u8) {
    asm {
        LDX {dst}
        LDY {w_ofs}
        LDA {w},Y
        STA {wk},X
        INX
        INY
        LDA {w},Y
        STA {wk},X
        INX
        INY
        LDA {w},Y
        STA {wk},X
        INX
        INY
        LDA {w},Y
        STA {wk},X
    }
}

// wk[dst..dst+4] += w[w_ofs..w_ofs+4]
fun add_w_to_wk(dst: u8, w_ofs: u8) {
    asm {
        LDX {dst}
        LDY {w_ofs}
        CLC
        LDA {wk},X
        ADC {w},Y
        STA {wk},X
        INX
        INY
        LDA {wk},X
        ADC {w},Y
        STA {wk},X
        INX
        INY
        LDA {wk},X
        ADC {w},Y
        STA {wk},X
        INX
        INY
        LDA {wk},X
        ADC {w},Y
        STA {wk},X
    }
}

// w[w_ofs..w_ofs+4] = wk[src..src+4]
fun cp_wk_to_w(w_ofs: u8, src: u8) {
    asm {
        LDX {src}
        LDY {w_ofs}
        LDA {wk},X
        STA {w},Y
        INX
        INY
        LDA {wk},X
        STA {w},Y
        INX
        INY
        LDA {wk},X
        STA {w},Y
        INX
        INY
        LDA {wk},X
        STA {w},Y
    }
}

// h_state[h_ofs..h_ofs+4] += wk[src..src+4]
fun add_wk_to_h(h_ofs: u8, src: u8) {
    asm {
        LDX {h_ofs}
        LDY {src}
        CLC
        LDA {h_state},X
        ADC {wk},Y
        STA {h_state},X
        INX
        INY
        LDA {h_state},X
        ADC {wk},Y
        STA {h_state},X
        INX
        INY
        LDA {h_state},X
        ADC {wk},Y
        STA {h_state},X
        INX
        INY
        LDA {h_state},X
        ADC {wk},Y
        STA {h_state},X
    }
}

// wk[dst..dst+4] += _K_BYTES[k_ofs..k_ofs+4]
fun add_k_to_wk(dst: u8, k_ofs: u8) {
    asm {
        LDX {dst}
        LDY {k_ofs}
        CLC
        LDA {wk},X
        ADC {_K_BYTES},Y
        STA {wk},X
        INX
        INY
        LDA {wk},X
        ADC {_K_BYTES},Y
        STA {wk},X
        INX
        INY
        LDA {wk},X
        ADC {_K_BYTES},Y
        STA {wk},X
        INX
        INY
        LDA {wk},X
        ADC {_K_BYTES},Y
        STA {wk},X
    }
}

// ── σ and Σ helpers ─────────────────────────────────────────
//
// Each Σ/σ function writes its 32-bit result at wk[OFS_SIG].
// OFS_TMP is used internally as scratch. Callers must not
// pass `src` == OFS_SIG / OFS_TMP.

// Σ0(src) = rotr(src, 2) ^ rotr(src, 13) ^ rotr(src, 22)
fun big_sigma0(src: u8) {
    cp_wk(OFS_SIG, src)
    rotr_wk_2(OFS_SIG)
    cp_wk(OFS_TMP, src)
    rotr_wk_13(OFS_TMP)
    xor_wk(OFS_SIG, OFS_TMP)
    cp_wk(OFS_TMP, src)
    rotr_wk_22(OFS_TMP)
    xor_wk(OFS_SIG, OFS_TMP)
}

// Σ1(src) = rotr(src, 6) ^ rotr(src, 11) ^ rotr(src, 25)
fun big_sigma1(src: u8) {
    cp_wk(OFS_SIG, src)
    rotr_wk_6(OFS_SIG)
    cp_wk(OFS_TMP, src)
    rotr_wk_11(OFS_TMP)
    xor_wk(OFS_SIG, OFS_TMP)
    cp_wk(OFS_TMP, src)
    rotr_wk_25(OFS_TMP)
    xor_wk(OFS_SIG, OFS_TMP)
}

// σ0(src) = rotr(src, 7) ^ rotr(src, 18) ^ (src >> 3)
fun small_sigma0(src: u8) {
    cp_wk(OFS_SIG, src)
    rotr_wk_7(OFS_SIG)
    cp_wk(OFS_TMP, src)
    rotr_wk_18(OFS_TMP)
    xor_wk(OFS_SIG, OFS_TMP)
    cp_wk(OFS_TMP, src)
    shr_wk_3(OFS_TMP)
    xor_wk(OFS_SIG, OFS_TMP)
}

// σ1(src) = rotr(src, 17) ^ rotr(src, 19) ^ (src >> 10)
fun small_sigma1(src: u8) {
    cp_wk(OFS_SIG, src)
    rotr_wk_17(OFS_SIG)
    cp_wk(OFS_TMP, src)
    rotr_wk_19(OFS_TMP)
    xor_wk(OFS_SIG, OFS_TMP)
    cp_wk(OFS_TMP, src)
    shr_wk_10(OFS_TMP)
    xor_wk(OFS_SIG, OFS_TMP)
}

// ── Block-level helpers ─────────────────────────────────────

// Copy H_INIT[0..32] into h_state[0..32]. Used at the start of
// every hash so the driver can be re-run on a new message
// after the user clears the input.
fun reset_hash_state() {
    var i: u8 = 0
    while i < 32 {
        h_state[i] = H_INIT[i]
        i += 1
    }
}

// Build the 64-byte padded message block directly into
// w[0..63]. `msg[0..msg_len]` is the ASCII input; padding
// follows FIPS 180-4 §5.1.1:
//
//     pad[0..msg_len]     = msg[0..msg_len]
//     pad[msg_len]        = 0x80
//     pad[msg_len+1..56]  = 0
//     pad[56..62]         = 0          (high 48 bits of length)
//     pad[62..64]         = message length in bits, big-endian
//
// Since msg_len ≤ 16 the bit length fits in 8 bits (max 128),
// so only the very last byte of the block is nonzero for the
// length field. The loader also byte-swaps each 4-byte word so
// our little-endian internal layout matches SHA-256's big-
// endian word order.
fun build_padded_block() {
    // Step 1: zero the whole block.
    var i: u8 = 0
    while i < 64 {
        w[i] = 0
        i += 1
    }

    // Step 2: copy the ASCII message bytes into the block,
    // reversing byte order within each 4-byte group so the
    // "big-endian word" becomes our "little-endian word". The
    // byte index inside each word flips: 0↔3, 1↔2, 2↔1, 3↔0.
    i = 0
    while i < msg_len {
        var word_idx: u8 = i & 0xFC                 // i rounded down to 4
        var byte_idx: u8 = i & 0x03                 // 0..3
        var w_ofs: u8 = word_idx + (3 - byte_idx)   // byte-swap within word
        w[w_ofs] = msg[i]
        i += 1
    }

    // Step 3: append the 0x80 end-of-message marker at the
    // byte-swapped position for `msg_len`.
    var pad_word: u8 = msg_len & 0xFC
    var pad_byte: u8 = msg_len & 0x03
    var pad_ofs: u8 = pad_word + (3 - pad_byte)
    w[pad_ofs] = 0x80

    // Step 4: write the 64-bit big-endian length into bytes
    // 56..63 of the block. The SHA-256 view puts the MSB at
    // b_56 and the LSB at b_63; since `msg_len` ≤ 16, the bit
    // length is ≤ 128 and fits in a single byte. That byte is
    // b_63, which under our byte-swap-within-word convention
    // lands at w[60] (= word 15 byte 0 = u32 LSB).
    w[60] = msg_len << 3
}

// ── Schedule and round steps ────────────────────────────────
//
// `schedule_one` computes w[i] from the earlier four entries;
// `round_one` runs one SHA-256 iteration against the current
// a..h at wk[0..31]. Both are written as plain NEScript so the
// compression driver can loop over them one step at a time
// between `wait_frame`s.

// Compute w[i] = σ1(w[i-2]) + w[i-7] + σ0(w[i-15]) + w[i-16].
// `w_byte` is the byte offset of w[i] inside the w[] array,
// i.e. `4 * i`.
fun schedule_one(w_byte: u8) {
    // Temp accumulator lives at OFS_T1. Seed with w[i-16].
    cp_w_to_wk(OFS_T1, w_byte - 64)            // w[i-16]
    add_w_to_wk(OFS_T1, w_byte - 28)           // + w[i-7]

    // Load w[i-15] into OFS_T2, then apply σ0 into OFS_SIG.
    cp_w_to_wk(OFS_T2, w_byte - 60)
    small_sigma0(OFS_T2)                       // SIG = σ0(T2)
    add_wk(OFS_T1, OFS_SIG)

    // Load w[i-2] into OFS_T2, then apply σ1 into OFS_SIG.
    cp_w_to_wk(OFS_T2, w_byte - 8)
    small_sigma1(OFS_T2)                       // SIG = σ1(T2)
    add_wk(OFS_T1, OFS_SIG)

    // Store T1 back into w[i].
    cp_wk_to_w(w_byte, OFS_T1)
}

// Ch(e, f, g) = (e & f) ^ (~e & g). Writes to wk[OFS_SIG].
// Uses wk[OFS_TMP] as scratch (clobbered).
fun ch_into_sig() {
    cp_wk(OFS_SIG, OFS_E)
    and_wk(OFS_SIG, OFS_F)                     // SIG = e & f
    cp_wk(OFS_TMP, OFS_E)
    not_wk(OFS_TMP)                            // TMP = ~e
    and_wk(OFS_TMP, OFS_G)                     // TMP = ~e & g
    xor_wk(OFS_SIG, OFS_TMP)                   // SIG = ch
}

// Maj(a, b, c) = (a & b) ^ (a & c) ^ (b & c). Writes to
// wk[OFS_SIG]. Uses wk[OFS_TMP] as scratch (clobbered).
fun maj_into_sig() {
    cp_wk(OFS_SIG, OFS_A)
    and_wk(OFS_SIG, OFS_B)                     // SIG = a & b
    cp_wk(OFS_TMP, OFS_A)
    and_wk(OFS_TMP, OFS_C)                     // TMP = a & c
    xor_wk(OFS_SIG, OFS_TMP)                   // SIG = (a&b) ^ (a&c)
    cp_wk(OFS_TMP, OFS_B)
    and_wk(OFS_TMP, OFS_C)                     // TMP = b & c
    xor_wk(OFS_SIG, OFS_TMP)                   // SIG = maj
}

// Run one SHA-256 compression round. `kw_byte` is the byte
// offset shared by K[i] and w[i] (both tables hold 32-bit
// words at 4 bytes each, so their i-th entries sit at byte
// 4*i).
fun round_one(kw_byte: u8) {
    // T1 = h + Σ1(e) + Ch(e,f,g) + K[i] + W[i]
    cp_wk(OFS_T1, OFS_H)
    big_sigma1(OFS_E)                          // SIG = Σ1(e)
    add_wk(OFS_T1, OFS_SIG)

    ch_into_sig()                              // SIG = ch
    add_wk(OFS_T1, OFS_SIG)

    add_k_to_wk(OFS_T1, kw_byte)               // T1 += K[i]
    add_w_to_wk(OFS_T1, kw_byte)               // T1 += W[i]

    // T2 = Σ0(a) + Maj(a,b,c). Compute Σ0(a) into SIG, stash
    // in T2, then replace SIG with Maj and add into T2.
    big_sigma0(OFS_A)                          // SIG = Σ0(a)
    cp_wk(OFS_T2, OFS_SIG)
    maj_into_sig()                             // SIG = maj
    add_wk(OFS_T2, OFS_SIG)

    // Shift registers: h=g, g=f, f=e, e=d+T1, d=c, c=b, b=a,
    // a=T1+T2. Done in an order that avoids stomping live
    // data (always write the later slot before reading the
    // earlier).
    cp_wk(OFS_H, OFS_G)
    cp_wk(OFS_G, OFS_F)
    cp_wk(OFS_F, OFS_E)
    cp_wk(OFS_E, OFS_D)
    add_wk(OFS_E, OFS_T1)
    cp_wk(OFS_D, OFS_C)
    cp_wk(OFS_C, OFS_B)
    cp_wk(OFS_B, OFS_A)
    cp_wk(OFS_A, OFS_T1)
    add_wk(OFS_A, OFS_T2)
}

// Initialise a..h from h_state. Called once before the 64
// rounds start (inside Computing's on_enter).
fun init_abcdefgh() {
    var i: u8 = 0
    while i < 32 {
        wk[i] = h_state[i]
        i += 1
    }
}

// Fold wk[A..H] back into h_state with eight 32-bit adds —
// the "H_i' = H_i + a_i" step at the end of block compression.
fun fold_abcdefgh() {
    add_wk_to_h(0,  OFS_A)
    add_wk_to_h(4,  OFS_B)
    add_wk_to_h(8,  OFS_C)
    add_wk_to_h(12, OFS_D)
    add_wk_to_h(16, OFS_E)
    add_wk_to_h(20, OFS_F)
    add_wk_to_h(24, OFS_G)
    add_wk_to_h(28, OFS_H)
}
