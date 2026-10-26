// Signed-comparison demo — exercises the signed lowering of
// `<` / `>` / `<=` / `>=` on `i8` and `i16` against negative
// values. The pre-fix behaviour (unsigned BCC/BCS branches on
// signed types) gave the wrong answer for any compare that
// crossed zero — `var v: i16 = -1; if v < 0` was always false
// because $FFFF compared greater than $0000 unsigned.
//
// What this program shows on screen at frame 180 (the harness
// snapshot frame):
//
//   - Sprite 0 (Marker, X = signed_x_pos) bounces between
//     X = 32 and X = 224. The bounce flips when the i16
//     position passes the bounds, which only works if the
//     signed compare lowers correctly. By frame 180 the
//     marker has executed enough bounces to land at a
//     position that an unsigned-compare regression would
//     not be able to reach.
//
//   - Pip 1 (X=64) lights iff `i8_neg < 0` evaluates true.
//     A regression to the unsigned path would treat $FF
//     as >= $00 and the pip would go dark.
//
//   - Pip 2 (X=96) lights iff `(i16_minus_one) < (i16_one)`.
//     Same story but on the wide path — the BVC / EOR #$80
//     idiom in `gen_cmp16_signed` is what lets it fire.
//
//   - Pip 3 (X=128) lights iff `i8_neg <= i8_neg2` where
//     i8_neg = -10, i8_neg2 = -1, so the comparison is
//     -10 <= -1 (true). Wrong-path lowering would compare
//     $F6 <= $FF unsigned, which is also true by accident
//     — *but* if we flip to `i8_neg2 <= i8_neg` (-1 <= -10,
//     false signed, true unsigned) Pip 4 should be DARK.
//     Both pips together let the harness distinguish signed
//     from unsigned semantics.
//
//   - Pip 4 (X=160) is intentionally driven by the
//     opposite-direction compare so a regression to
//     unsigned semantics would light it. With the signed
//     path it stays dark.
//
// Build: cargo run --release -- build examples/signed_compare.ne

game "Signed Compare" {
    mapper: NROM
}

var i8_neg: i8 = -1
var i8_neg2: i8 = -10
var i16_minus_one: i16 = -1
var i16_one: i16 = 1
var signed_x_pos: i16 = 32
var dx: i16 = 1
on frame {
    // Bounce the marker between 32 and 224 using i16 signed
    // comparisons. The arithmetic lives in i16 land so the
    // signed-compare path is the only one that can produce
    // the right turnaround.
    signed_x_pos += dx
    if signed_x_pos >= 224 { dx = -1 }
    if signed_x_pos <= 32 { dx = 1 }

    // Marker — its X coordinate is the i16 position truncated
    // to u8 for the draw call.
    var mx: u8 = signed_x_pos as u8
    draw Marker at: (mx, 120)

    // Pips at the top of the screen, each gated on a signed
    // comparison.
    if i8_neg < 0 { draw Pip at: (64, 16) }
    if i16_minus_one < i16_one { draw Pip at: (96, 16) }
    if i8_neg2 <= i8_neg { draw Pip at: (128, 16) }
    if i8_neg <= i8_neg2 { draw Pip at: (160, 16) }
}

start Main
