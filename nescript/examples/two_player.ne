// Two Player — proves the compiler can read both NES controllers.
//
// Player 1 input goes through `button.*` (the implicit default,
// equivalent to `p1.button.*`); player 2 input goes through
// `p2.button.*`. The language guide mentions both; until this
// example, no runtime test actually exercised player 2.
//
// What this exercises end-to-end:
//   - `p2.button.up/down/left/right/a` reads from the player-2
//     ZP slot ($08) rather than player 1 ($01)
//   - The runtime's NMI controller poll reads both $4016 and
//     $4017 per frame and shifts the bits into $01 and $08
//   - Two independently-controlled sprites sharing a frame
//     handler's OAM cursor
//
// Controls:
//   D-pad, A/B   — player 1 moves red sprite
//   p2.D-pad,    — player 2 moves blue sprite
//   p2.A/B       — p2 shoots "bullets" (visual marker)
//
// Build: cargo run -- build examples/two_player.ne

game "Two Player" {
    mapper: NROM
}

var p1x: u8 = 64
var p1y: u8 = 112
var p2x: u8 = 192
var p2y: u8 = 112

// A simple "shot" indicator for each player — when any button is
// pressed this frame, we light up a pixel near the player.
var p1_shot: u8 = 0
var p2_shot: u8 = 0

on frame {
    // Player 1 — uses the implicit prefix.
    if button.left  { p1x -= 1 }
    if button.right { p1x += 1 }
    if button.up    { p1y -= 1 }
    if button.down  { p1y += 1 }
    if button.a or button.b {
        p1_shot = 1
    } else {
        p1_shot = 0
    }

    // Player 2 — explicit `p2.` prefix.
    if p2.button.left  { p2x -= 1 }
    if p2.button.right { p2x += 1 }
    if p2.button.up    { p2y -= 1 }
    if p2.button.down  { p2y += 1 }
    if p2.button.a or p2.button.b {
        p2_shot = 1
    } else {
        p2_shot = 0
    }

    // Draw each player, and a shot indicator above their head
    // whenever they're holding a face button. Using separate
    // `draw` statements so each gets its own OAM slot via the
    // runtime cursor.
    draw Player1 at: (p1x, p1y)
    draw Player2 at: (p2x, p2y)
    if p1_shot == 1 {
        draw Shot at: (p1x, p1y - 8)
    }
    if p2_shot == 1 {
        draw Shot at: (p2x, p2y - 8)
    }
}

start Main
