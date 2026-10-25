// Match Demo — demonstrates the `match` statement.
//
// Match dispatches on a value against a sequence of patterns. Each
// arm runs only when its pattern compares equal to the scrutinee,
// and the underscore arm catches everything else. Here we drive a
// tiny title/playing/paused/game-over menu purely through a match
// on a u8 screen mode, cycled by the d-pad buttons.
//
// Build: cargo run -- build examples/match_demo.ne

game "Match Demo" {
    mapper: NROM
}

enum Screen { Title, Playing, Paused, GameOver }

var screen: u8 = Title
var x: u8 = 120
var y: u8 = 112
var debounce: u8 = 0

on frame {
    // Debounce so a held button doesn't spam transitions each frame.
    if debounce > 0 {
        debounce -= 1
    }

    match screen {
        Title => {
            // Blink the pointer by alternating its position.
            draw Arrow at: (80, 112)
            if button.start and debounce == 0 {
                screen = Playing
                debounce = 20
            }
        }
        Playing => {
            if button.right { x += 2 }
            if button.left  { x -= 2 }
            if button.down  { y += 2 }
            if button.up    { y -= 2 }
            draw Player at: (x, y)

            if button.select and debounce == 0 {
                screen = Paused
                debounce = 20
            }
            if button.b and debounce == 0 {
                screen = GameOver
                debounce = 20
            }
        }
        Paused => {
            // Freeze the player where it was and show a pause marker.
            draw Player at: (x, y)
            draw Arrow at: (120, 80)
            if button.select and debounce == 0 {
                screen = Playing
                debounce = 20
            }
        }
        GameOver => {
            draw Skull at: (120, 112)
            if button.a and debounce == 0 {
                screen = Title
                debounce = 20
            }
        }
        _ => {
            // Defensive: an unexpected value lands back on the title.
            screen = Title
        }
    }
}

start Main
