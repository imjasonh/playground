// sha256/background.ne — the static nametable.
//
// Painted once at reset-time (the first `background` declaration
// in the program is loaded before rendering is enabled). Contains
// the title banner, section labels, and the 5 × 8 keyboard grid.
// The Entering and Showing state handlers draw the dynamic input
// buffer, the cursor, and the 64-digit hash on top of this
// background via sprites.
//
// Legend characters are chosen to read cleanly when glanced over
// as ASCII art:
//   upper-case A-Z and 0-9      → their matching glyph tile
//   space ' '                   → blank tile (tile 44)
//   ':' ',' '-' '.'             → punctuation glyph tiles
//   '_'                         → space-key glyph on the keyboard
//   'p'                         → period-key glyph on the keyboard
//   '<' '>'                     → backspace / enter key glyphs
//
// `palette_map:` leaves every metatile on bg sub-palette 0; the
// keyboard keys render as lt_gray (palette index 2), which reads
// cleanly against the dk_blue universal background.

background Screen {
    legend {
        " ": 44   // blank (universal colour)
        "A": 1
        "B": 2
        "C": 3
        "D": 4
        "E": 5
        "F": 6
        "G": 7
        "H": 8
        "I": 9
        "J": 10
        "K": 11
        "L": 12
        "M": 13
        "N": 14
        "O": 15
        "P": 16
        "Q": 17
        "R": 18
        "S": 19
        "T": 20
        "U": 21
        "V": 22
        "W": 23
        "X": 24
        "Y": 25
        "Z": 26
        "0": 27
        "1": 28
        "2": 29
        "3": 30
        "4": 31
        "5": 32
        "6": 33
        "7": 34
        "8": 35
        "9": 36
        "_": 37   // space-key glyph (underscore bar)
        "p": 38   // period-key glyph
        ":": 39
        "-": 40
        "<": 41   // backspace
        ">": 42   // enter
    }

    map: [
        "                                ",   // row 0
        "         SHA-256 HASHER         ",   // row 1 — title
        "                                ",   // row 2
        "  INPUT:                        ",   // row 3 — input label
        "                                ",   // row 4 — input row A
        "                                ",   // row 5 — input row B
        "                                ",   // row 6
        "  TYPE A MESSAGE  PRESS >       ",   // row 7 — prompt
        "                                ",   // row 8
        "                                ",   // row 9
        "                                ",   // row 10
        "                                ",   // row 11
        "           A B C D E F G H      ",   // row 12 — kb row 0
        "           I J K L M N O P      ",   // row 13 — kb row 1
        "           Q R S T U V W X      ",   // row 14 — kb row 2
        "           Y Z 0 1 2 3 4 5      ",   // row 15 — kb row 3
        "           6 7 8 9 _ p < >      ",   // row 16 — kb row 4
        "                                ",   // row 17
        "                                ",   // row 18
        "                                ",   // row 19
        "  SHA-256:                      ",   // row 20 — hash label
        "                                ",   // row 21 — hash rows
        "                                ",   // row 22
        "                                ",   // row 23
        "                                ",   // row 24
        "                                ",   // row 25
        "                                ",   // row 26
        "                                ",   // row 27
        "                                ",   // row 28
        "                                "    // row 29
    ]
}
