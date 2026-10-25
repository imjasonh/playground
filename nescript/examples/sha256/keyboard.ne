// sha256/keyboard.ne — key-to-character lookup + input dispatch.
//
// The on-screen keyboard is a 5-row × 8-column grid of cells.
// `kb_row` and `kb_col` in state.ne store the cursor position.
// The character produced when the user presses A is looked up
// here. Special values are encoded with ASCII control codes so
// they're distinguishable from printable bytes:
//
//     KEY_BKSP   (0x08)   — bottom row col 6. Delete one char.
//     KEY_ENTER  (0x0A)   — bottom row col 7. Start compression.
//
// The grid layout (matches the keyboard in background.ne):
//
//     row 0:  A B C D E F G H
//     row 1:  I J K L M N O P
//     row 2:  Q R S T U V W X
//     row 3:  Y Z 0 1 2 3 4 5
//     row 4:  6 7 8 9 _ . < >

var KB_CHARS: u8[40] = [
    0x41, 0x42, 0x43, 0x44, 0x45, 0x46, 0x47, 0x48,   // A B C D E F G H
    0x49, 0x4A, 0x4B, 0x4C, 0x4D, 0x4E, 0x4F, 0x50,   // I J K L M N O P
    0x51, 0x52, 0x53, 0x54, 0x55, 0x56, 0x57, 0x58,   // Q R S T U V W X
    0x59, 0x5A, 0x30, 0x31, 0x32, 0x33, 0x34, 0x35,   // Y Z 0 1 2 3 4 5
    0x36, 0x37, 0x38, 0x39, 0x20, 0x2E, 0x08, 0x0A    // 6 7 8 9 ' ' '.' BKSP ENTER
]

// Look up the character emitted by the key at (kb_row, kb_col).
fun current_key() -> u8 {
    var idx: u8 = (kb_row << 3) + kb_col           // row * 8 + col
    return KB_CHARS[idx]
}

// Append a byte to the input buffer. Does nothing if the buffer
// is already at INPUT_MAX — users wanting to correct their
// input reach for backspace first.
fun input_append(ch: u8) {
    if msg_len >= INPUT_MAX {
        return
    }
    msg[msg_len] = ch
    msg_len += 1
}

// Delete the last byte, if any.
fun input_backspace() {
    if msg_len == 0 {
        return
    }
    msg_len -= 1
    msg[msg_len] = 0
}

// Wipe the entire buffer. Triggered by SELECT from any state.
fun input_clear() {
    var i: u8 = 0
    while i < INPUT_MAX {
        msg[i] = 0
        i += 1
    }
    msg_len = 0
}
