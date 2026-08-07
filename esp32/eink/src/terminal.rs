//! Small, allocation-free terminal buffer.
//!
//! The first firmware only types a configured command and captures its output,
//! so a complete xterm emulator would be wasted flash. This parser implements
//! the control sequences commonly emitted by a login shell and keeps exactly
//! the 80×25 cells that fit the display. Unsupported escape sequences are
//! ignored instead of being rendered as garbage.

pub const COLS: usize = 80;
pub const ROWS: usize = 25;

#[derive(Clone, Copy, Debug)]
enum ParserState {
    Ground,
    Escape,
    Csi {
        params: [u16; 4],
        count: usize,
        value: u16,
        has_value: bool,
    },
}

pub struct TerminalBuffer {
    cells: [[u8; COLS]; ROWS],
    row: usize,
    col: usize,
    state: ParserState,
}

impl Default for TerminalBuffer {
    fn default() -> Self {
        Self::new()
    }
}

impl TerminalBuffer {
    pub const fn new() -> Self {
        Self {
            cells: [[b' '; COLS]; ROWS],
            row: 0,
            col: 0,
            state: ParserState::Ground,
        }
    }

    pub fn clear(&mut self) {
        self.cells = [[b' '; COLS]; ROWS];
        self.row = 0;
        self.col = 0;
        self.state = ParserState::Ground;
    }

    pub fn feed(&mut self, bytes: &[u8]) {
        for &byte in bytes {
            self.feed_byte(byte);
        }
    }

    pub fn write_line(&mut self, text: &str) {
        self.feed(text.as_bytes());
        self.feed(b"\r\n");
    }

    pub fn line(&self, row: usize) -> &[u8; COLS] {
        &self.cells[row]
    }

    pub fn cursor(&self) -> (usize, usize) {
        (self.row, self.col)
    }

    fn feed_byte(&mut self, byte: u8) {
        match self.state {
            ParserState::Ground => self.feed_ground(byte),
            ParserState::Escape => {
                self.state = if byte == b'[' {
                    ParserState::Csi {
                        params: [0; 4],
                        count: 0,
                        value: 0,
                        has_value: false,
                    }
                } else {
                    ParserState::Ground
                };
            }
            ParserState::Csi {
                mut params,
                mut count,
                mut value,
                mut has_value,
            } => match byte {
                b'0'..=b'9' => {
                    value = value
                        .saturating_mul(10)
                        .saturating_add((byte - b'0') as u16);
                    has_value = true;
                    self.state = ParserState::Csi {
                        params,
                        count,
                        value,
                        has_value,
                    };
                }
                b';' => {
                    if count < params.len() {
                        params[count] = if has_value { value } else { 0 };
                        count += 1;
                    }
                    self.state = ParserState::Csi {
                        params,
                        count,
                        value: 0,
                        has_value: false,
                    };
                }
                0x40..=0x7e => {
                    if count < params.len() {
                        params[count] = if has_value { value } else { 0 };
                        count += 1;
                    }
                    self.apply_csi(byte, &params[..count]);
                    self.state = ParserState::Ground;
                }
                _ => {
                    self.state = ParserState::Ground;
                }
            },
        }
    }

    fn feed_ground(&mut self, byte: u8) {
        match byte {
            0x1b => self.state = ParserState::Escape,
            b'\r' => self.col = 0,
            b'\n' => self.newline(),
            b'\x08' | b'\x7f' => self.col = self.col.saturating_sub(1),
            b'\t' => {
                let next = ((self.col / 8) + 1) * 8;
                self.col = next.min(COLS - 1);
            }
            0x20..=0x7e => self.put(byte),
            // Keep the framebuffer ASCII-only for the built-in font. Replace
            // each non-ASCII code unit rather than leaking raw UTF-8 bytes.
            0x80..=0xff => self.put(b'?'),
            _ => {}
        }
    }

    fn put(&mut self, byte: u8) {
        self.cells[self.row][self.col] = byte;
        self.col += 1;
        if self.col == COLS {
            self.col = 0;
            self.newline();
        }
    }

    fn newline(&mut self) {
        if self.row + 1 < ROWS {
            self.row += 1;
        } else {
            for row in 1..ROWS {
                self.cells[row - 1] = self.cells[row];
            }
            self.cells[ROWS - 1] = [b' '; COLS];
        }
    }

    fn apply_csi(&mut self, final_byte: u8, params: &[u16]) {
        let first = params.first().copied().unwrap_or(0) as usize;
        match final_byte {
            // Select Graphic Rendition. The panel is monochrome, so attributes
            // are intentionally ignored.
            b'm' => {}
            b'A' => self.row = self.row.saturating_sub(first.max(1)),
            b'B' => self.row = (self.row + first.max(1)).min(ROWS - 1),
            b'C' => self.col = (self.col + first.max(1)).min(COLS - 1),
            b'D' => self.col = self.col.saturating_sub(first.max(1)),
            b'H' | b'f' => {
                let row = params.first().copied().unwrap_or(1).max(1) as usize;
                let col = params.get(1).copied().unwrap_or(1).max(1) as usize;
                self.row = (row - 1).min(ROWS - 1);
                self.col = (col - 1).min(COLS - 1);
            }
            b'J' if first == 2 || first == 3 => self.clear(),
            b'K' => {
                let mode = first;
                match mode {
                    1 => self.cells[self.row][..=self.col].fill(b' '),
                    2 => self.cells[self.row].fill(b' '),
                    _ => self.cells[self.row][self.col..].fill(b' '),
                }
            }
            _ => {}
        }
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    fn row_text(term: &TerminalBuffer, row: usize) -> String {
        String::from_utf8(term.line(row).to_vec()).unwrap()
    }

    #[test]
    fn handles_crlf_and_ignores_color() {
        let mut term = TerminalBuffer::new();
        term.feed(b"hello\r\n\x1b[31mworld\x1b[0m");

        assert!(row_text(&term, 0).starts_with("hello"));
        assert!(row_text(&term, 1).starts_with("world"));
        assert_eq!(term.cursor(), (1, 5));
    }

    #[test]
    fn wraps_at_eighty_columns() {
        let mut term = TerminalBuffer::new();
        term.feed(&[b'x'; COLS + 1]);

        assert_eq!(term.line(0), &[b'x'; COLS]);
        assert_eq!(term.line(1)[0], b'x');
        assert_eq!(term.cursor(), (1, 1));
    }

    #[test]
    fn scrolls_after_twenty_five_rows() {
        let mut term = TerminalBuffer::new();
        for n in 0..=ROWS {
            term.write_line(&format!("line {n:02}"));
        }

        assert!(row_text(&term, 0).starts_with("line 02"));
        assert!(row_text(&term, ROWS - 2).starts_with("line 25"));
    }

    #[test]
    fn supports_cursor_position_and_clear_line() {
        let mut term = TerminalBuffer::new();
        term.feed(b"abcdef\x1b[1;3H\x1b[KZ");

        assert_eq!(&term.line(0)[..3], b"abZ");
        assert!(term.line(0)[3..].iter().all(|byte| *byte == b' '));
    }
}
