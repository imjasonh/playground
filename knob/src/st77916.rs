//! ST77916 init commands for the 360x360 round panel.
//!
//! QSPI writes use opcode 0x02 for registers and 0x32 for pixel data.
//! The table is the vendor sequence this panel needs before sleep-out.
//! A short SLPOUT plus DISPON leaves the glass blank.

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub struct Cmd {
    pub cmd: u8,
    pub delay_ms: u16,
    pub data: &'static [u8],
}

pub const CMD_WRITE: u32 = 0x02;
pub const COLOR_QIO: u32 = 0x32;
pub const CASET: u8 = 0x2A;
pub const RASET: u8 = 0x2B;
pub const RAMWR: u8 = 0x2C;
pub const SLPOUT: u8 = 0x11;
pub const DISPON: u8 = 0x29;
pub const COLMOD: u8 = 0x3A;

/// 32-bit QSPI header. Opcode, then the 24-bit address `0x00, command, 0x00`.
pub fn header(opcode: u32, cmd: u8) -> [u8; 4] {
    let word = (opcode << 24) | (u32::from(cmd) << 8);
    word.to_be_bytes()
}

pub fn caset_raset(x0: u16, y0: u16, x1: u16, y1: u16) -> [[u8; 4]; 2] {
    let mut x = [0u8; 4];
    x[0..2].copy_from_slice(&x0.to_be_bytes());
    x[2..4].copy_from_slice(&x1.to_be_bytes());
    let mut y = [0u8; 4];
    y[0..2].copy_from_slice(&y0.to_be_bytes());
    y[2..4].copy_from_slice(&y1.to_be_bytes());
    [x, y]
}

pub static INIT: &[Cmd] = &[
    Cmd {
        cmd: 0xF0,
        delay_ms: 0,
        data: &[0x28],
    },
    Cmd {
        cmd: 0xF2,
        delay_ms: 0,
        data: &[0x28],
    },
    Cmd {
        cmd: 0x73,
        delay_ms: 0,
        data: &[0xF0],
    },
    Cmd {
        cmd: 0x7C,
        delay_ms: 0,
        data: &[0xD1],
    },
    Cmd {
        cmd: 0x83,
        delay_ms: 0,
        data: &[0xE0],
    },
    Cmd {
        cmd: 0x84,
        delay_ms: 0,
        data: &[0x61],
    },
    Cmd {
        cmd: 0xF2,
        delay_ms: 0,
        data: &[0x82],
    },
    Cmd {
        cmd: 0xF0,
        delay_ms: 0,
        data: &[0x00],
    },
    Cmd {
        cmd: 0xF0,
        delay_ms: 0,
        data: &[0x01],
    },
    Cmd {
        cmd: 0xF1,
        delay_ms: 0,
        data: &[0x01],
    },
    Cmd {
        cmd: 0xB0,
        delay_ms: 0,
        data: &[0x56],
    },
    Cmd {
        cmd: 0xB1,
        delay_ms: 0,
        data: &[0x4D],
    },
    Cmd {
        cmd: 0xB2,
        delay_ms: 0,
        data: &[0x24],
    },
    Cmd {
        cmd: 0xB4,
        delay_ms: 0,
        data: &[0x87],
    },
    Cmd {
        cmd: 0xB5,
        delay_ms: 0,
        data: &[0x44],
    },
    Cmd {
        cmd: 0xB6,
        delay_ms: 0,
        data: &[0x8B],
    },
    Cmd {
        cmd: 0xB7,
        delay_ms: 0,
        data: &[0x40],
    },
    Cmd {
        cmd: 0xB8,
        delay_ms: 0,
        data: &[0x86],
    },
    Cmd {
        cmd: 0xBA,
        delay_ms: 0,
        data: &[0x00],
    },
    Cmd {
        cmd: 0xBB,
        delay_ms: 0,
        data: &[0x08],
    },
    Cmd {
        cmd: 0xBC,
        delay_ms: 0,
        data: &[0x08],
    },
    Cmd {
        cmd: 0xBD,
        delay_ms: 0,
        data: &[0x00],
    },
    Cmd {
        cmd: 0xC0,
        delay_ms: 0,
        data: &[0x80],
    },
    Cmd {
        cmd: 0xC1,
        delay_ms: 0,
        data: &[0x10],
    },
    Cmd {
        cmd: 0xC2,
        delay_ms: 0,
        data: &[0x37],
    },
    Cmd {
        cmd: 0xC3,
        delay_ms: 0,
        data: &[0x80],
    },
    Cmd {
        cmd: 0xC4,
        delay_ms: 0,
        data: &[0x10],
    },
    Cmd {
        cmd: 0xC5,
        delay_ms: 0,
        data: &[0x37],
    },
    Cmd {
        cmd: 0xC6,
        delay_ms: 0,
        data: &[0xA9],
    },
    Cmd {
        cmd: 0xC7,
        delay_ms: 0,
        data: &[0x41],
    },
    Cmd {
        cmd: 0xC8,
        delay_ms: 0,
        data: &[0x01],
    },
    Cmd {
        cmd: 0xC9,
        delay_ms: 0,
        data: &[0xA9],
    },
    Cmd {
        cmd: 0xCA,
        delay_ms: 0,
        data: &[0x41],
    },
    Cmd {
        cmd: 0xCB,
        delay_ms: 0,
        data: &[0x01],
    },
    Cmd {
        cmd: 0xD0,
        delay_ms: 0,
        data: &[0x91],
    },
    Cmd {
        cmd: 0xD1,
        delay_ms: 0,
        data: &[0x68],
    },
    Cmd {
        cmd: 0xD2,
        delay_ms: 0,
        data: &[0x68],
    },
    Cmd {
        cmd: 0xF5,
        delay_ms: 0,
        data: &[0x00, 0xA5],
    },
    Cmd {
        cmd: 0xDD,
        delay_ms: 0,
        data: &[0x4F],
    },
    Cmd {
        cmd: 0xDE,
        delay_ms: 0,
        data: &[0x4F],
    },
    Cmd {
        cmd: 0xF1,
        delay_ms: 0,
        data: &[0x10],
    },
    Cmd {
        cmd: 0xF0,
        delay_ms: 0,
        data: &[0x00],
    },
    Cmd {
        cmd: 0xF0,
        delay_ms: 0,
        data: &[0x02],
    },
    Cmd {
        cmd: 0xE0,
        delay_ms: 0,
        data: &[
            0xF0, 0x0A, 0x10, 0x09, 0x09, 0x36, 0x35, 0x33, 0x4A, 0x29, 0x15, 0x15, 0x2E, 0x34,
        ],
    },
    Cmd {
        cmd: 0xE1,
        delay_ms: 0,
        data: &[
            0xF0, 0x0A, 0x0F, 0x08, 0x08, 0x05, 0x34, 0x33, 0x4A, 0x39, 0x15, 0x15, 0x2D, 0x33,
        ],
    },
    Cmd {
        cmd: 0xF0,
        delay_ms: 0,
        data: &[0x10],
    },
    Cmd {
        cmd: 0xF3,
        delay_ms: 0,
        data: &[0x10],
    },
    Cmd {
        cmd: 0xE0,
        delay_ms: 0,
        data: &[0x07],
    },
    Cmd {
        cmd: 0xE1,
        delay_ms: 0,
        data: &[0x00],
    },
    Cmd {
        cmd: 0xE2,
        delay_ms: 0,
        data: &[0x00],
    },
    Cmd {
        cmd: 0xE3,
        delay_ms: 0,
        data: &[0x00],
    },
    Cmd {
        cmd: 0xE4,
        delay_ms: 0,
        data: &[0xE0],
    },
    Cmd {
        cmd: 0xE5,
        delay_ms: 0,
        data: &[0x06],
    },
    Cmd {
        cmd: 0xE6,
        delay_ms: 0,
        data: &[0x21],
    },
    Cmd {
        cmd: 0xE7,
        delay_ms: 0,
        data: &[0x01],
    },
    Cmd {
        cmd: 0xE8,
        delay_ms: 0,
        data: &[0x05],
    },
    Cmd {
        cmd: 0xE9,
        delay_ms: 0,
        data: &[0x02],
    },
    Cmd {
        cmd: 0xEA,
        delay_ms: 0,
        data: &[0xDA],
    },
    Cmd {
        cmd: 0xEB,
        delay_ms: 0,
        data: &[0x00],
    },
    Cmd {
        cmd: 0xEC,
        delay_ms: 0,
        data: &[0x00],
    },
    Cmd {
        cmd: 0xED,
        delay_ms: 0,
        data: &[0x0F],
    },
    Cmd {
        cmd: 0xEE,
        delay_ms: 0,
        data: &[0x00],
    },
    Cmd {
        cmd: 0xEF,
        delay_ms: 0,
        data: &[0x00],
    },
    Cmd {
        cmd: 0xF8,
        delay_ms: 0,
        data: &[0x00],
    },
    Cmd {
        cmd: 0xF9,
        delay_ms: 0,
        data: &[0x00],
    },
    Cmd {
        cmd: 0xFA,
        delay_ms: 0,
        data: &[0x00],
    },
    Cmd {
        cmd: 0xFB,
        delay_ms: 0,
        data: &[0x00],
    },
    Cmd {
        cmd: 0xFC,
        delay_ms: 0,
        data: &[0x00],
    },
    Cmd {
        cmd: 0xFD,
        delay_ms: 0,
        data: &[0x00],
    },
    Cmd {
        cmd: 0xFE,
        delay_ms: 0,
        data: &[0x00],
    },
    Cmd {
        cmd: 0xFF,
        delay_ms: 0,
        data: &[0x00],
    },
    Cmd {
        cmd: 0x60,
        delay_ms: 0,
        data: &[0x40],
    },
    Cmd {
        cmd: 0x61,
        delay_ms: 0,
        data: &[0x04],
    },
    Cmd {
        cmd: 0x62,
        delay_ms: 0,
        data: &[0x00],
    },
    Cmd {
        cmd: 0x63,
        delay_ms: 0,
        data: &[0x42],
    },
    Cmd {
        cmd: 0x64,
        delay_ms: 0,
        data: &[0xD9],
    },
    Cmd {
        cmd: 0x65,
        delay_ms: 0,
        data: &[0x00],
    },
    Cmd {
        cmd: 0x66,
        delay_ms: 0,
        data: &[0x00],
    },
    Cmd {
        cmd: 0x67,
        delay_ms: 0,
        data: &[0x00],
    },
    Cmd {
        cmd: 0x68,
        delay_ms: 0,
        data: &[0x00],
    },
    Cmd {
        cmd: 0x69,
        delay_ms: 0,
        data: &[0x00],
    },
    Cmd {
        cmd: 0x6A,
        delay_ms: 0,
        data: &[0x00],
    },
    Cmd {
        cmd: 0x6B,
        delay_ms: 0,
        data: &[0x00],
    },
    Cmd {
        cmd: 0x70,
        delay_ms: 0,
        data: &[0x40],
    },
    Cmd {
        cmd: 0x71,
        delay_ms: 0,
        data: &[0x03],
    },
    Cmd {
        cmd: 0x72,
        delay_ms: 0,
        data: &[0x00],
    },
    Cmd {
        cmd: 0x73,
        delay_ms: 0,
        data: &[0x42],
    },
    Cmd {
        cmd: 0x74,
        delay_ms: 0,
        data: &[0xD8],
    },
    Cmd {
        cmd: 0x75,
        delay_ms: 0,
        data: &[0x00],
    },
    Cmd {
        cmd: 0x76,
        delay_ms: 0,
        data: &[0x00],
    },
    Cmd {
        cmd: 0x77,
        delay_ms: 0,
        data: &[0x00],
    },
    Cmd {
        cmd: 0x78,
        delay_ms: 0,
        data: &[0x00],
    },
    Cmd {
        cmd: 0x79,
        delay_ms: 0,
        data: &[0x00],
    },
    Cmd {
        cmd: 0x7A,
        delay_ms: 0,
        data: &[0x00],
    },
    Cmd {
        cmd: 0x7B,
        delay_ms: 0,
        data: &[0x00],
    },
    Cmd {
        cmd: 0x80,
        delay_ms: 0,
        data: &[0x48],
    },
    Cmd {
        cmd: 0x81,
        delay_ms: 0,
        data: &[0x00],
    },
    Cmd {
        cmd: 0x82,
        delay_ms: 0,
        data: &[0x06],
    },
    Cmd {
        cmd: 0x83,
        delay_ms: 0,
        data: &[0x02],
    },
    Cmd {
        cmd: 0x84,
        delay_ms: 0,
        data: &[0xD6],
    },
    Cmd {
        cmd: 0x85,
        delay_ms: 0,
        data: &[0x04],
    },
    Cmd {
        cmd: 0x86,
        delay_ms: 0,
        data: &[0x00],
    },
    Cmd {
        cmd: 0x87,
        delay_ms: 0,
        data: &[0x00],
    },
    Cmd {
        cmd: 0x88,
        delay_ms: 0,
        data: &[0x48],
    },
    Cmd {
        cmd: 0x89,
        delay_ms: 0,
        data: &[0x00],
    },
    Cmd {
        cmd: 0x8A,
        delay_ms: 0,
        data: &[0x08],
    },
    Cmd {
        cmd: 0x8B,
        delay_ms: 0,
        data: &[0x02],
    },
    Cmd {
        cmd: 0x8C,
        delay_ms: 0,
        data: &[0xD8],
    },
    Cmd {
        cmd: 0x8D,
        delay_ms: 0,
        data: &[0x04],
    },
    Cmd {
        cmd: 0x8E,
        delay_ms: 0,
        data: &[0x00],
    },
    Cmd {
        cmd: 0x8F,
        delay_ms: 0,
        data: &[0x00],
    },
    Cmd {
        cmd: 0x90,
        delay_ms: 0,
        data: &[0x48],
    },
    Cmd {
        cmd: 0x91,
        delay_ms: 0,
        data: &[0x00],
    },
    Cmd {
        cmd: 0x92,
        delay_ms: 0,
        data: &[0x0A],
    },
    Cmd {
        cmd: 0x93,
        delay_ms: 0,
        data: &[0x02],
    },
    Cmd {
        cmd: 0x94,
        delay_ms: 0,
        data: &[0xDA],
    },
    Cmd {
        cmd: 0x95,
        delay_ms: 0,
        data: &[0x04],
    },
    Cmd {
        cmd: 0x96,
        delay_ms: 0,
        data: &[0x00],
    },
    Cmd {
        cmd: 0x97,
        delay_ms: 0,
        data: &[0x00],
    },
    Cmd {
        cmd: 0x98,
        delay_ms: 0,
        data: &[0x48],
    },
    Cmd {
        cmd: 0x99,
        delay_ms: 0,
        data: &[0x00],
    },
    Cmd {
        cmd: 0x9A,
        delay_ms: 0,
        data: &[0x0C],
    },
    Cmd {
        cmd: 0x9B,
        delay_ms: 0,
        data: &[0x02],
    },
    Cmd {
        cmd: 0x9C,
        delay_ms: 0,
        data: &[0xDC],
    },
    Cmd {
        cmd: 0x9D,
        delay_ms: 0,
        data: &[0x04],
    },
    Cmd {
        cmd: 0x9E,
        delay_ms: 0,
        data: &[0x00],
    },
    Cmd {
        cmd: 0x9F,
        delay_ms: 0,
        data: &[0x00],
    },
    Cmd {
        cmd: 0xA0,
        delay_ms: 0,
        data: &[0x48],
    },
    Cmd {
        cmd: 0xA1,
        delay_ms: 0,
        data: &[0x00],
    },
    Cmd {
        cmd: 0xA2,
        delay_ms: 0,
        data: &[0x05],
    },
    Cmd {
        cmd: 0xA3,
        delay_ms: 0,
        data: &[0x02],
    },
    Cmd {
        cmd: 0xA4,
        delay_ms: 0,
        data: &[0xD5],
    },
    Cmd {
        cmd: 0xA5,
        delay_ms: 0,
        data: &[0x04],
    },
    Cmd {
        cmd: 0xA6,
        delay_ms: 0,
        data: &[0x00],
    },
    Cmd {
        cmd: 0xA7,
        delay_ms: 0,
        data: &[0x00],
    },
    Cmd {
        cmd: 0xA8,
        delay_ms: 0,
        data: &[0x48],
    },
    Cmd {
        cmd: 0xA9,
        delay_ms: 0,
        data: &[0x00],
    },
    Cmd {
        cmd: 0xAA,
        delay_ms: 0,
        data: &[0x07],
    },
    Cmd {
        cmd: 0xAB,
        delay_ms: 0,
        data: &[0x02],
    },
    Cmd {
        cmd: 0xAC,
        delay_ms: 0,
        data: &[0xD7],
    },
    Cmd {
        cmd: 0xAD,
        delay_ms: 0,
        data: &[0x04],
    },
    Cmd {
        cmd: 0xAE,
        delay_ms: 0,
        data: &[0x00],
    },
    Cmd {
        cmd: 0xAF,
        delay_ms: 0,
        data: &[0x00],
    },
    Cmd {
        cmd: 0xB0,
        delay_ms: 0,
        data: &[0x48],
    },
    Cmd {
        cmd: 0xB1,
        delay_ms: 0,
        data: &[0x00],
    },
    Cmd {
        cmd: 0xB2,
        delay_ms: 0,
        data: &[0x09],
    },
    Cmd {
        cmd: 0xB3,
        delay_ms: 0,
        data: &[0x02],
    },
    Cmd {
        cmd: 0xB4,
        delay_ms: 0,
        data: &[0xD9],
    },
    Cmd {
        cmd: 0xB5,
        delay_ms: 0,
        data: &[0x04],
    },
    Cmd {
        cmd: 0xB6,
        delay_ms: 0,
        data: &[0x00],
    },
    Cmd {
        cmd: 0xB7,
        delay_ms: 0,
        data: &[0x00],
    },
    Cmd {
        cmd: 0xB8,
        delay_ms: 0,
        data: &[0x48],
    },
    Cmd {
        cmd: 0xB9,
        delay_ms: 0,
        data: &[0x00],
    },
    Cmd {
        cmd: 0xBA,
        delay_ms: 0,
        data: &[0x0B],
    },
    Cmd {
        cmd: 0xBB,
        delay_ms: 0,
        data: &[0x02],
    },
    Cmd {
        cmd: 0xBC,
        delay_ms: 0,
        data: &[0xDB],
    },
    Cmd {
        cmd: 0xBD,
        delay_ms: 0,
        data: &[0x04],
    },
    Cmd {
        cmd: 0xBE,
        delay_ms: 0,
        data: &[0x00],
    },
    Cmd {
        cmd: 0xBF,
        delay_ms: 0,
        data: &[0x00],
    },
    Cmd {
        cmd: 0xC0,
        delay_ms: 0,
        data: &[0x10],
    },
    Cmd {
        cmd: 0xC1,
        delay_ms: 0,
        data: &[0x47],
    },
    Cmd {
        cmd: 0xC2,
        delay_ms: 0,
        data: &[0x56],
    },
    Cmd {
        cmd: 0xC3,
        delay_ms: 0,
        data: &[0x65],
    },
    Cmd {
        cmd: 0xC4,
        delay_ms: 0,
        data: &[0x74],
    },
    Cmd {
        cmd: 0xC5,
        delay_ms: 0,
        data: &[0x88],
    },
    Cmd {
        cmd: 0xC6,
        delay_ms: 0,
        data: &[0x99],
    },
    Cmd {
        cmd: 0xC7,
        delay_ms: 0,
        data: &[0x01],
    },
    Cmd {
        cmd: 0xC8,
        delay_ms: 0,
        data: &[0xBB],
    },
    Cmd {
        cmd: 0xC9,
        delay_ms: 0,
        data: &[0xAA],
    },
    Cmd {
        cmd: 0xD0,
        delay_ms: 0,
        data: &[0x10],
    },
    Cmd {
        cmd: 0xD1,
        delay_ms: 0,
        data: &[0x47],
    },
    Cmd {
        cmd: 0xD2,
        delay_ms: 0,
        data: &[0x56],
    },
    Cmd {
        cmd: 0xD3,
        delay_ms: 0,
        data: &[0x65],
    },
    Cmd {
        cmd: 0xD4,
        delay_ms: 0,
        data: &[0x74],
    },
    Cmd {
        cmd: 0xD5,
        delay_ms: 0,
        data: &[0x88],
    },
    Cmd {
        cmd: 0xD6,
        delay_ms: 0,
        data: &[0x99],
    },
    Cmd {
        cmd: 0xD7,
        delay_ms: 0,
        data: &[0x01],
    },
    Cmd {
        cmd: 0xD8,
        delay_ms: 0,
        data: &[0xBB],
    },
    Cmd {
        cmd: 0xD9,
        delay_ms: 0,
        data: &[0xAA],
    },
    Cmd {
        cmd: 0xF3,
        delay_ms: 0,
        data: &[0x01],
    },
    Cmd {
        cmd: 0xF0,
        delay_ms: 0,
        data: &[0x00],
    },
    Cmd {
        cmd: 0x3A,
        delay_ms: 0,
        data: &[0x55],
    },
    Cmd {
        cmd: 0x36,
        delay_ms: 0,
        data: &[0xC0],
    },
    Cmd {
        cmd: 0x35,
        delay_ms: 0,
        data: &[0x00],
    },
    Cmd {
        cmd: 0x21,
        delay_ms: 0,
        data: &[],
    },
    Cmd {
        cmd: SLPOUT,
        delay_ms: 120,
        data: &[],
    },
    Cmd {
        cmd: DISPON,
        delay_ms: 20,
        data: &[],
    },
];

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn init_ends_with_sleep_out_and_display_on() {
        assert!(INIT.len() > 40);
        assert_eq!(INIT[INIT.len() - 2].cmd, SLPOUT);
        assert_eq!(INIT[INIT.len() - 2].delay_ms, 120);
        assert_eq!(INIT.last().unwrap().cmd, DISPON);
        assert!(INIT.iter().any(|c| c.cmd == COLMOD && c.data == [0x55]));
    }

    #[test]
    fn header_and_full_window() {
        assert_eq!(header(CMD_WRITE, 0x2C), [0x02, 0x00, 0x2C, 0x00]);
        assert_eq!(header(COLOR_QIO, RAMWR), [0x32, 0x00, 0x2C, 0x00]);
        let [x, y] = caset_raset(0, 0, 359, 359);
        assert_eq!(x, [0x00, 0x00, 0x01, 0x67]);
        assert_eq!(y, [0x00, 0x00, 0x01, 0x67]);
    }
}
