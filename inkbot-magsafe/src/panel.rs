//! Geometry and command set for the 4.26-inch 480x800 mono e-ink panel
//! (SSD1677 chip-on-glass controller), mounted portrait.
//!
//! The controller packs 8 horizontal pixels per byte and addresses RAM on byte
//! boundaries, so partial-refresh windows round their width up to whole bytes.

/// Panel width in pixels (portrait: the short axis).
pub const WIDTH: u16 = 480;

/// Panel height in pixels (portrait: the long axis).
pub const HEIGHT: u16 = 800;

/// Length in bytes of a full 1-bit-per-pixel framebuffer (48000 bytes).
pub const FRAME_BYTES: usize = (WIDTH as usize * HEIGHT as usize) / 8;

/// SSD1677 command opcodes the driver issues over SPI.
#[derive(Clone, Copy, PartialEq, Eq, Debug)]
#[repr(u8)]
pub enum Command {
    DriverOutputControl = 0x01,
    DeepSleep = 0x10,
    DataEntryMode = 0x11,
    SwReset = 0x12,
    TemperatureSensorControl = 0x18,
    MasterActivation = 0x20,
    DisplayUpdateControl2 = 0x22,
    WriteRam = 0x24,
    SetRamXAddress = 0x44,
    SetRamYAddress = 0x45,
    SetRamXCounter = 0x4E,
    SetRamYCounter = 0x4F,
}

impl Command {
    /// The raw opcode byte to clock out on the command phase.
    pub const fn opcode(self) -> u8 {
        self as u8
    }
}

/// A rectangular region of the panel, in pixels.
#[derive(Clone, Copy, PartialEq, Eq, Debug)]
pub struct Window {
    pub x: u16,
    pub y: u16,
    pub w: u16,
    pub h: u16,
}

impl Window {
    /// The whole panel, for a full refresh.
    pub const FULL: Window = Window {
        x: 0,
        y: 0,
        w: WIDTH,
        h: HEIGHT,
    };

    /// Returns `true` when the window is non-empty and inside the panel bounds.
    pub fn is_valid(self) -> bool {
        self.w != 0
            && self.h != 0
            && self
                .x
                .checked_add(self.w)
                .is_some_and(|right| right <= WIDTH)
            && self
                .y
                .checked_add(self.h)
                .is_some_and(|bottom| bottom <= HEIGHT)
    }

    /// Bytes needed to hold this window as 1bpp, rows padded to whole bytes.
    pub fn packed_bytes(self) -> usize {
        let bytes_per_row = self.w.div_ceil(8) as usize;
        bytes_per_row * self.h as usize
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn full_frame_is_48000_bytes() {
        assert_eq!(FRAME_BYTES, 48_000);
        assert_eq!(Window::FULL.packed_bytes(), FRAME_BYTES);
    }

    #[test]
    fn opcodes_match_datasheet() {
        assert_eq!(Command::WriteRam.opcode(), 0x24);
        assert_eq!(Command::MasterActivation.opcode(), 0x20);
        assert_eq!(Command::SwReset.opcode(), 0x12);
    }

    #[test]
    fn window_bounds_are_checked() {
        assert!(Window::FULL.is_valid());
        assert!(Window {
            x: 8,
            y: 8,
            w: 16,
            h: 16
        }
        .is_valid());
        assert!(!Window {
            x: 0,
            y: 0,
            w: 0,
            h: 10
        }
        .is_valid());
        assert!(!Window {
            x: 472,
            y: 0,
            w: 16,
            h: 10
        }
        .is_valid());
    }

    #[test]
    fn odd_width_rounds_up_to_whole_bytes() {
        // 10 px wide rounds to 2 bytes per row.
        let w = Window {
            x: 0,
            y: 0,
            w: 10,
            h: 3,
        };
        assert_eq!(w.packed_bytes(), 2 * 3);
    }
}
