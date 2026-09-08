//! Geometry and command set for the 3.97-inch 800x480 mono e-ink panel
//! (SSD1677 chip-on-glass controller), mounted with its long axis vertical.
//!
//! The glass is physically portrait, but the controller RAM remains 800 pixels
//! on its source axis by 480 pixels on its gate axis. The sender rotates the
//! portrait face into this controller-native order before transfer. Keeping the
//! wire payload native avoids a 48 KB transpose buffer on the device.
//!
//! The controller packs 8 source-axis pixels per byte and addresses RAM on byte
//! boundaries, so partial-refresh windows must align their `x` and `w` values
//! to whole bytes.

/// SSD1677 source-axis width in pixels.
pub const WIDTH: u16 = 800;

/// SSD1677 gate-axis height in pixels.
pub const HEIGHT: u16 = 480;

/// Visible width after the panel is mounted in portrait orientation.
pub const PORTRAIT_WIDTH: u16 = HEIGHT;

/// Visible height after the panel is mounted in portrait orientation.
pub const PORTRAIT_HEIGHT: u16 = WIDTH;

/// Length in bytes of a full 1-bit-per-pixel framebuffer (48000 bytes).
pub const FRAME_BYTES: usize = (WIDTH as usize * HEIGHT as usize) / 8;

/// Bytes in one controller-native scan row.
pub const ROW_BYTES: usize = WIDTH as usize / 8;

/// Expected BUSY polarity from the selected panel specification.
///
/// Verify this on the released panel revision before enabling refresh.
pub const BUSY_ACTIVE_HIGH: bool = true;

/// Provisional EVT timeout for one panel operation.
pub const BUSY_TIMEOUT_MS: u32 = 10_000;

/// Provisional EVT limit before a cleaning full refresh.
pub const MAX_CONSECUTIVE_PARTIALS: u8 = 10;

/// SSD1677 command opcodes the driver issues over SPI.
#[derive(Clone, Copy, PartialEq, Eq, Debug)]
#[repr(u8)]
pub enum Command {
    DriverOutputControl = 0x01,
    BoosterSoftStart = 0x0C,
    DeepSleep = 0x10,
    DataEntryMode = 0x11,
    SwReset = 0x12,
    TemperatureSensorControl = 0x18,
    WriteTemperature = 0x1A,
    MasterActivation = 0x20,
    DisplayUpdateControl1 = 0x21,
    DisplayUpdateControl2 = 0x22,
    WriteRam = 0x24,
    WriteRam2 = 0x26,
    BorderWaveformControl = 0x3C,
    SetRamXAddress = 0x44,
    SetRamYAddress = 0x45,
    SetRamXCounter = 0x4E,
    SetRamYCounter = 0x4F,
}

// Values from the GDEM0397T81 vendor sequence for the same SSD1677 glass
// geometry. Confirm them against the released GDEY0397T81P sample and drawing.
pub const INTERNAL_TEMPERATURE_SENSOR: [u8; 1] = [0x80];
pub const BOOSTER_SOFT_START: [u8; 5] = [0xae, 0xc7, 0xc3, 0xc0, 0x80];
pub const DRIVER_OUTPUT: [u8; 3] = [((HEIGHT - 1) & 0xff) as u8, ((HEIGHT - 1) >> 8) as u8, 0x02];
pub const BORDER_WAVEFORM: [u8; 1] = [0x01];
pub const DISPLAY_CONTROL_BW_ONLY: [u8; 2] = [0x40, 0x00];
pub const DISPLAY_CONTROL_PARTIAL: [u8; 2] = [0x00, 0x00];
pub const UPDATE_FULL: [u8; 1] = [0xf7];
pub const UPDATE_FAST: [u8; 1] = [0xd7];
pub const UPDATE_PARTIAL: [u8; 1] = [0xfc];
pub const UPDATE_POWER_OFF: [u8; 1] = [0x83];
pub const DEEP_SLEEP: [u8; 1] = [0x03];

impl Command {
    /// The raw opcode byte to clock out on the command phase.
    pub const fn opcode(self) -> u8 {
        self as u8
    }
}

/// A rectangular region in SSD1677 controller-native coordinates.
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
            && self.x.is_multiple_of(8)
            && self.w.is_multiple_of(8)
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

    /// Build SSD1677 address data for the panel's reversed gate wiring.
    pub fn address_plan(self) -> Option<AddressPlan> {
        if !self.is_valid() {
            return None;
        }
        let native_y = HEIGHT - self.y - self.h;
        let x_end = self.x + self.w - 1;
        let y_end = native_y + self.h - 1;
        Some(AddressPlan {
            data_entry_mode: [0x01],
            x_window: words(self.x, x_end),
            y_window: words(y_end, native_y),
            x_counter: word(self.x),
            y_counter: word(y_end),
        })
    }
}

/// Data bytes for commands 0x11, 0x44, 0x45, 0x4e, and 0x4f.
#[derive(Clone, Copy, PartialEq, Eq, Debug)]
pub struct AddressPlan {
    pub data_entry_mode: [u8; 1],
    pub x_window: [u8; 4],
    pub y_window: [u8; 4],
    pub x_counter: [u8; 2],
    pub y_counter: [u8; 2],
}

const fn word(value: u16) -> [u8; 2] {
    value.to_le_bytes()
}

const fn words(first: u16, second: u16) -> [u8; 4] {
    let first = word(first);
    let second = word(second);
    [first[0], first[1], second[0], second[1]]
}

/// The waveform class requested for the next update.
#[derive(Clone, Copy, PartialEq, Eq, Debug)]
pub enum RefreshKind {
    Full,
    Partial,
}

#[derive(Clone, Copy, PartialEq, Eq, Debug)]
pub enum PatchError {
    InvalidWindow,
    InvalidFrameLength,
    InvalidPatchLength,
}

/// Merge a controller-native partial payload into a complete framebuffer.
pub fn apply_patch(frame: &mut [u8], window: Window, patch: &[u8]) -> Result<(), PatchError> {
    if !window.is_valid() {
        return Err(PatchError::InvalidWindow);
    }
    if frame.len() != FRAME_BYTES {
        return Err(PatchError::InvalidFrameLength);
    }
    if patch.len() != window.packed_bytes() {
        return Err(PatchError::InvalidPatchLength);
    }

    let patch_row_bytes = window.w as usize / 8;
    let destination_x = window.x as usize / 8;
    for row in 0..window.h as usize {
        let destination_start = (window.y as usize + row) * ROW_BYTES + destination_x;
        let source_start = row * patch_row_bytes;
        frame[destination_start..destination_start + patch_row_bytes]
            .copy_from_slice(&patch[source_start..source_start + patch_row_bytes]);
    }
    Ok(())
}

/// Tracks partial refreshes so ghosting cannot grow without a cleaning update.
#[derive(Clone, Copy, PartialEq, Eq, Debug)]
pub struct RefreshPolicy {
    consecutive_partials: u8,
}

impl RefreshPolicy {
    /// Start with a full refresh requirement after power-up.
    pub const fn new() -> Self {
        Self {
            consecutive_partials: MAX_CONSECUTIVE_PARTIALS,
        }
    }

    /// Select the effective refresh kind for a requested panel window.
    pub fn choose(&self, requested: RefreshKind, window: Window) -> RefreshKind {
        if requested == RefreshKind::Full
            || window == Window::FULL
            || self.consecutive_partials >= MAX_CONSECUTIVE_PARTIALS
        {
            RefreshKind::Full
        } else {
            RefreshKind::Partial
        }
    }

    /// Record a successfully completed refresh.
    pub fn record_success(&mut self, completed: RefreshKind) {
        match completed {
            RefreshKind::Full => self.consecutive_partials = 0,
            RefreshKind::Partial => {
                self.consecutive_partials = self.consecutive_partials.saturating_add(1)
            }
        }
    }

    /// Return the number of partial refreshes since the last full refresh.
    pub const fn consecutive_partials(&self) -> u8 {
        self.consecutive_partials
    }
}

impl Default for RefreshPolicy {
    fn default() -> Self {
        Self::new()
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn full_frame_is_48000_bytes() {
        assert_eq!(FRAME_BYTES, 48_000);
        assert_eq!(Window::FULL.packed_bytes(), FRAME_BYTES);
        assert_eq!((PORTRAIT_WIDTH, PORTRAIT_HEIGHT), (480, 800));
    }

    #[test]
    fn opcodes_match_datasheet() {
        assert_eq!(Command::WriteRam.opcode(), 0x24);
        assert_eq!(Command::WriteRam2.opcode(), 0x26);
        assert_eq!(Command::MasterActivation.opcode(), 0x20);
        assert_eq!(Command::SwReset.opcode(), 0x12);
        assert_eq!(DRIVER_OUTPUT, [0xdf, 0x01, 0x02]);
        assert_eq!(BOOSTER_SOFT_START, [0xae, 0xc7, 0xc3, 0xc0, 0x80]);
        assert_eq!(UPDATE_FULL, [0xf7]);
        assert_eq!(UPDATE_PARTIAL, [0xfc]);
        assert_eq!(DEEP_SLEEP, [0x03]);
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
            x: 792,
            y: 0,
            w: 16,
            h: 10
        }
        .is_valid());
        assert!(Window {
            x: 792,
            y: 479,
            w: 8,
            h: 1
        }
        .is_valid());
        assert!(!Window {
            x: 0,
            y: 480,
            w: 8,
            h: 1
        }
        .is_valid());
        assert!(!Window {
            x: 1,
            y: 0,
            w: 8,
            h: 1
        }
        .is_valid());
        assert!(!Window {
            x: 0,
            y: 0,
            w: 10,
            h: 1
        }
        .is_valid());
    }

    #[test]
    fn packed_bytes_are_row_aligned() {
        let w = Window {
            x: 0,
            y: 0,
            w: 16,
            h: 3,
        };
        assert_eq!(w.packed_bytes(), 2 * 3);
    }

    #[test]
    fn address_plan_uses_pixel_x_and_reversed_gate_y() {
        let full = Window::FULL.address_plan().unwrap();
        assert_eq!(full.data_entry_mode, [0x01]);
        assert_eq!(full.x_window, [0x00, 0x00, 0x1f, 0x03]);
        assert_eq!(full.y_window, [0xdf, 0x01, 0x00, 0x00]);
        assert_eq!(full.x_counter, [0x00, 0x00]);
        assert_eq!(full.y_counter, [0xdf, 0x01]);

        let partial = Window {
            x: 16,
            y: 20,
            w: 32,
            h: 10,
        }
        .address_plan()
        .unwrap();
        assert_eq!(partial.x_window, [16, 0, 47, 0]);
        assert_eq!(partial.y_window, [0xcb, 0x01, 0xc2, 0x01]);
        assert_eq!(partial.x_counter, [16, 0]);
        assert_eq!(partial.y_counter, [0xcb, 0x01]);
    }

    #[test]
    fn partial_patch_updates_only_its_native_rows() {
        let mut frame = [0xff; FRAME_BYTES];
        let window = Window {
            x: 16,
            y: 2,
            w: 16,
            h: 2,
        };
        apply_patch(&mut frame, window, &[0x12, 0x34, 0x56, 0x78]).unwrap();
        assert_eq!(&frame[2 * ROW_BYTES + 2..2 * ROW_BYTES + 4], &[0x12, 0x34]);
        assert_eq!(&frame[3 * ROW_BYTES + 2..3 * ROW_BYTES + 4], &[0x56, 0x78]);
        assert!(frame[..2 * ROW_BYTES + 2].iter().all(|byte| *byte == 0xff));
        assert!(frame[3 * ROW_BYTES + 4..].iter().all(|byte| *byte == 0xff));
    }

    #[test]
    fn patch_rejects_every_length_or_geometry_mismatch() {
        let mut frame = [0; FRAME_BYTES];
        assert_eq!(
            apply_patch(&mut frame, Window::FULL, &[0; 1]),
            Err(PatchError::InvalidPatchLength)
        );
        assert_eq!(
            apply_patch(&mut frame[..FRAME_BYTES - 1], Window::FULL, &[]),
            Err(PatchError::InvalidFrameLength)
        );
        assert_eq!(
            apply_patch(
                &mut frame,
                Window {
                    x: 1,
                    y: 0,
                    w: 8,
                    h: 1,
                },
                &[0]
            ),
            Err(PatchError::InvalidWindow)
        );
    }

    #[test]
    fn refresh_policy_forces_periodic_full_updates() {
        let partial = Window {
            x: 0,
            y: 0,
            w: 16,
            h: 16,
        };
        let mut policy = RefreshPolicy::new();
        assert_eq!(
            policy.choose(RefreshKind::Partial, partial),
            RefreshKind::Full
        );
        policy.record_success(RefreshKind::Full);
        for expected in 1..=MAX_CONSECUTIVE_PARTIALS {
            assert_eq!(
                policy.choose(RefreshKind::Partial, partial),
                RefreshKind::Partial
            );
            policy.record_success(RefreshKind::Partial);
            assert_eq!(policy.consecutive_partials(), expected);
        }
        assert_eq!(
            policy.choose(RefreshKind::Partial, partial),
            RefreshKind::Full
        );
    }
}
