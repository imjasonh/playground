//! Grayscale planning for the UC8179's native 4-level "4 Gray" mode.
//!
//! The four shade levels and the two-plane (`old`/`new`) bit encoding below
//! are re-derived from Waveshare's own `EPD_7IN5_V2_Display_4Gray()`
//! (<https://github.com/waveshare/e-Paper>,
//! `Arduino_R4/src/e-Paper/EPD_7in5_V2.cpp>`), not an invented waveform:
//! that function reads each 2-bit source pixel and writes one bit to each of
//! the controller's two image planes (`DTM1` = "old", `DTM2` = "new"); the
//! table in [`Shade::plane_bits`] is that same mapping. `grayscale_display.rs`
//! drives the panel with the same controller mode Waveshare's demo code uses
//! (`Init_4Gray`, temperature-select value `0x5F`) — no waveform-LUT
//! registers (`0x20`-`0x25`) are written, and no one-time-programming
//! command is sent.
//!
//! This only gets the four fixed gray levels the controller already
//! supports. InkBoy's technique — a short *custom* waveform repeated many
//! times a second, redriving only pixels that changed — doesn't apply here:
//! Waveshare's 4-gray mode still redrives the whole panel in one `DISPLAY
//! REFRESH` (`0x12`) call, timed by its own factory waveform, not by
//! anything this firmware controls. That per-call time is not yet measured
//! on real hardware; see `grayscale_display.rs` and `grayscale_main.rs`.
//!
//! [`pixelate`] shrinks 384,000 physical pixels down to a smaller logical
//! grid (2×2 blocks by default) so a scene generator's per-pixel state fits
//! comfortably in the ESP32's RAM.

mod pack;
pub mod scene;

pub use pack::{pack_4gray_planes, pixelate};

use crate::panel::{PANEL_HEIGHT, PANEL_WIDTH};

/// Baked into the grayscale demo ELF so `make flash APP=grayscale` can
/// refuse a stale image, the same way `MAZE_FIRMWARE_ID` does for maze.
pub const GRAYSCALE_FIRMWARE_ID: &str = "grayscale-esp32/0.1";

/// One of the UC8179's four fixed gray levels. Discriminants match each
/// level's 2-bit code in Waveshare's own 2bpp image format.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
#[repr(u8)]
pub enum Shade {
    Black = 0b00,
    /// Darker gray ("gray2" in Waveshare's source).
    Gray2 = 0b01,
    /// Lighter gray ("gray1" in Waveshare's source).
    Gray1 = 0b10,
    White = 0b11,
}

impl Shade {
    /// `(old_bit, new_bit)` pair written to `DTM1`/`DTM2`, which the UC8179
    /// uses to pick one of its four fixed waveform rows. Verified against
    /// `EPD_7IN5_V2_Display_4Gray()`: `0xC0`→(0,0), `0x00`→(1,1), `0x80`→(1,0),
    /// `0x40`→(0,1), reading each byte's two-bit fields MSB-first — the same
    /// order as [`Shade`]'s discriminants.
    pub const fn plane_bits(self) -> (bool, bool) {
        match self {
            Shade::White => (false, false),
            Shade::Black => (true, true),
            Shade::Gray1 => (true, false),
            Shade::Gray2 => (false, true),
        }
    }

    /// Quantize an 8-bit luma sample (`0` = black, `255` = white) into one
    /// of the four levels with even thresholds. Not vendor-specified — tune
    /// freely without touching [`plane_bits`].
    pub fn quantize(luma: u8) -> Shade {
        match luma {
            0..=63 => Shade::Black,
            64..=127 => Shade::Gray2,
            128..=191 => Shade::Gray1,
            _ => Shade::White,
        }
    }
}

/// Logical pixels are expanded to `LOGICAL_BLOCK`×`LOGICAL_BLOCK` physical
/// blocks. `2` trades resolution for a planner state (and a demo scene) that
/// comfortably fits ESP32 RAM: 400×240 logical pixels instead of 384,000.
pub const LOGICAL_BLOCK: usize = 2;
pub const LOGICAL_WIDTH: usize = PANEL_WIDTH as usize / LOGICAL_BLOCK;
pub const LOGICAL_HEIGHT: usize = PANEL_HEIGHT as usize / LOGICAL_BLOCK;

pub const PHYSICAL_PIXELS: usize = PANEL_WIDTH as usize * PANEL_HEIGHT as usize;
/// Bytes per plane the panel expects. Matches [`crate::panel::FRAME_BYTES`];
/// a test below checks that directly.
pub const PLANE_BYTES: usize = PHYSICAL_PIXELS / 8;

/// Pixelate a `LOGICAL_WIDTH`×`LOGICAL_HEIGHT` scene to the full panel and
/// pack it into the two planes `grayscale_display::Panel::show_4gray` sends
/// over SPI.
pub fn plan_panel_frame(logical: &[Shade]) -> (Vec<u8>, Vec<u8>) {
    let physical = pixelate(LOGICAL_WIDTH, LOGICAL_HEIGHT, LOGICAL_BLOCK, logical);
    debug_assert_eq!(physical.len(), PHYSICAL_PIXELS);
    pack_4gray_planes(&physical)
}

/// Remembers the logical shade grid most recently handed to the panel, so a
/// scene generator that produces the same picture twice in a row can skip
/// the refresh. This is the UC8179-equivalent of never redriving a pixel
/// that didn't change — but the smallest unit this controller lets the
/// firmware skip is one whole refresh, not one pixel: a single changed
/// logical pixel still means resending and redriving every pixel on the
/// next `show_4gray` call.
#[derive(Default)]
pub struct ChangeTracker {
    last: Option<Vec<Shade>>,
}

impl ChangeTracker {
    pub fn new() -> Self {
        Self::default()
    }

    /// Returns `true`, and remembers `logical`, when it differs from the
    /// frame passed to the previous call (always `true` the first time).
    pub fn changed(&mut self, logical: &[Shade]) -> bool {
        let changed = self.last.as_deref() != Some(logical);
        if changed {
            self.last = Some(logical.to_vec());
        }
        changed
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn plane_bytes_matches_panel_frame_bytes() {
        assert_eq!(PLANE_BYTES, crate::panel::FRAME_BYTES);
    }

    #[test]
    fn logical_dims_tile_the_panel_exactly() {
        assert_eq!(LOGICAL_WIDTH * LOGICAL_BLOCK, PANEL_WIDTH as usize);
        assert_eq!(LOGICAL_HEIGHT * LOGICAL_BLOCK, PANEL_HEIGHT as usize);
    }

    #[test]
    fn plane_bits_match_the_vendor_table() {
        // EPD_7IN5_V2_Display_4Gray(): 0xC0 -> (0,0), 0x00 -> (1,1),
        // 0x80 -> (1,0), 0x40 -> (0,1).
        assert_eq!(Shade::White.plane_bits(), (false, false));
        assert_eq!(Shade::Black.plane_bits(), (true, true));
        assert_eq!(Shade::Gray1.plane_bits(), (true, false));
        assert_eq!(Shade::Gray2.plane_bits(), (false, true));
    }

    #[test]
    fn quantize_covers_the_full_byte_range() {
        assert_eq!(Shade::quantize(0), Shade::Black);
        assert_eq!(Shade::quantize(63), Shade::Black);
        assert_eq!(Shade::quantize(64), Shade::Gray2);
        assert_eq!(Shade::quantize(127), Shade::Gray2);
        assert_eq!(Shade::quantize(128), Shade::Gray1);
        assert_eq!(Shade::quantize(191), Shade::Gray1);
        assert_eq!(Shade::quantize(192), Shade::White);
        assert_eq!(Shade::quantize(255), Shade::White);
    }

    #[test]
    fn plan_panel_frame_produces_panel_sized_planes() {
        let logical = vec![Shade::White; LOGICAL_WIDTH * LOGICAL_HEIGHT];
        let (old, new) = plan_panel_frame(&logical);
        assert_eq!(old.len(), PLANE_BYTES);
        assert_eq!(new.len(), PLANE_BYTES);
    }

    #[test]
    fn change_tracker_flags_only_real_changes() {
        let mut tracker = ChangeTracker::new();
        let a = vec![Shade::White; 4];
        let b = vec![Shade::Black, Shade::White, Shade::White, Shade::White];

        assert!(tracker.changed(&a), "first frame is always a change");
        assert!(!tracker.changed(&a), "identical frame is not a change");
        assert!(tracker.changed(&b), "different frame is a change");
        assert!(
            !tracker.changed(&b),
            "repeating the new frame is not a change"
        );
    }
}
