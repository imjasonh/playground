//! Custom UC8179 waveform tables for one short drive step per refresh.
//!
//! The register format comes from GxEPD2's driver for this panel
//! (<https://github.com/ZinggJM/GxEPD2>, `src/epd/GxEPD2_750_T7.cpp`,
//! panel GDEW075T7 = Waveshare 7.5″ V2), which writes its own fast-partial
//! tables to registers `0x20`-`0x25`. Each register holds 42 bytes: up to
//! seven 6-byte groups, zero-filled after the last one used. A group is
//! `[levels, frames₁, frames₂, frames₃, frames₄, repeat]`, where `levels`
//! packs four 2-bit voltage selections, MSB first, one per phase. GxEPD2's
//! comments give `01` as the black-ward level and `10` as the white-ward
//! level; `00` holds the pixel.
//!
//! These tables use only the first phase of one group: hold, push black,
//! or push white for [`DriveLuts::frames`] frames. The voltages the levels
//! select are set elsewhere (power setting `0x01`, unchanged from
//! Waveshare's init), so a table can choose how long a pixel is driven but
//! not how hard.
//!
//! The controller picks a pixel's table from its `(old, new)` plane bits:
//! `WW` = `(0, 0)`, `KW` = `(1, 0)`, `WK` = `(0, 1)`, `KK` = `(1, 1)`. The
//! drive planner keeps a pixel's direction in the old plane and sets the new
//! plane to differ from it only when the pixel should move, so `WW` and `KK`
//! hold, `WK` pushes black, and `KW` pushes white.

pub const LUT_REGISTER_BYTES: usize = 42;

pub const CMD_LUT_VCOM: u8 = 0x20;
pub const CMD_LUT_WW: u8 = 0x21;
pub const CMD_LUT_KW: u8 = 0x22;
pub const CMD_LUT_WK: u8 = 0x23;
pub const CMD_LUT_KK: u8 = 0x24;
pub const CMD_LUT_BD: u8 = 0x25;

const LEVEL_HOLD: u8 = 0b00_00_00_00;
const LEVEL_BLACK: u8 = 0b01_00_00_00;
const LEVEL_WHITE: u8 = 0b10_00_00_00;

/// Panel setting `0x00`: GxEPD2's "LUT from registers" value. Waveshare's
/// OTP-waveform init uses `0x1F`.
pub const PANEL_SETTING_REGISTER_LUT: u8 = 0x3F;

/// VCOM and data interval `0x50`. GxEPD2's partial init sends `0x39, 0x07`;
/// this clears bit 3 (N2OCP, "copy new to old"), so the old plane keeps each
/// pixel's drive direction across refreshes instead of being overwritten.
pub const VCOM_DATA_INTERVAL: [u8; 2] = [0x31, 0x07];

/// VCOM DC `0x82`: GxEPD2's partial-mode value (−2.0 V).
pub const VCOM_DC: u8 = 0x26;

/// One table per `0x20`-`0x25` register, in register order.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct DriveLuts {
    pub frames: u8,
    pub registers: [(u8, [u8; LUT_REGISTER_BYTES]); 6],
}

impl DriveLuts {
    /// Build tables that drive for `frames` frames per refresh.
    /// `swap_polarity` exchanges the black and white pushes, for a panel
    /// whose plane polarity turns out opposite to GxEPD2's comments.
    pub fn new(frames: u8, swap_polarity: bool) -> Self {
        assert!(frames > 0, "a drive step needs at least one frame");
        let (to_black, to_white) = if swap_polarity {
            (LEVEL_WHITE, LEVEL_BLACK)
        } else {
            (LEVEL_BLACK, LEVEL_WHITE)
        };
        let row = |level: u8| {
            let mut bytes = [0u8; LUT_REGISTER_BYTES];
            bytes[..6].copy_from_slice(&[level, frames, 0, 0, 0, 1]);
            bytes
        };
        Self {
            frames,
            registers: [
                (CMD_LUT_VCOM, row(LEVEL_HOLD)),
                (CMD_LUT_WW, row(LEVEL_HOLD)),
                (CMD_LUT_KW, row(to_white)),
                (CMD_LUT_WK, row(to_black)),
                (CMD_LUT_KK, row(LEVEL_HOLD)),
                (CMD_LUT_BD, row(LEVEL_HOLD)),
            ],
        }
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    impl DriveLuts {
        fn register(&self, command: u8) -> &[u8; LUT_REGISTER_BYTES] {
            &self
                .registers
                .iter()
                .find(|(c, _)| *c == command)
                .expect("every LUT register is present")
                .1
        }
    }

    #[test]
    fn registers_are_in_order_and_42_bytes() {
        let luts = DriveLuts::new(1, false);
        let commands: Vec<u8> = luts.registers.iter().map(|(c, _)| *c).collect();
        assert_eq!(commands, vec![0x20, 0x21, 0x22, 0x23, 0x24, 0x25]);
    }

    #[test]
    fn only_the_first_group_is_used() {
        let luts = DriveLuts::new(3, false);
        for (_, bytes) in &luts.registers {
            assert_eq!(bytes[1], 3, "phase-1 frame count");
            assert_eq!(&bytes[2..5], &[0, 0, 0], "phases 2-4 unused");
            assert_eq!(bytes[5], 1, "group runs once");
            assert!(bytes[6..].iter().all(|&b| b == 0), "groups 2-7 empty");
        }
    }

    #[test]
    fn wk_pushes_black_kw_pushes_white_others_hold() {
        let luts = DriveLuts::new(1, false);
        assert_eq!(luts.register(CMD_LUT_WK)[0], 0x40);
        assert_eq!(luts.register(CMD_LUT_KW)[0], 0x80);
        for hold in [CMD_LUT_VCOM, CMD_LUT_WW, CMD_LUT_KK, CMD_LUT_BD] {
            assert_eq!(luts.register(hold)[0], 0x00);
        }
    }

    #[test]
    fn swapped_polarity_exchanges_only_the_pushes() {
        let normal = DriveLuts::new(2, false);
        let swapped = DriveLuts::new(2, true);
        assert_eq!(swapped.register(CMD_LUT_WK), normal.register(CMD_LUT_KW));
        assert_eq!(swapped.register(CMD_LUT_KW), normal.register(CMD_LUT_WK));
        assert_eq!(swapped.register(CMD_LUT_WW), normal.register(CMD_LUT_WW));
    }

    #[test]
    fn vcom_interval_differs_from_gxepd2_only_in_n2ocp() {
        const GXEPD2_PARTIAL: u8 = 0x39;
        const N2OCP: u8 = 1 << 3;
        assert_eq!(VCOM_DATA_INTERVAL[0] ^ GXEPD2_PARTIAL, N2OCP);
        assert_eq!(VCOM_DATA_INTERVAL[0] & N2OCP, 0);
    }
}
