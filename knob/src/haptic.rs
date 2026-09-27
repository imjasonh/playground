//! DRV2605 register programs for the onboard LRA.
//!
//! The hardware-explorer sketch found the part at I2C 0x5A and got a strong
//! click from library 5 with CONTROL3 set to 0xA8. Effects 1 through 123 are
//! the ROM library. 1 is a strong click.

pub const ADDR: u8 = 0x5A;
pub const STRONG_CLICK: u8 = 1;
pub const BUZZ: u8 = 47;

pub const REG_MODE: u8 = 0x01;
pub const REG_RTP: u8 = 0x02;
pub const REG_LIBRARY: u8 = 0x03;
pub const REG_WAVESEQ1: u8 = 0x04;
pub const REG_WAVESEQ2: u8 = 0x05;
pub const REG_GO: u8 = 0x0C;
pub const REG_FEEDBACK: u8 = 0x1A;
pub const REG_CONTROL3: u8 = 0x1D;

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub struct Write {
    pub reg: u8,
    pub val: u8,
}

/// Bring the LRA out of standby and select library 5.
pub fn boot() -> [Write; 4] {
    [
        Write {
            reg: REG_MODE,
            val: 0x00,
        },
        Write {
            reg: REG_FEEDBACK,
            val: 0xB6,
        },
        Write {
            reg: REG_CONTROL3,
            val: 0xA8,
        },
        Write {
            reg: REG_LIBRARY,
            val: 5,
        },
    ]
}

/// Play one ROM effect, then stop the sequence.
pub fn play(effect: u8) -> [Write; 4] {
    let effect = effect.clamp(1, 123);
    [
        Write {
            reg: REG_MODE,
            val: 0x00,
        },
        Write {
            reg: REG_WAVESEQ1,
            val: effect,
        },
        Write {
            reg: REG_WAVESEQ2,
            val: 0x00,
        },
        Write {
            reg: REG_GO,
            val: 0x01,
        },
    ]
}

/// Real-time amplitude, 0 silent through 127 full.
pub fn realtime(amplitude: u8) -> [Write; 3] {
    [
        Write {
            reg: REG_MODE,
            val: 0x05,
        },
        Write {
            reg: REG_RTP,
            val: amplitude.min(127),
        },
        Write {
            reg: REG_GO,
            val: 0x01,
        },
    ]
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn boot_selects_the_lra_library() {
        let seq = boot();
        assert!(seq.iter().any(|w| w.reg == REG_LIBRARY && w.val == 5));
        assert!(seq.iter().any(|w| w.reg == REG_CONTROL3 && w.val == 0xA8));
    }

    #[test]
    fn play_clamps_and_fires_go() {
        let seq = play(0);
        assert_eq!(seq[1].val, 1);
        assert_eq!(
            seq[3],
            Write {
                reg: REG_GO,
                val: 1
            }
        );
        assert_eq!(play(200)[1].val, 123);
    }
}
