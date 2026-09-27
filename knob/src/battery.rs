//! Battery divider math.
//!
//! GPIO 1 reads half the cell voltage. A 12-bit conversion at 11 dB
//! attenuation covers about 0 to 3.3 V on the pin, so 0 to 6.6 V at the cell.
//! The pack is a 3.7 V Li-ion. Percent is linear from 3.30 V to 4.20 V.

pub const FULL_SCALE_MV: u32 = 3300;
pub const DIVIDER_NUM: u32 = 2;
pub const DIVIDER_DEN: u32 = 1;
pub const EMPTY_MV: u32 = 3300;
pub const FULL_MV: u32 = 4200;

pub fn millivolts(raw: u16) -> u32 {
    let counts = u32::from(raw.min(4095));
    counts * FULL_SCALE_MV / 4095 * DIVIDER_NUM / DIVIDER_DEN
}

pub fn percent(mv: u32) -> u8 {
    if mv <= EMPTY_MV {
        return 0;
    }
    if mv >= FULL_MV {
        return 100;
    }
    ((mv - EMPTY_MV) * 100 / (FULL_MV - EMPTY_MV)) as u8
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn midscale_is_about_one_cell() {
        let mv = millivolts(2048);
        assert!(mv > 3000 && mv < 3600, "{mv}");
        assert_eq!(percent(3300), 0);
        assert_eq!(percent(4200), 100);
        assert_eq!(percent(3750), 50);
    }
}
