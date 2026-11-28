//! The security level: a unary eFuse counter for image anti-rollback.

/// The security level stored in the 16-bit `SECURE_VERSION` field: the
/// number of set bits.
pub fn level_of(secure_version: u16) -> u8 {
    u8::try_from(secure_version.count_ones()).unwrap_or(u8::MAX)
}

/// The mask of the next bit to program to raise the level by one, or `None`
/// if all 16 bits are set.
pub fn next_bit(secure_version: u16) -> Option<u16> {
    let mask = !secure_version & secure_version.wrapping_add(1);
    if mask == 0 { None } else { Some(mask) }
}

/// The level the bootloader must reach before it jumps to a slot.
///
/// That is the slot's level if the boot-state record marks the slot
/// confirmed and its level is higher than the eFuse level, and the eFuse
/// level otherwise.
pub fn burn_target(slot_level: u8, confirmed: bool, efuse_level: u8) -> u8 {
    if confirmed && slot_level > efuse_level {
        slot_level
    } else {
        efuse_level
    }
}

#[cfg(test)]
#[allow(clippy::arithmetic_side_effects, clippy::indexing_slicing)]
mod tests {
    use super::*;

    #[test]
    fn counts_bits_not_binary_value() {
        assert_eq!(level_of(0), 0);
        assert_eq!(level_of(0b100), 1);
        assert_eq!(level_of(0xFFFF), 16);
    }

    #[test]
    fn programs_lowest_clear_bit() {
        assert_eq!(next_bit(0), Some(1));
        assert_eq!(next_bit(0b1011), Some(0b100));
        assert_eq!(next_bit(0xFFFF), None);
        let mut v = 0u16;
        for expected in 1..=16 {
            v |= next_bit(v).unwrap();
            assert_eq!(level_of(v), expected);
        }
    }

    #[test]
    fn burns_only_for_confirmed_higher_slots() {
        assert_eq!(burn_target(5, true, 3), 5);
        assert_eq!(burn_target(5, false, 3), 3);
        assert_eq!(burn_target(3, true, 3), 3);
        assert_eq!(burn_target(2, true, 3), 3);
    }
}
