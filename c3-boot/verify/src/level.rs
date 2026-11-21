//! The security level: one unary eFuse counter shared by image anti-rollback
//! and trust-root rotation.

use crate::error::Error;
use crate::image::MAX_SECURITY_VERSION;

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

/// Checks the level rules for one slot.
///
/// The image's security version must be at most 16 and equal the blob's
/// level. The blob's level must be at least the chain's last link level and
/// at least the eFuse level.
pub fn check_slot(
    chain_level: u8,
    blob_level: u8,
    security_version: u8,
    efuse_level: u8,
) -> Result<(), Error> {
    let ok = security_version <= MAX_SECURITY_VERSION
        && security_version == blob_level
        && blob_level >= chain_level
        && blob_level >= efuse_level;
    if ok { Ok(()) } else { Err(Error::BadLevel) }
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
    fn slot_rules() {
        assert_eq!(check_slot(2, 3, 3, 3), Ok(()));
        assert_eq!(check_slot(0, 0, 0, 0), Ok(()));
        assert_eq!(check_slot(2, 3, 4, 3), Err(Error::BadLevel));
        assert_eq!(check_slot(4, 3, 3, 3), Err(Error::BadLevel));
        assert_eq!(check_slot(2, 3, 3, 4), Err(Error::BadLevel));
        assert_eq!(check_slot(2, 2, 2, 3), Err(Error::BadLevel));
        assert_eq!(check_slot(0, 17, 17, 0), Err(Error::BadLevel));
    }

    #[test]
    fn burns_only_for_confirmed_higher_slots() {
        assert_eq!(burn_target(5, true, 3), 5);
        assert_eq!(burn_target(5, false, 3), 3);
        assert_eq!(burn_target(3, true, 3), 3);
        assert_eq!(burn_target(2, true, 3), 3);
    }
}
