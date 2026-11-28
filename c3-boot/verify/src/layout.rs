//! The fixed flash layout and memory map from `docs/formats.md`.
//!
//! The memory addresses come from the ESP32-C3 technical reference manual and
//! ESP-IDF, and need checking on a real board.

/// A half-open range of addresses or offsets, `start..end`.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub struct Region {
    /// The first address in the region.
    pub start: u32,
    /// The first address past the region.
    pub end: u32,
}

impl Region {
    /// Reports whether `start..start + len` lies inside this region.
    ///
    /// Returns `false` if `start + len` overflows.
    pub fn contains_range(&self, start: u32, len: u32) -> bool {
        match start.checked_add(len) {
            Some(end) => self.start <= start && end <= self.end,
            None => false,
        }
    }
}

/// Reports whether `a_start..a_start + a_len` and `b_start..b_start + b_len`
/// share an address. Callers pass ranges that don't overflow.
pub fn ranges_overlap(a_start: u32, a_len: u32, b_start: u32, b_len: u32) -> bool {
    match (a_start.checked_add(a_len), b_start.checked_add(b_len)) {
        (Some(a_end), Some(b_end)) => a_start < b_end && b_start < a_end,
        _ => true,
    }
}

/// The flash chip size the layout assumes.
pub const FLASH_SIZE: u32 = 0x40_0000;
/// The size of each OTA slot in flash.
pub const SLOT_SIZE: u32 = 0x1E_0000;
/// The flash offset of slot A.
pub const SLOT_A_OFFSET: u32 = 0x03_0000;
/// The flash offset of slot B.
pub const SLOT_B_OFFSET: u32 = 0x21_0000;
/// The flash offset of boot-state copy A.
pub const BOOT_STATE_A_OFFSET: u32 = 0x02_8000;
/// The flash offset of boot-state copy B.
pub const BOOT_STATE_B_OFFSET: u32 = 0x02_9000;
/// The flash erase-sector size.
pub const SECTOR_SIZE: u32 = 0x1000;
/// The cache's flash page size, which flash segments must align to.
pub const FLASH_PAGE: u32 = 0x1_0000;
/// The slot offset where the signed image starts.
pub const IMAGE_OFFSET: u32 = 0x1_0000;

/// Virtual addresses of the instruction cache's flash window.
pub const FLASH_CODE: Region = Region {
    start: 0x4200_0000,
    end: 0x4280_0000,
};
/// Virtual addresses of the data cache's flash window.
pub const FLASH_DATA: Region = Region {
    start: 0x3C00_0000,
    end: 0x3C80_0000,
};
/// Instruction-bus addresses of the application RAM region.
pub const RAM_CODE: Region = Region {
    start: 0x4038_0000,
    end: 0x403A_0000,
};
/// Data-bus addresses of the application RAM region.
pub const RAM_DATA: Region = Region {
    start: 0x3FC8_0000,
    end: 0x3FCA_0000,
};
/// The distance from an instruction-bus SRAM address down to its data-bus
/// alias.
pub const IRAM_TO_DRAM: u32 = 0x70_0000;

#[cfg(test)]
#[allow(clippy::arithmetic_side_effects, clippy::indexing_slicing)]
mod tests {
    use super::*;

    #[test]
    fn region_rejects_overflow_and_edges() {
        let r = Region { start: 10, end: 20 };
        assert!(r.contains_range(10, 10));
        assert!(!r.contains_range(10, 11));
        assert!(!r.contains_range(9, 1));
        assert!(!r.contains_range(u32::MAX, 2));
    }

    #[test]
    fn overlap_is_half_open() {
        assert!(!ranges_overlap(0, 10, 10, 10));
        assert!(ranges_overlap(0, 11, 10, 10));
        assert!(ranges_overlap(u32::MAX, 2, 0, 1));
    }

    #[test]
    fn ram_views_alias() {
        assert_eq!(RAM_CODE.start - IRAM_TO_DRAM, RAM_DATA.start);
        assert_eq!(RAM_CODE.end - IRAM_TO_DRAM, RAM_DATA.end);
    }
}
