//! Flash and RAM regions shared by the application, frame store, and factory
//! image tooling.

use crate::panel::FRAME_BYTES;

/// nRF52840 erase-page size.
pub const FLASH_PAGE_BYTES: u32 = 4096;

/// One half-open region in internal flash.
#[derive(Clone, Copy, PartialEq, Eq, Debug)]
pub struct FlashRegion {
    pub start: u32,
    pub end: u32,
}

impl FlashRegion {
    pub const fn len(self) -> u32 {
        self.end - self.start
    }

    pub const fn contains(self, address: u32) -> bool {
        address >= self.start && address < self.end
    }
}

pub const SOFTDEVICE: FlashRegion = FlashRegion {
    start: 0x00000,
    end: 0x1c000,
};
pub const APPLICATION: FlashRegion = FlashRegion {
    start: 0x1c000,
    end: 0x5c000,
};
pub const UPDATE: FlashRegion = FlashRegion {
    start: 0x5c000,
    end: 0x9c000,
};
pub const SETTINGS: FlashRegion = FlashRegion {
    start: 0x9c000,
    end: 0xa0000,
};
pub const FRAME_A: FlashRegion = FlashRegion {
    start: 0xa0000,
    end: 0xac000,
};
pub const FRAME_B: FlashRegion = FlashRegion {
    start: 0xac000,
    end: 0xb8000,
};
pub const FRAME_METADATA: FlashRegion = FlashRegion {
    start: 0xb8000,
    end: 0xba000,
};
pub const FAULT_LOG: FlashRegion = FlashRegion {
    start: 0xba000,
    end: 0xbc000,
};
pub const RESERVED: FlashRegion = FlashRegion {
    start: 0xbc000,
    end: 0xe0000,
};
pub const BOOTLOADER: FlashRegion = FlashRegion {
    start: 0xe0000,
    end: 0xfe000,
};
pub const MBR_PARAMETERS: FlashRegion = FlashRegion {
    start: 0xfe000,
    end: 0xff000,
};
pub const BOOTLOADER_SETTINGS: FlashRegion = FlashRegion {
    start: 0xff000,
    end: 0x100000,
};

pub const FLASH_REGIONS: [FlashRegion; 12] = [
    SOFTDEVICE,
    APPLICATION,
    UPDATE,
    SETTINGS,
    FRAME_A,
    FRAME_B,
    FRAME_METADATA,
    FAULT_LOG,
    RESERVED,
    BOOTLOADER,
    MBR_PARAMETERS,
    BOOTLOADER_SETTINGS,
];

const _: () = assert!(FRAME_A.len() as usize == FRAME_BYTES);
const _: () = assert!(FRAME_B.len() as usize == FRAME_BYTES);
const _: () = assert!(APPLICATION.len() == UPDATE.len());

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn regions_are_page_aligned_contiguous_and_cover_flash() {
        assert_eq!(FLASH_REGIONS[0].start, 0);
        for (index, region) in FLASH_REGIONS.iter().enumerate() {
            assert!(region.start < region.end);
            assert_eq!(region.start % FLASH_PAGE_BYTES, 0);
            assert_eq!(region.end % FLASH_PAGE_BYTES, 0);
            if let Some(next) = FLASH_REGIONS.get(index + 1) {
                assert_eq!(region.end, next.start);
            }
        }
        assert_eq!(FLASH_REGIONS.last().unwrap().end, 1024 * 1024);
    }

    #[test]
    fn operational_regions_have_required_capacity() {
        assert_eq!(SOFTDEVICE.len(), 112 * 1024);
        assert_eq!(APPLICATION.len(), 256 * 1024);
        assert_eq!(UPDATE.len(), 256 * 1024);
        assert_eq!(FRAME_A.len(), FRAME_BYTES as u32);
        assert_eq!(FRAME_B.len(), FRAME_BYTES as u32);
        assert_eq!(FRAME_METADATA.len(), 2 * FLASH_PAGE_BYTES);
        assert_eq!(FAULT_LOG.len(), 2 * FLASH_PAGE_BYTES);
        assert!(BOOTLOADER.len() >= 64 * 1024);
    }

    #[test]
    fn application_linker_script_matches_the_shared_map() {
        let linker = include_str!("../memory-app.x");
        assert!(linker.contains("FLASH : ORIGIN = 0x0001C000,       LENGTH = 256K"));
        assert!(linker.contains("RAM   : ORIGIN = 0x20000000 + 32K, LENGTH = 256K - 32K"));
    }
}
