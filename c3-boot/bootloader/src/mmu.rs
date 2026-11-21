//! The cache's shared MMU table, which maps flash pages into the
//! instruction and data windows.
//!
//! Addresses come from ESP-IDF's `reg_base.h`, `ext_mem_defs.h`, and
//! `extmem_reg.h`. (hardware)

use c3_verify::image::Segment;
use c3_verify::image::SegmentKind;
use c3_verify::layout::FLASH_CODE;
use c3_verify::layout::FLASH_DATA;
use c3_verify::layout::FLASH_PAGE;

const MMU_TABLE: usize = 0x600C_5000;
const MMU_ENTRIES: usize = 128;
const MMU_INVALID: u32 = 1 << 8;
const EXTMEM_ICACHE_CTRL1: usize = 0x600C_4004;
const SHUT_IBUS: u32 = 1 << 0;
const SHUT_DBUS: u32 = 1 << 1;

fn write_entry(index: usize, value: u32) {
    if index < MMU_ENTRIES {
        // SAFETY: `index` is below the table size, so the address is one of
        // the MMU table's word-aligned entries.
        unsafe { core::ptr::write_volatile((MMU_TABLE + 4 * index) as *mut u32, value) }
    }
}

/// Maps the image's flash segments and enables both cache buses.
///
/// `image_flash` is the flash address of the image's first byte. Every
/// segment passed the image checks, so each is page-aligned and inside its
/// window, and no two flash segments share an MMU entry.
pub fn map(image_flash: u32, segments: &[Segment]) -> bool {
    let autoload = crate::rom::cache_suspend();
    for i in 0..MMU_ENTRIES {
        write_entry(i, MMU_INVALID);
    }
    let mut ok = true;
    for s in segments {
        let base = match s.kind {
            SegmentKind::FlashCode => FLASH_CODE.start,
            SegmentKind::FlashData => FLASH_DATA.start,
            SegmentKind::RamCode | SegmentKind::RamData => continue,
        };
        // c3-verify requires whole pages; dividing down means a segment that
        // broke that rule would map less, never bytes past its end.
        let pages = s.length / FLASH_PAGE;
        let first_entry = s.address.wrapping_sub(base) / FLASH_PAGE;
        let first_page = image_flash.wrapping_add(s.offset) / FLASH_PAGE;
        for p in 0..pages {
            let Ok(index) = usize::try_from(first_entry.wrapping_add(p)) else {
                ok = false;
                continue;
            };
            write_entry(index, first_page.wrapping_add(p) & 0xFF);
        }
    }
    // SAFETY: EXTMEM_ICACHE_CTRL1 is the cache controller's bus-shutdown
    // register; clearing both bits enables the instruction and data buses.
    unsafe {
        let v = core::ptr::read_volatile(EXTMEM_ICACHE_CTRL1 as *const u32);
        core::ptr::write_volatile(
            EXTMEM_ICACHE_CTRL1 as *mut u32,
            v & !(SHUT_IBUS | SHUT_DBUS),
        );
    }
    crate::rom::cache_invalidate_and_resume(autoload);
    ok
}
