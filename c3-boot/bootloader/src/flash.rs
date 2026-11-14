//! Byte-granular flash reads and the boot-state writes, on top of the ROM's
//! word-aligned flash functions.

/// The size of the aligned bounce buffer for unaligned reads.
const BOUNCE_WORDS: usize = 64;

/// Reads `out.len()` bytes from flash at `addr`, which needn't be aligned.
pub fn read(addr: u32, out: &mut [u8]) -> bool {
    let mut bounce = [0u32; BOUNCE_WORDS];
    let mut done = 0usize;
    while done < out.len() {
        let Ok(offset) = u32::try_from(done) else {
            return false;
        };
        let Some(pos) = addr.checked_add(offset) else {
            return false;
        };
        let aligned = pos & !3;
        let skip = (pos - aligned) as usize;
        let want = (out.len() - done).min(BOUNCE_WORDS * 4 - skip);
        let words = (skip + want).div_ceil(4);
        let Some(chunk) = bounce.get_mut(..words) else {
            return false;
        };
        if !crate::rom::flash_read_words(aligned, chunk) {
            return false;
        }
        for (i, dst) in out.iter_mut().skip(done).take(want).enumerate() {
            let byte = skip + i;
            let word = bounce.get(byte / 4).copied().unwrap_or(0);
            *dst = word.to_le_bytes().get(byte % 4).copied().unwrap_or(0);
        }
        done += want;
    }
    true
}

/// Copies `len` bytes from flash at `src` to RAM at `dest`. All three are
/// multiples of 4, which the image checks guarantee for RAM segments.
///
/// # Safety
///
/// `dest..dest + len` must be RAM that nothing else uses, outside the
/// bootloader's own memory.
pub unsafe fn copy_to_ram(src: u32, dest: u32, len: u32) -> bool {
    let words = (len / 4) as usize;
    // SAFETY: the caller guarantees the destination range is unused RAM, and
    // the image checks make it 4-aligned.
    let target = unsafe { core::slice::from_raw_parts_mut(dest as *mut u32, words) };
    crate::rom::flash_read_words(src, target)
}

/// Erases the sector at `addr` and writes `record` at its start.
pub fn write_record(addr: u32, record: &[u8; c3_verify::bootstate::RECORD_LEN]) -> bool {
    let mut words = [0u32; c3_verify::bootstate::RECORD_LEN / 4];
    for (w, chunk) in words.iter_mut().zip(record.as_chunks::<4>().0) {
        *w = u32::from_le_bytes(*chunk);
    }
    crate::rom::flash_erase_sector(addr / c3_verify::layout::SECTOR_SIZE)
        && crate::rom::flash_write_words(addr, &words)
}
