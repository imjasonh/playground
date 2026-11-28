//! ESP32-C3 ROM functions that the bootloader calls.
//!
//! `rom.x` gives each function's address, from ESP-IDF's `esp32c3.rom.ld`.
//! These functions are the plan's ROM hooks: the proofs use their contracts,
//! not their code. (hardware)

/// A ROM flash function's success result.
const SPIFLASH_OK: i32 = 0;

unsafe extern "C" {
    fn esp_rom_spiflash_read(src: u32, dest: *mut u32, len: i32) -> i32;
    fn esp_rom_spiflash_write(dest: u32, src: *const u32, len: i32) -> i32;
    fn esp_rom_spiflash_erase_sector(sector: u32) -> i32;
    fn esp_rom_spiflash_unlock() -> i32;
    fn Cache_Suspend_ICache() -> u32;
    fn Cache_Resume_ICache(autoload: u32);
    fn Cache_Invalidate_ICache_All();
    fn ets_printf(fmt: *const core::ffi::c_char, ...) -> i32;
    /// Points to the ROM flash driver's state, which starts with its
    /// `esp_rom_spiflash_chip_t`: `device_id`, then `chip_size`.
    static rom_spiflash_legacy_data: *mut u32;
}

/// Sets the flash size that the ROM flash functions check addresses against.
///
/// The ROM refuses reads and writes past the size it was given, which need
/// not cover the whole chip. ESP-IDF's bootloader sets the same field in
/// `bootloader_flash_update_size`. (hardware)
#[unsafe(link_section = ".text_boot")]
pub fn set_flash_size(bytes: u32) {
    // SAFETY: the ROM sets this pointer before it runs the bootloader, and
    // the word after `device_id` is `chip_size`.
    unsafe {
        let chip = rom_spiflash_legacy_data;
        chip.add(1).write_volatile(bytes);
    }
}

/// Reads `dest.len()` words from flash at `src`, which must be 4-aligned.
#[unsafe(link_section = ".text_boot")]
pub fn flash_read_words(src: u32, dest: &mut [u32]) -> bool {
    let Ok(len) = i32::try_from(dest.len().saturating_mul(4)) else {
        return false;
    };
    // SAFETY: the ROM function writes exactly `len` bytes to `dest`, a valid,
    // aligned, exclusive buffer of that size.
    unsafe { esp_rom_spiflash_read(src, dest.as_mut_ptr(), len) == SPIFLASH_OK }
}

/// Writes `src` to flash at `dest`, which must be 4-aligned and erased.
#[unsafe(link_section = ".text_boot")]
pub fn flash_write_words(dest: u32, src: &[u32]) -> bool {
    let Ok(len) = i32::try_from(src.len().saturating_mul(4)) else {
        return false;
    };
    // SAFETY: the ROM functions read exactly `len` bytes from `src`, a valid
    // buffer of that size.
    unsafe {
        esp_rom_spiflash_unlock() == SPIFLASH_OK
            && esp_rom_spiflash_write(dest, src.as_ptr(), len) == SPIFLASH_OK
    }
}

/// Erases the 4 KiB flash sector with index `sector`.
#[unsafe(link_section = ".text_boot")]
pub fn flash_erase_sector(sector: u32) -> bool {
    // SAFETY: the ROM functions take no pointers.
    unsafe {
        esp_rom_spiflash_unlock() == SPIFLASH_OK
            && esp_rom_spiflash_erase_sector(sector) == SPIFLASH_OK
    }
}

/// Suspends the instruction cache and returns its autoload state.
#[unsafe(link_section = ".text_boot")]
pub fn cache_suspend() -> u32 {
    // SAFETY: the ROM function takes no arguments.
    unsafe { Cache_Suspend_ICache() }
}

/// Invalidates the instruction cache and resumes it with `autoload`.
#[unsafe(link_section = ".text_boot")]
pub fn cache_invalidate_and_resume(autoload: u32) {
    // SAFETY: the ROM functions take no pointers.
    unsafe {
        Cache_Invalidate_ICache_All();
        Cache_Resume_ICache(autoload);
    }
}

/// Prints a message with one number through the ROM's UART console.
/// `message` has at most one `%x` conversion. Call it through [`log!`].
#[unsafe(link_section = ".text_boot")]
pub fn print(message: &'static core::ffi::CStr, value: u32) {
    // SAFETY: `message` is NUL-terminated with at most one conversion, which
    // `value` supplies.
    unsafe {
        ets_printf(message.as_ptr(), value);
    }
}

/// Prints `$text`, a string literal with at most one `%x` conversion, with
/// the number `$value`. The text goes in `.rodata_boot`, which
/// `bootloader.x` links after the libraries' constants, so that changing a
/// message moves no library constant.
macro_rules! log {
    ($text:literal, $value:expr) => {{
        const TEXT: &str = concat!($text, "\0");
        #[unsafe(link_section = ".rodata_boot")]
        static BYTES: [u8; TEXT.len()] = *TEXT.as_bytes().first_chunk().unwrap();
        const MESSAGE: &core::ffi::CStr = match core::ffi::CStr::from_bytes_with_nul(&BYTES) {
            Ok(m) => m,
            Err(_) => panic!("a log message holds a NUL"),
        };
        $crate::rom::print(MESSAGE, $value)
    }};
}
pub(crate) use log;
