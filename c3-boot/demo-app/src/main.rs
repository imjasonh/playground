//! A demo application for c3-boot.
//!
//! It prints which slot it runs from and a message from flash, then confirms
//! its slot in the boot-state record. That confirmation is the
//! application's side of the update protocol in `docs/formats.md`. The
//! application is untrusted: the bootloader checks it before it runs.

#![no_std]
#![no_main]

use c3_verify::bootstate;
use c3_verify::layout;

/// The version this build reports, set at build time with `C3_DEMO_VERSION`.
const VERSION: u32 = match option_env!("C3_DEMO_VERSION") {
    Some(v) => parse_version(v.as_bytes()),
    None => 0,
};

const fn parse_version(digits: &[u8]) -> u32 {
    let mut n = 0u32;
    let mut i = 0;
    while i < digits.len() {
        n = n * 10 + (digits[i] - b'0') as u32;
        i += 1;
    }
    n
}

/// A message in the flash data window. Reading it proves the bootloader
/// mapped the flash segment.
#[unsafe(link_section = ".flash_rodata")]
#[used]
static FLASH_MESSAGE: [u8; 28] = *b"c3-demo: flash mapping ok\n\0\0";

unsafe extern "C" {
    fn ets_printf(fmt: *const core::ffi::c_char, ...) -> i32;
    fn esp_rom_spiflash_read(src: u32, dest: *mut u32, len: i32) -> i32;
    fn esp_rom_spiflash_write(dest: u32, src: *const u32, len: i32) -> i32;
    fn esp_rom_spiflash_erase_sector(sector: u32) -> i32;
    fn esp_rom_spiflash_unlock() -> i32;
}

core::arch::global_asm!(
    r#"
    .section .text._start, "ax"
    .globl _start
_start:
    la sp, _stack_top
    mv s0, a0
    la t0, _bss_start
    la t1, _bss_end
1:
    bgeu t0, t1, 2f
    sw zero, 0(t0)
    addi t0, t0, 4
    j 1b
2:
    mv a0, s0
    call app_main
3:
    j 3b
"#
);

fn read_record(addr: u32) -> [u8; bootstate::RECORD_LEN] {
    let mut words = [0u32; bootstate::RECORD_LEN / 4];
    // SAFETY: the ROM function fills the 32-byte, word-aligned buffer.
    unsafe {
        esp_rom_spiflash_read(addr, words.as_mut_ptr(), bootstate::RECORD_LEN as i32);
    }
    let mut out = [0u8; bootstate::RECORD_LEN];
    for (chunk, w) in out.as_chunks_mut::<4>().0.iter_mut().zip(words) {
        *chunk = w.to_le_bytes();
    }
    out
}

fn write_record(addr: u32, record: &[u8; bootstate::RECORD_LEN]) {
    let mut words = [0u32; bootstate::RECORD_LEN / 4];
    for (w, chunk) in words.iter_mut().zip(record.as_chunks::<4>().0) {
        *w = u32::from_le_bytes(*chunk);
    }
    // SAFETY: the ROM flash functions read the 32-byte, word-aligned buffer.
    unsafe {
        esp_rom_spiflash_unlock();
        esp_rom_spiflash_erase_sector(addr / layout::SECTOR_SIZE);
        esp_rom_spiflash_write(addr, words.as_ptr(), bootstate::RECORD_LEN as i32);
    }
}

#[unsafe(no_mangle)]
extern "C" fn app_main(slot_index: u32) -> ! {
    // SAFETY: NUL-terminated format strings with matching arguments.
    unsafe {
        ets_printf(
            c"c3-demo: running from slot %d, version %d\n".as_ptr(),
            slot_index,
            VERSION,
        );
        ets_printf(FLASH_MESSAGE.as_ptr().cast());
    }

    let slot = if slot_index == 0 {
        bootstate::Slot::A
    } else {
        bootstate::Slot::B
    };
    let current = bootstate::read(
        &read_record(layout::BOOT_STATE_A_OFFSET),
        &read_record(layout::BOOT_STATE_B_OFFSET),
    );
    if !current.state.is_confirmed(slot)
        || current.state.preferred != slot
        || current.state.trial.is_some()
    {
        let mut next = current.state.without_trial().with_confirmed(slot);
        next.preferred = slot;
        let target = match current.write_target() {
            bootstate::Copy::A => layout::BOOT_STATE_A_OFFSET,
            bootstate::Copy::B => layout::BOOT_STATE_B_OFFSET,
        };
        write_record(target, &bootstate::encode(&next));
        // SAFETY: as above.
        unsafe { ets_printf(c"c3-demo: confirmed slot %d\n".as_ptr(), slot_index) };
    }
    // SAFETY: as above.
    unsafe { ets_printf(c"c3-demo: idle\n".as_ptr()) };
    loop {
        core::hint::spin_loop();
    }
}

#[panic_handler]
fn panic(_: &core::panic::PanicInfo<'_>) -> ! {
    loop {
        core::hint::spin_loop();
    }
}
