//! The boot watchdog.
//!
//! The ROM arms the watchdogs of timer groups 0 and 1 in flash-boot mode,
//! with a timeout of 26,000,000 bus-clock ticks: 1.3 s at the ROM's 20 MHz,
//! and 0.33 s once the bus runs at 80 MHz. A boot takes longer than either.
//! The bootloader turns off timer group 1's and gives timer group 0's a
//! fixed budget counted on the 40 MHz crystal, so the clock switch doesn't
//! change it.
//!
//! The watchdog stays armed through the jump. An application that hangs
//! before it confirms a trial slot is reset, and the next boot counts the
//! trial down. The application feeds the watchdog or turns it off once it
//! runs. Register fields come from ESP-IDF's `timer_group_reg.h`. (hardware)

const TIMG0_BASE: usize = 0x6001_F000;
const TIMG1_BASE: usize = 0x6002_0000;
const WDTCONFIG0: usize = 0x48;
const WDTCONFIG1: usize = 0x4c;
const WDTCONFIG2: usize = 0x50;
const WDTFEED: usize = 0x60;
const WDTWPROTECT: usize = 0x64;
const WDT_WKEY: u32 = 0x50D8_3AA1;

/// `WDTCONFIG0` fields.
const WDT_EN: u32 = 1 << 31;
/// Stage 0 resets the whole chip.
const WDT_STG0_RESET_SYSTEM: u32 = 3 << 29;
const WDT_CONF_UPDATE_EN: u32 = 1 << 22;
const WDT_USE_XTAL: u32 = 1 << 21;
const WDT_CPU_RESET_LENGTH: u32 = 7 << 18;
const WDT_SYS_RESET_LENGTH: u32 = 7 << 15;

/// `WDTCONFIG1`: the crystal divided by 40,000 ticks at 1 kHz. Bit 0, which
/// restarts the divider, stays clear: Espressif's QEMU drops the prescaler
/// to 1 when it's set.
const TICKS_1KHZ: u32 = 40_000 << 16;

/// The time from the start of the bootloader until a reset, unless the
/// application feeds the watchdog or turns it off. One slot check takes
/// about 1.2 s at 160 MHz, and a boot can check both slots. The bound from
/// `maxSteps` isn't computed yet.
const BUDGET_MS: u32 = 10_000;

#[unsafe(link_section = ".text_setup")]
fn write_reg(addr: usize, value: u32) {
    // SAFETY: `addr` is one of a timer group's watchdog registers,
    // word-aligned.
    unsafe { core::ptr::write_volatile(addr as *mut u32, value) }
}

/// Writes `config` to a timer group's `WDTCONFIG0` and latches it.
#[unsafe(link_section = ".text_setup")]
fn configure(base: usize, config: u32) {
    write_reg(base + WDTCONFIG0, config);
    write_reg(base + WDTCONFIG0, config | WDT_CONF_UPDATE_EN);
}

/// Replaces the ROM's flash-boot watchdogs with timer group 0's watchdog
/// set to `BUDGET_MS`.
#[unsafe(link_section = ".text_setup")]
pub fn arm() {
    write_reg(TIMG1_BASE + WDTWPROTECT, WDT_WKEY);
    configure(TIMG1_BASE, 0);
    write_reg(TIMG1_BASE + WDTWPROTECT, 0);

    write_reg(TIMG0_BASE + WDTWPROTECT, WDT_WKEY);
    configure(TIMG0_BASE, 0);
    write_reg(TIMG0_BASE + WDTCONFIG1, TICKS_1KHZ);
    write_reg(TIMG0_BASE + WDTCONFIG2, BUDGET_MS);
    configure(
        TIMG0_BASE,
        WDT_EN | WDT_STG0_RESET_SYSTEM | WDT_USE_XTAL | WDT_CPU_RESET_LENGTH | WDT_SYS_RESET_LENGTH,
    );
    write_reg(TIMG0_BASE + WDTFEED, 1);
    write_reg(TIMG0_BASE + WDTWPROTECT, 0);
}
