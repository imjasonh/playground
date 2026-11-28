//! The CPU clock.
//!
//! The ROM runs the CPU from the 40 MHz crystal divided by 2, so a boot
//! that takes 1.2 s at 160 MHz takes 9.3 s at the ROM's 20 MHz. The ROM's
//! USB console already runs the 480 MHz PLL, so selecting it and its 160 MHz
//! divider is enough; the bus clock becomes 80 MHz. Register fields come from
//! ESP-IDF's `system_reg.h`. Measured on an ESP32-C3 v0.4 powered over USB.
//! (hardware)

const CPU_PER_CONF: usize = 0x600C_0008;
const SYSCLK_CONF: usize = 0x600C_0058;
/// `CPUPERIOD_SEL`, bits 0 and 1: 1 selects 160 MHz from the PLL.
const CPUPERIOD_MASK: u32 = 0b11;
const CPUPERIOD_160: u32 = 1;
/// `PRE_DIV_CNT`, bits 0 through 9, and `SOC_CLK_SEL`, bits 10 and 11, where
/// 1 selects the PLL.
const SYSCLK_MASK: u32 = 0xFFF;
const SOC_CLK_PLL: u32 = 1 << 10;

#[unsafe(link_section = ".text_setup")]
fn read_reg(addr: usize) -> u32 {
    // SAFETY: `addr` is one of the system registers above, word-aligned.
    unsafe { core::ptr::read_volatile(addr as *const u32) }
}

#[unsafe(link_section = ".text_setup")]
fn write_reg(addr: usize, value: u32) {
    // SAFETY: `addr` is one of the system registers above, word-aligned.
    unsafe { core::ptr::write_volatile(addr as *mut u32, value) }
}

/// Runs the CPU at 160 MHz from the PLL.
#[unsafe(link_section = ".text_setup")]
pub fn run_at_160mhz() {
    write_reg(
        CPU_PER_CONF,
        (read_reg(CPU_PER_CONF) & !CPUPERIOD_MASK) | CPUPERIOD_160,
    );
    write_reg(
        SYSCLK_CONF,
        (read_reg(SYSCLK_CONF) & !SYSCLK_MASK) | SOC_CLK_PLL,
    );
}
