//! The `SECURE_VERSION` eFuse field: reading the security level and raising
//! it one bit at a time.
//!
//! Register addresses, the program sequence, and the programming timing come
//! from ESP-IDF's `efuse_reg.h`, `efuse_ll.h`, and eFuse HAL, which set the
//! same timing for every clock configuration. (hardware)
//!
//! The programming code exists only in builds with `C3_EFUSE_BURN=on`, so a
//! test build has no path that writes an eFuse.

const EFUSE_BASE: usize = 0x6000_8800;
/// Block 0 bits 128 through 159. Word 0 of block 0 reads through
/// `RD_WR_DIS`, so word 4, which `PGM_DATA4` programs, reads through
/// `RD_REPEAT_DATA3`.
const RD_REPEAT_DATA3: usize = EFUSE_BASE + 0x3c;
/// `SECURE_VERSION` is block 0 bits 142 through 157.
const SECURE_VERSION_SHIFT: u32 = 14;

#[unsafe(link_section = ".text_boot")]
fn read_reg(addr: usize) -> u32 {
    // SAFETY: `addr` is a word-aligned register of the eFuse controller or
    // the permission controller.
    unsafe { core::ptr::read_volatile(addr as *const u32) }
}

#[unsafe(link_section = ".text_boot")]
fn write_reg(addr: usize, value: u32) {
    // SAFETY: `addr` is a word-aligned register of the eFuse controller or
    // the permission controller.
    unsafe { core::ptr::write_volatile(addr as *mut u32, value) }
}

/// The raw 16-bit `SECURE_VERSION` field.
#[unsafe(link_section = ".text_boot")]
pub fn secure_version() -> u16 {
    let word = read_reg(RD_REPEAT_DATA3) >> SECURE_VERSION_SHIFT;
    u16::try_from(word & 0xFFFF).unwrap_or(u16::MAX)
}

#[cfg(c3_efuse_burn)]
pub use program::raise_level;

#[cfg(c3_efuse_burn)]
mod program {
    use super::EFUSE_BASE;
    use super::SECURE_VERSION_SHIFT;
    use super::read_reg;
    use super::secure_version;
    use super::write_reg;

    const PGM_DATA0: usize = EFUSE_BASE;
    const PGM_CHECK_VALUE0: usize = EFUSE_BASE + 0x20;
    const CONF: usize = EFUSE_BASE + 0x1cc;
    const CMD: usize = EFUSE_BASE + 0x1d4;
    const DAC_CONF: usize = EFUSE_BASE + 0x1e8;
    const WR_TIM_CONF1: usize = EFUSE_BASE + 0x1f0;
    const WR_TIM_CONF2: usize = EFUSE_BASE + 0x1f4;
    const OP_CODE_WRITE: u32 = 0x5A5A;
    const OP_CODE_READ: u32 = 0x5AA5;
    const CMD_READ: u32 = 1 << 0;
    const CMD_PGM: u32 = 1 << 1;
    const PGM_WORDS: usize = 8;
    const CHECK_WORDS: usize = 3;
    /// How long to wait for a command before treating the hardware as failed.
    const POLL_LIMIT: u32 = 1_000_000;

    /// Sets `width` bits of the register at `addr`, from bit `shift`, to
    /// `value`.
    #[unsafe(link_section = ".text_boot")]
    fn set_field(addr: usize, shift: u32, width: u32, value: u32) {
        let mask = ((1u32 << width) - 1) << shift;
        write_reg(addr, (read_reg(addr) & !mask) | ((value << shift) & mask));
    }

    /// Sets the programming and read timing: `DAC_CLK_DIV` 0x28, `DAC_NUM`
    /// 0xFF, `PWR_ON_NUM` 0x3000, and `PWR_OFF_NUM` 0x190, as
    /// `efuse_hal_set_timing` does. (hardware)
    #[unsafe(link_section = ".text_boot")]
    fn set_timing() {
        set_field(DAC_CONF, 0, 8, 0x28);
        set_field(DAC_CONF, 9, 8, 0xFF);
        set_field(WR_TIM_CONF1, 8, 16, 0x3000);
        set_field(WR_TIM_CONF2, 0, 16, 0x190);
    }

    /// Runs an eFuse command and waits for it to finish.
    #[unsafe(link_section = ".text_boot")]
    fn run(op_code: u32, cmd: u32) -> bool {
        write_reg(CONF, op_code);
        write_reg(CMD, cmd);
        for _ in 0..POLL_LIMIT {
            if read_reg(CMD) & cmd == 0 {
                return true;
            }
        }
        false
    }

    /// Programs the single `SECURE_VERSION` bit in `mask`, then reloads the
    /// eFuse read registers. Returns whether both commands completed.
    #[unsafe(link_section = ".text_boot")]
    fn program_bit(mask: u16) -> bool {
        set_timing();
        for i in 0..PGM_WORDS {
            write_reg(PGM_DATA0 + 4 * i, 0);
        }
        for i in 0..CHECK_WORDS {
            write_reg(PGM_CHECK_VALUE0 + 4 * i, 0);
        }
        write_reg(PGM_DATA0 + 4 * 4, u32::from(mask) << SECURE_VERSION_SHIFT);
        let programmed = run(OP_CODE_WRITE, CMD_PGM);
        for i in 0..PGM_WORDS {
            write_reg(PGM_DATA0 + 4 * i, 0);
        }
        programmed && run(OP_CODE_READ, CMD_READ)
    }

    /// Raises the security level to `target`, one bit at a time, reading the
    /// level back after each bit. Returns `false` if a bit doesn't read back
    /// as set after three attempts.
    #[unsafe(link_section = ".text_boot")]
    pub fn raise_level(target: u8) -> bool {
        let mut attempts = 0u8;
        loop {
            let current = secure_version();
            if c3_verify::level::level_of(current) >= target {
                return true;
            }
            let Some(mask) = c3_verify::level::next_bit(current) else {
                return false;
            };
            if attempts >= 3 {
                return false;
            }
            program_bit(mask);
            if secure_version() & mask != 0 {
                attempts = 0;
            } else {
                attempts = attempts.saturating_add(1);
            }
        }
    }
}

const SENSITIVE_BASE: usize = 0x600C_1000;
/// `SENSITIVE_REGION_PMS_CONSTRAIN_0_REG`: bit 0 locks every region
/// permission register until reset.
const REGION_PMS_LOCK: usize = SENSITIVE_BASE + 0x104;
/// `SENSITIVE_REGION_PMS_CONSTRAIN_1_REG`: World 0's permissions for areas
/// 0 through 6, two bits each, bit 1 read and bit 0 write.
const REGION_PMS_WORLD0: usize = SENSITIVE_BASE + 0x108;
/// `SENSITIVE_REGION_PMS_CONSTRAIN_3_REG` through `_10_REG`: the eight
/// area boundaries, as word addresses. Area n runs from boundary n to
/// boundary n + 1.
const REGION_PMS_ADDR0: usize = SENSITIVE_BASE + 0x110;
const REGION_PMS_ADDRS: usize = 8;
const EFUSE_END: usize = EFUSE_BASE + 0x800;

/// Locks the eFuse controller against writes until the next reset.
///
/// Region permission control makes area 0 the controller's registers,
/// leaves areas 1 through 6 empty, makes area 0 read-only for World 0,
/// which the bootloader and the application run in, and then locks the
/// region permission registers. Whether a write the lock refuses fails or
/// is dropped, and whether the boundary registers hold word addresses,
/// needs checking on a board. (hardware)
#[unsafe(link_section = ".text_boot")]
pub fn lock() {
    const READ_ONLY: u32 = 0b10;
    write_reg(REGION_PMS_ADDR0, (EFUSE_BASE >> 2) as u32);
    for i in 1..REGION_PMS_ADDRS {
        write_reg(REGION_PMS_ADDR0 + 4 * i, (EFUSE_END >> 2) as u32);
    }
    write_reg(
        REGION_PMS_WORLD0,
        (read_reg(REGION_PMS_WORLD0) & !0b11) | READ_ONLY,
    );
    write_reg(REGION_PMS_LOCK, 1);
}
