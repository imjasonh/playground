//! The `SECURE_VERSION` eFuse field: reading the security level and raising
//! it one bit at a time.
//!
//! Register addresses and the program sequence come from ESP-IDF's
//! `efuse_reg.h` and eFuse HAL. Programming timing on real silicon depends on
//! the clock configuration and needs checking on a board. (hardware)

const EFUSE_BASE: usize = 0x6000_8800;
const PGM_DATA0: usize = EFUSE_BASE;
const PGM_CHECK_VALUE0: usize = EFUSE_BASE + 0x20;
/// Block 0 bits 128 through 159. Word 0 of block 0 reads through
/// `RD_WR_DIS`, so word 4, which `PGM_DATA4` programs, reads through
/// `RD_REPEAT_DATA3`.
const RD_REPEAT_DATA3: usize = EFUSE_BASE + 0x3c;
const CONF: usize = EFUSE_BASE + 0x1cc;
const CMD: usize = EFUSE_BASE + 0x1d4;
const OP_CODE_WRITE: u32 = 0x5A5A;
const OP_CODE_READ: u32 = 0x5AA5;
const CMD_READ: u32 = 1 << 0;
const CMD_PGM: u32 = 1 << 1;
/// `SECURE_VERSION` is block 0 bits 142 through 157.
const SECURE_VERSION_SHIFT: u32 = 14;
const PGM_WORDS: usize = 8;
const CHECK_WORDS: usize = 3;
/// How long to wait for a command before treating the hardware as failed.
const POLL_LIMIT: u32 = 1_000_000;

fn read_reg(addr: usize) -> u32 {
    // SAFETY: `addr` is one of the eFuse controller's word-aligned registers.
    unsafe { core::ptr::read_volatile(addr as *const u32) }
}

fn write_reg(addr: usize, value: u32) {
    // SAFETY: `addr` is one of the eFuse controller's word-aligned registers.
    unsafe { core::ptr::write_volatile(addr as *mut u32, value) }
}

/// Runs an eFuse command and waits for it to finish.
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

/// The raw 16-bit `SECURE_VERSION` field.
pub fn secure_version() -> u16 {
    let word = read_reg(RD_REPEAT_DATA3) >> SECURE_VERSION_SHIFT;
    u16::try_from(word & 0xFFFF).unwrap_or(u16::MAX)
}

/// Programs the single `SECURE_VERSION` bit in `mask`, then reloads the
/// eFuse read registers. Returns whether both commands completed.
fn program_bit(mask: u16) -> bool {
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
/// level back after each bit. Returns `false` if a bit doesn't read back as
/// set after three attempts.
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

/// Locks the eFuse controller against writes until the next reset.
///
/// Not implemented yet. Which protection unit can lock the controller's
/// registers against machine-mode code is a phase 0 hardware question, and
/// the lock is a release blocker. (hardware)
pub fn lock() {}
