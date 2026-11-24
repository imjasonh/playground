//! The c3-boot second-stage bootloader for the ESP32-C3.
//!
//! The ROM loads this image into SRAM and jumps to `_start`. The bootloader
//! reads the boot-state record, checks slots with `c3-verify` from the
//! pinned Sigstore TUF root and the release identity policy compiled into
//! it, raises the security level for a confirmed slot, loads and maps the
//! chosen image, and jumps to it. Every decision comes from `c3-verify`;
//! this crate only moves bytes and touches hardware.
//!
//! The crate's functions and constants are in `.text_boot` and
//! `.rodata_boot`, which `bootloader.x` links after the libraries' code and
//! constants, so that a change confined to this crate moves no library
//! function or constant.

#![no_std]
#![no_main]

mod clock;
mod efuse;
mod flash;
mod mmu;
mod rom;
mod watchdog;

use c3_verify::boot::Outcome;
use c3_verify::boot::decide;
use c3_verify::bootstate::Current;
use c3_verify::bootstate::Slot;
use c3_verify::bootstate::State;
use c3_verify::image::SegmentKind;
use c3_verify::layout;
use c3_verify::tuf::MAX_DOC_LEN;
use c3_verify::tuf::Source;
use c3_verify::tuf::TufError;
use c3_verify::tuf_slot::Accepted;
use c3_verify::tuf_slot::TufSlotParts;

use rom::log;

/// The pinned Sigstore TUF root, in canonical JSON, and the release
/// identity policy `POLICY`, from `build.rs`.
mod pinned {
    use c3_verify::trustroot::Policy;

    include!(concat!(env!("OUT_DIR"), "/pinned.rs"));
}

const MAX_HEADER: usize = 20 + 16 * c3_verify::image::MAX_SEGMENTS;
const MAX_BUNDLE: usize = 16_384;
const DOC: usize = MAX_DOC_LEN as usize;
/// `trusted_root::buffer_len(MAX_DOC_LEN)`: room for the keys of the
/// longest `trusted_root.json`.
const KEYS: usize = 2 * DOC + 64;

core::arch::global_asm!(
    r#"
    .section .text._start, "ax"
    .globl _start
_start:
    la sp, _stack_top
    la t0, _bss_start
    la t1, _bss_end
1:
    bgeu t0, t1, 2f
    sw zero, 0(t0)
    addi t0, t0, 4
    j 1b
2:
    call setup
3:
    j 3b
"#
);

/// Buffers for one slot's parts. They live on the stack, inside the
/// bootloader's own memory. `doc` holds each chunk of the image while it is
/// hashed, then each document of the TUF part in turn.
struct Buffers {
    header: [u8; MAX_HEADER],
    bundle: [u8; MAX_BUNDLE],
    doc: [u8; DOC],
    keys: [u8; KEYS],
}

/// A slot's TUF part in flash, which `c3-verify` reads one document at a
/// time.
#[derive(Clone, Copy)]
struct FlashPart {
    addr: u32,
    length: u32,
}

impl Source for FlashPart {
    #[unsafe(link_section = ".text_boot")]
    fn read(&mut self, offset: u32, out: &mut [u8]) -> bool {
        let Ok(n) = u32::try_from(out.len()) else {
            return false;
        };
        let in_part = offset.checked_add(n).is_some_and(|end| end <= self.length);
        in_part
            && self
                .addr
                .checked_add(offset)
                .is_some_and(|addr| flash::read(addr, out))
    }
}

#[unsafe(link_section = ".text_boot")]
fn slot_base(slot: Slot) -> u32 {
    match slot {
        Slot::A => layout::SLOT_A_OFFSET,
        Slot::B => layout::SLOT_B_OFFSET,
    }
}

#[unsafe(link_section = ".text_boot")]
fn record_addr(copy: c3_verify::bootstate::Copy) -> u32 {
    match copy {
        c3_verify::bootstate::Copy::A => layout::BOOT_STATE_A_OFFSET,
        c3_verify::bootstate::Copy::B => layout::BOOT_STATE_B_OFFSET,
    }
}

#[unsafe(link_section = ".text_boot")]
fn halt(code: u32) -> ! {
    log!("c3-boot: halt %x\n", code);
    loop {
        core::hint::spin_loop();
    }
}

/// Reads one region of a slot into `buf` and returns the filled prefix.
#[unsafe(link_section = ".text_boot")]
fn read_part(base: u32, part: c3_verify::manifest::Part, buf: &mut [u8]) -> Option<&[u8]> {
    let len = usize::try_from(part.length).ok()?;
    let dst = buf.get_mut(..len)?;
    let addr = base.checked_add(part.offset)?;
    flash::read(addr, dst).then_some(&*dst)
}

/// Checks one slot and returns what `c3-verify` accepted, with the flash
/// address of the image. Logs when the slot can't be booted.
#[unsafe(link_section = ".text_boot")]
fn check(slot: Slot, efuse_level: u8, b: &mut Buffers) -> Option<(Accepted, u32)> {
    let result = check_slot(slot, efuse_level, b);
    if result.is_none() {
        let index = match slot {
            Slot::A => 0xA,
            Slot::B => 0xB,
        };
        log!("c3-boot: slot %x not bootable\n", index);
    }
    result
}

/// The number a rejection logs: the `c3_verify::Error` index for a shared
/// check, or 0x100 plus the variant's index for a TUF error.
#[unsafe(link_section = ".text_boot")]
fn reason(e: TufError) -> u32 {
    match e {
        TufError::Json => 0x100,
        TufError::Schema => 0x101,
        TufError::Version => 0x102,
        TufError::Threshold => 0x103,
        TufError::Target => 0x104,
        TufError::Expired => 0x105,
        TufError::Read => 0x106,
        TufError::Check(e) => e as u32,
    }
}

/// Reads and hashes one slot from flash and passes it to `c3-verify`.
#[unsafe(link_section = ".text_boot")]
fn check_slot(slot: Slot, efuse_level: u8, b: &mut Buffers) -> Option<(Accepted, u32)> {
    let base = slot_base(slot);
    let mut raw = [0u8; c3_verify::manifest::MANIFEST_LEN];
    if !flash::read(base, &mut raw) {
        return None;
    }
    let m = c3_verify::manifest::parse(&raw).ok()?;
    let image_flash = base.checked_add(m.image.offset)?;

    let header_len = usize::try_from(m.image.length).ok()?.min(MAX_HEADER);
    let header = b.header.get_mut(..header_len)?;
    if !flash::read(image_flash, header) {
        return None;
    }

    let mut hasher = c3_crypto::Sha256::new();
    let mut done = 0u32;
    while done < m.image.length {
        let n = (m.image.length - done).min(DOC as u32);
        let chunk = b.doc.get_mut(..n as usize)?;
        if !flash::read(image_flash.checked_add(done)?, chunk) {
            return None;
        }
        hasher.update(chunk);
        done += n;
    }
    let image_digest = hasher.finish();

    let bundle = read_part(base, m.bundle, &mut b.bundle)?;
    let tuf = FlashPart {
        addr: base.checked_add(m.tuf.offset)?,
        length: m.tuf.length,
    };
    let parts = TufSlotParts {
        image_header: b.header.get(..header_len)?,
        image_length: m.image.length,
        image_digest,
        bundle,
        tuf,
        tuf_length: m.tuf.length,
    };
    match c3_verify::tuf_slot::accept_slot(
        parts,
        &pinned::ROOT,
        &pinned::POLICY,
        efuse_level,
        &mut b.doc,
        &mut b.keys,
    ) {
        Ok(accepted) => Some((accepted, image_flash)),
        Err(e) => {
            log!("c3-boot: slot rejected %x\n", reason(e));
            None
        }
    }
}

/// Writes `state` to the copy not in use. A failed write leaves the record
/// as it was, which the next boot reads again.
#[unsafe(link_section = ".text_boot")]
fn write_state(current: &Current, state: &State) {
    let record = c3_verify::bootstate::encode(state);
    if !flash::write_record(record_addr(current.write_target()), &record) {
        log!("c3-boot: boot-state write failed %x\n", 0);
    }
}

/// Raises the eFuse level to `target`, which can't be undone.
#[cfg(c3_efuse_burn)]
#[unsafe(link_section = ".text_boot")]
fn raise(target: u8) {
    log!("c3-boot: raising security level to %x\n", u32::from(target));
    if efuse::raise_level(target) {
        return;
    }
    // A test board must stay updatable, so a development build boots the
    // accepted slot without the raise rather than halting on every boot.
    #[cfg(c3_dev_root)]
    log!("c3-boot: raise failed; booting without it %x\n", 0);
    #[cfg(not(c3_dev_root))]
    halt(0xE1);
}

/// Logs the raise that a build with `C3_EFUSE_BURN=on` would make.
#[cfg(not(c3_efuse_burn))]
#[unsafe(link_section = ".text_boot")]
fn raise(target: u8) {
    log!(
        "c3-boot: eFuse burns off; not raising security level to %x\n",
        u32::from(target)
    );
}

/// Raises the level if needed, loads and maps the image, and jumps to it.
#[unsafe(link_section = ".text_boot")]
fn boot(slot: Slot, accepted: &Accepted, image_flash: u32, target: u8, efuse_level: u8) -> ! {
    if target > efuse_level {
        raise(target);
    }
    efuse::lock();

    let segments = accepted.header.segments();
    for s in segments {
        let dest = match s.kind {
            SegmentKind::RamCode => s.address - layout::IRAM_TO_DRAM,
            SegmentKind::RamData => s.address,
            SegmentKind::FlashCode | SegmentKind::FlashData => continue,
        };
        // SAFETY: the image checks put every RAM segment inside the
        // application RAM region, which is outside the bootloader's memory and
        // unused until the application starts, and make it word-aligned.
        if !unsafe { flash::copy_to_ram(image_flash + s.offset, dest, s.length) } {
            halt(0xE2);
        }
    }
    if !mmu::map(image_flash, segments) {
        halt(0xE3);
    }
    log!("c3-boot: jumping to %x\n", accepted.header.entry_point);
    let slot_index = match slot {
        Slot::A => 0,
        Slot::B => 1,
    };
    // SAFETY: the entry point lies in an executable segment of an image that
    // passed every check, and that segment is now loaded or mapped. The
    // application receives the slot index in a0, as docs/formats.md says.
    let entry: extern "C" fn(u32) -> ! =
        unsafe { core::mem::transmute(accepted.header.entry_point as usize) };
    entry(slot_index)
}

/// Replaces the ROM's watchdogs and clock, then boots. Everything it runs
/// is in `.text_setup`, which `bootloader.x` links after the rest of the
/// code, so that a change here moves no function the proofs cover.
#[unsafe(no_mangle)]
#[unsafe(link_section = ".text_setup")]
extern "C" fn setup() -> ! {
    // The ROM's watchdog counts bus-clock ticks, so replace it before the
    // clock switch shortens it.
    watchdog::arm();
    clock::run_at_160mhz();
    boot_main()
}

#[unsafe(no_mangle)]
#[unsafe(link_section = ".text_boot")]
extern "C" fn boot_main() -> ! {
    log!("c3-boot: start %x\n", 0);
    #[cfg(c3_dev_root)]
    log!(
        "c3-boot: WARNING: built with the public development TUF root %x\n",
        0
    );
    rom::set_flash_size(layout::FLASH_SIZE);
    let mut a = [0u8; c3_verify::bootstate::RECORD_LEN];
    let mut b = [0u8; c3_verify::bootstate::RECORD_LEN];
    let read_ok = flash::read(layout::BOOT_STATE_A_OFFSET, &mut a)
        && flash::read(layout::BOOT_STATE_B_OFFSET, &mut b);
    if !read_ok {
        halt(0xE4);
    }
    let current = c3_verify::bootstate::read(&a, &b);
    let efuse_level = c3_verify::level::level_of(efuse::secure_version());
    log!("c3-boot: security level %x\n", u32::from(efuse_level));

    let mut buffers = Buffers {
        header: [0; MAX_HEADER],
        bundle: [0; MAX_BUNDLE],
        doc: [0; DOC],
        keys: [0; KEYS],
    };
    let outcome = decide(
        &current.state,
        efuse_level,
        |slot| check(slot, efuse_level, &mut buffers).map(|found| (found, found.0.level)),
        |state| write_state(&current, state),
    );
    match outcome {
        Outcome::Boot {
            slot,
            accepted: (accepted, image_flash),
            level_target,
        } => boot(slot, &accepted, image_flash, level_target, efuse_level),
        Outcome::Halt => halt(0xE5),
    }
}

#[panic_handler]
#[unsafe(link_section = ".text_boot")]
fn panic(_: &core::panic::PanicInfo<'_>) -> ! {
    halt(0xEF)
}
