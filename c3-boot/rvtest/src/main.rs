//! Lockstep test firmware for the Lean RV32 model. The ROM loads it as the
//! bootloader. For each generated case it copies the case's memory into the
//! test buffer, runs the case, and prints the sequence's address, the
//! registers it ended with, and the buffer, for `rv-check` to compare with
//! the Lean model's run.

#![no_std]
#![no_main]

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
    call rv_main
3:
    j 3b
"#
);

core::arch::global_asm!(include_str!(concat!(env!("OUT_DIR"), "/cases.S")));

unsafe extern "C" {
    fn ets_printf(fmt: *const core::ffi::c_char, ...) -> i32;
    static rv_cases: [Case; 0];
    static rv_case_count: u32;
    fn rv_call(entry: unsafe extern "C" fn());
}

/// One generated case: its entry point, its sequence's address, and its
/// initial registers and memory.
#[repr(C)]
struct Case {
    run: unsafe extern "C" fn(),
    seq: u32,
    init: *const u32,
    mem: *const u8,
}

/// Callee-saved registers, saved while a case runs.
#[unsafe(no_mangle)]
static mut RV_SAVE: [u32; 16] = [0; 16];

/// `x1` through `x31` after a case.
#[unsafe(no_mangle)]
static mut RV_OUT: [u32; 31] = [0; 31];

#[unsafe(link_section = ".rvbuf")]
#[unsafe(no_mangle)]
static mut RV_BUF: [u8; 256] = [0; 256];

#[unsafe(no_mangle)]
extern "C" fn rv_main() -> ! {
    // SAFETY: the generated tables hold `rv_case_count` entries, and each
    // case's memory is 256 bytes. The buffer and output are only touched
    // here and by the case that runs.
    unsafe {
        let count = rv_case_count as usize;
        let cases = core::slice::from_raw_parts(rv_cases.as_ptr(), count);
        for (n, case) in cases.iter().enumerate() {
            let buf = &raw mut RV_BUF;
            core::ptr::copy_nonoverlapping(case.mem, buf.cast::<u8>(), 256);
            rv_call(case.run);
            ets_printf(c"rv %d SEQ=%08x R=".as_ptr(), n as u32, case.seq);
            let out = &raw const RV_OUT;
            for r in (*out).iter() {
                ets_printf(c"%08x".as_ptr(), *r);
            }
            ets_printf(c" M=".as_ptr());
            for b in (*buf).iter() {
                ets_printf(c"%02x".as_ptr(), u32::from(*b));
            }
            ets_printf(c"\n".as_ptr());
        }
        ets_printf(c"rvtest: done\n".as_ptr());
    }
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
