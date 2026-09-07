#![cfg_attr(target_os = "none", no_std)]
#![cfg_attr(target_os = "none", no_main)]

//! Bare-metal entry point for the nRF52833. The interesting logic lives in the
//! [`inkbot_magsafe`] library so it can be unit-tested on the host; this file
//! wires it to the chip.
//!
//! On a non-embedded host (during `cargo test` and `cargo clippy`) the firmware
//! module is compiled out and a placeholder `main` keeps the binary target
//! building.

#[cfg(all(
    target_os = "none",
    not(any(feature = "bringup-stub", feature = "factory-bringup"))
))]
compile_error!(
    "the device binary is inert; use --features bringup-stub for the S140 app \
     slot or --features factory-bringup for blank-device SWD provisioning"
);

#[cfg(all(feature = "bringup-stub", feature = "factory-bringup"))]
compile_error!("bringup-stub and factory-bringup select incompatible memory maps");

#[cfg(target_os = "none")]
mod firmware {
    use cortex_m_rt::entry;
    use inkbot_magsafe::{
        boot::{self, RegoutPlan},
        panel,
    };
    use panic_halt as _;

    const NVMC_READY: *const u32 = 0x4001_E400 as *const u32;
    const NVMC_CONFIG: *mut u32 = 0x4001_E504 as *mut u32;
    const NVMC_READ_ONLY: u32 = 0;
    const NVMC_WRITE_ENABLE: u32 = 1;

    const APP_RAM_BYTES: usize = (128 - 31) * 1024;
    const MIN_RUNTIME_RAM_BYTES: usize = 32 * 1024;

    // Keep room for stacks, SoftDevice-facing state, flash buffers, and
    // peripheral drivers after allocating the mono framebuffer. The linked
    // image and the SoftDevice-reported RAM origin remain release gates.
    const _: () = assert!(panel::FRAME_BYTES + MIN_RUNTIME_RAM_BYTES <= APP_RAM_BYTES);

    fn wait_for_nvmc() {
        while unsafe { core::ptr::read_volatile(NVMC_READY) } == 0 {
            cortex_m::asm::nop();
        }
    }

    unsafe fn program_regout0(value: u32) -> ! {
        wait_for_nvmc();
        core::ptr::write_volatile(NVMC_CONFIG, NVMC_WRITE_ENABLE);
        wait_for_nvmc();
        core::ptr::write_volatile(boot::REGOUT0_ADDRESS as *mut u32, value);
        wait_for_nvmc();
        core::ptr::write_volatile(NVMC_CONFIG, NVMC_READ_ONLY);
        wait_for_nvmc();
        let programmed = core::ptr::read_volatile(boot::REGOUT0_ADDRESS as *const u32);
        if programmed & boot::REGOUT0_VOUT_MASK != boot::REGOUT0_3V0 {
            loop {
                cortex_m::asm::wfi();
            }
        }
        cortex_m::peripheral::SCB::sys_reset()
    }

    fn ensure_regout0_3v0() {
        let current = unsafe { core::ptr::read_volatile(boot::REGOUT0_ADDRESS as *const u32) };
        match boot::plan_regout0(current) {
            RegoutPlan::Ready => {}
            RegoutPlan::ProgramAndReset(value) => unsafe { program_regout0(value) },
            RegoutPlan::Reject => loop {
                // UICR cannot change a programmed 0 bit back to 1. Keep every
                // output unconfigured until an SWD fixture erases and
                // reprovisions the device.
                cortex_m::asm::wfi();
            },
        }
    }

    #[entry]
    fn main() -> ! {
        ensure_regout0_3v0();

        // Remaining production firmware sequence:
        //   1. Configure panel power disabled and charge enabled before any
        //      other GPIO changes.
        //   2. Start the 32.768 kHz LFXO and S140.
        //   3. Initialize SPI, BUSY timeout handling, VDDHDIV5 sampling, the
        //      watchdog, and reset-reason retention.
        //   4. Advertise only the bonded service and serve encrypted GATT and
        //      L2CAP transfers.
        //   5. Verify a complete frame in flash before enabling the panel.
        loop {
            cortex_m::asm::wfi();
        }
    }
}

#[cfg(not(target_os = "none"))]
fn main() {}
