#![cfg_attr(target_os = "none", no_std)]
#![cfg_attr(target_os = "none", no_main)]

//! Bare-metal entry point for the nRF52833. The interesting logic lives in the
//! [`inkbot_magsafe`] library so it can be unit-tested on the host; this file
//! wires it to the chip.
//!
//! On a non-embedded host (during `cargo test` and `cargo clippy`) the firmware
//! module is compiled out and a placeholder `main` keeps the binary target
//! building.

#[cfg(all(target_os = "none", not(feature = "bringup-stub")))]
compile_error!("the device binary is inert; use --features bringup-stub for CI only");

#[cfg(target_os = "none")]
mod firmware {
    use cortex_m_rt::entry;
    use inkbot_magsafe::panel;
    use panic_halt as _;

    const APP_RAM_BYTES: usize = (128 - 32) * 1024;
    const MIN_RUNTIME_RAM_BYTES: usize = 32 * 1024;

    // Keep room for stacks, SoftDevice-facing state, flash buffers, and
    // peripheral drivers after allocating the mono framebuffer. The linked
    // image and the SoftDevice-reported RAM origin remain release gates.
    const _: () = assert!(panel::FRAME_BYTES + MIN_RUNTIME_RAM_BYTES <= APP_RAM_BYTES);

    #[entry]
    fn main() -> ! {
        // Remaining production firmware sequence:
        //   1. Keep panel power and charging disabled before other GPIO changes.
        //   2. Start the 32.768 kHz LFXO and S113.
        //   3. Configure BQ25186 JEITA, current, and voltage limits over I2C,
        //      verify readback, then enable charging through Q2. Recheck the
        //      registers while charging and drop Q2 on any mismatch.
        //   4. Initialize SPI, BUSY timeout handling, SYS sampling, the
        //      watchdog, and reset-reason retention.
        //   5. Advertise only the bonded service and serve encrypted GATT and
        //      L2CAP transfers.
        //   6. Verify a complete frame before enabling the panel.
        loop {
            cortex_m::asm::wfi();
        }
    }
}

#[cfg(not(target_os = "none"))]
fn main() {}
