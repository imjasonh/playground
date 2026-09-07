#![cfg_attr(target_os = "none", no_std)]
#![cfg_attr(target_os = "none", no_main)]

//! Bare-metal entry point for the nRF52833. The interesting logic lives in the
//! [`inkbot_magsafe`] library so it can be unit-tested on the host; this file
//! wires it to the chip.
//!
//! On a non-embedded host (during `cargo test` and `cargo clippy`) the firmware
//! module is compiled out and a placeholder `main` keeps the binary target
//! building.

#[cfg(target_os = "none")]
mod firmware {
    use cortex_m_rt::entry;
    use inkbot_magsafe::panel;
    use panic_halt as _;

    // Compile-time guard: the mono framebuffer must fit the RAM budget we
    // reserve for it (see memory.x). If the geometry ever changes, the build
    // fails here rather than at runtime.
    const _: () = assert!(panel::FRAME_BYTES == 48_000);

    #[entry]
    fn main() -> ! {
        // Bring-up sequence, filled in as drivers land:
        //   1. Start HFXO and the 32.768 kHz LFXO for low-power BLE timing.
        //   2. Init SPI to the panel, the panel-rail load switch, and SAADC
        //      (battery, thermistor).
        //   3. Paint the last frame held in flash so the tile shows something
        //      before the phone connects.
        //   4. Start the SoftDevice, advertise, and serve the GATT table plus
        //      the L2CAP channel from `inkbot_magsafe::protocol`.
        //   5. Sleep in WFI between radio and refresh events.
        loop {
            cortex_m::asm::wfi();
        }
    }
}

#[cfg(not(target_os = "none"))]
fn main() {}
