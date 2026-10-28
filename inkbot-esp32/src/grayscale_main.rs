//! grayscale-esp32 — experimental UC8179 "4 Gray" measurement demo.
//!
//! Loops a procedurally generated moving scene through the panel's native
//! 4-level grayscale mode and logs each refresh's wall-clock time, so the
//! real refresh rate for this board and panel can be read off the serial
//! monitor instead of estimated. See `grayscale_display.rs` for exactly
//! which panel commands this sends and what is still unverified.
//!
//! No Wi-Fi, no OTA pull, and no OTA registration: USB-flash only
//! (`make flash APP=grayscale`). This is a measurement tool, not a shipped
//! experience — it is not part of the `inkbot`/`maze` OTA app registry.

mod grayscale_display;

use std::thread;
use std::time::{Duration, Instant};

use anyhow::Result;
use esp_idf_svc::hal::peripherals::Peripherals;
use log::info;

use grayscale_display::Panel;
use inkbot_esp32::grayscale::{plan_panel_frame, scene::render_demo_frame, GRAYSCALE_FIRMWARE_ID};

fn main() -> Result<()> {
    esp_idf_svc::sys::link_patches();
    esp_idf_svc::log::EspLogger::initialize_default();
    info!("{GRAYSCALE_FIRMWARE_ID} boot");

    let peripherals = Peripherals::take()?;
    let mut panel = Panel::new(
        peripherals.spi2,
        peripherals.pins.gpio13,
        peripherals.pins.gpio14,
        peripherals.pins.gpio15,
        peripherals.pins.gpio25,
        peripherals.pins.gpio27,
        peripherals.pins.gpio26,
    )?;

    let mut tick: u32 = 0;
    loop {
        let logical = render_demo_frame(tick);
        let (old, new) = plan_panel_frame(&logical);

        let start = Instant::now();
        let result = panel.show_4gray(&old, &new);
        let elapsed = start.elapsed();

        match result {
            Ok(()) => {
                let ms = elapsed.as_millis().max(1);
                info!(
                    "4gray refresh tick={tick} elapsed_ms={ms} hz={:.2}",
                    1000.0 / ms as f64
                );
            }
            Err(e) => {
                log::error!("4gray refresh failed: {e:#}");
                thread::sleep(Duration::from_secs(2));
            }
        }

        tick = tick.wrapping_add(1);
    }
}
