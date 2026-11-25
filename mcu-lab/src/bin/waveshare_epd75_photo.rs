//! Waveshare 7.5″ e-Paper ESP32 Driver Board + `PhotoApp` (4-gray / 1-bit photo frame).

use anyhow::Result;
use mcu_lab::apps::photo::PhotoApp;
use mcu_lab::boards::waveshare_epd75::WaveshareEpd75;

fn main() -> Result<()> {
    mcu_lab::platform::run::<WaveshareEpd75, PhotoApp>()
}
