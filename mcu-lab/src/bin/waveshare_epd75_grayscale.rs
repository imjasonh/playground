//! Waveshare 7.5″ e-Paper ESP32 Driver Board + `GrayscaleApp` (experimental grayscale boids).

use anyhow::Result;
use mcu_lab::apps::grayscale::GrayscaleApp;
use mcu_lab::boards::waveshare_epd75::WaveshareEpd75;

fn main() -> Result<()> {
    mcu_lab::platform::run::<WaveshareEpd75, GrayscaleApp>()
}
