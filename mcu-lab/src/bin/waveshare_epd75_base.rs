//! Waveshare 7.5″ e-Paper ESP32 Driver Board + universal `BaseApp` (OTA-ready + OTel bootstrap).

use anyhow::Result;
use mcu_lab::apps::base::BaseApp;
use mcu_lab::boards::waveshare_epd75::WaveshareEpd75;

fn main() -> Result<()> {
    mcu_lab::platform::run::<WaveshareEpd75, BaseApp>()
}
