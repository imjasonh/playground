//! Waveshare 7.5″ e-Paper ESP32 + `GzipBenchApp` (ROM `tinfl`/`tdefl` gzip/DEFLATE benchmark + OTel).

use anyhow::Result;
use mcu_lab::apps::gzip_bench::GzipBenchApp;
use mcu_lab::boards::waveshare_epd75::WaveshareEpd75;

fn main() -> Result<()> {
    mcu_lab::platform::run::<WaveshareEpd75, GzipBenchApp>()
}
