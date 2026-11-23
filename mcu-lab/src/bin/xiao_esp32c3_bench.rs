//! Seeed Studio XIAO ESP32-C3 + `BenchApp` (sensor/compute/EPD-sim profiler).

use anyhow::Result;
use mcu_lab::apps::bench::BenchApp;
use mcu_lab::boards::xiao_esp32c3::XiaoEsp32C3;

fn main() -> Result<()> {
    mcu_lab::platform::run::<XiaoEsp32C3, BenchApp>()
}
