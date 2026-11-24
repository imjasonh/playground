//! Seeed Studio XIAO ESP32-C3 + `GzipBenchApp` (`miniz_oxide` gzip/DEFLATE benchmark + OTel).

use anyhow::Result;
use mcu_lab::apps::gzip_bench::GzipBenchApp;
use mcu_lab::boards::xiao_esp32c3::XiaoEsp32C3;

fn main() -> Result<()> {
    mcu_lab::platform::run::<XiaoEsp32C3, GzipBenchApp>()
}
