//! Seeed Studio XIAO ESP32-C3 + universal `BaseApp` (OTA-ready + OTel bootstrap).

use anyhow::Result;
use mcu_lab::apps::base::BaseApp;
use mcu_lab::boards::xiao_esp32c3::XiaoEsp32C3;

fn main() -> Result<()> {
    mcu_lab::platform::run::<XiaoEsp32C3, BaseApp>()
}
