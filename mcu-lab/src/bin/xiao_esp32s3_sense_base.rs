//! Seeed Studio XIAO ESP32-S3 Sense + universal `BaseApp` (OTA-ready + OTel bootstrap).

use anyhow::Result;
use mcu_lab::apps::base::BaseApp;
use mcu_lab::boards::xiao_esp32s3_sense::XiaoEsp32S3Sense;

fn main() -> Result<()> {
    mcu_lab::platform::run::<XiaoEsp32S3Sense, BaseApp>()
}
