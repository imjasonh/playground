//! Seeed Studio XIAO ESP32-S3 Sense + `RecorderApp` (1-minute A/V clips to SD + HTTP server).

use anyhow::Result;
use mcu_lab::apps::recorder::RecorderApp;
use mcu_lab::boards::xiao_esp32s3_sense::XiaoEsp32S3Sense;

fn main() -> Result<()> {
    mcu_lab::platform::run::<XiaoEsp32S3Sense, RecorderApp>()
}
