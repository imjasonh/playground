//! Seeed Studio XIAO ESP32-C3 board support package.

use anyhow::Result;
use esp_idf_svc::hal::gpio::{Output, PinDriver};
use esp_idf_svc::hal::peripherals::Peripherals;

use crate::boards::{Board, HasLogicProbe};
use crate::platform::RunMode;
use crate::profiler::now_us;
use crate::protocol::{BoardSpec, BOARD_XIAO_ESP32C3, CHIP_ID_ESP32C3, DEVICE_NAME};

/// Seeed Studio XIAO ESP32-C3 (RISC-V single-core 160 MHz, GPIO2 logic marker, battery powered).
pub struct XiaoEsp32C3 {
    probe: PinDriver<'static, Output>,
}

impl Board for XiaoEsp32C3 {
    const SPEC: BoardSpec = BoardSpec {
        board_id: BOARD_XIAO_ESP32C3,
        board: "xiao-esp32c3",
        chip: "esp32c3",
        gap_name: DEVICE_NAME,
        chip_id: CHIP_ID_ESP32C3,
        cpu_mhz: 160,
        min_ota_battery_mv: 3500,
    };

    fn default_run_mode() -> RunMode {
        RunMode::DeepSleep {
            interval_us: 5_000_000,
            burst_ms: 150,
        }
    }

    fn init(peripherals: Peripherals) -> Result<Self> {
        let mut probe = PinDriver::output(peripherals.pins.gpio2)?;
        probe.set_low()?;
        Ok(Self { probe })
    }

    fn self_test(&mut self) -> Result<()> {
        self.probe.set_high()?;
        self.probe.set_low()?;
        Ok(())
    }

    fn read_battery_mv(&mut self) -> u16 {
        3850
    }
}

impl HasLogicProbe for XiaoEsp32C3 {
    fn measure_phase<T>(&mut self, f: impl FnOnce() -> T) -> Result<(T, u32)> {
        self.probe.set_high()?;
        let start_us = now_us();
        let out = f();
        let elapsed_us = u32::try_from(now_us().saturating_sub(start_us)).unwrap_or(u32::MAX);
        self.probe.set_low()?;
        Ok((out, elapsed_us))
    }
}
