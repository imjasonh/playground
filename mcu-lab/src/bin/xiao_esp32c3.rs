//! Seeed Studio XIAO ESP32-C3 profiling, BLE advertisement telemetry, and
//! on-demand BLE GATT OTA firmware receiver, built on [`mcu_lab::platform::McuApp`].

use anyhow::Result;
use esp_idf_svc::hal::delay::FreeRtos;
use esp_idf_svc::hal::gpio::{Gpio2, Output, PinDriver};
use esp_idf_svc::hal::peripherals::Peripherals;
use log::info;
use mcu_lab::platform::{McuApp, RunMode, StepContext, StepOutput};
use mcu_lab::profiler::now_us;
use mcu_lab::protocol::{
    simulate_epd_frame, simulate_sensor_filter, BoardConfig, BOARD_XIAO_ESP32C3, CHIP_ID_ESP32C3,
    DEVICE_NAME, EPD_FRAME_BYTES, EPD_FULL_REFRESH_SIM_US, EPD_PARTIAL_REFRESH_SIM_US, FIRMWARE_ID,
    FLAG_EPD_PARTIAL,
};

struct XiaoApp {
    probe: PinDriver<'static, Gpio2, Output>,
}

impl McuApp for XiaoApp {
    const BOARD: BoardConfig = BoardConfig {
        board_id: BOARD_XIAO_ESP32C3,
        board: "xiao-esp32c3",
        chip: "esp32c3",
        app: "xiao-esp32c3",
        gap_name: DEVICE_NAME,
        chip_id: CHIP_ID_ESP32C3,
        cpu_mhz: 160,
        min_ota_battery_mv: 3500,
    };

    const FIRMWARE_ID: &'static str = FIRMWARE_ID;

    const RUN_MODE: RunMode = RunMode::DeepSleep {
        interval_us: 5_000_000,
        burst_ms: 150,
    };

    fn init(peripherals: Peripherals) -> Result<Self> {
        let mut probe = PinDriver::output(peripherals.pins.gpio2)?;
        probe.set_low()?;
        Ok(Self { probe })
    }

    fn self_test(&mut self) -> Result<()> {
        // Verify logic-probe GPIO toggles cleanly before confirming an OTA slot.
        self.probe.set_high()?;
        self.probe.set_low()?;
        Ok(())
    }

    fn step(&mut self, ctx: &mut StepContext<'_>) -> Result<StepOutput> {
        let is_partial_epd = !ctx.wake_count.is_multiple_of(10);
        let flags = if is_partial_epd { FLAG_EPD_PARTIAL } else { 0 };

        // Phase 1: Sensor read + fixed-point filter.
        let sensor_start = now_us();
        let (battery_mv, sensor_us) = measure_phase(&mut self.probe, || {
            simulate_sensor_filter(ctx.wake_count, 64)
        })?;
        ctx.record_span("sensor.adc_filter", "sensor", sensor_start, now_us());

        // Phase 2: Compute / 1-bit e-paper framebuffer render (static BSS buffer avoids 5 KB heap alloc/free per wake).
        let compute_start = now_us();
        static mut EPD_FRAME_BUF: [u8; EPD_FRAME_BYTES] = [0u8; EPD_FRAME_BYTES];
        // SAFETY: single-core ESP32-C3 main task; `epd_buf` does not escape `step`.
        let epd_buf = unsafe { &mut *core::ptr::addr_of_mut!(EPD_FRAME_BUF) };
        let (checksum, compute_us) = measure_phase(&mut self.probe, || {
            simulate_epd_frame(epd_buf, ctx.wake_count, battery_mv, is_partial_epd)
        })?;
        ctx.record_span("compute.epd_render", "compute", compute_start, now_us());

        // Phase 3: E-paper SPI transfer + refresh wait.
        let (_, epd_refresh_us) = measure_phase(&mut self.probe, || {
            simulate_epd_spi_and_refresh(epd_buf, is_partial_epd, ctx);
        })?;

        info!("epd_checksum={checksum:#010x}");

        Ok(StepOutput {
            sensor_us,
            compute_us,
            epd_refresh_us,
            battery_mv,
            flags,
            post_burst_delay_ms: 0,
        })
    }
}

fn measure_phase<T>(
    probe: &mut PinDriver<'_, Gpio2, Output>,
    f: impl FnOnce() -> T,
) -> Result<(T, u32)> {
    probe.set_high()?;
    let start_us = now_us();
    let out = f();
    let elapsed_us = u32::try_from(now_us().saturating_sub(start_us)).unwrap_or(u32::MAX);
    probe.set_low()?;
    Ok((out, elapsed_us))
}

fn simulate_epd_spi_and_refresh(frame: &[u8], partial: bool, ctx: &mut StepContext<'_>) {
    let spi_start = now_us();
    let mut acc: u32 = 0;
    for chunk in frame.chunks(64) {
        for &b in chunk {
            acc = acc.wrapping_add(u32::from(b));
        }
    }
    std::hint::black_box(acc);
    ctx.record_span("epd.spi_transfer", "epd_refresh", spi_start, now_us());

    let busy_start = now_us();
    let delay_ms = if partial {
        EPD_PARTIAL_REFRESH_SIM_US / 10_000 // 32 ms bench scaling
    } else {
        EPD_FULL_REFRESH_SIM_US / 10_000 // 185 ms bench scaling
    };
    FreeRtos::delay_ms(delay_ms);
    ctx.record_span("epd.busy_wait", "epd_refresh", busy_start, now_us());
}

fn main() -> Result<()> {
    mcu_lab::platform::run::<XiaoApp>()
}
