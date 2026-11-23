//! `BenchApp` — sensor filter + 1-bit e-paper framebuffer render + simulated
//! SPI/BUSY refresh benchmark for boards with a [`HasLogicProbe`] marker pin.

use anyhow::Result;
use esp_idf_svc::hal::delay::FreeRtos;
use log::info;

use crate::boards::{Board, HasLogicProbe};
use crate::platform::{App, StepContext, StepOutput};
use crate::profiler::now_us;
use crate::protocol::{
    simulate_epd_frame, simulate_sensor_filter, EPD_FRAME_BYTES, EPD_FULL_REFRESH_SIM_US,
    EPD_PARTIAL_REFRESH_SIM_US, FIRMWARE_ID, FLAG_EPD_PARTIAL,
};

/// Power & phase-timing benchmark workload for boards with a logic marker pin.
pub struct BenchApp;

impl<B: Board + HasLogicProbe> App<B> for BenchApp {
    const APP_NAME: &'static str = "bench";
    const FIRMWARE_ID: &'static str = FIRMWARE_ID;

    fn init(_board: &mut B) -> Result<Self> {
        Ok(Self)
    }

    fn step(&mut self, board: &mut B, ctx: &mut StepContext<'_>) -> Result<StepOutput> {
        let is_partial_epd = !ctx.wake_count.is_multiple_of(10);
        let flags = if is_partial_epd { FLAG_EPD_PARTIAL } else { 0 };

        // Phase 1: Sensor read + fixed-point filter.
        let sensor_start = now_us();
        let (battery_mv, sensor_us) =
            board.measure_phase(|| simulate_sensor_filter(ctx.wake_count, 64))?;
        ctx.record_span("sensor.adc_filter", "sensor", sensor_start, now_us());

        // Phase 2: Compute / 1-bit e-paper framebuffer render (static BSS buffer avoids 5 KB heap alloc/free per wake).
        let compute_start = now_us();
        static mut EPD_FRAME_BUF: [u8; EPD_FRAME_BYTES] = [0u8; EPD_FRAME_BYTES];
        // SAFETY: single-threaded main task; `epd_buf` does not escape `step`.
        let epd_buf = unsafe { &mut *core::ptr::addr_of_mut!(EPD_FRAME_BUF) };
        let (checksum, compute_us) = board.measure_phase(|| {
            simulate_epd_frame(epd_buf, ctx.wake_count, battery_mv, is_partial_epd)
        })?;
        ctx.record_span("compute.epd_render", "compute", compute_start, now_us());

        // Phase 3: E-paper SPI transfer + refresh wait.
        let (_, epd_refresh_us) = board.measure_phase(|| {
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
