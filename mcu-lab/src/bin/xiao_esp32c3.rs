//! Seeed Studio XIAO ESP32-C3 profiling, BLE advertisement telemetry, and
//! on-demand BLE GATT OTA firmware receiver.

use anyhow::Result;
use esp_idf_svc::hal::delay::FreeRtos;
use esp_idf_svc::hal::gpio::{Output, PinDriver};
use esp_idf_svc::hal::peripherals::Peripherals;
use esp_idf_svc::sys::{esp_deep_sleep_start, esp_reset_reason, esp_sleep_enable_timer_wakeup};
use log::info;
use mcu_lab::ble_ota::{mark_ota_slot_valid_if_pending, BleOtaNode};
use mcu_lab::profiler::{now_us, WakeProfiler};
use mcu_lab::protocol::{
    encode_board_flags, format_status_line, reset_reason_name, simulate_epd_frame,
    simulate_sensor_filter, BoardConfig, PhaseAccumulator, BOARD_XIAO_ESP32C3, CHIP_ID_ESP32C3,
    DEVICE_NAME, EPD_FRAME_BYTES, EPD_FULL_REFRESH_SIM_US, EPD_PARTIAL_REFRESH_SIM_US, FIRMWARE_ID,
    FLAG_BROWNOUT_RESET, FLAG_DEEP_SLEEP_WAKE, FLAG_EPD_PARTIAL,
};

const BOARD: BoardConfig = BoardConfig {
    board_id: BOARD_XIAO_ESP32C3,
    board: "xiao-esp32c3",
    chip: "esp32c3",
    app: "xiao-esp32c3",
    gap_name: DEVICE_NAME,
    chip_id: CHIP_ID_ESP32C3,
    cpu_mhz: 160,
};

/// Logic marker pin for Nordic PPK2 / oscilloscope correlation (GPIO 2 = XIAO D0).
const PROBE_GPIO_LABEL: &str = "GPIO2 (D0)";

/// Duration of each BLE advertising burst in milliseconds.
const BLE_BURST_MS: u32 = 150;

/// Deep-sleep interval between wake cycles in microseconds (5 seconds for bench profiling).
const DEEP_SLEEP_INTERVAL_US: u64 = 5_000_000;

/// Persistent phase accumulator placed in RTC slow memory so counters survive deep sleep.
#[link_section = ".rtc.data"]
static mut RTC_ACCUMULATOR: PhaseAccumulator = PhaseAccumulator::new();

fn main() -> Result<()> {
    let wake_start_us = now_us();
    esp_idf_svc::sys::link_patches();
    esp_idf_svc::log::EspLogger::initialize_default();

    let mut prof = WakeProfiler::start(BOARD, wake_start_us);
    let reset_code = unsafe { esp_reset_reason() } as i32;
    let reset_name = reset_reason_name(reset_code);
    info!("{FIRMWARE_ID} wake (reset={reset_name}({reset_code}), probe={PROBE_GPIO_LABEL})");

    let peripherals = Peripherals::take()?;
    let mut probe = PinDriver::output(peripherals.pins.gpio2)?;
    probe.set_low()?;
    prof.record("boot.init", "wake", wake_start_us, now_us());

    let mut flags: u8 = encode_board_flags(BOARD.board_id);
    if reset_code == 8 {
        flags |= FLAG_DEEP_SLEEP_WAKE;
    } else if reset_code == 9 {
        flags |= FLAG_BROWNOUT_RESET;
    }

    let next_wake = unsafe { RTC_ACCUMULATOR.wake_count.saturating_add(1) };
    let is_partial_epd = !next_wake.is_multiple_of(10);
    if is_partial_epd {
        flags |= FLAG_EPD_PARTIAL;
    }

    // Phase 1: Sensor read + fixed-point filter.
    let sensor_start = now_us();
    let (battery_mv, sensor_us) =
        measure_phase(&mut probe, || simulate_sensor_filter(next_wake, 64))?;
    prof.record("sensor.adc_filter", "sensor", sensor_start, now_us());

    // Phase 2: Compute / 1-bit e-paper framebuffer render (static BSS buffer avoids 5 KB heap alloc/free per wake).
    let compute_start = now_us();
    static mut EPD_FRAME_BUF: [u8; EPD_FRAME_BYTES] = [0u8; EPD_FRAME_BYTES];
    // SAFETY: single-core ESP32-C3 main task; `epd_buf` does not escape `main` and is not accessed from interrupts or BLE callbacks.
    let epd_buf = unsafe { &mut *core::ptr::addr_of_mut!(EPD_FRAME_BUF) };
    let (checksum, compute_us) = measure_phase(&mut probe, || {
        simulate_epd_frame(epd_buf, next_wake, battery_mv, is_partial_epd)
    })?;
    prof.record("compute.epd_render", "compute", compute_start, now_us());

    // Phase 3: E-paper SPI transfer + refresh wait.
    let (_, epd_refresh_us) = measure_phase(&mut probe, || {
        simulate_epd_spi_and_refresh(epd_buf, is_partial_epd, &mut prof)
    })?;

    let metrics = unsafe {
        // SAFETY: single-core ESP32-C3 main task before BLE callbacks mutate RTC_ACCUMULATOR.
        let acc = &mut *core::ptr::addr_of_mut!(RTC_ACCUMULATOR);
        acc.record_wake(sensor_us, compute_us, epd_refresh_us, battery_mv, flags)
    };

    let profile_json = prof.finish_json(&metrics);
    info!(
        "{} epd_checksum={checksum:#010x}",
        format_status_line(&metrics)
    );

    // Phase 4: BLE advertisement burst + on-demand BLE GATT OTA.
    let ble = BleOtaNode::init(BOARD);
    let (_, radio_us) = measure_phase(&mut probe, || {
        ble.broadcast_burst(&metrics, profile_json.as_deref(), BLE_BURST_MS);
    })?;

    mark_ota_slot_valid_if_pending();

    unsafe {
        // SAFETY: single-core ESP32-C3 main task after BLE stop and before deep sleep.
        let acc = &mut *core::ptr::addr_of_mut!(RTC_ACCUMULATOR);
        acc.record_radio_tx(radio_us);
    }

    info!(
        "radio_tx_us={radio_us}; entering deep sleep for {} ms",
        DEEP_SLEEP_INTERVAL_US / 1_000
    );

    unsafe {
        esp_sleep_enable_timer_wakeup(DEEP_SLEEP_INTERVAL_US);
        esp_deep_sleep_start();
    }
}

fn measure_phase<T>(probe: &mut PinDriver<'_, Output>, f: impl FnOnce() -> T) -> Result<(T, u32)> {
    probe.set_high()?;
    let start_us = now_us();
    let out = f();
    let elapsed_us = u32::try_from(now_us().saturating_sub(start_us)).unwrap_or(u32::MAX);
    probe.set_low()?;
    Ok((out, elapsed_us))
}

fn simulate_epd_spi_and_refresh(frame: &[u8], partial: bool, prof: &mut WakeProfiler) {
    let spi_start = now_us();
    let mut acc: u32 = 0;
    for chunk in frame.chunks(64) {
        for &b in chunk {
            acc = acc.wrapping_add(u32::from(b));
        }
    }
    std::hint::black_box(acc);
    let spi_end = now_us();
    prof.record("epd.spi_transfer", "epd_refresh", spi_start, spi_end);

    let busy_start = now_us();
    let delay_ms = if partial {
        EPD_PARTIAL_REFRESH_SIM_US / 10_000 // 32 ms bench scaling
    } else {
        EPD_FULL_REFRESH_SIM_US / 10_000 // 185 ms bench scaling
    };
    FreeRtos::delay_ms(delay_ms);
    prof.record("epd.busy_wait", "epd_refresh", busy_start, now_us());
}
