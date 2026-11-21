//! Seeed Studio XIAO ESP32C3 profiling and BLE advertisement telemetry prototype.
//!
//! Each wake cycle executes four instrumented stages:
//! 1. `sensor_us`: reads battery voltage and runs the fixed-point spike/EMA filter.
//! 2. `compute_us`: renders a 200×200 1-bit e-paper status tile in RAM.
//! 3. `epd_refresh_us`: measures the e-paper SPI transfer and BUSY refresh wait
//!    (partial refresh on most wakes, full refresh every 10th wake).
//! 4. `radio_us`: broadcasts a 150 ms connectionless BLE Manufacturer Specific Data
//!    (`0xFFFF`) burst at a 20–30 ms interval, records the radio duration in RTC
//!    slow memory for the next wake, and enters deep sleep.
//!
//! GPIO 2 (D0 on the XIAO ESP32C3) toggles HIGH during each active phase as a
//! logic-analyzer / Nordic PPK2 power-profiler marker pin.

use anyhow::Result;
use esp32_nimble::enums::ConnMode;
use esp32_nimble::{BLEAdvertisementData, BLEDevice};
use esp_idf_svc::hal::delay::FreeRtos;
use esp_idf_svc::hal::gpio::{Output, PinDriver};
use esp_idf_svc::hal::peripherals::Peripherals;
use esp_idf_svc::sys::{
    esp_deep_sleep_start, esp_reset_reason, esp_sleep_enable_timer_wakeup, esp_timer_get_time,
};
use log::info;
use xiao_esp32c3::protocol::{
    encode_mfg_data, format_status_line, reset_reason_name, simulate_epd_frame,
    simulate_sensor_filter, PhaseAccumulator, DEVICE_NAME, EPD_FRAME_BYTES,
    EPD_FULL_REFRESH_SIM_US, EPD_PARTIAL_REFRESH_SIM_US, FIRMWARE_ID, FLAG_BROWNOUT_RESET,
    FLAG_DEEP_SLEEP_WAKE, FLAG_EPD_PARTIAL,
};

/// Logic marker pin for Nordic PPK2 / oscilloscope correlation (GPIO 2 = XIAO D0).
const PROBE_GPIO_LABEL: &str = "GPIO2 (D0)";

/// Duration of each connectionless BLE advertising burst in milliseconds.
/// At 20–30 ms advertising intervals, 150 ms emits ~6–7 packets across channels 37/38/39.
const BLE_BURST_MS: u32 = 150;

/// Deep-sleep interval between wake cycles in microseconds (5 seconds for bench profiling).
const DEEP_SLEEP_INTERVAL_US: u64 = 5_000_000;

/// Persistent phase accumulator placed in RTC slow memory so counters survive deep sleep.
#[link_section = ".rtc.data"]
static mut RTC_ACCUMULATOR: PhaseAccumulator = PhaseAccumulator::new();

fn main() -> Result<()> {
    esp_idf_svc::sys::link_patches();
    esp_idf_svc::log::EspLogger::initialize_default();

    let reset_code = unsafe { esp_reset_reason() } as i32;
    let reset_name = reset_reason_name(reset_code);
    info!("{FIRMWARE_ID} wake (reset={reset_name}({reset_code}), probe={PROBE_GPIO_LABEL})");

    let peripherals = Peripherals::take()?;
    let mut probe = PinDriver::output(peripherals.pins.gpio2)?;
    probe.set_low()?;

    let mut flags: u8 = 0;
    if reset_code == 8 {
        flags |= FLAG_DEEP_SLEEP_WAKE;
    } else if reset_code == 9 {
        flags |= FLAG_BROWNOUT_RESET;
    }

    // Read current wake index from RTC slow memory.
    let next_wake = unsafe { RTC_ACCUMULATOR.wake_count.saturating_add(1) };
    let is_partial_epd = !next_wake.is_multiple_of(10);
    if is_partial_epd {
        flags |= FLAG_EPD_PARTIAL;
    }

    // Phase 1: Sensor read + fixed-point filter.
    let (battery_mv, sensor_us) =
        measure_phase(&mut probe, || simulate_sensor_filter(next_wake, 64))?;

    // Phase 2: Compute / 1-bit e-paper framebuffer render.
    let mut epd_buf = vec![0u8; EPD_FRAME_BYTES];
    let (checksum, compute_us) = measure_phase(&mut probe, || {
        simulate_epd_frame(&mut epd_buf, next_wake, battery_mv, is_partial_epd)
    })?;

    // Phase 3: E-paper SPI transfer + refresh wait.
    let (_, epd_refresh_us) = measure_phase(&mut probe, || {
        simulate_epd_spi_and_refresh(&epd_buf, is_partial_epd)
    })?;

    // Build the 24-byte metrics snapshot in RTC slow memory.
    let metrics = unsafe {
        // SAFETY: single-core ESP32-C3 main task before BLE callbacks mutate RTC_ACCUMULATOR.
        let acc = &mut *core::ptr::addr_of_mut!(RTC_ACCUMULATOR);
        acc.record_wake(sensor_us, compute_us, epd_refresh_us, battery_mv, flags)
    };

    info!(
        "{} epd_checksum={checksum:#010x}",
        format_status_line(&metrics)
    );

    // Phase 4: BLE connectionless advertisement burst (26-byte Manufacturer Data: 0xFFFF + 24B payload).
    let (_, radio_us) = measure_phase(&mut probe, || broadcast_ble_burst(&metrics))?;

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

/// Toggle the GPIO logic marker pin HIGH while running `f`, and return `(output, elapsed_us)`.
fn measure_phase<T>(probe: &mut PinDriver<'_, Output>, f: impl FnOnce() -> T) -> Result<(T, u32)> {
    probe.set_high()?;
    let start_us = now_us();
    let out = f();
    let elapsed_us = u32::try_from(now_us().saturating_sub(start_us)).unwrap_or(u32::MAX);
    probe.set_low()?;
    Ok((out, elapsed_us))
}

fn now_us() -> u64 {
    // SAFETY: esp_timer_get_time returns monotonic microseconds since boot and takes no arguments.
    unsafe { esp_timer_get_time().max(0) as u64 }
}

/// Benchmark e-paper SPI byte streaming and panel BUSY refresh latency.
fn simulate_epd_spi_and_refresh(frame: &[u8], partial: bool) {
    // Simulate 4 MHz SPI transfer of the 5,000-byte 1-bit buffer (~10 ms) plus a short
    // bench refresh delay so real hardware measurements show distinct partial vs full phases.
    let mut acc: u32 = 0;
    for chunk in frame.chunks(64) {
        for &b in chunk {
            acc = acc.wrapping_add(u32::from(b));
        }
    }
    std::hint::black_box(acc);
    let delay_ms = if partial {
        EPD_PARTIAL_REFRESH_SIM_US / 10_000 // 32 ms bench scaling
    } else {
        EPD_FULL_REFRESH_SIM_US / 10_000 // 185 ms bench scaling
    };
    FreeRtos::delay_ms(delay_ms);
}

/// Broadcast the 24-byte metrics struct inside BLE Manufacturer Specific Data (`0xFFFF`)
/// for [`BLE_BURST_MS`] without accepting GATT connections.
fn broadcast_ble_burst(metrics: &xiao_esp32c3::protocol::AdvMetrics) {
    let device = BLEDevice::take();
    let advertising = device.get_advertising();

    let mfg = encode_mfg_data(metrics);
    let mut adv = BLEAdvertisementData::new();
    adv.name(DEVICE_NAME).manufacturer_data(&mfg);

    let mut guard = advertising.lock();
    // 20 ms to 30 ms interval (in 0.625 ms units: 32..48) in non-connectable mode,
    // with scan response enabled so the device name fits in the scan response packet
    // while the 31-byte primary packet carries Flags (3B) + Manufacturer Data (28B).
    guard
        .advertisement_type(ConnMode::Non)
        .scan_response(true)
        .min_interval(32)
        .max_interval(48);

    if let Err(err) = guard.set_data(&mut adv) {
        info!("ble set_data error: {err:?}");
        return;
    }
    if let Err(err) = guard.start() {
        info!("ble start error: {err:?}");
        return;
    }
    drop(guard);

    FreeRtos::delay_ms(BLE_BURST_MS);

    if let Err(err) = advertising.lock().stop() {
        info!("ble stop error: {err:?}");
    }
}
