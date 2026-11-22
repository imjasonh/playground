//! Seeed Studio XIAO ESP32C3 profiling, BLE advertisement telemetry, and
//! on-demand BLE GATT OTA firmware receiver.
//!
//! Each wake cycle executes four instrumented stages:
//! 1. `sensor_us`: reads battery voltage and runs the fixed-point spike/EMA filter.
//! 2. `compute_us`: renders a 200×200 1-bit e-paper status tile in RAM.
//! 3. `epd_refresh_us`: measures the e-paper SPI transfer and BUSY refresh wait
//!    (partial refresh on most wakes, full refresh every 10th wake).
//! 4. `radio_us`: broadcasts a 150 ms BLE Manufacturer Specific Data (`0xFFFF`)
//!    burst at a 20–30 ms interval.
//!
//! The advertisement is connectable (`ConnMode::Und`) with the custom OTA GATT
//! service registered. On normal wakes when the iPhone only listens passively,
//! zero connections occur and the XIAO enters deep sleep immediately after the
//! 150 ms burst. When the user arms a firmware update in the iPhone app, the
//! iPhone connects during that 150 ms burst, keeping the XIAO awake just long
//! enough to stream the new image into the inactive OTA slot (`ota_0` / `ota_1`),
//! verify its SHA-256 digest, and reboot.
//!
//! GPIO 2 (D0 on the XIAO ESP32C3) toggles HIGH during each active phase as a
//! logic-analyzer / Nordic PPK2 power-profiler marker pin.

use std::sync::atomic::{AtomicBool, Ordering};
use std::sync::{Arc, Mutex};

use anyhow::Result;
use esp32_nimble::enums::ConnMode;
use esp32_nimble::utilities::BleUuid;
use esp32_nimble::{uuid128, BLEAdvertisementData, BLECharacteristic, BLEDevice, NimbleProperties};
use esp_idf_svc::hal::delay::FreeRtos;
use esp_idf_svc::hal::gpio::{Output, PinDriver};
use esp_idf_svc::hal::peripherals::Peripherals;
use esp_idf_svc::sys::{
    esp_deep_sleep_start, esp_ota_abort, esp_ota_begin, esp_ota_end,
    esp_ota_get_next_update_partition, esp_ota_get_running_partition, esp_ota_get_state_partition,
    esp_ota_handle_t, esp_ota_img_states_t, esp_ota_img_states_t_ESP_OTA_IMG_PENDING_VERIFY,
    esp_ota_mark_app_valid_cancel_rollback, esp_ota_set_boot_partition, esp_ota_write,
    esp_partition_t, esp_reset_reason, esp_restart, esp_sleep_enable_timer_wakeup,
    esp_timer_get_time, ESP_OK,
};
use log::{info, warn};
use sha2::{Digest, Sha256};
use xiao_esp32c3::protocol::{
    encode_mfg_data, format_ota_status, format_status_line, parse_ota_command, reset_reason_name,
    simulate_epd_frame, simulate_sensor_filter, OtaCommand, OtaStatus, PhaseAccumulator,
    DEVICE_NAME, EPD_FRAME_BYTES, EPD_FULL_REFRESH_SIM_US, EPD_PARTIAL_REFRESH_SIM_US, FIRMWARE_ID,
    FLAG_BROWNOUT_RESET, FLAG_DEEP_SLEEP_WAKE, FLAG_EPD_PARTIAL, OTA_CONTROL_UUID, OTA_DATA_UUID,
    OTA_SERVICE_UUID, OTA_SLOT_BYTES, OTA_STATUS_UUID,
};

/// Logic marker pin for Nordic PPK2 / oscilloscope correlation (GPIO 2 = XIAO D0).
const PROBE_GPIO_LABEL: &str = "GPIO2 (D0)";

/// Duration of each BLE advertising burst in milliseconds.
/// At 20–30 ms advertising intervals, 150 ms emits ~6–7 packets across channels 37/38/39.
const BLE_BURST_MS: u32 = 150;

/// Maximum time an active BLE OTA connection may keep the board awake before timing out (120 s).
const OTA_SESSION_TIMEOUT_MS: u32 = 120_000;

/// Maximum idle time on an open BLE connection without any OTA control/data write (15 s).
const OTA_IDLE_TIMEOUT_US: u64 = 15_000_000;

/// ESP-IDF firmware binary magic byte (`ESP_IMAGE_HEADER_MAGIC`).
const ESP_IMAGE_HEADER_MAGIC: u8 = 0xE9;

/// Deep-sleep interval between wake cycles in microseconds (5 seconds for bench profiling).
const DEEP_SLEEP_INTERVAL_US: u64 = 5_000_000;

/// Persistent phase accumulator placed in RTC slow memory so counters survive deep sleep.
#[link_section = ".rtc.data"]
static mut RTC_ACCUMULATOR: PhaseAccumulator = PhaseAccumulator::new();

fn main() -> Result<()> {
    let wake_start_us = now_us();
    esp_idf_svc::sys::link_patches();
    esp_idf_svc::log::EspLogger::initialize_default();

    let mut prof = profiler::WakeProfiler::start(wake_start_us);
    let reset_code = unsafe { esp_reset_reason() } as i32;
    let reset_name = reset_reason_name(reset_code);
    info!("{FIRMWARE_ID} wake (reset={reset_name}({reset_code}), probe={PROBE_GPIO_LABEL})");

    let peripherals = Peripherals::take()?;
    let mut probe = PinDriver::output(peripherals.pins.gpio2)?;
    probe.set_low()?;
    prof.record("boot.init", "wake", wake_start_us, now_us());

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

    // Build the 24-byte metrics snapshot in RTC slow memory.
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

    // Phase 4: BLE advertisement burst (26-byte Manufacturer Data: 0xFFFF + 24B payload),
    // plus on-demand BLE GATT OTA (and WakeProfile read in debug/profiling builds).
    let (_, radio_us) = measure_phase(&mut probe, || {
        broadcast_ble_and_serve_ota(&metrics, profile_json.as_deref())
    })?;

    // If this slot booted in PENDING_VERIFY after an OTA update, completing a wake cycle
    // and radio burst proves the image is healthy. Cancel rollback before deep sleeping.
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
fn simulate_epd_spi_and_refresh(frame: &[u8], partial: bool, prof: &mut profiler::WakeProfiler) {
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

/// Check if the running OTA partition is in `ESP_OTA_IMG_PENDING_VERIFY` and mark it valid.
fn mark_ota_slot_valid_if_pending() {
    // SAFETY: esp_ota_get_running_partition, esp_ota_get_state_partition, and
    // esp_ota_mark_app_valid_cancel_rollback are thread-safe ESP-IDF C APIs.
    unsafe {
        let part = esp_ota_get_running_partition();
        if part.is_null() {
            return;
        }
        let mut state: esp_ota_img_states_t = 0;
        if esp_ota_get_state_partition(part, &mut state) == ESP_OK
            && state == esp_ota_img_states_t_ESP_OTA_IMG_PENDING_VERIFY
        {
            let err = esp_ota_mark_app_valid_cancel_rollback();
            if err == ESP_OK {
                info!("ota: marked new firmware slot valid (rollback cancelled)");
            } else {
                warn!("ota: mark_app_valid failed err={err}");
            }
        }
    }
}

struct OtaWriterState {
    handle: Option<esp_ota_handle_t>,
    partition: *const esp_partition_t,
    expected_size: u32,
    expected_sha256: String,
    written: u32,
    next_notify_at: u32,
    last_activity_us: u64,
    hasher: Sha256,
    reboot_pending: bool,
}

// SAFETY: `partition` points to an immutable ESP-IDF partition descriptor table entry in flash/ROM.
unsafe impl Send for OtaWriterState {}

impl Default for OtaWriterState {
    fn default() -> Self {
        Self {
            handle: None,
            partition: core::ptr::null(),
            expected_size: 0,
            expected_sha256: String::new(),
            written: 0,
            next_notify_at: 0,
            last_activity_us: 0,
            hasher: Sha256::new(),
            reboot_pending: false,
        }
    }
}

impl OtaWriterState {
    fn abort_active(&mut self) {
        if let Some(h) = self.handle.take() {
            // SAFETY: `h` was returned by `esp_ota_begin` and has not been ended yet.
            unsafe {
                let _ = esp_ota_abort(h);
            }
        }
        self.partition = core::ptr::null();
        self.expected_size = 0;
        self.expected_sha256.clear();
        self.written = 0;
        self.next_notify_at = 0;
        self.hasher = Sha256::new();
    }

    fn begin(&mut self, size: u32, sha256: String) -> OtaStatus {
        self.abort_active();
        self.last_activity_us = now_us();
        if size == 0 || size > OTA_SLOT_BYTES {
            return OtaStatus::Error {
                message: format!("invalid size {size}"),
            };
        }
        // SAFETY: queries ESP-IDF's partition table for the inactive OTA app slot and opens it.
        unsafe {
            let part = esp_ota_get_next_update_partition(core::ptr::null());
            if part.is_null() {
                return OtaStatus::Error {
                    message: "no inactive OTA slot (run make flash-all)".to_string(),
                };
            }
            let mut handle: esp_ota_handle_t = 0;
            let err = esp_ota_begin(part, size as usize, &mut handle);
            if err != ESP_OK {
                return OtaStatus::Error {
                    message: format!("esp_ota_begin err={err}"),
                };
            }
            self.handle = Some(handle);
            self.partition = part;
            self.expected_size = size;
            self.expected_sha256 = sha256;
            self.written = 0;
            self.next_notify_at = 16 * 1024;
            self.hasher = Sha256::new();
            info!("ota: opened inactive partition for {size} bytes");
            OtaStatus::Ready { total: size }
        }
    }

    fn write_chunk(&mut self, chunk: &[u8]) -> Option<OtaStatus> {
        self.last_activity_us = now_us();
        let Some(handle) = self.handle else {
            return Some(OtaStatus::Error {
                message: "write before BEGIN".to_string(),
            });
        };
        if chunk.is_empty() {
            return None;
        }
        if self.written == 0 && chunk[0] != ESP_IMAGE_HEADER_MAGIC {
            self.abort_active();
            return Some(OtaStatus::Error {
                message: format!("invalid ESP-IDF image header byte {:#04x}", chunk[0]),
            });
        }
        let next_written = self.written.saturating_add(chunk.len() as u32);
        if next_written > self.expected_size {
            self.abort_active();
            return Some(OtaStatus::Error {
                message: format!("overflow: {next_written} > {}", self.expected_size),
            });
        }
        // SAFETY: `handle` is an active OTA handle and `chunk` is valid for `chunk.len()` bytes.
        let err = unsafe { esp_ota_write(handle, chunk.as_ptr().cast(), chunk.len()) };
        if err != ESP_OK {
            self.abort_active();
            return Some(OtaStatus::Error {
                message: format!("esp_ota_write err={err}"),
            });
        }
        self.hasher.update(chunk);
        self.written = next_written;
        if self.written >= self.next_notify_at || self.written == self.expected_size {
            self.next_notify_at = self.written.saturating_add(16 * 1024);
            return Some(OtaStatus::Progress {
                written: self.written,
                total: self.expected_size,
            });
        }
        None
    }

    fn commit(&mut self) -> OtaStatus {
        self.last_activity_us = now_us();
        let Some(handle) = self.handle.take() else {
            return OtaStatus::Error {
                message: "commit before BEGIN".to_string(),
            };
        };
        if self.written != self.expected_size {
            // SAFETY: `handle` was just taken and is still open.
            unsafe {
                let _ = esp_ota_abort(handle);
            }
            let w = self.written;
            let total = self.expected_size;
            self.abort_active();
            return OtaStatus::Error {
                message: format!("incomplete: {w}/{total} bytes"),
            };
        }
        let actual_sha = hex::encode(self.hasher.clone().finalize());
        if actual_sha != self.expected_sha256 {
            // SAFETY: `handle` was just taken and is still open.
            unsafe {
                let _ = esp_ota_abort(handle);
            }
            let expected = self.expected_sha256.clone();
            self.abort_active();
            return OtaStatus::Error {
                message: format!("sha256 mismatch: got {actual_sha}, want {expected}"),
            };
        }
        // SAFETY: finalizes the verified OTA image and switches `otadata` to boot `self.partition`.
        unsafe {
            let end_err = esp_ota_end(handle);
            if end_err != ESP_OK {
                self.abort_active();
                return OtaStatus::Error {
                    message: format!("esp_ota_end err={end_err}"),
                };
            }
            let boot_err = esp_ota_set_boot_partition(self.partition);
            if boot_err != ESP_OK {
                self.abort_active();
                return OtaStatus::Error {
                    message: format!("esp_ota_set_boot_partition err={boot_err}"),
                };
            }
        }
        info!("ota: committed {actual_sha}, rebooting into new slot");
        self.reboot_pending = true;
        OtaStatus::Ok { sha256: actual_sha }
    }
}

fn notify_ota_status(
    ch: &Arc<esp32_nimble::utilities::mutex::Mutex<BLECharacteristic>>,
    st: &OtaStatus,
) {
    let line = format_ota_status(st);
    info!("ota status: {line}");
    ch.lock().set_value(line.as_bytes()).notify();
}

/// Broadcast the 24-byte metrics struct inside BLE Manufacturer Specific Data (`0xFFFF`)
/// for [`BLE_BURST_MS`]. If an iPhone connects during that window to push an OTA update,
/// stay awake until the OTA transfer completes or disconnects.
fn broadcast_ble_and_serve_ota(
    metrics: &xiao_esp32c3::protocol::AdvMetrics,
    profile_json: Option<&str>,
) {
    let device = BLEDevice::take();
    let _ = device.set_preferred_mtu(512);
    let server = device.get_server();
    let advertising = device.get_advertising();

    let connected = Arc::new(AtomicBool::new(false));
    let ota_state = Arc::new(Mutex::new(OtaWriterState::default()));

    let conn_on_connect = Arc::clone(&connected);
    let state_on_connect = Arc::clone(&ota_state);
    server.on_connect(move |server, desc| {
        state_on_connect.lock().expect("ota_state").last_activity_us = now_us();
        conn_on_connect.store(true, Ordering::SeqCst);
        info!("ble connected for OTA/profile: {desc:?}");
        // Fast 7.5 ms - 15 ms connection interval for high-throughput BLE OTA streaming.
        let _ = server.update_conn_params(desc.conn_handle(), 6, 12, 0, 200);
    });

    let conn_on_disconnect = Arc::clone(&connected);
    let state_on_disconnect = Arc::clone(&ota_state);
    server.on_disconnect(move |_desc, reason| {
        info!("ble disconnected: {reason:?}");
        state_on_disconnect
            .lock()
            .expect("ota_state")
            .abort_active();
        conn_on_disconnect.store(false, Ordering::SeqCst);
    });

    let service = server.create_service(uuid_or_panic(OTA_SERVICE_UUID));
    let control_char = service
        .lock()
        .create_characteristic(uuid_or_panic(OTA_CONTROL_UUID), NimbleProperties::WRITE);
    let data_char = service.lock().create_characteristic(
        uuid_or_panic(OTA_DATA_UUID),
        NimbleProperties::WRITE | NimbleProperties::WRITE_NO_RSP,
    );
    let status_char = service.lock().create_characteristic(
        uuid_or_panic(OTA_STATUS_UUID),
        NimbleProperties::READ | NimbleProperties::NOTIFY,
    );

    status_char
        .lock()
        .set_value(format_ota_status(&OtaStatus::Idle).as_bytes());
    profiler::register_profile_char(&service, profile_json);

    let ctrl_state = Arc::clone(&ota_state);
    let ctrl_status_char = Arc::clone(&status_char);
    control_char.lock().on_write(move |args| {
        let raw = String::from_utf8_lossy(args.recv_data());
        info!("ota control write: {raw}");
        let mut guard = ctrl_state.lock().expect("ota_state");
        let reply = match parse_ota_command(raw.as_ref()) {
            Some(OtaCommand::Begin { size, sha256 }) => guard.begin(size, sha256),
            Some(OtaCommand::Commit) => guard.commit(),
            Some(OtaCommand::Abort) => {
                guard.abort_active();
                OtaStatus::Idle
            }
            None => OtaStatus::Error {
                message: "invalid OTA command".to_string(),
            },
        };
        notify_ota_status(&ctrl_status_char, &reply);
    });

    let data_state = Arc::clone(&ota_state);
    let data_status_char = Arc::clone(&status_char);
    data_char.lock().on_write(move |args| {
        let chunk = args.recv_data();
        let mut guard = data_state.lock().expect("ota_state");
        if let Some(status) = guard.write_chunk(chunk) {
            notify_ota_status(&data_status_char, &status);
        }
    });

    let mfg = encode_mfg_data(metrics);
    let mut adv = BLEAdvertisementData::new();
    adv.name(DEVICE_NAME).manufacturer_data(&mfg);

    let mut guard = advertising.lock();
    // Connectable undirected mode (`ConnMode::Und`) at 20–30 ms interval (`32..48` * 0.625 ms).
    // Passive listeners still read the exact same 31-byte primary packet (`3B` Flags + `28B` Mfg Data),
    // while an iPhone with a queued OTA update can connect during the 150 ms burst.
    guard
        .advertisement_type(ConnMode::Und)
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

    // If the iPhone connected during the 150 ms window to install an OTA update,
    // stay awake until the transfer finishes, disconnects, or hits the timeout.
    if connected.load(Ordering::SeqCst) {
        info!("ota: iPhone connected during burst; holding awake for BLE OTA");
        let mut waited_ms: u32 = 0;
        while connected.load(Ordering::SeqCst) && waited_ms < OTA_SESSION_TIMEOUT_MS {
            FreeRtos::delay_ms(50);
            waited_ms = waited_ms.saturating_add(50);
            let mut guard = ota_state.lock().expect("ota_state");
            if guard.reboot_pending {
                drop(guard);
                // Give NimBLE 250 ms to flush the final `OK sha256=...` notification before rebooting.
                FreeRtos::delay_ms(250);
                unsafe {
                    esp_restart();
                }
            }
            if now_us().saturating_sub(guard.last_activity_us) > OTA_IDLE_TIMEOUT_US {
                warn!("ota: idle timeout on BLE connection; aborting and entering deep sleep");
                guard.abort_active();
                break;
            }
        }
    }

    let _ = advertising.lock().stop();
}

fn uuid_or_panic(text: &str) -> BleUuid {
    match text {
        OTA_SERVICE_UUID => uuid128!("4fafc301-1fb5-459e-8fcc-c5c9c331914b"),
        OTA_CONTROL_UUID => uuid128!("beb5483e-36e1-4688-b7f5-ea07361bc301"),
        OTA_DATA_UUID => uuid128!("beb5483e-36e1-4688-b7f5-ea07361bc302"),
        OTA_STATUS_UUID => uuid128!("1a3c0001-36e1-4688-b7f5-ea07361bc303"),
        other => panic!("unknown UUID {other}"),
    }
}

#[cfg(any(debug_assertions, feature = "profiling"))]
mod profiler {
    use std::ffi::c_void;
    use std::sync::{Arc, Mutex};

    use esp32_nimble::utilities::mutex::Mutex as NimbleMutex;
    use esp32_nimble::{uuid128, BLEService, NimbleProperties};
    use esp_idf_svc::sys::{
        esp_get_free_heap_size, esp_get_minimum_free_heap_size, esp_timer_create,
        esp_timer_create_args_t, esp_timer_delete, esp_timer_dispatch_t_ESP_TIMER_TASK,
        esp_timer_handle_t, esp_timer_start_periodic, esp_timer_stop, uxTaskGetStackHighWaterMark,
        xTaskGetCurrentTaskHandle, TaskHandle_t, ESP_OK,
    };
    use log::info;
    use xiao_esp32c3::protocol::{
        format_wake_profile_json, AdvMetrics, PcHistogram, SpanRecorder, WakeProfile,
    };

    use super::now_us;

    /// 1 kHz sampling interval (1,000 µs) for the PC hotspot sampler.
    const PC_SAMPLE_PERIOD_US: u64 = 1_000;

    /// Maximum number of PC hotspots included in the BLE GATT WakeProfile JSON.
    const MAX_PC_HOTSPOTS: usize = 12;

    struct PcSamplerState {
        target_task: TaskHandle_t,
        hist: Mutex<PcHistogram>,
    }

    // SAFETY: `target_task` is an opaque FreeRTOS task handle for the main task,
    // which outlives the timer (the timer is stopped and deleted in `finish_json`).
    unsafe impl Send for PcSamplerState {}
    unsafe impl Sync for PcSamplerState {}

    /// Timer callback executed at 1 kHz from the high-priority `esp_timer` task.
    ///
    /// When `esp_timer` preempts the main task, FreeRTOS's RISC-V port saves the
    /// interrupted context (`RvExcFrame`, with `mepc` at offset 0) at the address
    /// stored in the first word (`pxTopOfStack`) of the main task's TCB.
    unsafe extern "C" fn pc_sample_timer_cb(arg: *mut c_void) {
        if arg.is_null() {
            return;
        }
        let state = &*(arg as *const PcSamplerState);
        if state.target_task.is_null() {
            return;
        }
        let px_top_of_stack = *(state.target_task as *const *const u32);
        if px_top_of_stack.is_null() {
            return;
        }
        let mepc = *px_top_of_stack;
        if let Ok(mut hist) = state.hist.try_lock() {
            hist.record(mepc);
        }
    }

    pub struct WakeProfiler {
        wake_start_us: u64,
        spans: SpanRecorder,
        timer: esp_timer_handle_t,
        sampler: *mut PcSamplerState,
    }

    impl WakeProfiler {
        pub fn start(wake_start_us: u64) -> Self {
            let target_task = unsafe { xTaskGetCurrentTaskHandle() };
            let sampler = Box::into_raw(Box::new(PcSamplerState {
                target_task,
                hist: Mutex::new(PcHistogram::new()),
            }));
            let mut timer: esp_timer_handle_t = core::ptr::null_mut();
            let args = esp_timer_create_args_t {
                callback: Some(pc_sample_timer_cb),
                arg: sampler.cast::<c_void>(),
                dispatch_method: esp_timer_dispatch_t_ESP_TIMER_TASK,
                name: c"xiao_prof".as_ptr(),
                skip_unhandled_events: true,
            };
            unsafe {
                if esp_timer_create(&args, &mut timer) == ESP_OK {
                    let _ = esp_timer_start_periodic(timer, PC_SAMPLE_PERIOD_US);
                } else {
                    timer = core::ptr::null_mut();
                }
            }
            Self {
                wake_start_us,
                spans: SpanRecorder::new(wake_start_us),
                timer,
                sampler,
            }
        }

        pub fn record(&mut self, name: &str, parent: &str, start_us: u64, end_us: u64) {
            self.spans.record(name, parent, start_us, end_us);
        }

        pub fn finish_json(mut self, metrics: &AdvMetrics) -> Option<String> {
            self.stop_timer();
            let (free_heap_bytes, min_free_heap_bytes, stack_high_water_bytes) = unsafe {
                (
                    esp_get_free_heap_size(),
                    esp_get_minimum_free_heap_size(),
                    uxTaskGetStackHighWaterMark(core::ptr::null_mut()),
                )
            };
            let cpu_cycles = now_us()
                .saturating_sub(self.wake_start_us)
                .saturating_mul(160);
            let pc_samples = if !self.sampler.is_null() {
                // SAFETY: timer has been stopped and deleted; we have exclusive access to `sampler`.
                let state = unsafe { &*self.sampler };
                state
                    .hist
                    .lock()
                    .map(|h| h.top_samples(MAX_PC_HOTSPOTS))
                    .unwrap_or_default()
            } else {
                Vec::new()
            };
            info!(
                "profile: free_heap={free_heap_bytes} min_heap={min_free_heap_bytes} stack_hw={stack_high_water_bytes} pc_hotspots={}",
                pc_samples.len()
            );
            let git_sha = option_env!("XIAO_GIT_SHA").unwrap_or("").to_string();
            let spans = core::mem::take(&mut self.spans).into_spans();
            let profile = WakeProfile {
                wake_count: metrics.wake_count,
                seq: metrics.seq,
                git_sha,
                free_heap_bytes,
                min_free_heap_bytes,
                stack_high_water_bytes,
                cpu_cycles,
                spans,
                pc_samples,
            };
            Some(format_wake_profile_json(&profile))
        }

        fn stop_timer(&mut self) {
            if !self.timer.is_null() {
                unsafe {
                    let _ = esp_timer_stop(self.timer);
                    let _ = esp_timer_delete(self.timer);
                }
                self.timer = core::ptr::null_mut();
            }
        }
    }

    impl Drop for WakeProfiler {
        fn drop(&mut self) {
            self.stop_timer();
            if !self.sampler.is_null() {
                // SAFETY: timer is stopped and deleted; `sampler` was allocated via `Box::into_raw`.
                unsafe {
                    drop(Box::from_raw(self.sampler));
                }
                self.sampler = core::ptr::null_mut();
            }
        }
    }

    pub fn register_profile_char(
        service: &Arc<NimbleMutex<BLEService>>,
        profile_json: Option<&str>,
    ) {
        if let Some(json) = profile_json {
            let profile_char = service.lock().create_characteristic(
                uuid128!("1a3c0002-36e1-4688-b7f5-ea07361bc303"),
                NimbleProperties::READ,
            );
            profile_char.lock().set_value(json.as_bytes());
        }
    }
}

#[cfg(not(any(debug_assertions, feature = "profiling")))]
mod profiler {
    use std::sync::Arc;

    use esp32_nimble::utilities::mutex::Mutex as NimbleMutex;
    use esp32_nimble::BLEService;
    use xiao_esp32c3::protocol::AdvMetrics;

    /// Zero-sized no-op profiler compiled into production release builds.
    pub struct WakeProfiler;

    impl WakeProfiler {
        #[inline(always)]
        pub fn start(_wake_start_us: u64) -> Self {
            Self
        }

        #[inline(always)]
        pub fn record(&mut self, _name: &str, _parent: &str, _start_us: u64, _end_us: u64) {}

        #[inline(always)]
        pub fn finish_json(self, _metrics: &AdvMetrics) -> Option<String> {
            None
        }
    }

    #[inline(always)]
    pub fn register_profile_char(
        _service: &Arc<NimbleMutex<BLEService>>,
        _profile_json: Option<&str>,
    ) {
    }
}
