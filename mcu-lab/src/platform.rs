//! Reusable `McuApp` platform runtime for `mcu-lab` firmware targets.
//!
//! Apps implement [`McuApp`] and call [`run`] from `fn main()`. The platform
//! owns boot initialization, Task Watchdog registration/feeding, CRC32-guarded
//! RTC state, crash-loop rollback protection, `WakeProfiler`, BLE telemetry,
//! resumable BLE GATT OTA, and flash coredump upload.

use std::thread;
use std::time::{Duration, Instant};

use anyhow::Result;
use esp_idf_svc::hal::peripherals::Peripherals;
use esp_idf_svc::sys::{
    esp_deep_sleep_start, esp_reset_reason, esp_sleep_enable_timer_wakeup, esp_task_wdt_add,
    esp_task_wdt_reset,
};
use log::{info, warn};

use crate::ble_ota::{
    has_flash_coredump, is_ota_slot_pending_verify, mark_ota_slot_valid_if_pending,
    rollback_ota_slot_and_reboot, BleOtaNode,
};
use crate::profiler::{now_us, WakeProfiler};
use crate::protocol::{
    encode_board_flags, format_status_line, reset_reason_name, BoardConfig, RtcState,
    FLAG_BROWNOUT_RESET, FLAG_DEEP_SLEEP_WAKE, MAX_CRASH_STREAK,
};

/// Persistent CRC32-guarded state placed in RTC slow RAM so wake counters and
/// crash-streak tracking survive deep sleep and recover cleanly from brownouts.
#[link_section = ".rtc.data"]
static mut RTC_STATE: RtcState = RtcState::new();

/// Execution cadence for an [`McuApp`].
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum RunMode {
    /// Execute one [`McuApp::step`], broadcast a BLE burst for `burst_ms`, then enter deep sleep.
    DeepSleep { interval_us: u64, burst_ms: u32 },
    /// Execute [`McuApp::step`] repeatedly in a loop, broadcasting a BLE burst after each step.
    Continuous { burst_ms: u32, min_step_ms: u64 },
}

/// Phase durations and metadata returned by a single [`McuApp::step`].
#[derive(Debug, Clone, Copy, Default, PartialEq, Eq)]
pub struct StepOutput {
    pub sensor_us: u32,
    pub compute_us: u32,
    pub epd_refresh_us: u32,
    pub battery_mv: u16,
    /// Additional low-nibble flag bits (`FLAG_EPD_ATTACHED`, `FLAG_EPD_PARTIAL`, etc.).
    /// Board ID, deep-sleep wake, and brownout bits are added automatically by the platform.
    pub flags: u8,
    /// Optional extra sleep after this step's BLE burst (e.g. hold a completed frame on screen).
    pub post_burst_delay_ms: u64,
}

/// Per-step runtime context passed into [`McuApp::step`].
pub struct StepContext<'a> {
    pub wake_count: u32,
    pub reset_code: i32,
    profiler: &'a mut WakeProfiler,
}

impl<'a> StepContext<'a> {
    /// Record a sub-phase profiling span (`name` under `parent`, in monotonic microseconds).
    pub fn record_span(&mut self, name: &str, parent: &str, start_us: u64, end_us: u64) {
        self.profiler.record(name, parent, start_us, end_us);
    }

    /// Measure a closure, returning `(result, elapsed_us)` and recording a profiling span.
    pub fn measure_span<T>(&mut self, name: &str, parent: &str, f: impl FnOnce() -> T) -> (T, u32) {
        let start = now_us();
        let out = f();
        let end = now_us();
        self.profiler.record(name, parent, start, end);
        let elapsed_us = u32::try_from(end.saturating_sub(start)).unwrap_or(u32::MAX);
        (out, elapsed_us)
    }

    /// Feed the ESP-IDF Task Watchdog during long hardware operations (e.g. full e-paper refresh).
    pub fn feed_watchdog(&self) {
        feed_task_watchdog();
    }
}

/// Trait implemented by every firmware app built on the `mcu-lab` platform.
pub trait McuApp: Sized {
    /// Static board, chip, GAP name, and battery-gate metadata.
    const BOARD: BoardConfig;

    /// Firmware identifier string embedded in the binary (verified by `make check-firmware`).
    const FIRMWARE_ID: &'static str;

    /// Deep-sleep or continuous-loop execution cadence.
    const RUN_MODE: RunMode;

    /// Initialize board-specific peripherals (GPIO, SPI, displays, sensors).
    fn init(peripherals: Peripherals) -> Result<Self>;

    /// Optional hardware self-test run once when booting a `PENDING_VERIFY` OTA slot.
    ///
    /// Returning `Err` rejects the new image and immediately rolls back to the previous slot.
    fn self_test(&mut self) -> Result<()> {
        Ok(())
    }

    /// Execute one wake or animation step and return its phase durations and flags.
    fn step(&mut self, ctx: &mut StepContext<'_>) -> Result<StepOutput>;
}

/// Feed the ESP-IDF Task Watchdog for the current task.
#[inline]
pub fn feed_task_watchdog() {
    // SAFETY: `esp_task_wdt_reset` is safe to call from any subscribed FreeRTOS task.
    unsafe {
        let _ = esp_task_wdt_reset();
    }
}

fn is_crash_reset(code: i32) -> bool {
    // 4=PANIC, 5=INT_WDT, 6=TASK_WDT, 7=WDT, 9=BROWNOUT
    matches!(code, 4 | 5 | 6 | 7 | 9)
}

/// Boot and run an [`McuApp`] on the shared `mcu-lab` platform.
pub fn run<A: McuApp>() -> Result<()> {
    let boot_start_us = now_us();
    esp_idf_svc::sys::link_patches();
    esp_idf_svc::log::EspLogger::initialize_default();

    // Subscribe main task to the ESP-IDF Task Watchdog (configured in sdkconfig.defaults).
    // SAFETY: `null_mut()` subscribes the currently executing FreeRTOS task.
    unsafe {
        let _ = esp_task_wdt_add(core::ptr::null_mut());
    }

    let reset_code = unsafe { esp_reset_reason() } as i32;
    let reset_name = reset_reason_name(reset_code);
    info!(
        "{} boot (board={}, chip={}, reset={reset_name}({reset_code}), coredump={})",
        A::FIRMWARE_ID,
        A::BOARD.board,
        A::BOARD.chip,
        has_flash_coredump(),
    );

    // Validate CRC32-protected RTC state and enforce crash-loop rollback on PENDING_VERIFY slots.
    let (rtc_valid, crash_streak) = unsafe {
        // SAFETY: single-threaded main task before BLE callbacks start.
        let rtc = &mut *core::ptr::addr_of_mut!(RTC_STATE);
        let valid = rtc.validate_or_reset();
        if is_crash_reset(reset_code) {
            rtc.crash_streak = rtc.crash_streak.saturating_add(1);
            rtc.seal();
        }
        (valid, rtc.crash_streak)
    };
    if !rtc_valid {
        info!("rtc: initialized fresh CRC-guarded RTC state");
    }
    if crash_streak >= MAX_CRASH_STREAK && is_ota_slot_pending_verify() {
        warn!("ota: crash_streak={crash_streak} >= {MAX_CRASH_STREAK} on PENDING_VERIFY slot; rolling back");
        rollback_ota_slot_and_reboot();
    }

    let peripherals = Peripherals::take()?;
    let mut app = match A::init(peripherals) {
        Ok(app) => app,
        Err(err) => {
            warn!("app init failed: {err:#}");
            if is_ota_slot_pending_verify() {
                rollback_ota_slot_and_reboot();
            }
            return Err(err);
        }
    };

    if is_ota_slot_pending_verify() {
        if let Err(err) = app.self_test() {
            warn!("ota: self_test failed on PENDING_VERIFY slot: {err:#}");
            rollback_ota_slot_and_reboot();
        }
        info!("ota: app self_test passed");
    }

    let ble = BleOtaNode::init(A::BOARD);
    let mut ota_verified = false;

    let mut base_flags = encode_board_flags(A::BOARD.board_id);
    if reset_code == 8 {
        base_flags |= FLAG_DEEP_SLEEP_WAKE;
    } else if reset_code == 9 {
        base_flags |= FLAG_BROWNOUT_RESET;
    }

    match A::RUN_MODE {
        RunMode::DeepSleep {
            interval_us,
            burst_ms,
        } => {
            run_one_step(
                &mut app,
                &ble,
                boot_start_us,
                reset_code,
                base_flags,
                burst_ms,
                &mut ota_verified,
            )?;

            info!("entering deep sleep for {} ms", interval_us / 1_000);
            unsafe {
                esp_sleep_enable_timer_wakeup(interval_us);
                esp_deep_sleep_start();
            }
        }
        RunMode::Continuous {
            burst_ms,
            min_step_ms,
        } => loop {
            feed_task_watchdog();
            let tick = Instant::now();
            let cycle_start = now_us();
            match run_one_step(
                &mut app,
                &ble,
                cycle_start,
                reset_code,
                base_flags,
                burst_ms,
                &mut ota_verified,
            ) {
                Ok(post_delay_ms) => {
                    let min_wait =
                        Duration::from_millis(min_step_ms).saturating_sub(tick.elapsed());
                    let total_wait = min_wait.max(Duration::from_millis(post_delay_ms));
                    sleep_feeding_wdt(total_wait);
                }
                Err(err) => {
                    warn!("{} step failed: {err:#}", A::BOARD.app);
                    sleep_feeding_wdt(Duration::from_secs(2));
                }
            }
        },
    }
}

fn run_one_step<A: McuApp>(
    app: &mut A,
    ble: &BleOtaNode,
    cycle_start_us: u64,
    reset_code: i32,
    base_flags: u8,
    burst_ms: u32,
    ota_verified: &mut bool,
) -> Result<u64> {
    feed_task_watchdog();
    let mut prof = WakeProfiler::start(A::BOARD, cycle_start_us);
    let next_wake = unsafe {
        let rtc = &*core::ptr::addr_of!(RTC_STATE);
        rtc.accumulator.wake_count.saturating_add(1)
    };

    let mut ctx = StepContext {
        wake_count: next_wake,
        reset_code,
        profiler: &mut prof,
    };
    let out = app.step(&mut ctx)?;
    feed_task_watchdog();

    let flags = base_flags | (out.flags & 0x0F);
    let metrics = unsafe {
        let rtc = &mut *core::ptr::addr_of_mut!(RTC_STATE);
        let m = rtc.accumulator.record_wake(
            out.sensor_us,
            out.compute_us,
            out.epd_refresh_us,
            out.battery_mv,
            flags,
        );
        rtc.seal();
        m
    };

    let profile_json = prof.finish_json(&metrics);
    info!("{}", format_status_line(&metrics));

    let radio_start = now_us();
    ble.broadcast_burst(&metrics, profile_json.as_deref(), burst_ms);
    let radio_us = u32::try_from(now_us().saturating_sub(radio_start)).unwrap_or(u32::MAX);

    if !*ota_verified {
        mark_ota_slot_valid_if_pending();
        *ota_verified = true;
    }

    unsafe {
        let rtc = &mut *core::ptr::addr_of_mut!(RTC_STATE);
        rtc.accumulator.record_radio_tx(radio_us);
        rtc.crash_streak = 0;
        rtc.seal();
    }

    Ok(out.post_burst_delay_ms)
}

fn sleep_feeding_wdt(total: Duration) {
    let mut remaining = total;
    while !remaining.is_zero() {
        let slice = remaining.min(Duration::from_secs(2));
        thread::sleep(slice);
        feed_task_watchdog();
        remaining = remaining.saturating_sub(slice);
    }
}
