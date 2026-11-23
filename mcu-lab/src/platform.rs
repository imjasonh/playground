//! Reusable `App<B: Board>` platform runtime for `mcu-lab` firmware targets.
//!
//! Hardware boards implement [`Board`](crate::boards::Board); applications
//! implement [`App<B>`]. A flashable firmware binary simply wires one board
//! and one app together via [`run::<B, A>()`].
//!
//! The platform owns boot initialization, Task Watchdog subscription/feeding,
//! CRC32-guarded RTC state, crash-loop rollback protection, `WakeProfiler`,
//! BLE telemetry, resumable BLE GATT OTA, and flash coredump upload.

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
use crate::boards::Board;
use crate::profiler::{now_us, WakeProfiler};
use crate::protocol::{
    encode_board_flags, format_status_line, reset_reason_name, RtcState, FLAG_BROWNOUT_RESET,
    FLAG_DEEP_SLEEP_WAKE, MAX_CRASH_STREAK,
};

/// Persistent CRC32-guarded state placed in RTC slow RAM so wake counters and
/// crash-streak tracking survive deep sleep and recover cleanly from brownouts.
#[link_section = ".rtc.data"]
static mut RTC_STATE: RtcState = RtcState::new();

/// Execution cadence for an [`App`].
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum RunMode {
    /// Execute one [`App::step`], broadcast a BLE burst for `burst_ms`, then enter deep sleep.
    DeepSleep { interval_us: u64, burst_ms: u32 },
    /// Execute [`App::step`] repeatedly in a loop, broadcasting a BLE burst after each step.
    Continuous { burst_ms: u32, min_step_ms: u64 },
}

/// Phase durations and metadata returned by a single [`App::step`].
#[derive(Debug, Clone, Copy, Default, PartialEq, Eq)]
pub struct StepOutput {
    pub sensor_us: u32,
    pub compute_us: u32,
    pub epd_refresh_us: u32,
    /// Optional battery/rail voltage override in mV (`0` falls back to `board.read_battery_mv()`).
    pub battery_mv: u16,
    /// Additional low-nibble flag bits (`FLAG_EPD_PARTIAL`, etc.).
    /// Board ID, hardware flags, deep-sleep wake, and brownout bits are added automatically.
    pub flags: u8,
    /// Optional extra sleep after this step's BLE burst (e.g. hold a completed frame on screen).
    pub post_burst_delay_ms: u64,
}

/// Per-step runtime context passed into [`App::step`].
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

/// Trait implemented by every application built on top of a `mcu-lab` [`Board`].
pub trait App<B: Board>: Sized {
    /// Short app slug (e.g. `"base"`, `"bench"`, `"maze"`). Combined with `B::SPEC.board`
    /// as `<board>-<app>` for OTel `mcu.app` and GHCR symbol lookup.
    const APP_NAME: &'static str;

    /// Firmware identifier string embedded in the binary (verified by `make check-firmware`).
    const FIRMWARE_ID: &'static str;

    /// Execution cadence for this app on board `B` (defaults to `B::default_run_mode()`).
    fn run_mode() -> RunMode {
        B::default_run_mode()
    }

    /// Initialize application state using the already-initialized `board`.
    fn init(board: &mut B) -> Result<Self>;

    /// Optional application-level self-test run after `board.self_test()` on `PENDING_VERIFY`.
    fn self_test(&mut self, _board: &mut B) -> Result<()> {
        Ok(())
    }

    /// Execute one wake or animation step and return its phase durations and flags.
    fn step(&mut self, board: &mut B, ctx: &mut StepContext<'_>) -> Result<StepOutput>;
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

/// Boot board `B` and run application `A` on the shared `mcu-lab` platform.
pub fn run<B: Board, A: App<B>>() -> Result<()> {
    let boot_start_us = now_us();
    esp_idf_svc::sys::link_patches();
    esp_idf_svc::log::EspLogger::initialize_default();

    // Subscribe main task to the ESP-IDF Task Watchdog (configured in sdkconfig.defaults).
    // SAFETY: `null_mut()` subscribes the currently executing FreeRTOS task.
    unsafe {
        let _ = esp_task_wdt_add(core::ptr::null_mut());
    }

    let target_name = format!("{}-{}", B::SPEC.board, A::APP_NAME);
    let reset_code = unsafe { esp_reset_reason() } as i32;
    let reset_name = reset_reason_name(reset_code);
    info!(
        "{} boot (target={target_name}, board={}, app={}, chip={}, reset={reset_name}({reset_code}), coredump={})",
        A::FIRMWARE_ID,
        B::SPEC.board,
        A::APP_NAME,
        B::SPEC.chip,
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
    let mut board = match B::init(peripherals) {
        Ok(b) => b,
        Err(err) => {
            warn!("board init failed: {err:#}");
            if is_ota_slot_pending_verify() {
                rollback_ota_slot_and_reboot();
            }
            return Err(err);
        }
    };

    let mut app = match A::init(&mut board) {
        Ok(a) => a,
        Err(err) => {
            warn!("app init failed: {err:#}");
            if is_ota_slot_pending_verify() {
                rollback_ota_slot_and_reboot();
            }
            return Err(err);
        }
    };

    if is_ota_slot_pending_verify() {
        if let Err(err) = board.self_test().and_then(|()| app.self_test(&mut board)) {
            warn!("ota: self_test failed on PENDING_VERIFY slot: {err:#}");
            rollback_ota_slot_and_reboot();
        }
        info!("ota: board + app self_test passed");
    }

    let ble = BleOtaNode::init(B::SPEC);
    let mut ota_verified = false;

    let mut base_flags = encode_board_flags(B::SPEC.board_id) | (board.hardware_flags() & 0x0F);
    if reset_code == 8 {
        base_flags |= FLAG_DEEP_SLEEP_WAKE;
    } else if reset_code == 9 {
        base_flags |= FLAG_BROWNOUT_RESET;
    }

    match A::run_mode() {
        RunMode::DeepSleep {
            interval_us,
            burst_ms,
        } => {
            run_one_step(
                &mut board,
                &mut app,
                &ble,
                &target_name,
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
                &mut board,
                &mut app,
                &ble,
                &target_name,
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
                    warn!("{target_name} step failed: {err:#}");
                    sleep_feeding_wdt(Duration::from_secs(2));
                }
            }
        },
    }
}

#[allow(clippy::too_many_arguments)]
fn run_one_step<B: Board, A: App<B>>(
    board: &mut B,
    app: &mut A,
    ble: &BleOtaNode,
    target_name: &str,
    cycle_start_us: u64,
    reset_code: i32,
    base_flags: u8,
    burst_ms: u32,
    ota_verified: &mut bool,
) -> Result<u64> {
    feed_task_watchdog();
    let mut prof = WakeProfiler::start(B::SPEC, target_name.to_string(), cycle_start_us);
    let next_wake = unsafe {
        let rtc = &*core::ptr::addr_of!(RTC_STATE);
        rtc.accumulator.wake_count.saturating_add(1)
    };

    let mut ctx = StepContext {
        wake_count: next_wake,
        reset_code,
        profiler: &mut prof,
    };
    let out = app.step(board, &mut ctx)?;
    feed_task_watchdog();

    let battery_mv = if out.battery_mv > 0 {
        out.battery_mv
    } else {
        board.read_battery_mv()
    };
    let flags = base_flags | (out.flags & 0x0F);
    let metrics = unsafe {
        let rtc = &mut *core::ptr::addr_of_mut!(RTC_STATE);
        let m = rtc.accumulator.record_wake(
            out.sensor_us,
            out.compute_us,
            out.epd_refresh_us,
            battery_mv,
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
