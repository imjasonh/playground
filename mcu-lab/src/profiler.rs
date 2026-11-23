//! Shared per-wake profiler (`WakeProfiler`) with 1 kHz PC hotspot sampling.
//!
//! Active in debug builds or when `--features profiling` is enabled; compiles to
//! a zero-sized no-op in production release builds (`--release --features firmware`).

use esp_idf_svc::sys::esp_timer_get_time;

/// Monotonic microseconds since boot.
pub fn now_us() -> u64 {
    // SAFETY: esp_timer_get_time returns monotonic microseconds since boot and takes no arguments.
    unsafe { esp_timer_get_time().max(0) as u64 }
}

/// Return the firmware's Build ID (40-char hex) if embedded at build time, falling
/// back to the ESP-IDF `esp_app_desc_t.app_elf_sha256` prefix if available.
pub fn firmware_build_id() -> String {
    if let Some(id) = option_env!("MCU_LAB_BUILD_ID") {
        if !id.is_empty() {
            return id.to_string();
        }
    }
    // SAFETY: esp_app_get_description returns a static pointer to the running app's descriptor.
    let desc = unsafe { esp_idf_svc::sys::esp_app_get_description() };
    if desc.is_null() {
        return String::new();
    }
    // SAFETY: `desc` is non-null and points to immutable flash-mapped `esp_app_desc_t`.
    let sha = unsafe { &(*desc).app_elf_sha256 };
    if sha.iter().all(|&b| b == 0) {
        return String::new();
    }
    // First 20 bytes (40 hex chars) match the 40-char Build ID format used by mcu-lab-backend.
    hex::encode(&sha[..20])
}

#[cfg(any(debug_assertions, feature = "profiling"))]
mod inner {
    use std::ffi::c_void;
    use std::sync::{Arc, Mutex};

    use esp32_nimble::utilities::mutex::Mutex as NimbleMutex;
    use esp32_nimble::{uuid128, BLECharacteristic, BLEService, NimbleProperties};
    use esp_idf_svc::hal::delay::FreeRtos;
    use esp_idf_svc::sys::{
        esp_get_free_heap_size, esp_get_minimum_free_heap_size, esp_timer_create,
        esp_timer_create_args_t, esp_timer_delete, esp_timer_dispatch_t_ESP_TIMER_TASK,
        esp_timer_handle_t, esp_timer_start_periodic, esp_timer_stop, uxTaskGetStackHighWaterMark,
        xTaskGetCurrentTaskHandle, TaskHandle_t, ESP_OK,
    };
    use log::info;

    use crate::protocol::{
        encode_blob_frames, format_wake_profile_json, AdvMetrics, BoardConfig, PcHistogram,
        SpanRecorder, WakeProfile,
    };

    use super::{firmware_build_id, now_us};

    /// 1 kHz sampling interval (1,000 µs) for the PC hotspot sampler.
    const PC_SAMPLE_PERIOD_US: u64 = 1_000;

    /// Maximum number of PC hotspots included in the BLE GATT WakeProfile JSON.
    const MAX_PC_HOTSPOTS: usize = 12;

    /// Maximum payload per BLE GATT notification frame (fits comfortably inside 512-byte ATT MTU).
    const PROFILE_CHUNK_PAYLOAD: usize = 460;

    struct PcSamplerState {
        target_task: TaskHandle_t,
        hist: Mutex<PcHistogram>,
    }

    // SAFETY: `target_task` is an opaque FreeRTOS task handle for the main task,
    // which outlives the timer (the timer is stopped and deleted in `finish_json` / `Drop`).
    unsafe impl Send for PcSamplerState {}
    unsafe impl Sync for PcSamplerState {}

    /// Guard against dereferencing unaligned or out-of-DRAM pointers when inspecting
    /// a FreeRTOS task's saved stack pointer.
    #[inline]
    fn is_valid_dram_ptr(ptr: *const u32) -> bool {
        let addr = ptr as usize;
        if addr == 0 || (addr & 0x3) != 0 {
            return false;
        }
        #[cfg(target_arch = "riscv32")]
        {
            // ESP32-C3 internal SRAM (DRAM): 0x3FC8_0000 .. 0x3FCE_0000
            (0x3FC8_0000..0x3FCE_0000).contains(&addr)
        }
        #[cfg(target_arch = "xtensa")]
        {
            // Classic ESP32 internal DRAM: 0x3FFB_0000 .. 0x4000_0000
            (0x3FFB_0000..0x4000_0000).contains(&addr)
        }
        #[cfg(not(any(target_arch = "riscv32", target_arch = "xtensa")))]
        {
            let _ = addr;
            false
        }
    }

    /// Read the interrupted program counter from the FreeRTOS saved exception frame.
    ///
    /// - RISC-V (`esp32c3`): `RvExcFrame` stores `mepc` at word offset 0.
    /// - Xtensa (`esp32`): both `XtExcFrame` (preempted, `exit != 0`) and `XtSolFrame`
    ///   (solicited switch, `exit == 0`) store `pc` at word offset 1. For `XtSolFrame`,
    ///   `pc` comes from windowed-ABI `a0`, whose top two bits encode the call window
    ///   increment (`01`/`10`/`11`) instead of the `0x4000_0000` IRAM/IROM prefix; we
    ///   normalize those top two bits back to `0x4000_0000`.
    #[inline]
    unsafe fn read_saved_pc(px_top_of_stack: *const u32) -> u32 {
        #[cfg(target_arch = "riscv32")]
        {
            *px_top_of_stack
        }
        #[cfg(target_arch = "xtensa")]
        {
            let exit = *px_top_of_stack;
            let raw_pc = *px_top_of_stack.add(1);
            if exit == 0 && raw_pc != 0 {
                (raw_pc & 0x3FFF_FFFF) | 0x4000_0000
            } else {
                raw_pc
            }
        }
        #[cfg(not(any(target_arch = "riscv32", target_arch = "xtensa")))]
        {
            let _ = px_top_of_stack;
            0
        }
    }

    /// Timer callback executed at 1 kHz from the high-priority `esp_timer` task.
    unsafe extern "C" fn pc_sample_timer_cb(arg: *mut c_void) {
        if arg.is_null() {
            return;
        }
        let state = &*(arg as *const PcSamplerState);
        if state.target_task.is_null() {
            return;
        }
        let tcb_ptr = state.target_task as *const *const u32;
        if !is_valid_dram_ptr(tcb_ptr.cast::<u32>()) {
            return;
        }
        let px_top_of_stack = core::ptr::read_volatile(tcb_ptr);
        if !is_valid_dram_ptr(px_top_of_stack) {
            return;
        }
        let pc = read_saved_pc(px_top_of_stack);
        if let Ok(mut hist) = state.hist.try_lock() {
            hist.record(pc);
        }
    }

    pub struct WakeProfiler {
        board: BoardConfig,
        wake_start_us: u64,
        spans: SpanRecorder,
        timer: esp_timer_handle_t,
        sampler: *mut PcSamplerState,
    }

    impl WakeProfiler {
        pub fn start(board: BoardConfig, wake_start_us: u64) -> Self {
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
                name: c"mculab_prof".as_ptr(),
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
                board,
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
                .saturating_mul(self.board.cpu_mhz);
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
                "profile({}): free_heap={free_heap_bytes} min_heap={min_free_heap_bytes} stack_hw={stack_high_water_bytes} pc_hotspots={}",
                self.board.app,
                pc_samples.len()
            );
            let git_sha = option_env!("MCU_LAB_GIT_SHA").unwrap_or("").to_string();
            let build_id = firmware_build_id();
            let spans = core::mem::take(&mut self.spans).into_spans();
            let profile = WakeProfile {
                wake_count: metrics.wake_count,
                seq: metrics.seq,
                board: self.board.board.to_string(),
                chip: self.board.chip.to_string(),
                app: self.board.app.to_string(),
                git_sha,
                build_id,
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

    pub struct ProfileCharHandle {
        ch: Arc<NimbleMutex<BLECharacteristic>>,
        latest_json: Arc<Mutex<Vec<u8>>>,
    }

    pub fn create_profile_char(
        service: &Arc<NimbleMutex<BLEService>>,
    ) -> Option<ProfileCharHandle> {
        let ch = service.lock().create_characteristic(
            uuid128!("1a3c0002-36e1-4688-b7f5-ea07361bc303"),
            NimbleProperties::READ | NimbleProperties::NOTIFY,
        );
        let latest_json = Arc::new(Mutex::new(Vec::new()));
        let ch_sub = Arc::clone(&ch);
        let buf_sub = Arc::clone(&latest_json);
        ch.lock().on_subscribe(move |_ch, _desc, sub_value| {
            // Stream chunked `MC` frames when a client enables notifications so profiles
            // larger than the 512-byte ATT characteristic limit never truncate.
            if sub_value.is_empty() {
                return;
            }
            let data = buf_sub.lock().unwrap_or_else(|e| e.into_inner()).clone();
            if data.is_empty() {
                return;
            }
            for frame in encode_blob_frames(&data, PROFILE_CHUNK_PAYLOAD) {
                ch_sub.lock().set_value(&frame).notify();
                FreeRtos::delay_ms(5);
            }
        });
        Some(ProfileCharHandle { ch, latest_json })
    }

    pub fn update_profile_char(handle: &Option<ProfileCharHandle>, profile_json: Option<&str>) {
        if let (Some(h), Some(json)) = (handle, profile_json) {
            let bytes = json.as_bytes();
            *h.latest_json.lock().unwrap_or_else(|e| e.into_inner()) = bytes.to_vec();
            // Keep direct READ backwards-compatible when JSON fits in a single ATT read;
            // larger payloads are still delivered intact via chunked NOTIFY on subscribe.
            if bytes.len() <= PROFILE_CHUNK_PAYLOAD {
                h.ch.lock().set_value(bytes);
            } else {
                let first = encode_blob_frames(bytes, PROFILE_CHUNK_PAYLOAD);
                if let Some(frame0) = first.first() {
                    h.ch.lock().set_value(frame0);
                }
            }
        }
    }
}

#[cfg(not(any(debug_assertions, feature = "profiling")))]
mod inner {
    use std::sync::Arc;

    use esp32_nimble::utilities::mutex::Mutex as NimbleMutex;
    use esp32_nimble::BLEService;

    use crate::protocol::{AdvMetrics, BoardConfig};

    pub type ProfileCharHandle = ();

    /// Zero-sized no-op profiler compiled into production release builds.
    pub struct WakeProfiler;

    impl WakeProfiler {
        #[inline(always)]
        pub fn start(_board: BoardConfig, _wake_start_us: u64) -> Self {
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
    pub fn create_profile_char(
        _service: &Arc<NimbleMutex<BLEService>>,
    ) -> Option<ProfileCharHandle> {
        None
    }

    #[inline(always)]
    pub fn update_profile_char(_handle: &Option<ProfileCharHandle>, _profile_json: Option<&str>) {}
}

pub use inner::{create_profile_char, update_profile_char, ProfileCharHandle, WakeProfiler};
