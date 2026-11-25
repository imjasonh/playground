//! Standalone USB-C 160 MHz ESP32-C3 (RISC-V) `miniz_oxide` benchmark + 2 kHz PC profiler.
//!
//! Flashed directly over USB-C (`make flash-gzip-bench-xiao`) with `CONFIG_BT_ENABLED=n`
//! so ESP32-C3's unified 400 KiB SRAM is uncontested for `miniz_oxide` inflate,
//! `miniz_oxide` deflate (`CompressorOxide`), and CRC32 benchmarking.

use core::ffi::c_void;
use std::collections::BTreeMap;
use std::sync::Mutex;

use anyhow::Result;
use esp_idf_svc::hal::delay::FreeRtos;
use esp_idf_svc::sys::{
    esp_get_free_heap_size, esp_timer_create, esp_timer_create_args_t, esp_timer_delete,
    esp_timer_dispatch_t_ESP_TIMER_TASK, esp_timer_get_time, esp_timer_handle_t,
    esp_timer_start_periodic, esp_timer_stop, heap_caps_get_largest_free_block,
    xTaskGetCurrentTaskHandle, TaskHandle_t, ESP_OK, MALLOC_CAP_8BIT,
};
use mcu_lab::gzip_bench::{
    inflate_miniz_oxide, parse_gzip_frame, CORPORA, GZIP_BENCH_FIRMWARE_ID, MAX_CORPUS_RAW_LEN,
};
use mcu_lab::protocol::crc32 as rust_crc32;
use miniz_oxide::deflate::core::CompressorOxide;
use miniz_oxide::deflate::stream::deflate as miniz_deflate_stream;
use miniz_oxide::inflate::core::DecompressorOxide;
use miniz_oxide::{MZFlush, MZStatus};

extern "C" {
    fn esp_clk_cpu_freq() -> i32;
    fn esp_rom_crc32_le(crc: u32, buf: *const u8, len: u32) -> u32;
    fn tinfl_decompress(
        r: *mut core::ffi::c_void,
        in_buf: *const u8,
        in_buf_size: *mut usize,
        out_buf_start: *mut u8,
        out_buf_next: *mut u8,
        out_buf_size: *mut usize,
        flags: u32,
    ) -> i32;
}

fn now_us() -> u64 {
    // SAFETY: `esp_timer_get_time` returns monotonic microseconds since boot.
    unsafe { esp_timer_get_time().max(0) as u64 }
}

struct SamplerState {
    target_task: TaskHandle_t,
    pcs: Mutex<Vec<u32>>,
}

// SAFETY: `target_task` is an opaque FreeRTOS task handle that outlives the timer.
unsafe impl Send for SamplerState {}
unsafe impl Sync for SamplerState {}

#[inline]
fn is_valid_dram_ptr(ptr: *const u32) -> bool {
    let addr = ptr as usize;
    // ESP32-C3 internal SRAM (DRAM): 0x3FC8_0000 .. 0x3FCE_0000 (400 KiB)
    addr != 0 && (addr & 0x3) == 0 && (0x3FC8_0000..0x3FCE_0000).contains(&addr)
}

unsafe extern "C" fn sample_cb(arg: *mut c_void) {
    if arg.is_null() {
        return;
    }
    let state = &*(arg as *const SamplerState);
    let tcb_ptr = state.target_task as *const *const u32;
    if !is_valid_dram_ptr(tcb_ptr.cast::<u32>()) {
        return;
    }
    let px_top = core::ptr::read_volatile(tcb_ptr);
    if !is_valid_dram_ptr(px_top) {
        return;
    }
    // On RISC-V ESP32-C3, `RvExcFrame` stores `mepc` at word offset 0.
    let pc = *px_top;
    if let Ok(mut v) = state.pcs.try_lock() {
        if v.len() < 8192 {
            v.push(pc & !0x1);
        }
    }
}

struct PhaseProfiler {
    timer: esp_timer_handle_t,
    state: *mut SamplerState,
}

impl PhaseProfiler {
    fn start(period_us: u64) -> Self {
        let target_task = unsafe { xTaskGetCurrentTaskHandle() };
        let state = Box::into_raw(Box::new(SamplerState {
            target_task,
            pcs: Mutex::new(Vec::with_capacity(4096)),
        }));
        let mut timer: esp_timer_handle_t = core::ptr::null_mut();
        let args = esp_timer_create_args_t {
            callback: Some(sample_cb),
            arg: state.cast::<c_void>(),
            dispatch_method: esp_timer_dispatch_t_ESP_TIMER_TASK,
            name: c"c3_prof".as_ptr(),
            skip_unhandled_events: true,
        };
        unsafe {
            if esp_timer_create(&args, &mut timer) == ESP_OK {
                let _ = esp_timer_start_periodic(timer, period_us);
            }
        }
        Self { timer, state }
    }

    fn finish(self, phase: &str) {
        unsafe {
            if !self.timer.is_null() {
                let _ = esp_timer_stop(self.timer);
                let _ = esp_timer_delete(self.timer);
            }
            let boxed = Box::from_raw(self.state);
            let samples = boxed.pcs.into_inner().unwrap_or_default();
            let mut counts: BTreeMap<u32, u32> = BTreeMap::new();
            for pc in &samples {
                *counts.entry(*pc).or_insert(0) += 1;
            }
            let mut sorted: Vec<(u32, u32)> = counts.into_iter().collect();
            sorted.sort_by(|a, b| b.1.cmp(&a.1).then_with(|| a.0.cmp(&b.0)));
            println!(
                "PROF_SUMMARY phase={} total_samples={} unique_pcs={}",
                phase,
                samples.len(),
                sorted.len()
            );
            for (pc, hits) in sorted.into_iter().take(48) {
                println!("PROF phase={} pc={:#010x} hits={}", phase, pc, hits);
            }
        }
    }
}

fn main() -> Result<()> {
    esp_idf_svc::sys::link_patches();
    esp_idf_svc::log::EspLogger::initialize_default();

    // Give USB-Serial/JTAG host time to re-attach after reset.
    FreeRtos::delay_ms(1200);
    let cpu_hz = unsafe { esp_clk_cpu_freq() };
    let free_heap = unsafe { esp_get_free_heap_size() };
    let largest_block = unsafe { heap_caps_get_largest_free_block(MALLOC_CAP_8BIT) };
    println!(
        "BENCH_START fw={} arch=riscv32imc cpu_hz={} free_heap={} largest_block={}",
        GZIP_BENCH_FIRMWARE_ID, cpu_hz, free_heap, largest_block
    );

    let mut out_buf = vec![0u8; MAX_CORPUS_RAW_LEN];
    let mut raw_corpora: Vec<(&str, usize, usize, Vec<u8>)> = Vec::new();

    // 1. SRAM memcpy ceiling (8 KiB SRAM -> SRAM).
    {
        let src = vec![0xA5u8; 8192];
        let mut dst = vec![0u8; 8192];
        let iters = 4000usize;
        let t0 = now_us();
        for _ in 0..iters {
            dst.copy_from_slice(&src);
            std::hint::black_box(&mut dst);
        }
        let us = now_us() - t0;
        println!(
            "BENCH kind=memcpy_sram impl=core corpus=8k_sram iters={} in_bytes=8192 out_bytes=8192 total_us={}",
            iters, us
        );
    }
    FreeRtos::delay_ms(10);

    // 2. Pure-Rust `miniz_oxide` inflate across all corpora (2 kHz RISC-V mepc sampling).
    {
        let mut decomp = Box::new(DecompressorOxide::new());
        let prof = PhaseProfiler::start(500);
        for corpus in CORPORA {
            let frame = parse_gzip_frame(corpus.gz_bytes).map_err(anyhow::Error::msg)?;
            let iters = 200usize;
            let mut last_written = 0usize;
            let t0 = now_us();
            for _ in 0..iters {
                last_written =
                    inflate_miniz_oxide(&mut decomp, frame.deflate_payload, &mut out_buf)
                        .map_err(anyhow::Error::msg)?;
            }
            let us = now_us() - t0;
            assert_eq!(last_written, corpus.raw_len);
            println!(
                "BENCH kind=inflate impl=miniz_oxide corpus={} iters={} in_bytes={} out_bytes={} total_us={}",
                corpus.name,
                iters,
                frame.deflate_payload.len(),
                last_written,
                us
            );
            raw_corpora.push((
                corpus.name,
                corpus.gz_bytes.len(),
                corpus.raw_len,
                out_buf[..last_written].to_vec(),
            ));
            FreeRtos::delay_ms(5);
        }
        prof.finish("c3_miniz_inflate");
    }

    // 2b. ESP32-C3 ROM `tinfl_decompress` inflate across all corpora.
    {
        const TINFL_FLAG_USING_NON_WRAPPING_OUTPUT_BUF: u32 = 4;
        const TINFL_STATUS_DONE: i32 = 0;
        let mut rom_tinfl_state = vec![0u32; 3072].into_boxed_slice();
        let prof = PcProfiler::start(task_handle);
        for corpus in CORPORA {
            let frame = parse_gzip_frame(corpus.gz_bytes).expect("valid gzip");
            let iters = 32usize;
            let mut last_written = 0usize;
            let t0 = now_us();
            for _ in 0..iters {
                rom_tinfl_state[0] = 0;
                let mut in_size = frame.deflate_payload.len();
                let mut out_size = out_buf.len();
                let status = unsafe {
                    tinfl_decompress(
                        rom_tinfl_state.as_mut_ptr().cast(),
                        frame.deflate_payload.as_ptr(),
                        &mut in_size,
                        out_buf.as_mut_ptr(),
                        out_buf.as_mut_ptr(),
                        &mut out_size,
                        TINFL_FLAG_USING_NON_WRAPPING_OUTPUT_BUF,
                    )
                };
                assert_eq!(status, TINFL_STATUS_DONE);
                last_written = out_size;
            }
            let us = now_us() - t0;
            assert_eq!(last_written, corpus.raw_len);
            println!(
                "BENCH kind=inflate impl=esp32c3_rom_miniz corpus={} iters={} in_bytes={} out_bytes={} total_us={}",
                corpus.name,
                iters,
                frame.deflate_payload.len(),
                last_written,
                us
            );
            FreeRtos::delay_ms(5);
        }
        prof.finish("c3_rom_inflate");
    }

    // 3. CRC32 comparison: ESP32-C3 ROM `esp_rom_crc32_le` vs pure-Rust bit-by-bit `protocol::crc32`.
    {
        let prof = PhaseProfiler::start(500);
        for (name, _, raw_len, raw) in &raw_corpora {
            let iters = 800usize;
            let t0 = now_us();
            let mut acc = 0u32;
            for _ in 0..iters {
                acc ^= unsafe { esp_rom_crc32_le(0, raw.as_ptr(), raw.len() as u32) };
            }
            std::hint::black_box(acc);
            let us = now_us() - t0;
            println!(
                "BENCH kind=crc32 impl=esp32c3_rom_crc32 corpus={} iters={} in_bytes={} out_bytes={} total_us={}",
                name, iters, raw_len, raw_len, us
            );
            FreeRtos::delay_ms(5);
        }
        prof.finish("c3_rom_crc32");
    }
    {
        let prof = PhaseProfiler::start(500);
        for (name, _, raw_len, raw) in &raw_corpora {
            let iters = 200usize;
            let t0 = now_us();
            let mut acc = 0u32;
            for _ in 0..iters {
                acc ^= rust_crc32(raw);
            }
            std::hint::black_box(acc);
            let us = now_us() - t0;
            println!(
                "BENCH kind=crc32 impl=rust_crc32 corpus={} iters={} in_bytes={} out_bytes={} total_us={}",
                name, iters, raw_len, raw_len, us
            );
            FreeRtos::delay_ms(5);
        }
        prof.finish("c3_rust_crc32");
    }

    // 4. `miniz_oxide` deflate (`CompressorOxide` requires ~308 KiB across HashBuffers,
    //    LZOxide, and LocalBuf, plus ~68 KiB stack during Default::default()).
    //    Check heap headroom before attempting allocation so we report OOM cleanly.
    let free_before_def = unsafe { esp_get_free_heap_size() } as usize;
    let largest_before_def = unsafe { heap_caps_get_largest_free_block(MALLOC_CAP_8BIT) };
    println!(
        "DEFLATE_HEAP free_heap={} largest_block={} sizeof_compressor={}",
        free_before_def,
        largest_before_def,
        core::mem::size_of::<CompressorOxide>()
    );

    if free_before_def >= 330_000 && largest_before_def >= 165_000 {
        let mut comp = std::thread::Builder::new()
            .name("c3-comp-init".into())
            .stack_size(72 * 1024)
            .spawn(Box::<CompressorOxide>::default)?
            .join()
            .expect("c3-comp-init thread");
        let free_after_def = unsafe { esp_get_free_heap_size() };
        let largest_after_def = unsafe { heap_caps_get_largest_free_block(MALLOC_CAP_8BIT) };
        println!(
            "DEFLATE_ALLOC ok=true free_after={} largest_after={}",
            free_after_def, largest_after_def
        );

        let mut comp_out = vec![0u8; MAX_CORPUS_RAW_LEN + 512];
        let mut decomp = Box::new(DecompressorOxide::new());

        for (label, level, iters) in [
            ("miniz_deflate_l1", 1u8, 40usize),
            ("miniz_deflate_l6", 6u8, 20usize),
            ("miniz_deflate_l9", 9u8, 8usize),
        ] {
            let prof = PhaseProfiler::start(500);
            for (name, _, raw_len, raw) in &raw_corpora {
                let mut out_len = 0usize;
                let t0 = now_us();
                for _ in 0..iters {
                    comp.reset();
                    comp.set_compression_level_raw(level);
                    let res = miniz_deflate_stream(&mut comp, raw, &mut comp_out, MZFlush::Finish);
                    assert_eq!(res.status, Ok(MZStatus::StreamEnd));
                    out_len = res.bytes_written;
                }
                let us = now_us() - t0;

                // Round-trip verify with `miniz_oxide` inflate + ROM CRC32!
                let dec_len = inflate_miniz_oxide(&mut decomp, &comp_out[..out_len], &mut out_buf)
                    .map_err(anyhow::Error::msg)?;
                assert_eq!(dec_len, *raw_len);
                let c1 = unsafe { esp_rom_crc32_le(0, raw.as_ptr(), raw.len() as u32) };
                let c2 = unsafe { esp_rom_crc32_le(0, out_buf.as_ptr(), dec_len as u32) };
                assert_eq!(c1, c2);

                println!(
                    "BENCH kind=deflate impl={} corpus={} iters={} in_bytes={} out_bytes={} total_us={}",
                    label, name, iters, raw_len, out_len, us
                );
                FreeRtos::delay_ms(5);
            }
            prof.finish(label);
        }
    } else {
        println!(
            "DEFLATE_ALLOC ok=false needed=~315000 free_heap={} largest_block={}",
            free_before_def, largest_before_def
        );
    }

    println!("BENCH_DONE");
    loop {
        FreeRtos::delay_ms(5_000);
    }
}
