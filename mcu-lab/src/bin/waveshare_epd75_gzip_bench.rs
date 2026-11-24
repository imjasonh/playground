//! Standalone USB-C 240 MHz ESP32 Mask-ROM `miniz` benchmark + 2 kHz PC profiler.
//!
//! Flashed directly over USB-C (`make flash-gzip-bench`) with `CONFIG_BT_ENABLED=n`
//! and `CONFIG_FREERTOS_UNICORE=y` so the lower 192 KiB DRAM bank provides >168 KiB
//! of contiguous SRAM for the silicon Mask-ROM `tdefl_compressor` (167,744 B).
//!
//! Run `make profile-gzip-bench` to capture serial output, symbolize PCs against
//! `esp32_rev300_rom.elf` + the app ELF, and generate an SVG flame chart.

use core::ffi::c_void;
use std::collections::BTreeMap;
use std::sync::Mutex;

use anyhow::Result;
use esp_idf_svc::hal::delay::FreeRtos;
use esp_idf_svc::sys::{
    esp_get_free_heap_size, esp_timer_create, esp_timer_create_args_t, esp_timer_delete,
    esp_timer_dispatch_t_ESP_TIMER_TASK, esp_timer_get_time, esp_timer_handle_t,
    esp_timer_start_periodic, esp_timer_stop, heap_caps_free, heap_caps_get_largest_free_block,
    heap_caps_malloc, xTaskGetCurrentTaskHandle, TaskHandle_t, ESP_OK, MALLOC_CAP_8BIT,
};
use mcu_lab::gzip_bench::{parse_gzip_frame, CORPORA, GZIP_BENCH_FIRMWARE_ID, MAX_CORPUS_RAW_LEN};

const TINFL_FLAG_USING_NON_WRAPPING_OUTPUT_BUF: u32 = 4;
const TINFL_STATUS_DONE: i32 = 0;
const TDEFL_FINISH: i32 = 4;
const TDEFL_STATUS_OKAY: i32 = 0;
const TDEFL_STATUS_DONE: i32 = 1;
const TDEFL_GREEDY_PARSING_FLAG: i32 = 0x4000;

/// Exact `sizeof(tdefl_compressor)` in ESP32 mask ROM (`esp_rom/include/esp32/rom/miniz.h`).
const ROM_TDEFL_COMPRESSOR_BYTES: usize = 167_744;
/// `sizeof(tinfl_decompressor)` in ESP32 mask ROM is ~10,952 B; 3,072 u32s = 12 KiB.
const ROM_TINFL_STATE_WORDS: usize = 3_072;

extern "C" {
    fn esp_clk_cpu_freq() -> i32;
    fn tinfl_decompress(
        r: *mut c_void,
        p_in_buf_next: *const u8,
        p_in_buf_size: *mut usize,
        p_out_buf_start: *mut u8,
        p_out_buf_next: *mut u8,
        p_out_buf_size: *mut usize,
        decomp_flags: u32,
    ) -> i32;
    fn tdefl_init(
        d: *mut c_void,
        p_put_buf_func: *const c_void,
        p_put_buf_user: *mut c_void,
        flags: i32,
    ) -> i32;
    fn tdefl_compress(
        d: *mut c_void,
        p_in_buf: *const c_void,
        p_in_buf_size: *mut usize,
        p_out_buf: *mut c_void,
        p_out_buf_size: *mut usize,
        flush: i32,
    ) -> i32;
    fn mz_crc32(crc: u32, ptr: *const u8, buf_len: usize) -> u32;
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
    addr != 0 && (addr & 0x3) == 0 && (0x3FF8_0000..0x4000_0000).contains(&addr)
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
    let exit = *px_top;
    let raw_pc = *px_top.add(1);
    let pc = if exit == 0 && raw_pc != 0 {
        (raw_pc & 0x3FFF_FFFF) | 0x4000_0000
    } else {
        raw_pc
    };
    if let Ok(mut v) = state.pcs.try_lock() {
        if v.len() < 8192 {
            v.push(pc & !0x3);
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
            name: c"rom_prof".as_ptr(),
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

    FreeRtos::delay_ms(500);
    let cpu_hz = unsafe { esp_clk_cpu_freq() };
    let free_heap = unsafe { esp_get_free_heap_size() };
    let largest_block = unsafe { heap_caps_get_largest_free_block(MALLOC_CAP_8BIT) };
    println!(
        "BENCH_START fw={} cpu_hz={} free_heap={} largest_block={}",
        GZIP_BENCH_FIRMWARE_ID, cpu_hz, free_heap, largest_block
    );

    // Allocate mask-ROM `tdefl_compressor` (167,744 B) from the lower DRAM bank BEFORE
    // spawning the 16 KiB benchmark worker thread (which lands in the upper ~127 KiB bank).
    let comp_ptr = unsafe { heap_caps_malloc(ROM_TDEFL_COMPRESSOR_BYTES, MALLOC_CAP_8BIT) };
    let free_after_tdefl = unsafe { esp_get_free_heap_size() };
    let largest_after_tdefl = unsafe { heap_caps_get_largest_free_block(MALLOC_CAP_8BIT) };
    println!(
        "TDEFL_ALLOC ok={} ptr={:#010x} size={} free_after={} largest_after={}",
        !comp_ptr.is_null(),
        comp_ptr as usize,
        ROM_TDEFL_COMPRESSOR_BYTES,
        free_after_tdefl,
        largest_after_tdefl
    );

    let comp_addr = comp_ptr as usize;
    let handle = std::thread::Builder::new()
        .name("gzip-bench".into())
        .stack_size(16 * 1024)
        .spawn(move || run_benchmarks(comp_addr as *mut c_void))?;
    handle.join().expect("gzip-bench thread")?;

    if !comp_ptr.is_null() {
        unsafe {
            heap_caps_free(comp_ptr);
        }
    }

    loop {
        FreeRtos::delay_ms(5_000);
    }
}

fn run_benchmarks(comp_ptr: *mut c_void) -> Result<()> {
    let mut out_buf = vec![0u8; MAX_CORPUS_RAW_LEN];
    let mut tinfl_state = vec![0u32; ROM_TINFL_STATE_WORDS];
    let mut raw_corpora: Vec<(&str, usize, usize, Vec<u8>)> = Vec::new();

    // 1. DRAM memcpy ceiling (8 KiB DRAM -> DRAM).
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
            "BENCH kind=memcpy_dram impl=core corpus=8k_dram iters={} in_bytes=8192 out_bytes=8192 total_us={}",
            iters, us
        );
    }
    FreeRtos::delay_ms(10);

    // 2. Mask-ROM `tinfl_decompress` across all corpora (2 kHz PC sampled).
    {
        let prof = PhaseProfiler::start(500);
        for corpus in CORPORA {
            let frame = parse_gzip_frame(corpus.gz_bytes).map_err(anyhow::Error::msg)?;
            let iters = 400usize;
            let mut last_written = 0usize;
            let t0 = now_us();
            for _ in 0..iters {
                tinfl_state[0] = 0;
                let mut in_sz = frame.deflate_payload.len();
                let mut out_sz = out_buf.len();
                let st = unsafe {
                    tinfl_decompress(
                        tinfl_state.as_mut_ptr().cast::<c_void>(),
                        frame.deflate_payload.as_ptr(),
                        &mut in_sz,
                        out_buf.as_mut_ptr(),
                        out_buf.as_mut_ptr(),
                        &mut out_sz,
                        TINFL_FLAG_USING_NON_WRAPPING_OUTPUT_BUF,
                    )
                };
                assert_eq!(st, TINFL_STATUS_DONE);
                last_written = out_sz;
            }
            let us = now_us() - t0;
            assert_eq!(last_written, corpus.raw_len);
            println!(
                "BENCH kind=inflate impl=esp32_rom_tinfl corpus={} iters={} in_bytes={} out_bytes={} total_us={}",
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
        prof.finish("rom_tinfl_240m");
    }

    // 3. Mask-ROM `mz_crc32` across all corpora (2 kHz PC sampled).
    {
        let prof = PhaseProfiler::start(500);
        for (name, _, raw_len, raw) in &raw_corpora {
            let iters = 800usize;
            let t0 = now_us();
            let mut acc = 0u32;
            for _ in 0..iters {
                acc ^= unsafe { mz_crc32(0, raw.as_ptr(), raw.len()) };
            }
            std::hint::black_box(acc);
            let us = now_us() - t0;
            println!(
                "BENCH kind=crc32 impl=esp32_rom_mz_crc32 corpus={} iters={} in_bytes={} out_bytes={} total_us={}",
                name, iters, raw_len, raw_len, us
            );
            FreeRtos::delay_ms(5);
        }
        prof.finish("rom_crc32_240m");
    }

    // 4. Mask-ROM `tdefl_init` + `tdefl_compress` across probe levels.
    if !comp_ptr.is_null() {
        let mut comp_out = vec![0u8; MAX_CORPUS_RAW_LEN + 512];

        {
            let prof = PhaseProfiler::start(500);
            let iters = 500usize;
            let t0 = now_us();
            for _ in 0..iters {
                let st =
                    unsafe { tdefl_init(comp_ptr, core::ptr::null(), core::ptr::null_mut(), 128) };
                assert_eq!(st, TDEFL_STATUS_OKAY);
            }
            let us = now_us() - t0;
            println!(
                "BENCH kind=tdefl_init impl=esp32_rom_tdefl corpus=state_164k iters={} in_bytes={} out_bytes=0 total_us={}",
                iters, ROM_TDEFL_COMPRESSOR_BYTES, us
            );
            prof.finish("rom_tdefl_init");
        }
        FreeRtos::delay_ms(10);

        for (label, flags, iters) in [
            ("rom_tdefl_p0_huff", 0, 120usize),
            (
                "rom_tdefl_p1_greedy",
                TDEFL_GREEDY_PARSING_FLAG | 1,
                80usize,
            ),
            ("rom_tdefl_p16_fast", 16, 40usize),
            ("rom_tdefl_p128_default", 128, 25usize),
            ("rom_tdefl_p4095_max", 4095, 10usize),
        ] {
            let prof = PhaseProfiler::start(500);
            for (name, _, raw_len, raw) in &raw_corpora {
                let mut out_len = 0usize;
                let mut total_compress_us = 0u64;
                let mut total_with_init_us = 0u64;
                for _ in 0..iters {
                    let t_init = now_us();
                    let st_init = unsafe {
                        tdefl_init(comp_ptr, core::ptr::null(), core::ptr::null_mut(), flags)
                    };
                    assert_eq!(st_init, TDEFL_STATUS_OKAY);
                    let t_comp = now_us();
                    let mut in_sz = raw.len();
                    let mut out_sz = comp_out.len();
                    let st = unsafe {
                        tdefl_compress(
                            comp_ptr,
                            raw.as_ptr().cast::<c_void>(),
                            &mut in_sz,
                            comp_out.as_mut_ptr().cast::<c_void>(),
                            &mut out_sz,
                            TDEFL_FINISH,
                        )
                    };
                    let t_end = now_us();
                    assert_eq!(st, TDEFL_STATUS_DONE);
                    total_compress_us += t_end - t_comp;
                    total_with_init_us += t_end - t_init;
                    out_len = out_sz;
                }

                // Round-trip verify with Mask-ROM `tinfl_decompress` + `mz_crc32`.
                tinfl_state[0] = 0;
                let mut in_sz = out_len;
                let mut out_sz = out_buf.len();
                let st = unsafe {
                    tinfl_decompress(
                        tinfl_state.as_mut_ptr().cast::<c_void>(),
                        comp_out.as_ptr(),
                        &mut in_sz,
                        out_buf.as_mut_ptr(),
                        out_buf.as_mut_ptr(),
                        &mut out_sz,
                        TINFL_FLAG_USING_NON_WRAPPING_OUTPUT_BUF,
                    )
                };
                assert_eq!(st, TINFL_STATUS_DONE);
                assert_eq!(out_sz, *raw_len);
                assert_eq!(unsafe { mz_crc32(0, raw.as_ptr(), raw.len()) }, unsafe {
                    mz_crc32(0, out_buf.as_ptr(), out_sz)
                });

                println!(
                    "BENCH kind=deflate impl={} corpus={} iters={} in_bytes={} out_bytes={} total_us={} with_init_us={}",
                    label, name, iters, raw_len, out_len, total_compress_us, total_with_init_us
                );
                FreeRtos::delay_ms(5);
            }
            prof.finish(label);
        }

        // Steady-state 32 KiB buffer (`json_otel` x 8) to amortize per-block Huffman overhead.
        if let Some((_, _, _, json_raw)) = raw_corpora.iter().find(|(n, _, _, _)| *n == "json_otel")
        {
            let mut big_buf = Vec::with_capacity(32 * 1024);
            for _ in 0..8 {
                big_buf.extend_from_slice(json_raw);
            }
            let expected_big_crc = unsafe { mz_crc32(0, big_buf.as_ptr(), big_buf.len()) };
            let mut big_out = vec![0u8; 16 * 1024];
            for (label, flags, iters) in [
                (
                    "rom_tdefl_p1_greedy",
                    TDEFL_GREEDY_PARSING_FLAG | 1,
                    20usize,
                ),
                ("rom_tdefl_p128_default", 128, 10usize),
            ] {
                let mut out_len = 0usize;
                let mut total_compress_us = 0u64;
                let mut total_with_init_us = 0u64;
                for _ in 0..iters {
                    let t_init = now_us();
                    let st_init = unsafe {
                        tdefl_init(comp_ptr, core::ptr::null(), core::ptr::null_mut(), flags)
                    };
                    assert_eq!(st_init, TDEFL_STATUS_OKAY);
                    let t_comp = now_us();
                    let mut in_sz = big_buf.len();
                    let mut out_sz = big_out.len();
                    let st = unsafe {
                        tdefl_compress(
                            comp_ptr,
                            big_buf.as_ptr().cast::<c_void>(),
                            &mut in_sz,
                            big_out.as_mut_ptr().cast::<c_void>(),
                            &mut out_sz,
                            TDEFL_FINISH,
                        )
                    };
                    let t_end = now_us();
                    assert_eq!(st, TDEFL_STATUS_DONE);
                    total_compress_us += t_end - t_comp;
                    total_with_init_us += t_end - t_init;
                    out_len = out_sz;
                }
                println!(
                    "BENCH kind=deflate impl={} corpus=json_otel_32k iters={} in_bytes={} out_bytes={} total_us={} with_init_us={}",
                    label,
                    iters,
                    big_buf.len(),
                    out_len,
                    total_compress_us,
                    total_with_init_us
                );
                if label == "rom_tdefl_p128_default" {
                    // Reuse `big_buf` in-place to verify & benchmark 32 KiB ROM inflate without extra RAM.
                    let inf_iters = 100usize;
                    let t0 = now_us();
                    for _ in 0..inf_iters {
                        tinfl_state[0] = 0;
                        let mut in_sz = out_len;
                        let mut out_sz = big_buf.len();
                        let st = unsafe {
                            tinfl_decompress(
                                tinfl_state.as_mut_ptr().cast::<c_void>(),
                                big_out.as_ptr(),
                                &mut in_sz,
                                big_buf.as_mut_ptr(),
                                big_buf.as_mut_ptr(),
                                &mut out_sz,
                                TINFL_FLAG_USING_NON_WRAPPING_OUTPUT_BUF,
                            )
                        };
                        assert_eq!(st, TINFL_STATUS_DONE);
                        assert_eq!(out_sz, 32 * 1024);
                    }
                    let inf_us = now_us() - t0;
                    assert_eq!(
                        unsafe { mz_crc32(0, big_buf.as_ptr(), big_buf.len()) },
                        expected_big_crc
                    );
                    println!(
                        "BENCH kind=inflate impl=esp32_rom_tinfl corpus=json_otel_32k iters={} in_bytes={} out_bytes={} total_us={}",
                        inf_iters,
                        out_len,
                        big_buf.len(),
                        inf_us
                    );
                }
                FreeRtos::delay_ms(5);
            }
        }
    }

    println!("BENCH_DONE");
    Ok(())
}
