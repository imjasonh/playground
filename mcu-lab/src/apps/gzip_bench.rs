//! `GzipBenchApp` — RFC 1952 gzip / DEFLATE benchmark exercising app-level OTel
//! metrics, traces (span + wake attributes), and 1 kHz PC hotspot profiling on
//! both `xiao-esp32c3` (`miniz_oxide`) and `waveshare-epd75` (ESP32 mask-ROM
//! `tinfl` / `tdefl` / `mz_crc32`).

use anyhow::Result;
use esp_idf_svc::sys::{esp_get_free_heap_size, heap_caps_get_largest_free_block, MALLOC_CAP_8BIT};
use log::{info, warn};

use crate::boards::Board;
use crate::gzip_bench::{
    parse_gzip_frame, ratio_milli, throughput_bps, BENCH_ITERATIONS, CORPORA,
    GZIP_BENCH_FIRMWARE_ID, MAX_CORPUS_RAW_LEN,
};
use crate::platform::{App, StepContext, StepOutput};
use crate::profiler::now_us;
use crate::protocol::AppCommandSpec;

#[allow(dead_code)]
enum DeflateAttempt {
    Ok {
        compressed_len: usize,
        deflate_us: u32,
    },
    Oom {
        needed_bytes: usize,
        free_heap: usize,
        largest_block: usize,
    },
    Err(String),
}

#[cfg(target_arch = "xtensa")]
mod backend {
    use core::ffi::c_void;
    use esp_idf_svc::sys::{
        esp_get_free_heap_size, heap_caps_free, heap_caps_get_largest_free_block, heap_caps_malloc,
        MALLOC_CAP_8BIT,
    };

    use crate::profiler::now_us;

    use super::DeflateAttempt;

    pub const IMPL_NAME: &str = "esp32_rom_miniz";

    /// `TINFL_FLAG_USING_NON_WRAPPING_OUTPUT_BUF` from `esp_rom/include/esp32/rom/miniz.h`.
    const TINFL_FLAG_USING_NON_WRAPPING_OUTPUT_BUF: u32 = 4;
    const TINFL_STATUS_DONE: i32 = 0;

    /// `TDEFL_DEFAULT_MAX_PROBES` and `TDEFL_FINISH` from `esp_rom/include/esp32/rom/miniz.h`.
    const TDEFL_DEFAULT_MAX_PROBES: i32 = 128;
    const TDEFL_FINISH: i32 = 4;
    const TDEFL_STATUS_OKAY: i32 = 0;
    const TDEFL_STATUS_DONE: i32 = 1;

    /// `sizeof(tdefl_compressor)` in ESP32 mask ROM is 167,744 bytes; round up to 165 KiB.
    const ROM_TDEFL_COMPRESSOR_BYTES: usize = 168_960;

    /// `sizeof(tinfl_decompressor)` in ESP32 mask ROM is ~10,952 bytes; 3,072 u32s = 12 KiB.
    const ROM_TINFL_STATE_WORDS: usize = 3_072;

    extern "C" {
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

    pub struct GzipBackend {
        tinfl_state: Box<[u32; ROM_TINFL_STATE_WORDS]>,
    }

    impl GzipBackend {
        pub fn new() -> Self {
            Self {
                tinfl_state: vec![0u32; ROM_TINFL_STATE_WORDS]
                    .into_boxed_slice()
                    .try_into()
                    .expect("tinfl state length"),
            }
        }

        pub fn inflate(&mut self, deflate: &[u8], out: &mut [u8]) -> Result<usize, String> {
            // `tinfl_init(r)` in rom/miniz.h resets `r->m_state = 0` (word 0).
            self.tinfl_state[0] = 0;
            let mut in_size = deflate.len();
            let mut out_size = out.len();
            let status = unsafe {
                tinfl_decompress(
                    self.tinfl_state.as_mut_ptr().cast::<c_void>(),
                    deflate.as_ptr(),
                    &mut in_size,
                    out.as_mut_ptr(),
                    out.as_mut_ptr(),
                    &mut out_size,
                    TINFL_FLAG_USING_NON_WRAPPING_OUTPUT_BUF,
                )
            };
            if status == TINFL_STATUS_DONE {
                Ok(out_size)
            } else {
                Err(format!("rom tinfl_decompress failed: status={status}"))
            }
        }

        pub fn crc32(&self, data: &[u8]) -> u32 {
            // SAFETY: `mz_crc32` in ESP32 ROM reads `data.len()` bytes from `data.as_ptr()`.
            unsafe { mz_crc32(0, data.as_ptr(), data.len()) }
        }

        pub fn try_deflate(&self, raw: &[u8]) -> DeflateAttempt {
            let (free_heap, largest_block) = unsafe {
                (
                    esp_get_free_heap_size() as usize,
                    heap_caps_get_largest_free_block(MALLOC_CAP_8BIT),
                )
            };
            let needed_bytes = ROM_TDEFL_COMPRESSOR_BYTES + raw.len() + 256;
            if largest_block < ROM_TDEFL_COMPRESSOR_BYTES + 4096 || free_heap < needed_bytes {
                return DeflateAttempt::Oom {
                    needed_bytes: ROM_TDEFL_COMPRESSOR_BYTES,
                    free_heap,
                    largest_block,
                };
            }
            let comp_ptr = unsafe { heap_caps_malloc(ROM_TDEFL_COMPRESSOR_BYTES, MALLOC_CAP_8BIT) };
            if comp_ptr.is_null() {
                return DeflateAttempt::Oom {
                    needed_bytes: ROM_TDEFL_COMPRESSOR_BYTES,
                    free_heap,
                    largest_block,
                };
            }

            let mut out_buf = vec![0u8; raw.len() + 256];
            let start = now_us();
            let init_status = unsafe {
                tdefl_init(
                    comp_ptr,
                    core::ptr::null(),
                    core::ptr::null_mut(),
                    TDEFL_DEFAULT_MAX_PROBES,
                )
            };
            let result = if init_status != TDEFL_STATUS_OKAY {
                DeflateAttempt::Err(format!("rom tdefl_init failed: status={init_status}"))
            } else {
                let mut in_size = raw.len();
                let mut out_size = out_buf.len();
                let status = unsafe {
                    tdefl_compress(
                        comp_ptr,
                        raw.as_ptr().cast::<c_void>(),
                        &mut in_size,
                        out_buf.as_mut_ptr().cast::<c_void>(),
                        &mut out_size,
                        TDEFL_FINISH,
                    )
                };
                let elapsed_us = u32::try_from(now_us().saturating_sub(start)).unwrap_or(u32::MAX);
                if status == TDEFL_STATUS_DONE {
                    DeflateAttempt::Ok {
                        compressed_len: out_size,
                        deflate_us: elapsed_us,
                    }
                } else {
                    DeflateAttempt::Err(format!("rom tdefl_compress failed: status={status}"))
                }
            };
            unsafe {
                heap_caps_free(comp_ptr);
            }
            result
        }
    }
}

#[cfg(not(target_arch = "xtensa"))]
mod backend {
    use esp_idf_svc::sys::{
        esp_get_free_heap_size, heap_caps_get_largest_free_block, MALLOC_CAP_8BIT,
    };

    use crate::gzip_bench::inflate_miniz_oxide;
    use crate::profiler::now_us;
    use crate::protocol::crc32;

    use super::DeflateAttempt;

    pub const IMPL_NAME: &str = "miniz_oxide";

    /// `miniz_oxide::deflate::core::CompressorOxide` allocates ~308 KiB across
    /// HashBuffers (160 KiB contiguous), LZOxide (64 KiB), and LocalBuf (83 KiB).
    const MINIZ_OXIDE_DEFLATE_MIN_HEAP: usize = 340 * 1024;
    const MINIZ_OXIDE_DEFLATE_MIN_LARGEST_BLOCK: usize = 170 * 1024;

    pub struct GzipBackend {
        decomp: Box<miniz_oxide::inflate::core::DecompressorOxide>,
    }

    impl GzipBackend {
        pub fn new() -> Self {
            Self {
                decomp: Box::new(miniz_oxide::inflate::core::DecompressorOxide::new()),
            }
        }

        pub fn inflate(&mut self, deflate: &[u8], out: &mut [u8]) -> Result<usize, String> {
            inflate_miniz_oxide(&mut self.decomp, deflate, out)
        }

        pub fn crc32(&self, data: &[u8]) -> u32 {
            crc32(data)
        }

        pub fn try_deflate(&self, raw: &[u8]) -> DeflateAttempt {
            let (free_heap, largest_block) = unsafe {
                (
                    esp_get_free_heap_size() as usize,
                    heap_caps_get_largest_free_block(MALLOC_CAP_8BIT),
                )
            };
            if free_heap < MINIZ_OXIDE_DEFLATE_MIN_HEAP
                || largest_block < MINIZ_OXIDE_DEFLATE_MIN_LARGEST_BLOCK
            {
                return DeflateAttempt::Oom {
                    needed_bytes: MINIZ_OXIDE_DEFLATE_MIN_HEAP,
                    free_heap,
                    largest_block,
                };
            }
            let start = now_us();
            let compressed = miniz_oxide::deflate::compress_to_vec(raw, 6);
            let elapsed_us = u32::try_from(now_us().saturating_sub(start)).unwrap_or(u32::MAX);
            DeflateAttempt::Ok {
                compressed_len: compressed.len(),
                deflate_us: elapsed_us,
            }
        }
    }
}

/// RFC 1952 gzip / DEFLATE benchmark app with full OTel metrics, traces, and PC profiling.
pub struct GzipBenchApp {
    backend: backend::GzipBackend,
    out_buf: Vec<u8>,
}

impl<B: Board> App<B> for GzipBenchApp {
    const APP_NAME: &'static str = "gzip-bench";
    const FIRMWARE_ID: &'static str = GZIP_BENCH_FIRMWARE_ID;

    fn commands() -> Vec<AppCommandSpec> {
        vec![AppCommandSpec {
            id: "run".to_string(),
            label: "Run Benchmark".to_string(),
            default_count: 10,
        }]
    }

    fn init(_board: &mut B) -> Result<Self> {
        Ok(Self {
            backend: backend::GzipBackend::new(),
            out_buf: vec![0u8; MAX_CORPUS_RAW_LEN],
        })
    }

    fn self_test(&mut self, _board: &mut B) -> Result<()> {
        // Verify the first corpus inflates and passes CRC32 before marking OTA slot valid.
        let corpus = &CORPORA[0];
        let frame = parse_gzip_frame(corpus.gz_bytes).map_err(anyhow::Error::msg)?;
        let written = self
            .backend
            .inflate(frame.deflate_payload, &mut self.out_buf)
            .map_err(anyhow::Error::msg)?;
        if written != corpus.raw_len {
            anyhow::bail!(
                "gzip-bench self_test length mismatch: got {written}, want {}",
                corpus.raw_len
            );
        }
        let got_crc = self.backend.crc32(&self.out_buf[..written]);
        if got_crc != corpus.expected_crc32 {
            anyhow::bail!(
                "gzip-bench self_test crc32 mismatch: got {got_crc:#010x}, want {:#010x}",
                corpus.expected_crc32
            );
        }
        Ok(())
    }

    fn step(&mut self, board: &mut B, ctx: &mut StepContext<'_>) -> Result<StepOutput> {
        // Lightweight idle heartbeat: advertise availability and the declarative "run"
        // command without hammering the CPU 24/7 or mixing BLE noise into benchmark data.
        let impl_name = backend::IMPL_NAME;
        ctx.record_attr("gzip.impl", impl_name);
        ctx.record_attr("gzip.state", "idle");

        let (battery_mv, _free_heap, largest_block, sensor_us) = self.probe_heap(board, ctx);
        info!("gzip-bench({impl_name}): idle heartbeat (largest_block={largest_block}B)");

        Ok(StepOutput {
            sensor_us,
            compute_us: 0,
            epd_refresh_us: 0,
            battery_mv,
            flags: 0,
            post_burst_delay_ms: 0,
        })
    }

    fn run_command(
        &mut self,
        cmd_id: &str,
        _run_index: u16,
        _total_runs: u16,
        board: &mut B,
        ctx: &mut StepContext<'_>,
    ) -> Result<StepOutput> {
        match cmd_id {
            "run" => {
                ctx.record_attr("gzip.state", "run");
                self.run_benchmark(board, ctx)
            }
            other => anyhow::bail!("unknown gzip-bench command: {other}"),
        }
    }
}

impl GzipBenchApp {
    fn probe_heap<B: Board>(
        &self,
        board: &mut B,
        ctx: &mut StepContext<'_>,
    ) -> (u16, usize, usize, u32) {
        let impl_name = backend::IMPL_NAME;
        let sensor_start = now_us();
        let battery_mv = board.read_battery_mv();
        let free_heap = unsafe { esp_get_free_heap_size() } as usize;
        let largest_block = unsafe { heap_caps_get_largest_free_block(MALLOC_CAP_8BIT) };
        let sensor_end = now_us();
        let sensor_us = u32::try_from(sensor_end.saturating_sub(sensor_start)).unwrap_or(u32::MAX);
        let free_heap_s = free_heap.to_string();
        let largest_block_s = largest_block.to_string();
        ctx.record_span_with_attrs(
            "gzip.heap_probe",
            "sensor",
            sensor_start,
            sensor_end,
            &[
                ("impl", impl_name),
                ("free_heap", &free_heap_s),
                ("largest_block", &largest_block_s),
            ],
        );
        ctx.record_metric(
            "gzip.heap_largest_block_bytes",
            largest_block as i64,
            "By",
            &[("impl", impl_name)],
        );
        (battery_mv, free_heap, largest_block, sensor_us)
    }

    fn run_benchmark<B: Board>(
        &mut self,
        board: &mut B,
        ctx: &mut StepContext<'_>,
    ) -> Result<StepOutput> {
        let impl_name = backend::IMPL_NAME;
        ctx.record_attr("gzip.impl", impl_name);
        ctx.record_attr("gzip.corpora", &CORPORA.len().to_string());
        ctx.record_attr("gzip.iterations", &BENCH_ITERATIONS.to_string());

        // Phase 1 ("sensor"): probe battery rail and heap fragmentation before work.
        let (battery_mv, _free_heap, largest_block, sensor_us) = self.probe_heap(board, ctx);

        // Phase 2 ("compute"): benchmark gunzip/inflate + CRC32 across all corpora,
        // then run heap-guarded deflate attempt.
        let compute_start = now_us();
        let mut total_bytes_in: usize = 0;
        let mut total_bytes_out: usize = 0;
        let mut total_inflate_us: u64 = 0;
        let mut verified_corpora: i64 = 0;

        for corpus in CORPORA {
            let frame = parse_gzip_frame(corpus.gz_bytes).map_err(anyhow::Error::msg)?;

            let inf_start = now_us();
            let mut last_written = 0usize;
            for _ in 0..BENCH_ITERATIONS {
                last_written = self
                    .backend
                    .inflate(frame.deflate_payload, &mut self.out_buf)
                    .map_err(anyhow::Error::msg)?;
            }
            let inf_end = now_us();
            let inf_us = u32::try_from(inf_end.saturating_sub(inf_start)).unwrap_or(u32::MAX);

            let bytes_in_total = corpus.gz_bytes.len() * BENCH_ITERATIONS;
            let bytes_out_total = last_written * BENCH_ITERATIONS;
            total_bytes_in += bytes_in_total;
            total_bytes_out += bytes_out_total;
            total_inflate_us += u64::from(inf_us);

            let bps = throughput_bps(bytes_out_total, inf_us);
            let ratio = ratio_milli(corpus.raw_len, corpus.gz_bytes.len());

            let gz_s = corpus.gz_bytes.len().to_string();
            let raw_s = last_written.to_string();
            let bps_s = bps.to_string();
            let ratio_s = ratio.to_string();
            let span_name = format!("gzip.inflate.{}", corpus.name);
            ctx.record_span_with_attrs(
                &span_name,
                "compute",
                inf_start,
                inf_end,
                &[
                    ("impl", impl_name),
                    ("corpus", corpus.name),
                    ("gz_bytes", &gz_s),
                    ("raw_bytes", &raw_s),
                    ("bps", &bps_s),
                    ("ratio_milli", &ratio_s),
                ],
            );

            // Verify CRC32 + ISIZE on the inflated output.
            let crc_start = now_us();
            let got_crc = self.backend.crc32(&self.out_buf[..last_written]);
            let crc_end = now_us();
            let crc_us = u32::try_from(crc_end.saturating_sub(crc_start)).unwrap_or(u32::MAX);
            let ok = last_written == corpus.raw_len
                && got_crc == frame.expected_crc32
                && (last_written as u32) == frame.expected_isize;
            if ok {
                verified_corpora += 1;
            } else {
                warn!(
                    "gzip-bench({}) corpus={} verification FAILED: len={}/{} crc={:#010x}/{:#010x}",
                    impl_name,
                    corpus.name,
                    last_written,
                    corpus.raw_len,
                    got_crc,
                    frame.expected_crc32
                );
            }

            let crc_span_name = format!("gzip.crc32.{}", corpus.name);
            ctx.record_span_with_attrs(
                &crc_span_name,
                "compute",
                crc_start,
                crc_end,
                &[
                    ("impl", impl_name),
                    ("corpus", corpus.name),
                    ("verified", if ok { "true" } else { "false" }),
                ],
            );

            ctx.record_metric(
                "gzip.inflate_us",
                i64::from(inf_us),
                "us",
                &[("corpus", corpus.name), ("impl", impl_name)],
            );
            ctx.record_metric(
                "gzip.inflate_bps",
                bps,
                "By/s",
                &[("corpus", corpus.name), ("impl", impl_name)],
            );
            ctx.record_metric(
                "gzip.crc_us",
                i64::from(crc_us),
                "us",
                &[("corpus", corpus.name), ("impl", impl_name)],
            );

            // Heap-guarded deflate attempt while `self.out_buf` holds the verified `json_otel` corpus.
            if corpus.name == "json_otel" {
                let def_start = now_us();
                let def_attempt = self.backend.try_deflate(&self.out_buf[..last_written]);
                let def_end = now_us();
                match def_attempt {
                    DeflateAttempt::Ok {
                        compressed_len,
                        deflate_us,
                    } => {
                        let def_bps = throughput_bps(last_written, deflate_us);
                        let raw_s = last_written.to_string();
                        let gz_s = compressed_len.to_string();
                        let bps_s = def_bps.to_string();
                        ctx.record_attr("gzip.deflate_status", "ok");
                        ctx.record_span_with_attrs(
                            "gzip.deflate.json_otel",
                            "compute",
                            def_start,
                            def_end,
                            &[
                                ("impl", impl_name),
                                ("raw_bytes", &raw_s),
                                ("gz_bytes", &gz_s),
                                ("bps", &bps_s),
                                ("status", "ok"),
                            ],
                        );
                        ctx.record_metric("gzip.deflate_oom", 0, "1", &[("impl", impl_name)]);
                        ctx.record_metric(
                            "gzip.deflate_bps",
                            def_bps,
                            "By/s",
                            &[("impl", impl_name)],
                        );
                    }
                    DeflateAttempt::Oom {
                        needed_bytes,
                        free_heap: cur_free,
                        largest_block: cur_largest,
                    } => {
                        let needed_s = needed_bytes.to_string();
                        let free_s = cur_free.to_string();
                        let largest_s = cur_largest.to_string();
                        ctx.record_attr("gzip.deflate_status", "oom");
                        ctx.record_attr("gzip.deflate_needed_bytes", &needed_s);
                        ctx.record_span_with_attrs(
                            "gzip.deflate.oom",
                            "compute",
                            def_start,
                            def_end,
                            &[
                                ("impl", impl_name),
                                ("needed_bytes", &needed_s),
                                ("free_heap", &free_s),
                                ("largest_block", &largest_s),
                                ("status", "oom"),
                            ],
                        );
                        ctx.record_metric("gzip.deflate_oom", 1, "1", &[("impl", impl_name)]);
                        ctx.record_metric("gzip.deflate_bps", 0, "By/s", &[("impl", impl_name)]);
                    }
                    DeflateAttempt::Err(msg) => {
                        warn!("gzip-bench({impl_name}) deflate error: {msg}");
                        ctx.record_attr("gzip.deflate_status", "error");
                        ctx.record_span_with_attrs(
                            "gzip.deflate.error",
                            "compute",
                            def_start,
                            def_end,
                            &[("impl", impl_name), ("status", "error"), ("error", &msg)],
                        );
                        ctx.record_metric("gzip.deflate_oom", 0, "1", &[("impl", impl_name)]);
                        ctx.record_metric("gzip.deflate_bps", 0, "By/s", &[("impl", impl_name)]);
                    }
                }
            }
            ctx.feed_watchdog();
        }

        let compute_us = u32::try_from(now_us().saturating_sub(compute_start)).unwrap_or(u32::MAX);
        let total_bps = throughput_bps(
            total_bytes_out,
            u32::try_from(total_inflate_us).unwrap_or(u32::MAX),
        );
        let all_ok = verified_corpora as usize == CORPORA.len();
        ctx.record_attr("gzip.verified", if all_ok { "true" } else { "false" });
        ctx.record_attr("gzip.total_bytes_out", &total_bytes_out.to_string());

        ctx.record_metric(
            "gzip.total_inflate_bps",
            total_bps,
            "By/s",
            &[("impl", impl_name)],
        );
        ctx.record_metric(
            "gzip.total_bytes_out",
            total_bytes_out as i64,
            "By",
            &[("impl", impl_name)],
        );
        ctx.record_metric(
            "gzip.total_bytes_in",
            total_bytes_in as i64,
            "By",
            &[("impl", impl_name)],
        );
        ctx.record_metric(
            "gzip.verified_corpora",
            verified_corpora,
            "1",
            &[("impl", impl_name)],
        );

        info!(
            "gzip-bench({impl_name}): verified={verified_corpora}/{} out={total_bytes_out}B in={total_bytes_in}B inflate_bps={total_bps} compute_us={compute_us} largest_block={largest_block}B",
            CORPORA.len()
        );

        Ok(StepOutput {
            sensor_us,
            compute_us,
            epd_refresh_us: 0,
            battery_mv,
            flags: 0,
            post_burst_delay_ms: 0,
        })
    }
}
