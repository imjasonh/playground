//! `RecorderApp` — continuous 1-minute audio+video `.mov` clip recorder to microSD
//! with on-device audio DSP, vision motion/color detection, SD-card custom `MCUM`
//! model hook, ring-buffer oldest-file eviction, and an HTTP range-streaming server
//! for the Seeed Studio XIAO ESP32-S3 Sense.

use std::fs::{self, File};
use std::io::{BufWriter, Read, Seek, SeekFrom};
use std::path::PathBuf;
use std::sync::atomic::{AtomicBool, Ordering};
use std::sync::{Arc, Mutex};
use std::thread;
use std::time::{Duration, Instant};

use anyhow::Result;
use esp_idf_svc::http::server::{Configuration as HttpConfig, EspHttpServer};
use esp_idf_svc::http::Method;
use esp_idf_svc::io::Write as EspWrite;
use log::{info, warn};

use crate::boards::xiao_esp32s3_sense::{
    decode_jpeg_to_rgb_grid, sd_space_info, SenseCamera, SenseMic, SenseSdCard, SenseWifi,
    SenseWifiInfo, CLIPS_DIR, MODELS_DIR,
};
use crate::boards::{Board, HasSenseAV};
use crate::platform::{App, RunMode, StepContext, StepOutput};
use crate::protocol::AppCommandSpec;
use crate::sense_clip::{
    clip_meta_name_for, extract_query_param, format_clip_meta_name, format_clip_name,
    format_clips_filtered_json, format_status_json, format_tags_summary_json,
    format_temp_clip_name, is_temp_clip_name, is_valid_clip_name, next_clip_seq, parse_byte_range,
    parse_clip_seq, plan_evictions, required_free_bytes, ClipEntry, MovMuxer, RecorderStatus,
    CLIP_DURATION_SECS, DEFAULT_AUDIO_SAMPLE_RATE, DEFAULT_VIDEO_HEIGHT, DEFAULT_VIDEO_WIDTH,
    RECORDER_FIRMWARE_ID,
};
use crate::sense_detect::{
    format_clip_sidecar_json, parse_clip_sidecar_json, AudioDetector, AudioFeatures, SdLinearModel,
    TagAccumulator, TagSource, VisionDetector, VisionFeatures,
};

/// Target frame interval during recording (~10 fps -> ~600 frames per 1-minute clip).
const TARGET_FRAME_INTERVAL: Duration = Duration::from_millis(100);
/// HTTP file streaming buffer size (16 KiB).
const HTTP_STREAM_CHUNK_BYTES: usize = 16 * 1024;
/// PDM audio read buffer per frame (~3200 bytes = 100 ms at 16 kHz 16-bit mono).
const AUDIO_READ_BUF_BYTES: usize = 4096;
/// Downsampled RGB888 grid dimensions for on-device vision motion/color analysis (~1 Hz).
const VISION_GRID_W: usize = 32;
const VISION_GRID_H: usize = 24;
/// Run full JPEG->RGB vision analysis every Nth frame (~1 Hz at 10 fps).
const VISION_SAMPLE_STRIDE: usize = 10;

struct SharedState {
    wifi_info: SenseWifiInfo,
    sd_mounted: bool,
    sd_total_bytes: u64,
    sd_free_bytes: u64,
    camera_ready: bool,
    mic_ready: bool,
    active_clip: Option<String>,
    active_tags: Vec<String>,
    models: Vec<String>,
    clips: Vec<ClipEntry>,
}

struct RecorderShared {
    recording: AtomicBool,
    rotate_requested: AtomicBool,
    state: Mutex<SharedState>,
}

impl RecorderShared {
    fn status_snapshot(&self) -> RecorderStatus {
        let recording = self.recording.load(Ordering::Relaxed);
        let st = self.state.lock().unwrap_or_else(|e| e.into_inner());
        RecorderStatus {
            recording,
            clip_duration_s: CLIP_DURATION_SECS,
            clip_count: st.clips.len(),
            active_clip: st.active_clip.clone(),
            sd_mounted: st.sd_mounted,
            sd_total_bytes: st.sd_total_bytes,
            sd_free_bytes: st.sd_free_bytes,
            wifi_mode: st.wifi_info.mode.clone(),
            ssid: st.wifi_info.ssid.clone(),
            ip: st.wifi_info.ip.clone(),
            camera_ready: st.camera_ready,
            mic_ready: st.mic_ready,
            models: st.models.clone(),
            active_tags: st.active_tags.clone(),
        }
    }
}

/// 1-minute A/V clip recorder + on-device tagger + HTTP clip server for XIAO ESP32-S3 Sense.
pub struct RecorderApp {
    _wifi: SenseWifi,
    _sd: Option<SenseSdCard>,
    _http: EspHttpServer<'static>,
    shared: Arc<RecorderShared>,
}

impl<B: Board + HasSenseAV> App<B> for RecorderApp {
    const APP_NAME: &'static str = "recorder";
    const FIRMWARE_ID: &'static str = RECORDER_FIRMWARE_ID;

    fn run_mode() -> RunMode {
        RunMode::Continuous {
            burst_ms: 500,
            min_step_ms: 5_500,
        }
    }

    fn commands() -> Vec<AppCommandSpec> {
        vec![
            AppCommandSpec {
                id: "toggle_record".to_string(),
                label: "Toggle Recording".to_string(),
                default_count: 1,
            },
            AppCommandSpec {
                id: "rotate_clip".to_string(),
                label: "Finalize Clip Now".to_string(),
                default_count: 1,
            },
        ]
    }

    fn init(board: &mut B) -> Result<Self> {
        let hw = board.take_sense_hardware()?;
        let wifi = SenseWifi::start(hw.modem)?;
        let wifi_info = wifi.info.clone();

        let sd = match SenseSdCard::mount(hw.spi2, hw.sd_sck, hw.sd_miso, hw.sd_mosi, hw.sd_cs) {
            Ok(card) => Some(card),
            Err(err) => {
                warn!("recorder: microSD mount failed (insert FAT32 card): {err:#}");
                None
            }
        };

        let sd_mounted = sd.is_some();
        let (sd_total_bytes, sd_free_bytes, initial_clips, sd_models) = if let Some(ref card) = sd {
            cleanup_temp_clips();
            let clips = scan_clips();
            let models = load_sd_models();
            let (total, free) = card.space_info().unwrap_or((0, 0));
            (total, free, clips, models)
        } else {
            (0, 0, Vec::new(), Vec::new())
        };
        let model_names: Vec<String> = sd_models.iter().map(|m| m.label.clone()).collect();

        let camera = match SenseCamera::init() {
            Ok(cam) => Some(cam),
            Err(err) => {
                warn!("recorder: camera init failed: {err:#}");
                None
            }
        };

        let mic = match SenseMic::init(hw.i2s0, hw.mic_clk, hw.mic_data) {
            Ok(m) => Some(m),
            Err(err) => {
                warn!("recorder: PDM mic init failed: {err:#}");
                None
            }
        };

        let can_record = sd_mounted && (camera.is_some() || mic.is_some());
        let shared = Arc::new(RecorderShared {
            recording: AtomicBool::new(can_record),
            rotate_requested: AtomicBool::new(false),
            state: Mutex::new(SharedState {
                wifi_info: wifi_info.clone(),
                sd_mounted,
                sd_total_bytes,
                sd_free_bytes,
                camera_ready: camera.is_some(),
                mic_ready: mic.is_some(),
                active_clip: None,
                active_tags: Vec::new(),
                models: model_names,
                clips: initial_clips,
            }),
        });

        let http = start_http_server(Arc::clone(&shared))?;
        info!(
            "recorder: HTTP server listening on http://{} (ssid={}, sd_mounted={}, cam={}, mic={}, models={})",
            wifi_info.ip,
            wifi_info.ssid,
            sd_mounted,
            camera.is_some(),
            mic.is_some(),
            sd_models.len()
        );

        if sd_mounted {
            let worker_shared = Arc::clone(&shared);
            thread::Builder::new()
                .name("sense-rec".to_string())
                .stack_size(16 * 1024)
                .spawn(move || recorder_worker(worker_shared, camera, mic, sd_models))?;
        } else {
            warn!("recorder: no microSD mounted; recorder worker not started");
        }

        Ok(Self {
            _wifi: wifi,
            _sd: sd,
            _http: http,
            shared,
        })
    }

    fn step(&mut self, _board: &mut B, ctx: &mut StepContext<'_>) -> Result<StepOutput> {
        let st = self.shared.status_snapshot();
        ctx.record_attr("sense.http_url", &format!("http://{}", st.ip));
        ctx.record_attr("sense.wifi_ssid", &st.ssid);
        ctx.record_attr("sense.wifi_mode", &st.wifi_mode);
        ctx.record_attr(
            "sense.recording",
            if st.recording { "true" } else { "false" },
        );
        ctx.record_attr(
            "sense.sd_mounted",
            if st.sd_mounted { "true" } else { "false" },
        );
        ctx.record_attr("sense.clips", &st.clip_count.to_string());
        ctx.record_attr("sense.models", &st.models.len().to_string());
        if let Some(last_tag) = st.active_tags.first() {
            ctx.record_attr("sense.last_tag", last_tag);
        }
        let free_mb = st.sd_free_bytes / (1024 * 1024);
        ctx.record_attr("sense.sd_free_mb", &free_mb.to_string());
        ctx.record_metric("sense.clips", st.clip_count as i64, "1", &[]);
        ctx.record_metric("sense.sd_free_mb", free_mb as i64, "MiB", &[]);

        Ok(StepOutput {
            sensor_us: 0,
            compute_us: 0,
            epd_refresh_us: 0,
            battery_mv: 0,
            flags: 0,
            post_burst_delay_ms: 0,
        })
    }

    fn run_command(
        &mut self,
        cmd_id: &str,
        _run_index: u16,
        _total_runs: u16,
        _board: &mut B,
        ctx: &mut StepContext<'_>,
    ) -> Result<StepOutput> {
        match cmd_id {
            "toggle_record" => {
                let can_record = {
                    let st = self.shared.state.lock().unwrap_or_else(|e| e.into_inner());
                    st.sd_mounted && (st.camera_ready || st.mic_ready)
                };
                let next = if self.shared.recording.load(Ordering::Acquire) {
                    self.shared.recording.store(false, Ordering::Release);
                    false
                } else if can_record {
                    self.shared.recording.store(true, Ordering::Release);
                    true
                } else {
                    false
                };
                info!("recorder: BLE toggle_record -> recording={next}");
                ctx.record_attr("sense.recording", if next { "true" } else { "false" });
            }
            "rotate_clip" => {
                self.shared.rotate_requested.store(true, Ordering::Release);
                info!("recorder: BLE rotate_clip requested");
            }
            other => anyhow::bail!("unknown recorder command: {other}"),
        }
        Ok(StepOutput::default())
    }
}

fn load_sd_models() -> Vec<SdLinearModel> {
    let _ = fs::create_dir_all(MODELS_DIR);
    let Ok(entries) = fs::read_dir(MODELS_DIR) else {
        return Vec::new();
    };
    let mut models = Vec::new();
    for entry in entries.flatten() {
        let path = entry.path();
        let Some(ext) = path.extension().and_then(|s| s.to_str()) else {
            continue;
        };
        if !ext.eq_ignore_ascii_case("mcum") {
            continue;
        }
        match fs::read(&path) {
            Ok(bytes) => match SdLinearModel::parse(&bytes) {
                Ok(model) => {
                    info!(
                        "recorder: loaded SD model '{}' ({:?}, threshold={}%)",
                        model.label, model.modality, model.threshold_pct
                    );
                    models.push(model);
                }
                Err(err) => warn!("recorder: ignoring invalid model {:?}: {err}", path),
            },
            Err(err) => warn!("recorder: failed reading model {:?}: {err}", path),
        }
    }
    models
}

fn cleanup_temp_clips() {
    let Ok(entries) = fs::read_dir(CLIPS_DIR) else {
        return;
    };
    for entry in entries.flatten() {
        let name = entry.file_name();
        let Some(name_str) = name.to_str() else {
            continue;
        };
        if is_temp_clip_name(name_str) {
            let path = entry.path();
            warn!("recorder: removing incomplete temp clip {name_str}");
            let _ = fs::remove_file(path);
        }
    }
}

fn remove_clip_and_sidecar(clip_name: &str) -> std::io::Result<()> {
    let clip_path = PathBuf::from(CLIPS_DIR).join(clip_name);
    fs::remove_file(&clip_path)?;
    if let Some(meta_name) = clip_meta_name_for(clip_name) {
        let meta_path = PathBuf::from(CLIPS_DIR).join(meta_name);
        let _ = fs::remove_file(meta_path);
    }
    Ok(())
}

fn scan_clips() -> Vec<ClipEntry> {
    let Ok(entries) = fs::read_dir(CLIPS_DIR) else {
        return Vec::new();
    };
    let mut clips = Vec::new();
    for entry in entries.flatten() {
        let name = entry.file_name();
        let Some(name_str) = name.to_str() else {
            continue;
        };
        let Some(seq) = parse_clip_seq(name_str) else {
            continue;
        };
        let size_bytes = entry.metadata().map(|m| m.len()).unwrap_or(0);
        let meta_path = PathBuf::from(CLIPS_DIR).join(format_clip_meta_name(seq));
        let tags = fs::read_to_string(&meta_path)
            .map(|s| parse_clip_sidecar_json(&s))
            .unwrap_or_default();
        clips.push(ClipEntry {
            name: name_str.to_string(),
            seq,
            size_bytes,
            duration_s: CLIP_DURATION_SECS,
            tags,
        });
    }
    clips.sort_by_key(|c| c.seq);
    clips
}

fn evict_oldest_clips_if_needed(shared: &RecorderShared) {
    let Ok((total, free)) = sd_space_info() else {
        return;
    };
    let required = required_free_bytes(total);
    let clips = scan_clips();
    let victims = plan_evictions(&clips, free, required);
    for name in victims {
        match remove_clip_and_sidecar(&name) {
            Ok(()) => info!("recorder: evicted oldest clip {name} to free SD space"),
            Err(err) => warn!("recorder: failed to evict {name}: {err}"),
        }
    }
    let updated_clips = scan_clips();
    let (new_total, new_free) = sd_space_info().unwrap_or((total, free));
    let mut st = shared.state.lock().unwrap_or_else(|e| e.into_inner());
    st.sd_total_bytes = new_total;
    st.sd_free_bytes = new_free;
    st.clips = updated_clips;
}

fn recorder_worker(
    shared: Arc<RecorderShared>,
    mut camera: Option<SenseCamera>,
    mut mic: Option<SenseMic>,
    sd_models: Vec<SdLinearModel>,
) {
    let mut audio_buf = vec![0u8; AUDIO_READ_BUF_BYTES];
    let mut scratch_rgb = Vec::<u8>::new();
    let mut vision_grid = [0u8; VISION_GRID_W * VISION_GRID_H * 3];
    let mut audio_detector = AudioDetector::new(DEFAULT_AUDIO_SAMPLE_RATE);
    let mut vision_detector = VisionDetector::new();

    loop {
        if !shared.recording.load(Ordering::Acquire) {
            thread::sleep(Duration::from_millis(250));
            continue;
        }

        evict_oldest_clips_if_needed(&shared);

        let seq = {
            let st = shared.state.lock().unwrap_or_else(|e| e.into_inner());
            let names: Vec<String> = st.clips.iter().map(|c| c.name.clone()).collect();
            next_clip_seq(&names)
        };
        let tmp_name = format_temp_clip_name(seq);
        let final_name = format_clip_name(seq);
        let meta_name = format_clip_meta_name(seq);
        let tmp_path = PathBuf::from(CLIPS_DIR).join(&tmp_name);
        let final_path = PathBuf::from(CLIPS_DIR).join(&final_name);
        let meta_path = PathBuf::from(CLIPS_DIR).join(&meta_name);

        {
            let mut st = shared.state.lock().unwrap_or_else(|e| e.into_inner());
            st.active_clip = Some(tmp_name.clone());
            st.active_tags.clear();
        }

        let file = match File::create(&tmp_path) {
            Ok(f) => f,
            Err(err) => {
                warn!("recorder-worker: failed to create {tmp_name}: {err}");
                thread::sleep(Duration::from_secs(2));
                continue;
            }
        };

        let writer = BufWriter::with_capacity(16 * 1024, file);
        let mut muxer = match MovMuxer::begin(
            writer,
            DEFAULT_VIDEO_WIDTH,
            DEFAULT_VIDEO_HEIGHT,
            if mic.is_some() {
                DEFAULT_AUDIO_SAMPLE_RATE
            } else {
                0
            },
        ) {
            Ok(m) => m,
            Err(err) => {
                warn!("recorder-worker: mov begin failed: {err}");
                let _ = fs::remove_file(&tmp_path);
                thread::sleep(Duration::from_secs(1));
                continue;
            }
        };

        info!("recorder-worker: recording {final_name} ({CLIP_DURATION_SECS}s target)");
        vision_detector.reset();
        let mut tag_acc = TagAccumulator::new();
        let mut latest_audio_feats = AudioFeatures::default();
        let mut latest_vision_feats = VisionFeatures::default();
        let clip_start = Instant::now();
        let target_duration = Duration::from_secs(u64::from(CLIP_DURATION_SECS));
        let mut last_frame_at = clip_start;
        let mut frame_index = 0usize;
        let mut write_failed = false;

        while clip_start.elapsed() < target_duration {
            if !shared.recording.load(Ordering::Acquire)
                || shared.rotate_requested.swap(false, Ordering::AcqRel)
            {
                break;
            }

            let loop_start = Instant::now();
            let elapsed_s = clip_start.elapsed().as_secs() as u32;
            let mut tags_updated = false;

            if let Some(ref mut cam) = camera {
                if let Some(frame) = cam.capture() {
                    if muxer.video_frame_count() == 0 {
                        muxer.set_dimensions(frame.width(), frame.height());
                    }
                    let bytes = frame.bytes();
                    let now = Instant::now();
                    let delta_ms = now
                        .saturating_duration_since(last_frame_at)
                        .as_millis()
                        .clamp(1, u128::from(u32::MAX)) as u32;
                    last_frame_at = now;
                    if let Err(err) = muxer.write_video_frame(bytes, delta_ms) {
                        warn!("recorder-worker: video write failed: {err}");
                        write_failed = true;
                        break;
                    }

                    // Run on-device vision detection (~1 Hz RGB grid + every-frame JPEG delta).
                    if frame_index % VISION_SAMPLE_STRIDE == 0 {
                        if decode_jpeg_to_rgb_grid(
                            bytes,
                            usize::from(frame.width()),
                            usize::from(frame.height()),
                            &mut scratch_rgb,
                            VISION_GRID_W,
                            VISION_GRID_H,
                            &mut vision_grid,
                        ) {
                            let (vhits, vfeats) = vision_detector.analyze_rgb888(
                                &vision_grid,
                                VISION_GRID_W,
                                VISION_GRID_H,
                            );
                            latest_vision_feats = vfeats;
                            for (label, conf) in vhits {
                                tag_acc.record(label, TagSource::Vision, conf, elapsed_s);
                                tags_updated = true;
                            }
                        } else if let Some((label, conf)) =
                            vision_detector.analyze_jpeg_size(bytes.len())
                        {
                            tag_acc.record(label, TagSource::Vision, conf, elapsed_s);
                            tags_updated = true;
                        }
                    }
                }
            }

            if let Some(ref mut m) = mic {
                let n = m.read_pcm(&mut audio_buf, 20);
                if n >= 2 {
                    let pcm = &audio_buf[..n];
                    if let Err(err) = muxer.write_audio_pcm(pcm) {
                        warn!("recorder-worker: audio write failed: {err}");
                        write_failed = true;
                        break;
                    }
                    let (ahits, afeats) = audio_detector.analyze_pcm_le16(pcm);
                    latest_audio_feats = afeats;
                    for (label, conf) in ahits {
                        tag_acc.record(label, TagSource::Audio, conf, elapsed_s);
                        tags_updated = true;
                    }
                }
            }

            // Evaluate any user-supplied SD-card `.mcum` models on the latest audio+vision features.
            if !sd_models.is_empty() && frame_index % VISION_SAMPLE_STRIDE == 0 {
                for model in &sd_models {
                    if let Some(conf) = model.evaluate(&latest_audio_feats, &latest_vision_feats) {
                        tag_acc.record(&model.label, TagSource::Model, conf, elapsed_s);
                        tags_updated = true;
                    }
                }
            }

            frame_index = frame_index.wrapping_add(1);

            if tags_updated {
                let active = tag_acc.active_labels();
                let mut st = shared.state.lock().unwrap_or_else(|e| e.into_inner());
                st.active_tags = active;
            }

            let elapsed = loop_start.elapsed();
            if let Some(rem) = TARGET_FRAME_INTERVAL.checked_sub(elapsed) {
                thread::sleep(rem);
            }
        }

        let actual_dur_s = clip_start.elapsed().as_secs().max(1) as u32;
        if write_failed {
            drop(muxer);
            let _ = fs::remove_file(&tmp_path);
            if let Some(oldest) = scan_clips().first() {
                if remove_clip_and_sidecar(&oldest.name).is_ok() {
                    warn!(
                        "recorder-worker: force-evicted oldest clip {} after write error",
                        oldest.name
                    );
                }
            }
            evict_oldest_clips_if_needed(&shared);
        } else {
            match muxer.finalize() {
                Ok(summary) if summary.video_frames > 0 || summary.audio_samples > 0 => {
                    if let Err(err) = fs::rename(&tmp_path, &final_path) {
                        warn!("recorder-worker: rename {tmp_name} -> {final_name} failed: {err}");
                        let _ = fs::remove_file(&tmp_path);
                    } else {
                        let tags = tag_acc.finalize();
                        let sidecar = format_clip_sidecar_json(&tags);
                        if let Err(err) = fs::write(&meta_path, sidecar.as_bytes()) {
                            warn!("recorder-worker: failed to write {meta_name}: {err}");
                        }
                        info!(
                            "recorder-worker: saved {final_name} ({} B, {} frames, {} audio samples, {}s, {} tags)",
                            summary.total_bytes,
                            summary.video_frames,
                            summary.audio_samples,
                            actual_dur_s,
                            tags.len()
                        );
                    }
                }
                Ok(_) => {
                    let _ = fs::remove_file(&tmp_path);
                }
                Err(err) => {
                    warn!("recorder-worker: mov finalize failed: {err}");
                    let _ = fs::remove_file(&tmp_path);
                }
            }
        }

        let clips = scan_clips();
        let (total, free) = sd_space_info().unwrap_or((0, 0));
        let mut st = shared.state.lock().unwrap_or_else(|e| e.into_inner());
        st.active_clip = None;
        st.active_tags.clear();
        st.sd_total_bytes = total;
        st.sd_free_bytes = free;
        st.clips = clips;
    }
}

fn start_http_server(shared: Arc<RecorderShared>) -> Result<EspHttpServer<'static>> {
    let config = HttpConfig {
        http_port: 80,
        stack_size: 10 * 1024,
        max_open_sockets: 5,
        uri_match_wildcard: true,
        ..Default::default()
    };
    let mut server = EspHttpServer::new(&config)?;

    // GET / — simple HTML status page for browser debugging.
    {
        let shared = Arc::clone(&shared);
        server.fn_handler("/", Method::Get, move |req| -> Result<()> {
            let st = shared.status_snapshot();
            let body = format!(
                concat!(
                    "<!doctype html><html><head><meta charset='utf-8'><title>XIAO ESP32-S3 Sense</title></head>",
                    "<body><h1>XIAO ESP32-S3 Sense Recorder</h1>",
                    "<p>Recording: {} | Clips: {} | SD Free: {} MiB</p>",
                    "<p><a href='/api/status'>/api/status</a> | <a href='/api/clips'>/api/clips</a> | <a href='/api/tags'>/api/tags</a></p>",
                    "</body></html>"
                ),
                st.recording,
                st.clip_count,
                st.sd_free_bytes / (1024 * 1024),
            );
            let mut resp = req.into_response(
                200,
                Some("OK"),
                &[("Content-Type", "text/html; charset=utf-8")],
            )?;
            resp.write_all(body.as_bytes())?;
            Ok(())
        })?;
    }

    // GET /api/status
    {
        let shared = Arc::clone(&shared);
        server.fn_handler("/api/status", Method::Get, move |req| -> Result<()> {
            let st = shared.status_snapshot();
            let json = format_status_json(&st);
            let mut resp = req.into_response(
                200,
                Some("OK"),
                &[
                    ("Content-Type", "application/json"),
                    ("Cache-Control", "no-store"),
                ],
            )?;
            resp.write_all(json.as_bytes())?;
            Ok(())
        })?;
    }

    // GET /api/tags
    {
        let shared = Arc::clone(&shared);
        server.fn_handler("/api/tags", Method::Get, move |req| -> Result<()> {
            let clips = {
                let st = shared.state.lock().unwrap_or_else(|e| e.into_inner());
                st.clips.clone()
            };
            let json = format_tags_summary_json(&clips);
            let mut resp = req.into_response(
                200,
                Some("OK"),
                &[
                    ("Content-Type", "application/json"),
                    ("Cache-Control", "no-store"),
                ],
            )?;
            resp.write_all(json.as_bytes())?;
            Ok(())
        })?;
    }

    // GET /api/clips (supports optional `?tag=<label>` filter)
    {
        let shared = Arc::clone(&shared);
        server.fn_handler("/api/clips", Method::Get, move |req| -> Result<()> {
            let uri = req.uri().to_string();
            let tag_filter = extract_query_param(&uri, "tag");
            let recording = shared.recording.load(Ordering::Relaxed);
            let (clips, total, free) = {
                let st = shared.state.lock().unwrap_or_else(|e| e.into_inner());
                (st.clips.clone(), st.sd_total_bytes, st.sd_free_bytes)
            };
            let json = format_clips_filtered_json(&clips, tag_filter, total, free, recording);
            let mut resp = req.into_response(
                200,
                Some("OK"),
                &[
                    ("Content-Type", "application/json"),
                    ("Cache-Control", "no-store"),
                ],
            )?;
            resp.write_all(json.as_bytes())?;
            Ok(())
        })?;
    }

    // POST /api/record/start
    {
        let shared = Arc::clone(&shared);
        server.fn_handler(
            "/api/record/start",
            Method::Post,
            move |req| -> Result<()> {
                let can_record = {
                    let st = shared.state.lock().unwrap_or_else(|e| e.into_inner());
                    st.sd_mounted && (st.camera_ready || st.mic_ready)
                };
                if can_record {
                    shared.recording.store(true, Ordering::Release);
                }
                let st = shared.status_snapshot();
                let json = format_status_json(&st);
                let mut resp =
                    req.into_response(200, Some("OK"), &[("Content-Type", "application/json")])?;
                resp.write_all(json.as_bytes())?;
                Ok(())
            },
        )?;
    }

    // POST /api/record/stop
    {
        let shared = Arc::clone(&shared);
        server.fn_handler("/api/record/stop", Method::Post, move |req| -> Result<()> {
            shared.recording.store(false, Ordering::Release);
            let st = shared.status_snapshot();
            let json = format_status_json(&st);
            let mut resp =
                req.into_response(200, Some("OK"), &[("Content-Type", "application/json")])?;
            resp.write_all(json.as_bytes())?;
            Ok(())
        })?;
    }

    // DELETE /api/clips/*
    {
        let shared = Arc::clone(&shared);
        server.fn_handler("/api/clips/*", Method::Delete, move |req| -> Result<()> {
            let uri = req.uri().to_string();
            let name = uri
                .strip_prefix("/api/clips/")
                .unwrap_or("")
                .split('?')
                .next()
                .unwrap_or("");
            if !is_valid_clip_name(name) {
                let mut resp = req.into_response(
                    400,
                    Some("Bad Request"),
                    &[("Content-Type", "application/json")],
                )?;
                resp.write_all(br#"{"error":"invalid clip name"}"#)?;
                return Ok(());
            }
            if remove_clip_and_sidecar(name).is_err() {
                let mut resp = req.into_response(
                    404,
                    Some("Not Found"),
                    &[("Content-Type", "application/json")],
                )?;
                resp.write_all(br#"{"error":"clip not found"}"#)?;
                return Ok(());
            }
            let space = sd_space_info().ok();
            {
                let mut st = shared.state.lock().unwrap_or_else(|e| e.into_inner());
                st.clips.retain(|c| c.name != name);
                if let Some((total, free)) = space {
                    st.sd_total_bytes = total;
                    st.sd_free_bytes = free;
                }
            }
            let body = format!(r#"{{"deleted":"{name}"}}"#);
            let mut resp =
                req.into_response(200, Some("OK"), &[("Content-Type", "application/json")])?;
            resp.write_all(body.as_bytes())?;
            Ok(())
        })?;
    }

    // HEAD /clips/* — AVPlayer uses HEAD or Range: bytes=0-1 to probe media length.
    server.fn_handler("/clips/*", Method::Head, move |req| -> Result<()> {
        let uri = req.uri().to_string();
        let name = uri
            .strip_prefix("/clips/")
            .unwrap_or("")
            .split('?')
            .next()
            .unwrap_or("");
        if !is_valid_clip_name(name) {
            let _ = req.into_response(400, Some("Bad Request"), &[])?;
            return Ok(());
        }
        let path = PathBuf::from(CLIPS_DIR).join(name);
        let Ok(meta) = fs::metadata(&path) else {
            let _ = req.into_response(404, Some("Not Found"), &[])?;
            return Ok(());
        };
        let len_str = meta.len().to_string();
        let _ = req.into_response(
            200,
            Some("OK"),
            &[
                ("Content-Type", "video/quicktime"),
                ("Accept-Ranges", "bytes"),
                ("Content-Length", len_str.as_str()),
            ],
        )?;
        Ok(())
    })?;

    // GET /clips/* — full or `206 Partial Content` byte-range streaming for AVPlayer.
    server.fn_handler("/clips/*", Method::Get, move |req| -> Result<()> {
        let uri = req.uri().to_string();
        let name = uri
            .strip_prefix("/clips/")
            .unwrap_or("")
            .split('?')
            .next()
            .unwrap_or("");
        if !is_valid_clip_name(name) {
            let mut resp =
                req.into_response(400, Some("Bad Request"), &[("Content-Type", "text/plain")])?;
            resp.write_all(b"invalid clip name")?;
            return Ok(());
        }

        let path = PathBuf::from(CLIPS_DIR).join(name);
        let Ok(mut file) = File::open(&path) else {
            let mut resp =
                req.into_response(404, Some("Not Found"), &[("Content-Type", "text/plain")])?;
            resp.write_all(b"clip not found")?;
            return Ok(());
        };
        let total_size = file.metadata().map(|m| m.len()).unwrap_or(0);
        let range_header = req.header("Range").map(str::to_string);

        let (status_code, status_text, start, mut remaining, content_range) =
            if let Some(ref rh) = range_header {
                if let Some(range) = parse_byte_range(rh, total_size) {
                    (
                        206u16,
                        "Partial Content",
                        range.start,
                        range.len(),
                        Some(format!("bytes {}-{}/{total_size}", range.start, range.end)),
                    )
                } else {
                    let cr = format!("bytes */{total_size}");
                    let _ = req.into_response(
                        416,
                        Some("Range Not Satisfiable"),
                        &[("Content-Range", cr.as_str())],
                    )?;
                    return Ok(());
                }
            } else {
                (200u16, "OK", 0u64, total_size, None)
            };

        if start > 0 {
            file.seek(SeekFrom::Start(start))?;
        }

        let content_len = remaining.to_string();
        let mut resp = if let Some(ref cr) = content_range {
            req.into_response(
                status_code,
                Some(status_text),
                &[
                    ("Content-Type", "video/quicktime"),
                    ("Accept-Ranges", "bytes"),
                    ("Content-Length", content_len.as_str()),
                    ("Content-Range", cr.as_str()),
                ],
            )?
        } else {
            req.into_response(
                status_code,
                Some(status_text),
                &[
                    ("Content-Type", "video/quicktime"),
                    ("Accept-Ranges", "bytes"),
                    ("Content-Length", content_len.as_str()),
                ],
            )?
        };

        let mut buf = vec![0u8; HTTP_STREAM_CHUNK_BYTES];
        while remaining > 0 {
            let to_read = (remaining as usize).min(buf.len());
            let n = file.read(&mut buf[..to_read])?;
            if n == 0 {
                break;
            }
            resp.write_all(&buf[..n])?;
            remaining -= n as u64;
        }
        Ok(())
    })?;

    Ok(server)
}
