//! On-device audio DSP, vision motion/color analysis, SD-card custom model hook (`MCUM`),
//! and clip tag aggregation for the Seeed Studio XIAO ESP32-S3 Sense recorder.
//!
//! All algorithms in this module are pure Rust and host-safe so `cargo test --lib`
//! verifies audio spectral detection, visual motion/color tagging, `MCUM` model loading,
//! and JSON sidecar serialization without needing the ESP-IDF toolchain.

use std::collections::BTreeMap;
use std::f32::consts::PI;

/// Source of a clip tag detected on-device.
#[derive(Debug, Clone, Copy, PartialEq, Eq, PartialOrd, Ord)]
pub enum TagSource {
    Audio,
    Vision,
    Model,
}

impl TagSource {
    pub const fn as_str(self) -> &'static str {
        match self {
            Self::Audio => "audio",
            Self::Vision => "vision",
            Self::Model => "model",
        }
    }

    pub fn parse(s: &str) -> Option<Self> {
        match s {
            "audio" => Some(Self::Audio),
            "vision" => Some(Self::Vision),
            "model" => Some(Self::Model),
            _ => None,
        }
    }
}

/// A single tag attached to a recorded clip (stored in `clip_NNNNNN.json` sidecar).
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct ClipTag {
    pub label: String,
    pub source: TagSource,
    /// Peak confidence percentage (`0..=100`).
    pub confidence: u8,
    /// Earliest second within the clip where this tag triggered.
    pub first_s: u32,
    /// Number of detection hits within the clip.
    pub count: u32,
}

/// Aggregates repeated detections over a 1-minute clip into deduplicated [`ClipTag`] entries.
#[derive(Debug, Default, Clone)]
pub struct TagAccumulator {
    entries: BTreeMap<(String, TagSource), ClipTag>,
}

impl TagAccumulator {
    pub fn new() -> Self {
        Self::default()
    }

    /// Record a detection hit at `elapsed_s` seconds into the clip.
    pub fn record(&mut self, label: &str, source: TagSource, confidence: u8, elapsed_s: u32) {
        let clamped = confidence.min(100);
        if label.is_empty() || clamped == 0 {
            return;
        }
        let key = (label.to_string(), source);
        self.entries
            .entry(key)
            .and_modify(|e| {
                e.confidence = e.confidence.max(clamped);
                e.first_s = e.first_s.min(elapsed_s);
                e.count = e.count.saturating_add(1);
            })
            .or_insert_with(|| ClipTag {
                label: label.to_string(),
                source,
                confidence: clamped,
                first_s: elapsed_s,
                count: 1,
            });
    }

    /// Return all unique labels seen so far (for live status reporting).
    pub fn active_labels(&self) -> Vec<String> {
        let mut labels: Vec<String> = self.entries.values().map(|t| t.label.clone()).collect();
        labels.sort();
        labels.dedup();
        labels
    }

    /// Finalize tags sorted by highest confidence first, then label ascending.
    pub fn finalize(&self) -> Vec<ClipTag> {
        let mut out: Vec<ClipTag> = self.entries.values().cloned().collect();
        out.sort_by(|a, b| {
            b.confidence
                .cmp(&a.confidence)
                .then_with(|| a.label.cmp(&b.label))
                .then_with(|| a.source.cmp(&b.source))
        });
        out
    }
}

/// 8-dimensional compact audio feature vector extracted from each 100 ms PCM chunk.
#[derive(Debug, Clone, Copy, Default)]
pub struct AudioFeatures {
    pub rms: f32,
    pub zcr: f32,
    pub low_ratio: f32,
    pub mid_ratio: f32,
    pub high_ratio: f32,
    pub high_peakiness: f32,
    pub onset_ratio: f32,
    pub snr: f32,
}

impl AudioFeatures {
    pub fn as_array(&self) -> [f32; 8] {
        [
            self.rms,
            self.zcr,
            self.low_ratio,
            self.mid_ratio,
            self.high_ratio,
            self.high_peakiness,
            self.onset_ratio,
            self.snr,
        ]
    }
}

/// On-device pure-Rust audio DSP detector for 16 kHz, 16-bit LE mono PCM streams.
///
/// Uses Goertzel single-bin DFT power across acoustic bands plus adaptive noise floor
/// tracking and ZCR to tag `bark`, `bird`, `bluejay`, `speech`, and `loud` in <1 ms
/// per 100 ms chunk on ESP32-S3.
pub struct AudioDetector {
    sample_rate: f32,
    noise_floor: f32,
    prev_rms: f32,
    speech_streak: u32,
    initialized: bool,
}

impl AudioDetector {
    pub fn new(sample_rate: u32) -> Self {
        Self {
            sample_rate: sample_rate.max(8_000) as f32,
            noise_floor: 0.015,
            prev_rms: 0.0,
            speech_streak: 0,
            initialized: false,
        }
    }

    /// Analyze one chunk of 16-bit signed LE mono PCM samples and emit any detected
    /// `(label, confidence)` tags plus the extracted [`AudioFeatures`] for SD models.
    pub fn analyze_pcm_le16(
        &mut self,
        pcm_le16: &[u8],
    ) -> (Vec<(&'static str, u8)>, AudioFeatures) {
        let sample_count = pcm_le16.len() / 2;
        if sample_count < 64 {
            return (Vec::new(), AudioFeatures::default());
        }

        // Convert to normalized f32 [-1.0, 1.0], compute RMS and Zero-Crossing Rate.
        let mut sum_sq = 0.0f32;
        let mut zero_crossings = 0u32;
        let mut prev_pos = false;
        // Analyze at most 1600 samples (100 ms at 16 kHz) per call to keep latency bounded.
        let n = sample_count.min(1600);
        let mut samples = [0.0f32; 1600];
        for (i, slot) in samples.iter_mut().take(n).enumerate() {
            let s = i16::from_le_bytes([pcm_le16[i * 2], pcm_le16[i * 2 + 1]]) as f32 / 32768.0;
            *slot = s;
            sum_sq += s * s;
            let pos = s >= 0.0;
            if i > 0 && pos != prev_pos {
                zero_crossings += 1;
            }
            prev_pos = pos;
        }
        let slice = &samples[..n];
        let rms = (sum_sq / n as f32).sqrt();
        let zcr = zero_crossings as f32 / (n - 1) as f32;

        if !self.initialized {
            self.noise_floor = rms.clamp(0.005, 0.05);
            self.prev_rms = rms;
            self.initialized = true;
        }

        let snr = rms / self.noise_floor.max(0.005);
        let onset_ratio = rms / self.prev_rms.max(0.005);

        // Update adaptive noise floor slowly during quiet chunks.
        if snr < 2.2 {
            self.noise_floor = (self.noise_floor * 0.92 + rms * 0.08).clamp(0.005, 0.08);
        }
        self.prev_rms = rms;

        // Goertzel band energies (normalized by N^2).
        let p_low = goertzel_power(slice, self.sample_rate, 350.0)
            + goertzel_power(slice, self.sample_rate, 650.0)
            + goertzel_power(slice, self.sample_rate, 1000.0);
        let p_mid = goertzel_power(slice, self.sample_rate, 1400.0)
            + goertzel_power(slice, self.sample_rate, 2000.0);
        let h1 = goertzel_power(slice, self.sample_rate, 2800.0);
        let h2 = goertzel_power(slice, self.sample_rate, 3600.0);
        let h3 = goertzel_power(slice, self.sample_rate, 4600.0);
        let h4 = goertzel_power(slice, self.sample_rate, 5800.0);
        let p_high = h1 + h2 + h3 + h4;
        let p_total = (p_low + p_mid + p_high).max(1e-9);

        let low_ratio = p_low / p_total;
        let mid_ratio = p_mid / p_total;
        let high_ratio = p_high / p_total;
        let max_high = h1.max(h2).max(h3).max(h4);
        let avg_high = (p_high / 4.0).max(1e-9);
        let high_peakiness = max_high / avg_high;

        let features = AudioFeatures {
            rms,
            zcr,
            low_ratio,
            mid_ratio,
            high_ratio,
            high_peakiness,
            onset_ratio,
            snr,
        };

        // Below acoustic activity threshold -> silence / background noise.
        if rms < 0.03 || snr < 2.8 {
            self.speech_streak = 0;
            return (Vec::new(), features);
        }

        let mut hits = Vec::new();

        // 1. Birdsong / chirp: dominant narrowband high-frequency energy (2.8–5.8 kHz) + high ZCR.
        if high_ratio >= 0.55 && high_peakiness >= 1.6 && zcr >= 0.25 {
            let conf = ((high_ratio * 60.0 + (snr.min(10.0) * 3.5)).clamp(55.0, 95.0)) as u8;
            hits.push(("bird", conf));
            self.speech_streak = 0;
        }
        // 2. Bluejay harsh "jeer" call: strong mid-high harmonic band (1.4–3.6 kHz) with sharp onset.
        else if (mid_ratio + high_ratio) >= 0.65
            && mid_ratio >= 0.30
            && h1 + h2 > h3 + h4
            && snr >= 3.5
            && (0.14..=0.36).contains(&zcr)
        {
            let conf = ((mid_ratio * 70.0 + snr.min(8.0) * 4.0).clamp(55.0, 90.0)) as u8;
            hits.push(("bluejay", conf));
            hits.push(("bird", conf.saturating_sub(5)));
            self.speech_streak = 0;
        }
        // 3. Dog bark: sharp loud impulsive low-mid burst (350–1400 Hz) with strong onset.
        else if (low_ratio + mid_ratio * 0.5) >= 0.60
            && onset_ratio >= 2.2
            && snr >= 4.0
            && zcr <= 0.22
        {
            let conf = ((low_ratio * 55.0 + onset_ratio.min(6.0) * 6.0).clamp(60.0, 95.0)) as u8;
            hits.push(("bark", conf));
            hits.push(("dog", conf.saturating_sub(10)));
            self.speech_streak = 0;
        }
        // 4. Speech: sustained low+mid formant energy over consecutive chunks.
        else if (low_ratio + mid_ratio) >= 0.65 && (0.04..=0.22).contains(&zcr) {
            self.speech_streak = self.speech_streak.saturating_add(1);
            if self.speech_streak >= 3 {
                let conf = ((55.0 + snr.min(8.0) * 4.0).clamp(55.0, 88.0)) as u8;
                hits.push(("speech", conf));
            }
        } else {
            self.speech_streak = 0;
        }

        if hits.is_empty() && snr >= 5.0 && rms >= 0.10 {
            let conf = ((50.0 + snr.min(10.0) * 3.5).clamp(55.0, 85.0)) as u8;
            hits.push(("loud", conf));
        }

        (hits, features)
    }
}

/// Goertzel single-frequency DFT power normalized by `N^2`.
fn goertzel_power(samples: &[f32], sample_rate: f32, target_hz: f32) -> f32 {
    let n = samples.len();
    if n == 0 {
        return 0.0;
    }
    let omega = 2.0 * PI * target_hz / sample_rate;
    let coeff = 2.0 * omega.cos();
    let mut s0;
    let mut s1 = 0.0f32;
    let mut s2 = 0.0f32;
    for &x in samples {
        s0 = x + coeff * s1 - s2;
        s2 = s1;
        s1 = s0;
    }
    let power = s1 * s1 + s2 * s2 - coeff * s1 * s2;
    let denom = (n as f32) * (n as f32);
    (power / denom).max(0.0)
}

/// 8-dimensional compact vision feature vector extracted from a frame or JPEG stream.
#[derive(Debug, Clone, Copy, Default)]
pub struct VisionFeatures {
    pub motion_score: f32,
    pub blue_ratio: f32,
    pub warm_brown_ratio: f32,
    pub white_ratio: f32,
    pub dark_ratio: f32,
    pub mean_luma: f32,
    pub luma_std: f32,
    pub active_area_ratio: f32,
}

impl VisionFeatures {
    pub fn as_array(&self) -> [f32; 8] {
        [
            self.motion_score,
            self.blue_ratio,
            self.warm_brown_ratio,
            self.white_ratio,
            self.dark_ratio,
            self.mean_luma,
            self.luma_std,
            self.active_area_ratio,
        ]
    }
}

/// On-device pure-Rust visual motion & color-cluster detector.
///
/// Works on either a small downsampled RGB888 grid (e.g. 32×24) for full motion +
/// moving-object color analysis (`motion`, `bluejay`, `animal`), or directly on
/// JPEG frame byte lengths (`analyze_jpeg_size`) as a zero-decode fallback.
pub struct VisionDetector {
    prev_luma: Vec<u8>,
    prev_jpeg_len: Option<usize>,
}

impl VisionDetector {
    pub fn new() -> Self {
        Self {
            prev_luma: Vec::new(),
            prev_jpeg_len: None,
        }
    }

    /// Reset motion baseline at the start of a new clip.
    pub fn reset(&mut self) {
        self.prev_luma.clear();
        self.prev_jpeg_len = None;
    }

    /// Analyze a downsampled RGB888 grid (`rgb.len() == width * height * 3`) for motion
    /// and moving-region plumage/coat color signatures.
    pub fn analyze_rgb888(
        &mut self,
        rgb: &[u8],
        width: usize,
        height: usize,
    ) -> (Vec<(&'static str, u8)>, VisionFeatures) {
        let pixels = width.saturating_mul(height);
        if pixels == 0 || rgb.len() < pixels * 3 {
            return (Vec::new(), VisionFeatures::default());
        }

        let mut luma = Vec::with_capacity(pixels);
        let mut luma_sum = 0.0f32;
        for i in 0..pixels {
            let r = rgb[i * 3] as u32;
            let g = rgb[i * 3 + 1] as u32;
            let b = rgb[i * 3 + 2] as u32;
            let y = ((77 * r + 150 * g + 29 * b) >> 8) as u8;
            luma.push(y);
            luma_sum += y as f32;
        }
        let mean_luma = (luma_sum / pixels as f32) / 255.0;
        let mut var_sum = 0.0f32;
        for &y in &luma {
            let d = (y as f32 / 255.0) - mean_luma;
            var_sum += d * d;
        }
        let luma_std = (var_sum / pixels as f32).sqrt();

        let mut motion_sum = 0u32;
        let mut moved_pixels = 0u32;
        let mut blue_moved = 0u32;
        let mut warm_moved = 0u32;
        let mut white_moved = 0u32;
        let mut dark_moved = 0u32;

        if self.prev_luma.len() == pixels {
            for i in 0..pixels {
                let diff = luma[i].abs_diff(self.prev_luma[i]);
                motion_sum += u32::from(diff);
                if diff >= 18 {
                    moved_pixels += 1;
                    let r = rgb[i * 3];
                    let g = rgb[i * 3 + 1];
                    let b = rgb[i * 3 + 2];
                    if is_bluejay_blue(r, g, b) {
                        blue_moved += 1;
                    } else if is_warm_fur_tone(r, g, b) {
                        warm_moved += 1;
                    } else if r >= 200 && g >= 200 && b >= 200 {
                        white_moved += 1;
                    } else if r <= 55 && g <= 55 && b <= 55 {
                        dark_moved += 1;
                    }
                }
            }
        }
        self.prev_luma = luma;

        let motion_score = (motion_sum as f32 / (pixels as f32 * 255.0)).clamp(0.0, 1.0);
        let active_area_ratio = moved_pixels as f32 / pixels as f32;
        let denom = moved_pixels.max(1) as f32;
        let blue_ratio = blue_moved as f32 / denom;
        let warm_brown_ratio = warm_moved as f32 / denom;
        let white_ratio = white_moved as f32 / denom;
        let dark_ratio = dark_moved as f32 / denom;

        let features = VisionFeatures {
            motion_score,
            blue_ratio,
            warm_brown_ratio,
            white_ratio,
            dark_ratio,
            mean_luma,
            luma_std,
            active_area_ratio,
        };

        let mut hits = Vec::new();
        if active_area_ratio >= 0.04 && motion_score >= 0.008 {
            let conf = ((50.0 + active_area_ratio * 180.0).clamp(55.0, 95.0)) as u8;
            hits.push(("motion", conf));

            // Compact moving object with distinct blue (+ optional white/black) plumage -> bluejay candidate.
            if active_area_ratio <= 0.45 && blue_ratio >= 0.25 {
                let bconf =
                    ((55.0 + blue_ratio * 60.0 + white_ratio * 20.0).clamp(60.0, 92.0)) as u8;
                hits.push(("bluejay", bconf));
                hits.push(("bird", bconf.saturating_sub(5)));
            }
        }

        (hits, features)
    }

    /// Lightweight zero-decode motion detector using JPEG frame byte-size delta.
    pub fn analyze_jpeg_size(&mut self, jpeg_len: usize) -> Option<(&'static str, u8)> {
        if jpeg_len == 0 {
            return None;
        }
        let prev = self.prev_jpeg_len.replace(jpeg_len)?;
        let diff = jpeg_len.abs_diff(prev);
        let ratio = diff as f32 / prev.max(1) as f32;
        if ratio >= 0.14 {
            let conf = ((50.0 + ratio * 150.0).clamp(55.0, 90.0)) as u8;
            Some(("motion", conf))
        } else {
            None
        }
    }
}

impl Default for VisionDetector {
    fn default() -> Self {
        Self::new()
    }
}

fn is_bluejay_blue(r: u8, g: u8, b: u8) -> bool {
    let rf = r as i16;
    let gf = g as i16;
    let bf = b as i16;
    bf >= 90 && (bf - rf) >= 35 && (bf - gf) >= 15
}

fn is_warm_fur_tone(r: u8, g: u8, b: u8) -> bool {
    let rf = r as i16;
    let gf = g as i16;
    let bf = b as i16;
    rf >= 80 && rf > gf && gf >= bf && (rf - bf) >= 25
}

/// Magic header for custom SD-card linear/logistic classifier models (`/sdcard/models/*.mcum`).
///
/// Binary layout (little-endian):
/// - `0..4`:   `b"MCUM"` magic
/// - `4`:      version (`1`)
/// - `5`:      modality (`1` = audio 8-dim features, `2` = vision 8-dim features, `3` = combined 16-dim)
/// - `6`:      `threshold_pct` (`1..=100`, minimum sigmoid percentage to emit tag)
/// - `7`:      `label_len` (`1..=32`)
/// - `8..8+L`: UTF-8 label bytes (e.g. `"dog"`, `"bluejay"`, `"squirrel"`)
/// - next 4 B: `bias: f32`
/// - next `4*D` B: `weights: [f32; D]` (`D = 8` for audio/vision, `16` for combined)
pub const MCUM_MAGIC: &[u8; 4] = b"MCUM";
pub const MCUM_VERSION: u8 = 1;

#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum ModelModality {
    Audio = 1,
    Vision = 2,
    Combined = 3,
}

impl ModelModality {
    pub const fn feature_dim(self) -> usize {
        match self {
            Self::Audio | Self::Vision => 8,
            Self::Combined => 16,
        }
    }

    fn from_byte(b: u8) -> Option<Self> {
        match b {
            1 => Some(Self::Audio),
            2 => Some(Self::Vision),
            3 => Some(Self::Combined),
            _ => None,
        }
    }
}

/// A custom on-device classifier loaded from `/sdcard/models/<name>.mcum`.
#[derive(Debug, Clone, PartialEq)]
pub struct SdLinearModel {
    pub label: String,
    pub modality: ModelModality,
    pub threshold_pct: u8,
    pub bias: f32,
    pub weights: Vec<f32>,
}

impl SdLinearModel {
    /// Parse a binary `MCUM` v1 model file loaded from the microSD card.
    pub fn parse(bytes: &[u8]) -> Result<Self, String> {
        if bytes.len() < 8 {
            return Err("MCUM file too short".to_string());
        }
        if &bytes[0..4] != MCUM_MAGIC {
            return Err("invalid MCUM magic".to_string());
        }
        if bytes[4] != MCUM_VERSION {
            return Err(format!("unsupported MCUM version {}", bytes[4]));
        }
        let modality = ModelModality::from_byte(bytes[5])
            .ok_or_else(|| format!("invalid MCUM modality {}", bytes[5]))?;
        let threshold_pct = bytes[6].clamp(1, 100);
        let label_len = bytes[7] as usize;
        if label_len == 0 || label_len > 32 {
            return Err(format!("invalid MCUM label length {label_len}"));
        }
        let dim = modality.feature_dim();
        let expected_len = 8 + label_len + 4 + dim * 4;
        if bytes.len() < expected_len {
            return Err(format!(
                "MCUM truncated: got {} bytes, need {expected_len}",
                bytes.len()
            ));
        }
        let label = std::str::from_utf8(&bytes[8..8 + label_len])
            .map_err(|_| "MCUM label is not valid UTF-8".to_string())?
            .to_string();
        let mut cursor = 8 + label_len;
        let bias = f32::from_le_bytes(bytes[cursor..cursor + 4].try_into().unwrap());
        cursor += 4;
        let mut weights = Vec::with_capacity(dim);
        for _ in 0..dim {
            let w = f32::from_le_bytes(bytes[cursor..cursor + 4].try_into().unwrap());
            weights.push(w);
            cursor += 4;
        }
        Ok(Self {
            label,
            modality,
            threshold_pct,
            bias,
            weights,
        })
    }

    /// Encode this model into binary `MCUM` v1 bytes (for tooling and tests).
    pub fn encode(&self) -> Vec<u8> {
        let label_bytes = self.label.as_bytes();
        let mut out = Vec::with_capacity(8 + label_bytes.len() + 4 + self.weights.len() * 4);
        out.extend_from_slice(MCUM_MAGIC);
        out.push(MCUM_VERSION);
        out.push(self.modality as u8);
        out.push(self.threshold_pct);
        out.push(label_bytes.len() as u8);
        out.extend_from_slice(label_bytes);
        out.extend_from_slice(&self.bias.to_le_bytes());
        for &w in &self.weights {
            out.extend_from_slice(&w.to_le_bytes());
        }
        out
    }

    /// Evaluate the logistic model on the given audio/vision features.
    /// Returns `Some(confidence_pct)` if the output meets `threshold_pct`.
    pub fn evaluate(&self, audio: &AudioFeatures, vision: &VisionFeatures) -> Option<u8> {
        let a = audio.as_array();
        let v = vision.as_array();
        let mut z = self.bias;
        match self.modality {
            ModelModality::Audio => {
                for (w, x) in self.weights.iter().zip(a.iter()) {
                    z += w * x;
                }
            }
            ModelModality::Vision => {
                for (w, x) in self.weights.iter().zip(v.iter()) {
                    z += w * x;
                }
            }
            ModelModality::Combined => {
                for (w, x) in self.weights.iter().zip(a.iter().chain(v.iter())) {
                    z += w * x;
                }
            }
        }
        let prob = 1.0 / (1.0 + (-z.clamp(-20.0, 20.0)).exp());
        let pct = (prob * 100.0).round().clamp(0.0, 100.0) as u8;
        if pct >= self.threshold_pct {
            Some(pct)
        } else {
            None
        }
    }
}

fn escape_json(s: &str) -> String {
    let mut out = String::with_capacity(s.len());
    for ch in s.chars() {
        match ch {
            '"' => out.push_str(r#"\""#),
            '\\' => out.push_str(r#"\\"#),
            '\n' => out.push_str(r#"\n"#),
            '\r' => out.push_str(r#"\r"#),
            '\t' => out.push_str(r#"\t"#),
            c if (c as u32) < 0x20 => out.push_str(&format!(r#"\u{:04x}"#, c as u32)),
            c => out.push(c),
        }
    }
    out
}

/// Format a clip's tags as a JSON array (used inside `GET /api/clips` and sidecar `.json`).
pub fn format_tags_array_json(tags: &[ClipTag]) -> String {
    let mut out = String::from("[");
    for (idx, tag) in tags.iter().enumerate() {
        if idx > 0 {
            out.push(',');
        }
        out.push_str(&format!(
            r#"{{"label":"{}","source":"{}","confidence":{},"first_s":{},"count":{}}}"#,
            escape_json(&tag.label),
            tag.source.as_str(),
            tag.confidence,
            tag.first_s,
            tag.count,
        ));
    }
    out.push(']');
    out
}

/// Format the full sidecar file `clip_NNNNNN.json`.
pub fn format_clip_sidecar_json(tags: &[ClipTag]) -> String {
    format!(r#"{{"tags":{}}}"#, format_tags_array_json(tags))
}

/// Parse tags from a sidecar file written by [`format_clip_sidecar_json`].
pub fn parse_clip_sidecar_json(json: &str) -> Vec<ClipTag> {
    let mut out = Vec::new();
    let Some(arr_start) = json.find('[') else {
        return out;
    };
    let Some(arr_end) = json.rfind(']') else {
        return out;
    };
    if arr_end <= arr_start {
        return out;
    }
    let inner = &json[arr_start + 1..arr_end];
    for obj in inner.split("},{") {
        let trimmed = obj.trim().trim_start_matches('{').trim_end_matches('}');
        if trimmed.is_empty() {
            continue;
        }
        let label = extract_json_string(trimmed, "label");
        let source = extract_json_string(trimmed, "source").and_then(|s| TagSource::parse(&s));
        let confidence = extract_json_u64(trimmed, "confidence").map(|v| v.min(100) as u8);
        let first_s = extract_json_u64(trimmed, "first_s").map(|v| v as u32);
        let count = extract_json_u64(trimmed, "count").map(|v| v as u32);
        if let (Some(label), Some(source), Some(confidence), Some(first_s), Some(count)) =
            (label, source, confidence, first_s, count)
        {
            out.push(ClipTag {
                label,
                source,
                confidence,
                first_s,
                count,
            });
        }
    }
    out
}

fn extract_json_string(obj: &str, key: &str) -> Option<String> {
    let pat = format!(r#""{key}":"#);
    let idx = obj.find(&pat)? + pat.len();
    let rest = obj[idx..].trim_start();
    let rest = rest.strip_prefix('"')?;
    let mut out = String::new();
    let mut chars = rest.chars();
    while let Some(c) = chars.next() {
        match c {
            '"' => return Some(out),
            '\\' => {
                if let Some(esc) = chars.next() {
                    out.push(esc);
                }
            }
            other => out.push(other),
        }
    }
    None
}

fn extract_json_u64(obj: &str, key: &str) -> Option<u64> {
    let pat = format!(r#""{key}":"#);
    let idx = obj.find(&pat)? + pat.len();
    let rest = obj[idx..].trim_start();
    let digits: String = rest.chars().take_while(|c| c.is_ascii_digit()).collect();
    digits.parse::<u64>().ok()
}

#[cfg(test)]
mod tests {
    use super::*;

    fn sine_pcm(sample_rate: u32, freq_hz: f32, amp: f32, num_samples: usize) -> Vec<u8> {
        let mut out = Vec::with_capacity(num_samples * 2);
        for i in 0..num_samples {
            let t = i as f32 / sample_rate as f32;
            let v = (2.0 * PI * freq_hz * t).sin() * amp;
            let s = (v.clamp(-1.0, 1.0) * 32767.0) as i16;
            out.extend_from_slice(&s.to_le_bytes());
        }
        out
    }

    fn silence_pcm(num_samples: usize) -> Vec<u8> {
        vec![0u8; num_samples * 2]
    }

    #[test]
    fn audio_detector_tags_bird_chirp_and_dog_bark() {
        let mut det = AudioDetector::new(16_000);
        // Prime noise floor with silence.
        let (quiet_hits, _) = det.analyze_pcm_le16(&silence_pcm(1600));
        assert!(quiet_hits.is_empty());

        // High-frequency tonal chirp at 3.6 kHz -> bird.
        let chirp = sine_pcm(16_000, 3600.0, 0.45, 1600);
        let (bird_hits, _) = det.analyze_pcm_le16(&chirp);
        assert!(
            bird_hits.iter().any(|(lbl, _)| *lbl == "bird"),
            "expected bird tag, got {bird_hits:?}"
        );

        // Return to silence, then emit sharp low-mid impulse at 650 Hz -> bark + dog.
        let _ = det.analyze_pcm_le16(&silence_pcm(1600));
        let bark = sine_pcm(16_000, 650.0, 0.75, 1600);
        let (bark_hits, _) = det.analyze_pcm_le16(&bark);
        assert!(
            bark_hits.iter().any(|(lbl, _)| *lbl == "bark"),
            "expected bark tag, got {bark_hits:?}"
        );
        assert!(
            bark_hits.iter().any(|(lbl, _)| *lbl == "dog"),
            "expected dog tag, got {bark_hits:?}"
        );
    }

    #[test]
    fn vision_detector_tags_motion_and_bluejay_plumage() {
        let mut det = VisionDetector::new();
        let w = 16;
        let h = 12;
        // Neutral gray background.
        let bg = vec![120u8; w * h * 3];
        let (hits0, _) = det.analyze_rgb888(&bg, w, h);
        assert!(hits0.is_empty());

        // Introduce a compact bright-blue moving object (~20% of pixels).
        let mut fg = bg.clone();
        for y in 2..7 {
            for x in 4..11 {
                let idx = (y * w + x) * 3;
                fg[idx] = 30;
                fg[idx + 1] = 100;
                fg[idx + 2] = 220;
            }
        }
        let (hits1, feats) = det.analyze_rgb888(&fg, w, h);
        assert!(feats.active_area_ratio > 0.10);
        assert!(hits1.iter().any(|(lbl, _)| *lbl == "motion"));
        assert!(hits1.iter().any(|(lbl, _)| *lbl == "bluejay"));
        assert!(hits1.iter().any(|(lbl, _)| *lbl == "bird"));
    }

    #[test]
    fn sd_linear_model_round_trips_and_evaluates() {
        let model = SdLinearModel {
            label: "dog".to_string(),
            modality: ModelModality::Audio,
            threshold_pct: 70,
            bias: -1.0,
            weights: vec![4.0, 0.0, 2.0, 0.0, 0.0, 0.0, 1.0, 0.0],
        };
        let encoded = model.encode();
        let decoded = SdLinearModel::parse(&encoded).unwrap();
        assert_eq!(decoded, model);

        let loud_low = AudioFeatures {
            rms: 0.6,
            low_ratio: 0.8,
            onset_ratio: 2.0,
            ..AudioFeatures::default()
        };
        let score = decoded.evaluate(&loud_low, &VisionFeatures::default());
        assert!(score.is_some_and(|pct| pct >= 70));

        let quiet = AudioFeatures::default();
        assert!(decoded
            .evaluate(&quiet, &VisionFeatures::default())
            .is_none());
    }

    #[test]
    fn sidecar_json_round_trips_tags() {
        let mut acc = TagAccumulator::new();
        acc.record("dog", TagSource::Audio, 75, 12);
        acc.record("dog", TagSource::Audio, 88, 15);
        acc.record("bluejay", TagSource::Vision, 82, 4);

        let tags = acc.finalize();
        assert_eq!(tags.len(), 2);
        assert_eq!(tags[0].label, "dog");
        assert_eq!(tags[0].confidence, 88);
        assert_eq!(tags[0].first_s, 12);
        assert_eq!(tags[0].count, 2);

        let json = format_clip_sidecar_json(&tags);
        let parsed = parse_clip_sidecar_json(&json);
        assert_eq!(parsed, tags);
    }
}
