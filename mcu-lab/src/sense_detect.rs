//! Host-safe TFLite Micro inference helpers, YAMNet log-mel spectrogram extractor,
//! label parsers, and clip tag sidecar serialization for XIAO ESP32-S3 Sense.
//!
//! No custom heuristic detectors live here — all tags come from pre-trained `.tflite`
//! models loaded from `/sdcard/models/` (vision + audio) and executed on device via
//! `espressif/esp-tflite-micro`.

use std::f32::consts::PI;

/// Default model directory on the microSD card.
pub const MODELS_DIR_NAME: &str = "/sdcard/models";

/// Expected vision model & labels paths on microSD.
pub const VISION_MODEL_PATH: &str = "/sdcard/models/vision.tflite";
pub const VISION_LABELS_PATH: &str = "/sdcard/models/vision_labels.txt";

/// Expected audio model & labels paths on microSD.
pub const AUDIO_MODEL_PATH: &str = "/sdcard/models/audio.tflite";
pub const AUDIO_LABELS_PATH: &str = "/sdcard/models/audio_labels.txt";
/// Alternative Google YAMNet CSV class map filename supported out of the box.
pub const AUDIO_LABELS_CSV_PATH: &str = "/sdcard/models/yamnet_class_map.csv";

/// Default minimum confidence (0.0..=1.0) to record a vision or audio tag.
pub const DEFAULT_VISION_MIN_CONFIDENCE: f32 = 0.45;
pub const DEFAULT_AUDIO_MIN_CONFIDENCE: f32 = 0.40;

/// Maximum number of tags stored per clip sidecar.
pub const MAX_TAGS_PER_CLIP: usize = 16;

/// Origin of a detected tag on a recorded clip.
#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash)]
pub enum TagSource {
    /// Detected by the on-device audio `.tflite` model (e.g. YAMNet INT8).
    Audio,
    /// Detected by the on-device vision `.tflite` model (e.g. MobileNet INT8/UINT8).
    Vision,
}

impl TagSource {
    pub fn as_str(self) -> &'static str {
        match self {
            Self::Audio => "audio",
            Self::Vision => "vision",
        }
    }

    pub fn parse(s: &str) -> Option<Self> {
        match s {
            "audio" => Some(Self::Audio),
            "vision" => Some(Self::Vision),
            _ => None,
        }
    }
}

/// Aggregated tag recorded for a clip.
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct ClipTag {
    pub label: String,
    pub source: TagSource,
    /// Peak confidence percentage (`0..=100`).
    pub confidence: u8,
    /// Offset in seconds from the start of the clip when first seen.
    pub first_s: u32,
    /// Number of inferences during the clip that matched this tag.
    pub count: u32,
}

/// Accumulates detections during a clip and emits a deduplicated, sorted tag list.
#[derive(Debug, Default)]
pub struct TagAccumulator {
    tags: Vec<ClipTag>,
}

impl TagAccumulator {
    pub fn new() -> Self {
        Self::default()
    }

    pub fn clear(&mut self) {
        self.tags.clear();
    }

    pub fn record(&mut self, label: &str, source: TagSource, confidence: u8, offset_s: u32) {
        let label_clean = normalize_label(label);
        if label_clean.is_empty() || is_background_label(&label_clean) {
            return;
        }
        let conf = confidence.min(100);
        if let Some(existing) = self
            .tags
            .iter_mut()
            .find(|t| t.label == label_clean && t.source == source)
        {
            if conf > existing.confidence {
                existing.confidence = conf;
            }
            if offset_s < existing.first_s {
                existing.first_s = offset_s;
            }
            existing.count = existing.count.saturating_add(1);
            return;
        }
        if self.tags.len() >= MAX_TAGS_PER_CLIP {
            if let Some((min_idx, min_tag)) = self
                .tags
                .iter()
                .enumerate()
                .min_by_key(|(_, t)| (t.confidence, t.count))
            {
                if conf <= min_tag.confidence {
                    return;
                }
                self.tags.remove(min_idx);
            }
        }
        self.tags.push(ClipTag {
            label: label_clean,
            source,
            confidence: conf,
            first_s: offset_s,
            count: 1,
        });
    }

    /// Current distinct tag labels (sorted by confidence descending) for live status reporting.
    pub fn active_labels(&self) -> Vec<String> {
        let mut sorted = self.tags.clone();
        sorted.sort_by(|a, b| {
            b.confidence
                .cmp(&a.confidence)
                .then_with(|| a.label.cmp(&b.label))
        });
        let mut out = Vec::new();
        for tag in sorted {
            if !out.contains(&tag.label) {
                out.push(tag.label);
            }
        }
        out
    }

    /// Finalize into a sorted `Vec<ClipTag>` suitable for writing to `clip_NNNNNN.json`.
    pub fn finalize(&self) -> Vec<ClipTag> {
        let mut out = self.tags.clone();
        out.sort_by(|a, b| {
            b.confidence
                .cmp(&a.confidence)
                .then_with(|| b.count.cmp(&a.count))
                .then_with(|| a.label.cmp(&b.label))
        });
        out
    }
}

/// Normalize a model label into a clean, lowercase tag string safe for JSON and URL queries.
pub fn normalize_label(raw: &str) -> String {
    let trimmed = raw.trim().trim_matches('"').trim();
    // Many ImageNet/AudioSet labels have comma-separated synonyms ("jay, Cyanocitta cristata"
    // or "Bird vocalization, bird call, bird song"). Keep the primary display term.
    let primary = trimmed.split(',').next().unwrap_or(trimmed).trim();
    let mut out = String::with_capacity(primary.len().min(32));
    let mut last_was_space = false;
    for ch in primary.chars() {
        let lc = ch.to_ascii_lowercase();
        if lc.is_ascii_alphanumeric() || lc == '_' || lc == '-' {
            out.push(lc);
            last_was_space = false;
        } else if (lc == ' ' || lc == '/') && !out.is_empty() && !last_was_space {
            out.push(' ');
            last_was_space = true;
        }
        if out.len() >= 32 {
            break;
        }
    }
    out.trim().to_string()
}

/// Returns true for non-object background/silence placeholder classes that should not be tagged.
pub fn is_background_label(label: &str) -> bool {
    matches!(
        label,
        "" | "background" | "__background__" | "silence" | "unknown" | "none" | "other"
    )
}

/// Parse a label file from SD card.
///
/// Supports both:
/// - Plain newline-separated `labels.txt` (e.g. `imagenet_labels.txt`, with or without
///   leading numeric indices like `18  jay` or `0 background`).
/// - Google YAMNet CSV class maps (`index,mid,display_name`, e.g.
///   `70,/m/0bt9lr,Dog` or `111,/m/015p6,"Bird vocalization, bird call, bird song"`).
pub fn parse_labels_file(contents: &str) -> Vec<String> {
    let mut lines = contents.lines().peekable();
    let is_yamnet_csv = lines
        .peek()
        .is_some_and(|first| first.trim().eq_ignore_ascii_case("index,mid,display_name"));
    if is_yamnet_csv {
        lines.next();
    }

    let mut labels = Vec::new();
    for raw_line in lines {
        let line = raw_line.trim();
        if line.is_empty() {
            continue;
        }
        if is_yamnet_csv {
            // Format: index,mid,display_name (display_name may be quoted with commas).
            let mut parts = line.splitn(3, ',');
            let _idx = parts.next();
            let _mid = parts.next();
            let display = parts.next().unwrap_or("");
            labels.push(normalize_label(display));
        } else {
            // Strip optional leading integer index ("18  jay" -> "jay", "0: background" -> "background").
            let stripped = strip_leading_index(line);
            labels.push(normalize_label(stripped));
        }
    }
    labels
}

fn strip_leading_index(line: &str) -> &str {
    let bytes = line.as_bytes();
    let mut i = 0;
    while i < bytes.len() && bytes[i].is_ascii_digit() {
        i += 1;
    }
    if i > 0 && i < bytes.len() && matches!(bytes[i], b' ' | b'\t' | b':' | b',') {
        line[i + 1..].trim_start()
    } else {
        line
    }
}

/// Extract up to `max_tags` highest-scoring non-background tags with `score >= min_confidence`.
pub fn extract_top_tags(
    scores: &[f32],
    labels: &[String],
    min_confidence: f32,
    max_tags: usize,
) -> Vec<(String, u8)> {
    let mut candidates: Vec<(usize, f32)> = scores
        .iter()
        .enumerate()
        .filter(|&(i, &s)| {
            s.is_finite()
                && s >= min_confidence
                && labels
                    .get(i)
                    .is_some_and(|l| !l.is_empty() && !is_background_label(l))
        })
        .map(|(i, &s)| (i, s))
        .collect();

    candidates.sort_by(|a, b| b.1.total_cmp(&a.1));

    let mut out = Vec::new();
    for (idx, score) in candidates {
        if out.len() >= max_tags {
            break;
        }
        let label = &labels[idx];
        if out.iter().any(|(existing, _)| existing == label) {
            continue;
        }
        let pct = (score.clamp(0.0, 1.0) * 100.0).round() as u8;
        out.push((label.clone(), pct));
    }
    out
}

/// Expected input image dimensions inferred from a loaded vision `.tflite` model.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub struct VisionInputShape {
    pub width: usize,
    pub height: usize,
    pub channels: usize,
}

/// Infer `(width, height, channels)` from a TFLite tensor's `dims` (typically `[1, H, W, C]`).
pub fn infer_vision_input_shape(dims: &[i32]) -> Option<VisionInputShape> {
    match dims {
        [1, h, w, c] if *h > 0 && *w > 0 && (*c == 1 || *c == 3) => Some(VisionInputShape {
            width: *w as usize,
            height: *h as usize,
            channels: *c as usize,
        }),
        [h, w, c] if *h > 0 && *w > 0 && (*c == 1 || *c == 3) => Some(VisionInputShape {
            width: *w as usize,
            height: *h as usize,
            channels: *c as usize,
        }),
        _ => None,
    }
}

/// Expected input format inferred from a loaded audio `.tflite` model.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum AudioInputKind {
    /// 2D log-mel spectrogram patch `[1, frames, mel_bins]` or `[1, frames, mel_bins, 1]`.
    /// (YAMNet TFLite Micro uses `frames = 96, mel_bins = 64`.)
    MelSpectrogram { frames: usize, mel_bins: usize },
    /// 1D normalized PCM waveform `[1, samples]` or `[samples]` at 16 kHz.
    RawWaveform { samples: usize },
}

/// Infer whether an audio `.tflite` model expects a log-mel spectrogram patch or raw 1D PCM.
pub fn infer_audio_input_kind(dims: &[i32]) -> Option<AudioInputKind> {
    match dims {
        [1, frames, bins, 1] if *frames >= 8 && *bins >= 16 => {
            Some(AudioInputKind::MelSpectrogram {
                frames: *frames as usize,
                mel_bins: *bins as usize,
            })
        }
        [1, frames, bins] if *frames >= 8 && *bins >= 16 => Some(AudioInputKind::MelSpectrogram {
            frames: *frames as usize,
            mel_bins: *bins as usize,
        }),
        [1, samples] if *samples >= 256 => Some(AudioInputKind::RawWaveform {
            samples: *samples as usize,
        }),
        [samples] if *samples >= 256 => Some(AudioInputKind::RawWaveform {
            samples: *samples as usize,
        }),
        _ => None,
    }
}

/// YAMNet-compatible log-mel spectrogram extractor (16 kHz mono PCM -> `[frames × mel_bins]` f32).
///
/// Matches Google YAMNet / `chayuto/yamnet-mel-int8-tflm`:
/// - Sample rate: 16 kHz mono
/// - Frame window: 400 samples (25 ms) periodic Hann window
/// - Frame hop: 160 samples (10 ms)
/// - FFT size: 512 (257 magnitude/power bins)
/// - Mel filterbank: HTK triangular bands from 125 Hz to 7500 Hz
/// - Log compression: `ln(mel_energy + 1e-10)`
pub struct MelSpectrogramExtractor {
    num_frames: usize,
    hop_frames: usize,
    num_mel_bins: usize,
    hann: [f32; Self::WIN_LEN],
    /// Precomputed sparse triangular mel weights: `(fft_bin, weight)` per mel band.
    mel_filters: Vec<Vec<(usize, f32)>>,
    /// Rolling PCM sample buffer (retains overlap between STFT hops).
    pcm_buf: Vec<f32>,
    /// Rolling ring of computed log-mel frames (`frames.len() <= num_frames`).
    frames: Vec<Vec<f32>>,
    frames_since_emit: usize,
}

impl MelSpectrogramExtractor {
    pub const SAMPLE_RATE: f32 = 16_000.0;
    pub const WIN_LEN: usize = 400;
    pub const HOP_LEN: usize = 160;
    pub const FFT_LEN: usize = 512;
    pub const MEL_LOW_HZ: f32 = 125.0;
    pub const MEL_HIGH_HZ: f32 = 7500.0;
    pub const LOG_OFFSET: f32 = 1e-10;

    pub fn new(num_frames: usize, num_mel_bins: usize) -> Self {
        let mut hann = [0.0f32; Self::WIN_LEN];
        for (i, w) in hann.iter_mut().enumerate() {
            // Periodic Hann window matching tf.signal.hann_window(400, periodic=True).
            *w = 0.5 - 0.5 * (2.0 * PI * i as f32 / Self::WIN_LEN as f32).cos();
        }
        let mel_filters = build_htk_mel_filterbank(
            Self::FFT_LEN,
            Self::SAMPLE_RATE,
            num_mel_bins,
            Self::MEL_LOW_HZ,
            Self::MEL_HIGH_HZ,
        );
        Self {
            num_frames: num_frames.max(1),
            hop_frames: (num_frames / 2).max(1),
            num_mel_bins: num_mel_bins.max(1),
            hann,
            mel_filters,
            pcm_buf: Vec::with_capacity(Self::WIN_LEN * 4),
            frames: Vec::with_capacity(num_frames),
            frames_since_emit: 0,
        }
    }

    /// Clear buffered audio/frames at the start of a new clip.
    pub fn reset(&mut self) {
        self.pcm_buf.clear();
        self.frames.clear();
        self.frames_since_emit = 0;
    }

    /// Push 16-bit signed little-endian mono PCM bytes (at 16 kHz).
    ///
    /// Returns `Some(patch)` containing `num_frames * num_mel_bins` float32 log-mel values
    /// whenever a new patch is ready (every `num_frames / 2` frames, i.e., ~0.48 s for YAMNet).
    pub fn push_pcm_le16(&mut self, pcm_le16: &[u8]) -> Option<Vec<f32>> {
        for &chunk in pcm_le16.as_chunks::<2>().0 {
            let s = i16::from_le_bytes(chunk) as f32 / 32768.0;
            self.pcm_buf.push(s);
        }

        let mut latest_patch = None;
        while self.pcm_buf.len() >= Self::WIN_LEN {
            let frame = self.compute_mel_frame(&self.pcm_buf[..Self::WIN_LEN]);
            self.pcm_buf.drain(..Self::HOP_LEN);

            if self.frames.len() == self.num_frames {
                self.frames.remove(0);
            }
            self.frames.push(frame);
            self.frames_since_emit += 1;

            if self.frames.len() == self.num_frames && self.frames_since_emit >= self.hop_frames {
                self.frames_since_emit = 0;
                let mut patch = Vec::with_capacity(self.num_frames * self.num_mel_bins);
                for f in &self.frames {
                    patch.extend_from_slice(f);
                }
                latest_patch = Some(patch);
            }
        }
        latest_patch
    }

    fn compute_mel_frame(&self, samples: &[f32]) -> Vec<f32> {
        let mut re = [0.0f32; Self::FFT_LEN];
        let mut im = [0.0f32; Self::FFT_LEN];
        for i in 0..Self::WIN_LEN {
            re[i] = samples[i] * self.hann[i];
        }
        fft_radix2_inplace(&mut re, &mut im);

        let n_bins = Self::FFT_LEN / 2 + 1;
        let mut power = [0.0f32; Self::FFT_LEN / 2 + 1];
        for k in 0..n_bins {
            power[k] = re[k] * re[k] + im[k] * im[k];
        }

        let mut mel = Vec::with_capacity(self.num_mel_bins);
        for filter in &self.mel_filters {
            let mut sum = 0.0f32;
            for &(bin, weight) in filter {
                sum += power[bin] * weight;
            }
            mel.push((sum + Self::LOG_OFFSET).ln());
        }
        mel
    }
}

fn hz_to_htk_mel(hz: f32) -> f32 {
    2595.0 * (1.0 + hz / 700.0).log10()
}

fn htk_mel_to_hz(mel: f32) -> f32 {
    700.0 * (10.0f32.powf(mel / 2595.0) - 1.0)
}

fn build_htk_mel_filterbank(
    fft_len: usize,
    sample_rate: f32,
    num_mel_bins: usize,
    low_hz: f32,
    high_hz: f32,
) -> Vec<Vec<(usize, f32)>> {
    let n_fft_bins = fft_len / 2 + 1;
    let low_mel = hz_to_htk_mel(low_hz);
    let high_mel = hz_to_htk_mel(high_hz);

    let mut band_edges_hz = Vec::with_capacity(num_mel_bins + 2);
    for i in 0..(num_mel_bins + 2) {
        let m = low_mel + (high_mel - low_mel) * (i as f32) / ((num_mel_bins + 1) as f32);
        band_edges_hz.push(htk_mel_to_hz(m));
    }

    let mut filters = Vec::with_capacity(num_mel_bins);
    for m in 0..num_mel_bins {
        let f_left = band_edges_hz[m];
        let f_center = band_edges_hz[m + 1];
        let f_right = band_edges_hz[m + 2];
        let mut weights = Vec::new();
        for k in 0..n_fft_bins {
            let freq = (k as f32) * sample_rate / (fft_len as f32);
            let w = if freq >= f_left && freq <= f_center && f_center > f_left {
                (freq - f_left) / (f_center - f_left)
            } else if freq > f_center && freq <= f_right && f_right > f_center {
                (f_right - freq) / (f_right - f_center)
            } else {
                0.0
            };
            if w > 0.0 {
                weights.push((k, w));
            }
        }
        filters.push(weights);
    }
    filters
}

/// In-place iterative radix-2 Cooley-Tukey FFT (`re.len() == im.len()`, power of 2).
fn fft_radix2_inplace(re: &mut [f32], im: &mut [f32]) {
    let n = re.len();
    debug_assert!(n.is_power_of_two() && im.len() == n);

    // Bit-reversal permutation.
    let mut j = 0usize;
    for i in 1..n {
        let mut bit = n >> 1;
        while (j & bit) != 0 {
            j ^= bit;
            bit >>= 1;
        }
        j ^= bit;
        if i < j {
            re.swap(i, j);
            im.swap(i, j);
        }
    }

    let mut len = 2;
    while len <= n {
        let half = len / 2;
        let angle = -2.0 * PI / (len as f32);
        let wlen_re = angle.cos();
        let wlen_im = angle.sin();
        let mut start = 0;
        while start < n {
            let mut w_re = 1.0f32;
            let mut w_im = 0.0f32;
            for k in 0..half {
                let u_re = re[start + k];
                let u_im = im[start + k];
                let v_re = re[start + k + half] * w_re - im[start + k + half] * w_im;
                let v_im = re[start + k + half] * w_im + im[start + k + half] * w_re;
                re[start + k] = u_re + v_re;
                im[start + k] = u_im + v_im;
                re[start + k + half] = u_re - v_re;
                im[start + k + half] = u_im - v_im;

                let next_w_re = w_re * wlen_re - w_im * wlen_im;
                w_im = w_re * wlen_im + w_im * wlen_re;
                w_re = next_w_re;
            }
            start += len;
        }
        len <<= 1;
    }
}

/// Format a clip's sidecar JSON (`clip_NNNNNN.json`).
pub fn format_clip_sidecar_json(tags: &[ClipTag]) -> String {
    format!(r#"{{"tags":{}}}"#, format_tags_array_json(tags))
}

/// Format a JSON array of `ClipTag` objects (`[...]`).
pub fn format_tags_array_json(tags: &[ClipTag]) -> String {
    let mut out = String::from("[");
    format_tags_array_into(&mut out, tags);
    out.push(']');
    out
}

/// Append a JSON array body of `ClipTag` objects (without surrounding `[` `]`).
pub fn format_tags_array_into(out: &mut String, tags: &[ClipTag]) {
    for (i, tag) in tags.iter().enumerate() {
        if i > 0 {
            out.push(',');
        }
        out.push_str(&format!(
            r#"{{"label":"{}","source":"{}","confidence":{},"first_s":{},"count":{}}}"#,
            json_escape_tag(&tag.label),
            tag.source.as_str(),
            tag.confidence,
            tag.first_s,
            tag.count,
        ));
    }
}

/// Parse a clip sidecar JSON (`{"tags":[...]}`) produced by [`format_clip_sidecar_json`].
///
/// Minimal zero-dependency parser so firmware stays small and host tests verify exact round-trip.
pub fn parse_clip_sidecar_json(input: &str) -> Vec<ClipTag> {
    let mut out = Vec::new();
    let Some(tags_pos) = input.find("\"tags\"") else {
        return out;
    };
    let rest = &input[tags_pos + 6..];
    let Some(arr_start) = rest.find('[') else {
        return out;
    };
    let Some(arr_end) = rest[arr_start..].find(']') else {
        return out;
    };
    let mut slice = &rest[arr_start + 1..arr_start + arr_end];
    while let Some(obj_start) = slice.find('{') {
        let Some(obj_end) = slice[obj_start..].find('}') else {
            break;
        };
        let obj = &slice[obj_start + 1..obj_start + obj_end];
        if let Some(tag) = parse_tag_object(obj) {
            out.push(tag);
        }
        slice = &slice[obj_start + obj_end + 1..];
    }
    out
}

fn parse_tag_object(obj: &str) -> Option<ClipTag> {
    let label = extract_json_string(obj, "label")?;
    let source_str = extract_json_string(obj, "source")?;
    let source = TagSource::parse(&source_str)?;
    let confidence = extract_json_u32(obj, "confidence")?.min(100) as u8;
    let first_s = extract_json_u32(obj, "first_s").unwrap_or(0);
    let count = extract_json_u32(obj, "count").unwrap_or(1);
    Some(ClipTag {
        label,
        source,
        confidence,
        first_s,
        count,
    })
}

fn extract_json_string(obj: &str, key: &str) -> Option<String> {
    let needle = format!("\"{key}\"");
    let pos = obj.find(&needle)?;
    let after = &obj[pos + needle.len()..];
    let colon = after.find(':')?;
    let val = after[colon + 1..].trim_start();
    let val = val.strip_prefix('"')?;
    let end = val.find('"')?;
    Some(val[..end].to_string())
}

fn extract_json_u32(obj: &str, key: &str) -> Option<u32> {
    let needle = format!("\"{key}\"");
    let pos = obj.find(&needle)?;
    let after = &obj[pos + needle.len()..];
    let colon = after.find(':')?;
    let val = after[colon + 1..].trim_start();
    let end = val.find(|c: char| !c.is_ascii_digit()).unwrap_or(val.len());
    val[..end].parse::<u32>().ok()
}

fn json_escape_tag(s: &str) -> String {
    let mut out = String::with_capacity(s.len());
    for ch in s.chars() {
        match ch {
            '"' => out.push_str("\\\""),
            '\\' => out.push_str("\\\\"),
            '\n' | '\r' | '\t' => out.push(' '),
            c if c.is_control() => {}
            c => out.push(c),
        }
    }
    out
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn parse_labels_handles_imagenet_txt_and_yamnet_csv() {
        let imagenet = "0  background\n18  jay\n207  golden retriever, Canis familiaris\n";
        let labels = parse_labels_file(imagenet);
        assert_eq!(labels, vec!["background", "jay", "golden retriever"]);

        let yamnet = concat!(
            "index,mid,display_name\n",
            "0,/m/09x0r,Speech\n",
            "70,/m/0bt9lr,Dog\n",
            "71,/m/05tny_,Bark\n",
            "111,/m/015p6,\"Bird vocalization, bird call, bird song\"\n",
            "494,/m/028v0c,Silence\n",
        );
        let audio_labels = parse_labels_file(yamnet);
        assert_eq!(
            audio_labels,
            vec!["speech", "dog", "bark", "bird vocalization", "silence"]
        );
    }

    #[test]
    fn extract_top_tags_filters_background_and_sorts() {
        let labels = vec![
            "background".to_string(),
            "jay".to_string(),
            "golden retriever".to_string(),
            "silence".to_string(),
        ];
        let scores = [0.95, 0.72, 0.88, 0.99];
        let tags = extract_top_tags(&scores, &labels, 0.50, 3);
        assert_eq!(
            tags,
            vec![
                ("golden retriever".to_string(), 88),
                ("jay".to_string(), 72)
            ]
        );
    }

    #[test]
    fn infer_model_input_shapes() {
        assert_eq!(
            infer_vision_input_shape(&[1, 128, 128, 3]),
            Some(VisionInputShape {
                width: 128,
                height: 128,
                channels: 3,
            })
        );
        assert_eq!(
            infer_audio_input_kind(&[1, 96, 64]),
            Some(AudioInputKind::MelSpectrogram {
                frames: 96,
                mel_bins: 64,
            })
        );
        assert_eq!(
            infer_audio_input_kind(&[1, 96, 64, 1]),
            Some(AudioInputKind::MelSpectrogram {
                frames: 96,
                mel_bins: 64,
            })
        );
        assert_eq!(
            infer_audio_input_kind(&[1, 15600]),
            Some(AudioInputKind::RawWaveform { samples: 15600 })
        );
    }

    #[test]
    fn mel_spectrogram_extractor_emits_yamnet_patch_with_peak_at_tone() {
        let mut ext = MelSpectrogramExtractor::new(96, 64);
        // Generate 1.1 seconds of 16 kHz PCM containing a pure 1000 Hz sine wave.
        let n_samples = 17_600;
        let mut pcm = Vec::with_capacity(n_samples * 2);
        for i in 0..n_samples {
            let t = i as f32 / 16_000.0;
            let s = ((2.0 * PI * 1000.0 * t).sin() * 16_000.0) as i16;
            pcm.extend_from_slice(&s.to_le_bytes());
        }

        let patch = ext
            .push_pcm_le16(&pcm)
            .expect("1.1s of 16 kHz audio should produce a 96x64 patch");
        assert_eq!(patch.len(), 96 * 64);

        // Verify the energy peak in the middle frame is near the 1000 Hz mel bin (~bin 18-24),
        // well above the quiet bins at the edges.
        let mid_frame = &patch[48 * 64..49 * 64];
        let (peak_bin, &peak_val) = mid_frame
            .iter()
            .enumerate()
            .max_by(|a, b| a.1.total_cmp(b.1))
            .unwrap();
        assert!(
            (15..=26).contains(&peak_bin),
            "expected 1 kHz peak around mel bin 18-24, got bin {peak_bin}"
        );
        assert!(peak_val > mid_frame[0] + 5.0);
        assert!(peak_val > mid_frame[63] + 5.0);
    }

    #[test]
    fn sidecar_json_round_trips_tags() {
        let mut acc = TagAccumulator::new();
        acc.record("Jay", TagSource::Vision, 84, 12);
        acc.record("jay", TagSource::Vision, 91, 20);
        acc.record("Bark", TagSource::Audio, 78, 5);
        let tags = acc.finalize();
        let json = format_clip_sidecar_json(&tags);
        let parsed = parse_clip_sidecar_json(&json);
        assert_eq!(parsed, tags);
        assert_eq!(parsed[0].label, "jay");
        assert_eq!(parsed[0].confidence, 91);
        assert_eq!(parsed[0].first_s, 12);
        assert_eq!(parsed[0].count, 2);
    }
}
