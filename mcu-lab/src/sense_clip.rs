//! Host-safe QuickTime `.mov` (MJPEG + 16-bit PCM) clip muxer, SD ring-buffer
//! eviction planner, HTTP `Range` parser, and JSON API formatters for the
//! XIAO ESP32-S3 Sense A/V recorder app.
//!
//! Keeping all container muxing, storage retention, and HTTP wire logic in this
//! host-safe module allows `cargo test --lib` to verify every byte on the host
//! without needing the ESP-IDF toolchain.

use std::io::{self, Seek, SeekFrom, Write};

/// On-wire / log identifier for the XIAO ESP32-S3 Sense A/V recorder app.
pub const RECORDER_FIRMWARE_ID: &str = "xiao-esp32s3-sense-recorder/0.1";

/// Target duration of each recorded audio+video clip in seconds (1 minute).
pub const CLIP_DURATION_SECS: u32 = 60;

/// Default PDM microphone sample rate (16 kHz, 16-bit signed LE mono = 32 KB/s).
pub const DEFAULT_AUDIO_SAMPLE_RATE: u32 = 16_000;

/// Default camera frame dimensions (VGA 640×480 JPEG).
pub const DEFAULT_VIDEO_WIDTH: u16 = 640;
pub const DEFAULT_VIDEO_HEIGHT: u16 = 480;

/// Maximum free-space headroom we keep available on the SD card (64 MiB).
pub const MIN_FREE_BYTES_CAP: u64 = 64 * 1024 * 1024;

/// Default SoftAP SSID and IPv4 address when no Wi-Fi STA credentials are set.
pub const DEFAULT_SOFTAP_SSID: &str = "XIAO-S3-Sense";
pub const DEFAULT_SOFTAP_IP: &str = "192.168.4.1";

/// QuickTime `ftyp` atom size (`qt  ` brand, 20 bytes).
const FTYP_LEN: u64 = 20;
/// Size of a standard 32-bit QuickTime atom header (`size` + `fourcc`).
const ATOM_HDR_LEN: u64 = 8;

/// Format a finalized clip filename for sequence number `seq` (`clip_000001.mov`).
pub fn format_clip_name(seq: u32) -> String {
    format!("clip_{seq:06}.mov")
}

/// Format an in-progress temporary clip filename (`clip_000001.tmp`).
pub fn format_temp_clip_name(seq: u32) -> String {
    format!("clip_{seq:06}.tmp")
}

/// Parse a finalized clip filename (`clip_NNNNNN.mov`) and return its sequence number.
///
/// Rejects path separators, relative segments, temporary files, and malformed names.
pub fn parse_clip_seq(name: &str) -> Option<u32> {
    let rest = name.strip_prefix("clip_")?;
    let digits = rest.strip_suffix(".mov")?;
    if digits.len() != 6 || !digits.bytes().all(|b| b.is_ascii_digit()) {
        return None;
    }
    digits.parse::<u32>().ok()
}

/// Returns true iff `name` is a strictly valid finalized clip filename (`clip_NNNNNN.mov`).
pub fn is_valid_clip_name(name: &str) -> bool {
    parse_clip_seq(name).is_some()
}

/// Returns true iff `name` is a temporary in-progress clip filename (`clip_NNNNNN.tmp`).
pub fn is_temp_clip_name(name: &str) -> bool {
    let Some(rest) = name.strip_prefix("clip_") else {
        return false;
    };
    let Some(digits) = rest.strip_suffix(".tmp") else {
        return false;
    };
    digits.len() == 6 && digits.bytes().all(|b| b.is_ascii_digit())
}

/// Choose the next monotonic clip sequence number given existing clip filenames.
pub fn next_clip_seq<S: AsRef<str>>(existing_names: &[S]) -> u32 {
    existing_names
        .iter()
        .filter_map(|s| parse_clip_seq(s.as_ref()))
        .max()
        .map_or(1, |m| m.saturating_add(1))
}

/// Metadata for a single finalized clip stored on the SD card.
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct ClipEntry {
    pub name: String,
    pub seq: u32,
    pub size_bytes: u64,
    pub duration_s: u32,
}

/// Compute target free-space headroom to keep available on an SD card of size `total_bytes`.
///
/// Uses `min(64 MiB, total_bytes / 4)` so large cards keep a comfortable 64 MiB buffer
/// while small cards still leave room for several clips.
pub fn required_free_bytes(total_bytes: u64) -> u64 {
    if total_bytes == 0 {
        return 0;
    }
    (total_bytes / 4).min(MIN_FREE_BYTES_CAP)
}

/// Plan which oldest clip filenames must be deleted to reach `required_free` bytes free.
///
/// Returns clip names in deletion order (oldest `seq` first).
pub fn plan_evictions(clips: &[ClipEntry], free_bytes: u64, required_free: u64) -> Vec<String> {
    if free_bytes >= required_free {
        return Vec::new();
    }
    let mut ordered: Vec<&ClipEntry> = clips.iter().collect();
    ordered.sort_by_key(|c| c.seq);

    let mut projected_free = free_bytes;
    let mut to_delete = Vec::new();
    for clip in ordered {
        if projected_free >= required_free {
            break;
        }
        to_delete.push(clip.name.clone());
        projected_free = projected_free.saturating_add(clip.size_bytes);
    }
    to_delete
}

/// Inclusive byte range `[start, end]` for HTTP `206 Partial Content` responses.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub struct ByteRange {
    pub start: u64,
    pub end: u64,
}

impl ByteRange {
    /// Number of bytes in this inclusive range.
    pub const fn len(&self) -> u64 {
        self.end - self.start + 1
    }

    pub const fn is_empty(&self) -> bool {
        false
    }
}

/// Parse a single HTTP `Range: bytes=...` header value against a resource of `total_size` bytes.
///
/// Supports `bytes=start-end`, `bytes=start-`, and `bytes=-suffix_len`.
/// Returns `None` for malformed, multi-range, or unsatisfiable ranges.
pub fn parse_byte_range(header: &str, total_size: u64) -> Option<ByteRange> {
    if total_size == 0 {
        return None;
    }
    let spec = header.trim().strip_prefix("bytes=")?.trim();
    if spec.contains(',') {
        return None;
    }
    let (start_s, end_s) = spec.split_once('-')?;
    let start_s = start_s.trim();
    let end_s = end_s.trim();

    if start_s.is_empty() {
        // Suffix range: `bytes=-N`
        let suffix = end_s.parse::<u64>().ok()?;
        if suffix == 0 {
            return None;
        }
        let start = total_size.saturating_sub(suffix);
        return Some(ByteRange {
            start,
            end: total_size - 1,
        });
    }

    let start = start_s.parse::<u64>().ok()?;
    if start >= total_size {
        return None;
    }
    let end = if end_s.is_empty() {
        total_size - 1
    } else {
        let parsed = end_s.parse::<u64>().ok()?;
        if parsed < start {
            return None;
        }
        parsed.min(total_size - 1)
    };
    Some(ByteRange { start, end })
}

/// One recorded JPEG video frame inside the `mdat` payload.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub struct VideoSample {
    pub offset: u32,
    pub size: u32,
    pub duration_ms: u32,
}

/// One recorded 16-bit LE mono PCM audio chunk inside the `mdat` payload.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub struct AudioChunk {
    pub offset: u32,
    pub sample_count: u32,
}

/// Summary returned when [`MovMuxer::finalize`] completes.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub struct MovSummary {
    pub video_frames: usize,
    pub audio_samples: u64,
    pub duration_ms: u32,
    pub total_bytes: u64,
}

/// Streaming QuickTime `.mov` muxer for Photo-JPEG (`jpeg`) video + 16-bit LE PCM (`sowt`) audio.
///
/// Writes `ftyp` + `mdat` sequentially while recording, keeping only compact per-frame
/// offset tables in RAM/PSRAM, then patches `mdat` size and appends the `moov` atom at
/// finalize time. iOS `AVPlayer` plays these `.mov` files natively over HTTP byte-range
/// requests (`Accept-Ranges: bytes` / `206 Partial Content`).
pub struct MovMuxer<W: Write + Seek> {
    writer: W,
    width: u16,
    height: u16,
    audio_sample_rate: u32,
    pos: u64,
    video_samples: Vec<VideoSample>,
    audio_chunks: Vec<AudioChunk>,
}

impl<W: Write + Seek> MovMuxer<W> {
    /// Start a new `.mov` file by writing the `ftyp` atom and `mdat` header placeholder.
    pub fn begin(
        mut writer: W,
        width: u16,
        height: u16,
        audio_sample_rate: u32,
    ) -> io::Result<Self> {
        let mut ftyp = Vec::with_capacity(FTYP_LEN as usize);
        ftyp.extend_from_slice(&(FTYP_LEN as u32).to_be_bytes());
        ftyp.extend_from_slice(b"ftyp");
        ftyp.extend_from_slice(b"qt  ");
        ftyp.extend_from_slice(&0x0000_0200u32.to_be_bytes());
        ftyp.extend_from_slice(b"qt  ");
        writer.write_all(&ftyp)?;

        // `mdat` header placeholder (size patched on finalize).
        writer.write_all(&0u32.to_be_bytes())?;
        writer.write_all(b"mdat")?;

        Ok(Self {
            writer,
            width,
            height,
            audio_sample_rate,
            pos: FTYP_LEN + ATOM_HDR_LEN,
            video_samples: Vec::new(),
            audio_chunks: Vec::new(),
        })
    }

    /// Append one JPEG video frame to `mdat`.
    pub fn write_video_frame(&mut self, jpeg: &[u8], duration_ms: u32) -> io::Result<()> {
        if jpeg.is_empty() {
            return Ok(());
        }
        let offset = u32::try_from(self.pos)
            .map_err(|_| io::Error::other("mov file exceeded 4 GiB offset limit"))?;
        let size = u32::try_from(jpeg.len())
            .map_err(|_| io::Error::other("jpeg frame exceeded u32 size"))?;
        self.writer.write_all(jpeg)?;
        self.pos = self.pos.saturating_add(jpeg.len() as u64);
        self.video_samples.push(VideoSample {
            offset,
            size,
            duration_ms: duration_ms.max(1),
        });
        Ok(())
    }

    /// Append one chunk of 16-bit signed little-endian mono PCM audio samples to `mdat`.
    pub fn write_audio_pcm(&mut self, pcm_le16: &[u8]) -> io::Result<()> {
        let even_len = pcm_le16.len() & !1;
        if even_len == 0 {
            return Ok(());
        }
        let offset = u32::try_from(self.pos)
            .map_err(|_| io::Error::other("mov file exceeded 4 GiB offset limit"))?;
        let sample_count = u32::try_from(even_len / 2)
            .map_err(|_| io::Error::other("audio chunk exceeded u32 sample count"))?;
        self.writer.write_all(&pcm_le16[..even_len])?;
        self.pos = self.pos.saturating_add(even_len as u64);
        self.audio_chunks.push(AudioChunk {
            offset,
            sample_count,
        });
        Ok(())
    }

    /// Current number of video frames written so far.
    pub fn video_frame_count(&self) -> usize {
        self.video_samples.len()
    }

    /// Current byte size written to the underlying file so far.
    pub fn bytes_written(&self) -> u64 {
        self.pos
    }

    /// Patch the `mdat` atom size, write the `moov` metadata atom, and flush the writer.
    pub fn finalize(mut self) -> io::Result<MovSummary> {
        let mdat_size = u32::try_from(self.pos - FTYP_LEN)
            .map_err(|_| io::Error::other("mdat exceeded 4 GiB limit"))?;

        // Patch `mdat` size field right after `ftyp`.
        self.writer.seek(SeekFrom::Start(FTYP_LEN))?;
        self.writer.write_all(&mdat_size.to_be_bytes())?;

        // Seek back to end of `mdat` and append `moov`.
        self.writer.seek(SeekFrom::Start(self.pos))?;
        let moov = build_moov_atom(
            self.width,
            self.height,
            self.audio_sample_rate,
            &self.video_samples,
            &self.audio_chunks,
        );
        self.writer.write_all(&moov)?;
        self.writer.flush()?;

        let video_dur_ms: u32 = self
            .video_samples
            .iter()
            .fold(0u32, |acc, s| acc.saturating_add(s.duration_ms));
        let audio_samples: u64 = self
            .audio_chunks
            .iter()
            .map(|c| u64::from(c.sample_count))
            .sum();
        let audio_dur_ms = if self.audio_sample_rate > 0 {
            ((audio_samples * 1000) / u64::from(self.audio_sample_rate)).min(u64::from(u32::MAX))
                as u32
        } else {
            0
        };
        let duration_ms = video_dur_ms.max(audio_dur_ms);
        let total_bytes = self.pos.saturating_add(moov.len() as u64);

        Ok(MovSummary {
            video_frames: self.video_samples.len(),
            audio_samples,
            duration_ms,
            total_bytes,
        })
    }
}

fn wrap_atom(fourcc: &[u8; 4], payload: &[u8]) -> Vec<u8> {
    let size = (8 + payload.len()) as u32;
    let mut out = Vec::with_capacity(size as usize);
    out.extend_from_slice(&size.to_be_bytes());
    out.extend_from_slice(fourcc);
    out.extend_from_slice(payload);
    out
}

fn build_dinf_atom() -> Vec<u8> {
    // Self-contained `url ` entry (flags = 0x000001).
    let url = wrap_atom(b"url ", &[0, 0, 0, 1]);
    let mut dref_payload = Vec::with_capacity(8 + url.len());
    dref_payload.extend_from_slice(&0u32.to_be_bytes()); // version + flags
    dref_payload.extend_from_slice(&1u32.to_be_bytes()); // entry count
    dref_payload.extend_from_slice(&url);
    let dref = wrap_atom(b"dref", &dref_payload);
    wrap_atom(b"dinf", &dref)
}

fn build_hdlr_atom(subtype: &[u8; 4], name: &[u8]) -> Vec<u8> {
    let mut p = Vec::with_capacity(24 + name.len() + 1);
    p.extend_from_slice(&0u32.to_be_bytes()); // version + flags
    p.extend_from_slice(b"mhlr"); // QuickTime component type
    p.extend_from_slice(subtype); // `vide` or `soun`
    p.extend_from_slice(&[0u8; 12]); // manufacturer + flags + mask
    p.push(name.len() as u8); // Pascal string length
    p.extend_from_slice(name);
    wrap_atom(b"hdlr", &p)
}

fn build_mvhd_atom(timescale: u32, duration: u32, next_track_id: u32) -> Vec<u8> {
    let mut p = Vec::with_capacity(100);
    p.extend_from_slice(&0u32.to_be_bytes()); // version 0 + flags
    p.extend_from_slice(&0u32.to_be_bytes()); // creation time
    p.extend_from_slice(&0u32.to_be_bytes()); // modification time
    p.extend_from_slice(&timescale.to_be_bytes());
    p.extend_from_slice(&duration.to_be_bytes());
    p.extend_from_slice(&0x0001_0000u32.to_be_bytes()); // preferred rate 1.0
    p.extend_from_slice(&0x0100u16.to_be_bytes()); // preferred volume 1.0
    p.extend_from_slice(&[0u8; 10]); // reserved
                                     // Identity 3x3 matrix (36 bytes)
    p.extend_from_slice(&0x0001_0000u32.to_be_bytes());
    p.extend_from_slice(&0u32.to_be_bytes());
    p.extend_from_slice(&0u32.to_be_bytes());
    p.extend_from_slice(&0u32.to_be_bytes());
    p.extend_from_slice(&0x0001_0000u32.to_be_bytes());
    p.extend_from_slice(&0u32.to_be_bytes());
    p.extend_from_slice(&0u32.to_be_bytes());
    p.extend_from_slice(&0u32.to_be_bytes());
    p.extend_from_slice(&0x4000_0000u32.to_be_bytes());
    p.extend_from_slice(&[0u8; 24]); // preview / poster / selection / current time
    p.extend_from_slice(&next_track_id.to_be_bytes());
    wrap_atom(b"mvhd", &p)
}

fn build_tkhd_atom(
    track_id: u32,
    duration_ms: u32,
    width: u16,
    height: u16,
    volume: u16,
) -> Vec<u8> {
    let mut p = Vec::with_capacity(84);
    p.extend_from_slice(&0x0000_000Fu32.to_be_bytes()); // version 0, flags: enabled|in_movie|in_preview|in_poster
    p.extend_from_slice(&0u32.to_be_bytes()); // creation time
    p.extend_from_slice(&0u32.to_be_bytes()); // modification time
    p.extend_from_slice(&track_id.to_be_bytes());
    p.extend_from_slice(&0u32.to_be_bytes()); // reserved
    p.extend_from_slice(&duration_ms.to_be_bytes());
    p.extend_from_slice(&[0u8; 8]); // reserved
    p.extend_from_slice(&0u16.to_be_bytes()); // layer
    p.extend_from_slice(&0u16.to_be_bytes()); // alternate group
    p.extend_from_slice(&volume.to_be_bytes());
    p.extend_from_slice(&0u16.to_be_bytes()); // reserved
                                              // Identity 3x3 matrix
    p.extend_from_slice(&0x0001_0000u32.to_be_bytes());
    p.extend_from_slice(&0u32.to_be_bytes());
    p.extend_from_slice(&0u32.to_be_bytes());
    p.extend_from_slice(&0u32.to_be_bytes());
    p.extend_from_slice(&0x0001_0000u32.to_be_bytes());
    p.extend_from_slice(&0u32.to_be_bytes());
    p.extend_from_slice(&0u32.to_be_bytes());
    p.extend_from_slice(&0u32.to_be_bytes());
    p.extend_from_slice(&0x4000_0000u32.to_be_bytes());
    p.extend_from_slice(&(u32::from(width) << 16).to_be_bytes());
    p.extend_from_slice(&(u32::from(height) << 16).to_be_bytes());
    wrap_atom(b"tkhd", &p)
}

fn build_mdhd_atom(timescale: u32, duration: u32) -> Vec<u8> {
    let mut p = Vec::with_capacity(24);
    p.extend_from_slice(&0u32.to_be_bytes()); // version 0 + flags
    p.extend_from_slice(&0u32.to_be_bytes()); // creation time
    p.extend_from_slice(&0u32.to_be_bytes()); // modification time
    p.extend_from_slice(&timescale.to_be_bytes());
    p.extend_from_slice(&duration.to_be_bytes());
    p.extend_from_slice(&0u16.to_be_bytes()); // language (English/und)
    p.extend_from_slice(&0u16.to_be_bytes()); // quality
    wrap_atom(b"mdhd", &p)
}

fn build_video_trak(width: u16, height: u16, samples: &[VideoSample]) -> Vec<u8> {
    let video_dur_ms: u32 = samples
        .iter()
        .fold(0u32, |acc, s| acc.saturating_add(s.duration_ms));

    let tkhd = build_tkhd_atom(1, video_dur_ms, width, height, 0);
    let mdhd = build_mdhd_atom(1000, video_dur_ms);
    let hdlr = build_hdlr_atom(b"vide", b"VideoHandler");

    // `vmhd` (version 0, flags = 1)
    let mut vmhd_p = Vec::with_capacity(12);
    vmhd_p.extend_from_slice(&1u32.to_be_bytes());
    vmhd_p.extend_from_slice(&[0u8; 8]);
    let vmhd = wrap_atom(b"vmhd", &vmhd_p);

    let dinf = build_dinf_atom();

    // `stsd` with one `jpeg` (Photo-JPEG) visual sample entry (86 bytes total).
    let mut jpeg_entry = Vec::with_capacity(78);
    jpeg_entry.extend_from_slice(&[0u8; 6]); // reserved
    jpeg_entry.extend_from_slice(&1u16.to_be_bytes()); // data reference index
    jpeg_entry.extend_from_slice(&0u16.to_be_bytes()); // version
    jpeg_entry.extend_from_slice(&0u16.to_be_bytes()); // revision
    jpeg_entry.extend_from_slice(b"appl"); // vendor
    jpeg_entry.extend_from_slice(&0u32.to_be_bytes()); // temporal quality
    jpeg_entry.extend_from_slice(&0x0000_0200u32.to_be_bytes()); // spatial quality
    jpeg_entry.extend_from_slice(&width.to_be_bytes());
    jpeg_entry.extend_from_slice(&height.to_be_bytes());
    jpeg_entry.extend_from_slice(&0x0048_0000u32.to_be_bytes()); // 72 dpi horiz
    jpeg_entry.extend_from_slice(&0x0048_0000u32.to_be_bytes()); // 72 dpi vert
    jpeg_entry.extend_from_slice(&0u32.to_be_bytes()); // data size
    jpeg_entry.extend_from_slice(&1u16.to_be_bytes()); // frame count
    let mut comp_name = [0u8; 32];
    let label = b"Photo - JPEG";
    comp_name[0] = label.len() as u8;
    comp_name[1..1 + label.len()].copy_from_slice(label);
    jpeg_entry.extend_from_slice(&comp_name);
    jpeg_entry.extend_from_slice(&24u16.to_be_bytes()); // depth
    jpeg_entry.extend_from_slice(&0xFFFFu16.to_be_bytes()); // color table ID (-1)
    let jpeg_atom = wrap_atom(b"jpeg", &jpeg_entry);

    let mut stsd_p = Vec::with_capacity(8 + jpeg_atom.len());
    stsd_p.extend_from_slice(&0u32.to_be_bytes());
    stsd_p.extend_from_slice(&1u32.to_be_bytes());
    stsd_p.extend_from_slice(&jpeg_atom);
    let stsd = wrap_atom(b"stsd", &stsd_p);

    // `stts`: run-length encoded frame durations in milliseconds.
    let mut stts_runs: Vec<(u32, u32)> = Vec::new();
    for s in samples {
        if let Some(last) = stts_runs.last_mut() {
            if last.1 == s.duration_ms {
                last.0 += 1;
                continue;
            }
        }
        stts_runs.push((1, s.duration_ms));
    }
    let mut stts_p = Vec::with_capacity(8 + stts_runs.len() * 8);
    stts_p.extend_from_slice(&0u32.to_be_bytes());
    stts_p.extend_from_slice(&(stts_runs.len() as u32).to_be_bytes());
    for (count, delta) in stts_runs {
        stts_p.extend_from_slice(&count.to_be_bytes());
        stts_p.extend_from_slice(&delta.to_be_bytes());
    }
    let stts = wrap_atom(b"stts", &stts_p);

    // `stsc`: 1 sample per chunk.
    let mut stsc_p = Vec::with_capacity(20);
    stsc_p.extend_from_slice(&0u32.to_be_bytes());
    stsc_p.extend_from_slice(&1u32.to_be_bytes());
    stsc_p.extend_from_slice(&1u32.to_be_bytes()); // first_chunk
    stsc_p.extend_from_slice(&1u32.to_be_bytes()); // samples_per_chunk
    stsc_p.extend_from_slice(&1u32.to_be_bytes()); // sample_description_index
    let stsc = wrap_atom(b"stsc", &stsc_p);

    // `stsz`: per-frame JPEG byte lengths.
    let mut stsz_p = Vec::with_capacity(12 + samples.len() * 4);
    stsz_p.extend_from_slice(&0u32.to_be_bytes());
    stsz_p.extend_from_slice(&0u32.to_be_bytes()); // variable sample size
    stsz_p.extend_from_slice(&(samples.len() as u32).to_be_bytes());
    for s in samples {
        stsz_p.extend_from_slice(&s.size.to_be_bytes());
    }
    let stsz = wrap_atom(b"stsz", &stsz_p);

    // `stco`: absolute file offset of each JPEG frame.
    let mut stco_p = Vec::with_capacity(8 + samples.len() * 4);
    stco_p.extend_from_slice(&0u32.to_be_bytes());
    stco_p.extend_from_slice(&(samples.len() as u32).to_be_bytes());
    for s in samples {
        stco_p.extend_from_slice(&s.offset.to_be_bytes());
    }
    let stco = wrap_atom(b"stco", &stco_p);

    let mut stbl_p =
        Vec::with_capacity(stsd.len() + stts.len() + stsc.len() + stsz.len() + stco.len());
    stbl_p.extend_from_slice(&stsd);
    stbl_p.extend_from_slice(&stts);
    stbl_p.extend_from_slice(&stsc);
    stbl_p.extend_from_slice(&stsz);
    stbl_p.extend_from_slice(&stco);
    let stbl = wrap_atom(b"stbl", &stbl_p);

    let mut minf_p = Vec::with_capacity(vmhd.len() + dinf.len() + stbl.len());
    minf_p.extend_from_slice(&vmhd);
    minf_p.extend_from_slice(&dinf);
    minf_p.extend_from_slice(&stbl);
    let minf = wrap_atom(b"minf", &minf_p);

    let mut mdia_p = Vec::with_capacity(mdhd.len() + hdlr.len() + minf.len());
    mdia_p.extend_from_slice(&mdhd);
    mdia_p.extend_from_slice(&hdlr);
    mdia_p.extend_from_slice(&minf);
    let mdia = wrap_atom(b"mdia", &mdia_p);

    let mut trak_p = Vec::with_capacity(tkhd.len() + mdia.len());
    trak_p.extend_from_slice(&tkhd);
    trak_p.extend_from_slice(&mdia);
    wrap_atom(b"trak", &trak_p)
}

fn build_audio_trak(sample_rate: u32, chunks: &[AudioChunk]) -> Vec<u8> {
    let total_samples_u64: u64 = chunks.iter().map(|c| u64::from(c.sample_count)).sum();
    let total_samples = total_samples_u64.min(u64::from(u32::MAX)) as u32;
    let audio_dur_ms = if sample_rate > 0 {
        ((total_samples_u64 * 1000) / u64::from(sample_rate)).min(u64::from(u32::MAX)) as u32
    } else {
        0
    };

    let tkhd = build_tkhd_atom(2, audio_dur_ms, 0, 0, 0x0100);
    let mdhd = build_mdhd_atom(sample_rate, total_samples);
    let hdlr = build_hdlr_atom(b"soun", b"SoundHandler");

    // `smhd` (version 0 + flags + balance + reserved)
    let smhd = wrap_atom(b"smhd", &[0u8; 8]);
    let dinf = build_dinf_atom();

    // `stsd` with one `sowt` (16-bit signed LE PCM) QuickTime Sound Sample Description v0.
    let mut sowt_entry = Vec::with_capacity(28);
    sowt_entry.extend_from_slice(&[0u8; 6]); // reserved
    sowt_entry.extend_from_slice(&1u16.to_be_bytes()); // data reference index
    sowt_entry.extend_from_slice(&0u16.to_be_bytes()); // version 0
    sowt_entry.extend_from_slice(&0u16.to_be_bytes()); // revision
    sowt_entry.extend_from_slice(&0u32.to_be_bytes()); // vendor
    sowt_entry.extend_from_slice(&1u16.to_be_bytes()); // channel count = 1 (mono)
    sowt_entry.extend_from_slice(&16u16.to_be_bytes()); // sample size = 16 bits
    sowt_entry.extend_from_slice(&0u16.to_be_bytes()); // compression ID = 0
    sowt_entry.extend_from_slice(&0u16.to_be_bytes()); // packet size = 0
    sowt_entry.extend_from_slice(&(sample_rate << 16).to_be_bytes()); // 16.16 fixed-point sample rate
    let sowt_atom = wrap_atom(b"sowt", &sowt_entry);

    let mut stsd_p = Vec::with_capacity(8 + sowt_atom.len());
    stsd_p.extend_from_slice(&0u32.to_be_bytes());
    stsd_p.extend_from_slice(&1u32.to_be_bytes());
    stsd_p.extend_from_slice(&sowt_atom);
    let stsd = wrap_atom(b"stsd", &stsd_p);

    // `stts`: 1 entry covering all PCM samples with delta = 1.
    let mut stts_p = Vec::with_capacity(16);
    stts_p.extend_from_slice(&0u32.to_be_bytes());
    stts_p.extend_from_slice(&1u32.to_be_bytes());
    stts_p.extend_from_slice(&total_samples.to_be_bytes());
    stts_p.extend_from_slice(&1u32.to_be_bytes());
    let stts = wrap_atom(b"stts", &stts_p);

    // `stsc`: run-length encode chunks with identical `sample_count`.
    let mut stsc_entries: Vec<(u32, u32)> = Vec::new();
    for (idx, chunk) in chunks.iter().enumerate() {
        let first_chunk = (idx + 1) as u32;
        if stsc_entries
            .last()
            .is_some_and(|(_, spc)| *spc == chunk.sample_count)
        {
            continue;
        }
        stsc_entries.push((first_chunk, chunk.sample_count));
    }
    let mut stsc_p = Vec::with_capacity(8 + stsc_entries.len() * 12);
    stsc_p.extend_from_slice(&0u32.to_be_bytes());
    stsc_p.extend_from_slice(&(stsc_entries.len() as u32).to_be_bytes());
    for (first_chunk, spc) in stsc_entries {
        stsc_p.extend_from_slice(&first_chunk.to_be_bytes());
        stsc_p.extend_from_slice(&spc.to_be_bytes());
        stsc_p.extend_from_slice(&1u32.to_be_bytes()); // sample_description_index
    }
    let stsc = wrap_atom(b"stsc", &stsc_p);

    // `stsz`: constant sample size = 2 bytes (16-bit mono PCM).
    let mut stsz_p = Vec::with_capacity(12);
    stsz_p.extend_from_slice(&0u32.to_be_bytes());
    stsz_p.extend_from_slice(&2u32.to_be_bytes()); // sample_size = 2 bytes
    stsz_p.extend_from_slice(&total_samples.to_be_bytes());
    let stsz = wrap_atom(b"stsz", &stsz_p);

    // `stco`: file offset of each PCM chunk.
    let mut stco_p = Vec::with_capacity(8 + chunks.len() * 4);
    stco_p.extend_from_slice(&0u32.to_be_bytes());
    stco_p.extend_from_slice(&(chunks.len() as u32).to_be_bytes());
    for chunk in chunks {
        stco_p.extend_from_slice(&chunk.offset.to_be_bytes());
    }
    let stco = wrap_atom(b"stco", &stco_p);

    let mut stbl_p =
        Vec::with_capacity(stsd.len() + stts.len() + stsc.len() + stsz.len() + stco.len());
    stbl_p.extend_from_slice(&stsd);
    stbl_p.extend_from_slice(&stts);
    stbl_p.extend_from_slice(&stsc);
    stbl_p.extend_from_slice(&stsz);
    stbl_p.extend_from_slice(&stco);
    let stbl = wrap_atom(b"stbl", &stbl_p);

    let mut minf_p = Vec::with_capacity(smhd.len() + dinf.len() + stbl.len());
    minf_p.extend_from_slice(&smhd);
    minf_p.extend_from_slice(&dinf);
    minf_p.extend_from_slice(&stbl);
    let minf = wrap_atom(b"minf", &minf_p);

    let mut mdia_p = Vec::with_capacity(mdhd.len() + hdlr.len() + minf.len());
    mdia_p.extend_from_slice(&mdhd);
    mdia_p.extend_from_slice(&hdlr);
    mdia_p.extend_from_slice(&minf);
    let mdia = wrap_atom(b"mdia", &mdia_p);

    let mut trak_p = Vec::with_capacity(tkhd.len() + mdia.len());
    trak_p.extend_from_slice(&tkhd);
    trak_p.extend_from_slice(&mdia);
    wrap_atom(b"trak", &trak_p)
}

/// Build the complete QuickTime `moov` atom for recorded video frames and optional audio chunks.
pub fn build_moov_atom(
    width: u16,
    height: u16,
    audio_sample_rate: u32,
    video_samples: &[VideoSample],
    audio_chunks: &[AudioChunk],
) -> Vec<u8> {
    let video_dur_ms: u32 = video_samples
        .iter()
        .fold(0u32, |acc, s| acc.saturating_add(s.duration_ms));
    let audio_samples: u64 = audio_chunks.iter().map(|c| u64::from(c.sample_count)).sum();
    let audio_dur_ms = if audio_sample_rate > 0 {
        ((audio_samples * 1000) / u64::from(audio_sample_rate)).min(u64::from(u32::MAX)) as u32
    } else {
        0
    };
    let movie_dur_ms = video_dur_ms.max(audio_dur_ms);
    let has_audio = !audio_chunks.is_empty() && audio_sample_rate > 0;
    let next_track_id = if has_audio { 3 } else { 2 };

    let mvhd = build_mvhd_atom(1000, movie_dur_ms, next_track_id);
    let video_trak = if !video_samples.is_empty() {
        Some(build_video_trak(width, height, video_samples))
    } else {
        None
    };
    let audio_trak = if has_audio {
        Some(build_audio_trak(audio_sample_rate, audio_chunks))
    } else {
        None
    };

    let mut payload = Vec::with_capacity(
        mvhd.len()
            + video_trak.as_ref().map_or(0, Vec::len)
            + audio_trak.as_ref().map_or(0, Vec::len),
    );
    payload.extend_from_slice(&mvhd);
    if let Some(vt) = video_trak {
        payload.extend_from_slice(&vt);
    }
    if let Some(at) = audio_trak {
        payload.extend_from_slice(&at);
    }
    wrap_atom(b"moov", &payload)
}

/// Snapshot of the recorder's runtime state for `GET /api/status`.
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct RecorderStatus {
    pub recording: bool,
    pub clip_duration_s: u32,
    pub clip_count: usize,
    pub active_clip: Option<String>,
    pub sd_mounted: bool,
    pub sd_total_bytes: u64,
    pub sd_free_bytes: u64,
    pub wifi_mode: String,
    pub ssid: String,
    pub ip: String,
    pub camera_ready: bool,
    pub mic_ready: bool,
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

/// Format `GET /api/status` JSON payload.
pub fn format_status_json(st: &RecorderStatus) -> String {
    let active_json = match &st.active_clip {
        Some(name) => format!(r#""{}""#, escape_json(name)),
        None => "null".to_string(),
    };
    format!(
        concat!(
            r#"{{"board":"xiao-esp32s3-sense","app":"recorder","firmware_id":"{}","#,
            r#""recording":{},"clip_duration_s":{},"clip_count":{},"active_clip":{},"#,
            r#""sd_mounted":{},"sd_total_bytes":{},"sd_free_bytes":{},"#,
            r#""wifi_mode":"{}","ssid":"{}","ip":"{}","camera_ready":{},"mic_ready":{}}}"#
        ),
        escape_json(RECORDER_FIRMWARE_ID),
        st.recording,
        st.clip_duration_s,
        st.clip_count,
        active_json,
        st.sd_mounted,
        st.sd_total_bytes,
        st.sd_free_bytes,
        escape_json(&st.wifi_mode),
        escape_json(&st.ssid),
        escape_json(&st.ip),
        st.camera_ready,
        st.mic_ready,
    )
}

/// Format `GET /api/clips` JSON payload (clips sorted newest-first).
pub fn format_clips_json(
    clips: &[ClipEntry],
    sd_total_bytes: u64,
    sd_free_bytes: u64,
    recording: bool,
) -> String {
    let mut ordered: Vec<&ClipEntry> = clips.iter().collect();
    ordered.sort_by_key(|a| std::cmp::Reverse(a.seq));

    let mut out = String::from(r#"{"clips":["#);
    for (idx, clip) in ordered.iter().enumerate() {
        if idx > 0 {
            out.push(',');
        }
        out.push_str(&format!(
            r#"{{"name":"{}","seq":{},"size_bytes":{},"duration_s":{}}}"#,
            escape_json(&clip.name),
            clip.seq,
            clip.size_bytes,
            clip.duration_s,
        ));
    }
    out.push_str(&format!(
        r#"],"sd_total_bytes":{sd_total_bytes},"sd_free_bytes":{sd_free_bytes},"recording":{recording}}}"#
    ));
    out
}

#[cfg(test)]
mod tests {
    use super::*;
    use std::io::Cursor;

    #[test]
    fn clip_name_formatting_and_validation() {
        assert_eq!(format_clip_name(1), "clip_000001.mov");
        assert_eq!(format_clip_name(42), "clip_000042.mov");
        assert_eq!(format_temp_clip_name(7), "clip_000007.tmp");

        assert_eq!(parse_clip_seq("clip_000001.mov"), Some(1));
        assert_eq!(parse_clip_seq("clip_999999.mov"), Some(999_999));
        assert!(is_valid_clip_name("clip_000123.mov"));
        assert!(is_temp_clip_name("clip_000123.tmp"));

        // Path traversal and malformed names must be rejected.
        for bad in [
            "",
            "clip_1.mov",
            "clip_000001.tmp",
            "clip_000001.avi",
            "../clip_000001.mov",
            "clip_000001.mov/extra",
            "clip_00000a.mov",
            "CLIP_000001.mov",
        ] {
            assert!(!is_valid_clip_name(bad), "expected {bad:?} to be rejected");
        }
    }

    #[test]
    fn next_clip_seq_resumes_after_max() {
        let empty: Vec<String> = Vec::new();
        assert_eq!(next_clip_seq(&empty), 1);

        let existing = vec![
            "clip_000002.mov",
            "clip_000010.mov",
            "clip_000099.tmp",
            "README.txt",
        ];
        assert_eq!(next_clip_seq(&existing), 11);
    }

    #[test]
    fn plan_evictions_deletes_oldest_until_headroom_met() {
        let clips = vec![
            ClipEntry {
                name: format_clip_name(5),
                seq: 5,
                size_bytes: 10_000_000,
                duration_s: 60,
            },
            ClipEntry {
                name: format_clip_name(2),
                seq: 2,
                size_bytes: 8_000_000,
                duration_s: 60,
            },
            ClipEntry {
                name: format_clip_name(3),
                seq: 3,
                size_bytes: 9_000_000,
                duration_s: 60,
            },
        ];

        // Already enough free space -> delete nothing.
        assert!(plan_evictions(&clips, 64_000_000, 64_000_000).is_empty());

        // Need 15 MB more -> delete seq 2 (8 MB) and seq 3 (9 MB), keep seq 5.
        let victims = plan_evictions(&clips, 50_000_000, 65_000_000);
        assert_eq!(victims, vec!["clip_000002.mov", "clip_000003.mov"]);

        // Required free bytes caps at 64 MiB on large cards and scales to 25% on small cards.
        assert_eq!(
            required_free_bytes(32 * 1024 * 1024 * 1024),
            MIN_FREE_BYTES_CAP
        );
        assert_eq!(required_free_bytes(64 * 1024 * 1024), 16 * 1024 * 1024);
    }

    #[test]
    fn byte_range_parsing_handles_standard_cases() {
        assert_eq!(
            parse_byte_range("bytes=0-1", 1000),
            Some(ByteRange { start: 0, end: 1 })
        );
        assert_eq!(
            parse_byte_range("bytes=500-", 1000),
            Some(ByteRange {
                start: 500,
                end: 999
            })
        );
        assert_eq!(
            parse_byte_range("bytes=0-999999", 1000),
            Some(ByteRange { start: 0, end: 999 })
        );
        assert_eq!(
            parse_byte_range("bytes=-100", 1000),
            Some(ByteRange {
                start: 900,
                end: 999
            })
        );
        assert_eq!(parse_byte_range("bytes=1000-", 1000), None);
        assert_eq!(parse_byte_range("bytes=500-400", 1000), None);
        assert_eq!(parse_byte_range("bytes=0-1,2-3", 1000), None);
        assert_eq!(parse_byte_range("items=0-1", 1000), None);
        assert_eq!(parse_byte_range("bytes=0-1", 0), None);
    }

    #[test]
    fn mov_muxer_produces_valid_atoms_and_offsets() {
        let mut cursor = Cursor::new(Vec::<u8>::new());
        let mut mux = MovMuxer::begin(&mut cursor, 640, 480, 16_000).unwrap();

        let fake_jpeg_1 = vec![0xFF, 0xD8, 0x11, 0x22, 0xFF, 0xD9];
        let fake_jpeg_2 = vec![0xFF, 0xD8, 0x33, 0x44, 0x55, 0x66, 0xFF, 0xD9];
        let fake_pcm_1 = vec![0x01, 0x02, 0x03, 0x04, 0x05, 0x06, 0x07, 0x08]; // 4 samples
        let fake_pcm_2 = vec![0x09, 0x0A, 0x0B, 0x0C]; // 2 samples

        mux.write_video_frame(&fake_jpeg_1, 100).unwrap();
        mux.write_audio_pcm(&fake_pcm_1).unwrap();
        mux.write_video_frame(&fake_jpeg_2, 100).unwrap();
        mux.write_audio_pcm(&fake_pcm_2).unwrap();

        let summary = mux.finalize().unwrap();
        assert_eq!(summary.video_frames, 2);
        assert_eq!(summary.audio_samples, 6);
        assert_eq!(summary.duration_ms, 200);

        let bytes = cursor.into_inner();
        assert_eq!(bytes.len() as u64, summary.total_bytes);

        // Top-level atoms: `ftyp`, `mdat`, `moov`.
        let ftyp_size = u32::from_be_bytes(bytes[0..4].try_into().unwrap()) as usize;
        assert_eq!(ftyp_size, 20);
        assert_eq!(&bytes[4..8], b"ftyp");
        assert_eq!(&bytes[8..12], b"qt  ");

        let mdat_size = u32::from_be_bytes(bytes[20..24].try_into().unwrap()) as usize;
        assert_eq!(&bytes[24..28], b"mdat");
        let expected_mdat =
            8 + fake_jpeg_1.len() + fake_pcm_1.len() + fake_jpeg_2.len() + fake_pcm_2.len();
        assert_eq!(mdat_size, expected_mdat);

        // Verify raw media bytes inside `mdat`.
        assert_eq!(&bytes[28..28 + fake_jpeg_1.len()], &fake_jpeg_1[..]);

        let moov_offset = ftyp_size + mdat_size;
        let moov_size =
            u32::from_be_bytes(bytes[moov_offset..moov_offset + 4].try_into().unwrap()) as usize;
        assert_eq!(&bytes[moov_offset + 4..moov_offset + 8], b"moov");
        assert_eq!(moov_offset + moov_size, bytes.len());

        // Ensure both video (`jpeg`) and audio (`sowt`) sample descriptions are present in `moov`.
        let moov_slice = &bytes[moov_offset..];
        assert!(moov_slice.windows(4).any(|w| w == b"mvhd"));
        assert!(moov_slice.windows(4).any(|w| w == b"jpeg"));
        assert!(moov_slice.windows(4).any(|w| w == b"sowt"));
        assert!(moov_slice.windows(4).any(|w| w == b"vide"));
        assert!(moov_slice.windows(4).any(|w| w == b"soun"));
    }

    #[test]
    fn json_formatters_emit_expected_schema() {
        let status = RecorderStatus {
            recording: true,
            clip_duration_s: 60,
            clip_count: 2,
            active_clip: Some("clip_000003.tmp".to_string()),
            sd_mounted: true,
            sd_total_bytes: 32_000_000_000,
            sd_free_bytes: 31_000_000_000,
            wifi_mode: "ap".to_string(),
            ssid: "XIAO-S3-Sense".to_string(),
            ip: "192.168.4.1".to_string(),
            camera_ready: true,
            mic_ready: true,
        };
        let status_json = format_status_json(&status);
        assert!(status_json.contains(r#""board":"xiao-esp32s3-sense""#));
        assert!(status_json.contains(r#""recording":true"#));
        assert!(status_json.contains(r#""active_clip":"clip_000003.tmp""#));

        let clips = vec![
            ClipEntry {
                name: "clip_000001.mov".to_string(),
                seq: 1,
                size_bytes: 7_500_000,
                duration_s: 60,
            },
            ClipEntry {
                name: "clip_000002.mov".to_string(),
                seq: 2,
                size_bytes: 8_200_000,
                duration_s: 60,
            },
        ];
        let clips_json = format_clips_json(&clips, 32_000_000_000, 31_000_000_000, true);
        // Newest clip (seq 2) appears before older clip (seq 1).
        let pos2 = clips_json.find("clip_000002.mov").unwrap();
        let pos1 = clips_json.find("clip_000001.mov").unwrap();
        assert!(pos2 < pos1);
    }
}
