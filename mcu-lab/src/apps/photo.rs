//! `PhotoApp` — high-quality 4-gray and 1-bit B&W photo frame with multi-photo
//! slideshow rotation for any board implementing [`Board`] + [`HasEpd75`].
//!
//! Photo albums (`MCUP` format) are uploaded from the Playground iOS app over
//! BLE GATT (`BEGIN_DATA`) into the inactive OTA flash partition, then the
//! device restarts and displays photo #0 immediately. When multiple photos are
//! present and `interval_secs > 0` (default 600 s = 10 minutes), the frame
//! automatically rotates through the album while keeping the panel asleep
//! between transitions and advertising BLE every ~5.5 s so iOS can push new
//! photos or send `next` / `prev` / `refresh` commands at any time.

use anyhow::{anyhow, Result};
use esp_idf_svc::sys::{
    esp_ota_get_next_update_partition, esp_partition_read, esp_partition_t, ESP_OK,
};
use log::{info, warn};

use crate::boards::{Board, HasEpd75};
use crate::photo::{
    fill_calibration_4gray_chunk, render_empty_placeholder, Crc32Hasher, PhotoAlbumHeader,
    PhotoMode, PHOTO_FIRMWARE_ID, PHOTO_HEADER_LEN,
};
use crate::platform::{feed_task_watchdog, App, RunMode, StepContext, StepOutput};
use crate::profiler::now_us;
use crate::protocol::AppCommandSpec;

struct LoadedAlbum {
    partition: *const esp_partition_t,
    header: PhotoAlbumHeader,
}

// SAFETY: `partition` points to an immutable ESP-IDF partition table descriptor in flash/ROM.
unsafe impl Send for LoadedAlbum {}

/// Photo frame application for Waveshare 7.5″ 800×480 e-Paper boards.
pub struct PhotoApp {
    album: Option<LoadedAlbum>,
    current_index: u16,
    displayed: bool,
    last_switch_us: u64,
}

impl<B: Board + HasEpd75> App<B> for PhotoApp {
    const APP_NAME: &'static str = "photo";
    const FIRMWARE_ID: &'static str = PHOTO_FIRMWARE_ID;

    fn run_mode() -> RunMode {
        RunMode::Continuous {
            burst_ms: 500,
            min_step_ms: 5_500,
        }
    }

    fn commands() -> Vec<AppCommandSpec> {
        vec![
            AppCommandSpec {
                id: "next".to_string(),
                label: "Next Photo".to_string(),
                default_count: 1,
            },
            AppCommandSpec {
                id: "prev".to_string(),
                label: "Previous Photo".to_string(),
                default_count: 1,
            },
            AppCommandSpec {
                id: "refresh".to_string(),
                label: "Refresh Display".to_string(),
                default_count: 1,
            },
            AppCommandSpec {
                id: "calibrate".to_string(),
                label: "Grayscale Calibration".to_string(),
                default_count: 1,
            },
        ]
    }

    fn init(_board: &mut B) -> Result<Self> {
        let album = load_album_from_inactive_slot();
        if let Some(ref loaded) = album {
            info!(
                "photo: loaded album mode={} count={} interval={}s",
                loaded.header.mode.as_str(),
                loaded.header.count,
                loaded.header.interval_secs
            );
        } else {
            info!("photo: no valid MCUP album in inactive OTA slot; will show ready screen");
        }
        Ok(Self {
            album,
            current_index: 0,
            displayed: false,
            last_switch_us: 0,
        })
    }

    fn step(&mut self, board: &mut B, ctx: &mut StepContext<'_>) -> Result<StepOutput> {
        self.record_album_attrs(ctx);

        if !self.displayed {
            ctx.record_attr("photo.state", "boot_display");
            let epd_us = self.display_current(board, ctx)?;
            self.displayed = true;
            self.last_switch_us = now_us();
            return Ok(StepOutput {
                sensor_us: 0,
                compute_us: 0,
                epd_refresh_us: epd_us,
                battery_mv: 0,
                flags: 0,
                post_burst_delay_ms: 0,
            });
        }

        if let Some(ref album) = self.album {
            let interval_secs = album.header.interval_secs;
            if album.header.count > 1 && interval_secs > 0 {
                let interval_us = u64::from(interval_secs).saturating_mul(1_000_000);
                if now_us().saturating_sub(self.last_switch_us) >= interval_us {
                    self.current_index = (self.current_index + 1) % album.header.count;
                    ctx.record_attr("photo.state", "rotate");
                    let epd_us = self.display_current(board, ctx)?;
                    self.last_switch_us = now_us();
                    return Ok(StepOutput {
                        sensor_us: 0,
                        compute_us: 0,
                        epd_refresh_us: epd_us,
                        battery_mv: 0,
                        flags: 0,
                        post_burst_delay_ms: 0,
                    });
                }
            }
        }

        ctx.record_attr("photo.state", "idle");
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
        board: &mut B,
        ctx: &mut StepContext<'_>,
    ) -> Result<StepOutput> {
        match cmd_id {
            "next" => {
                if let Some(ref album) = self.album {
                    if album.header.count > 1 {
                        self.current_index = (self.current_index + 1) % album.header.count;
                    }
                }
                ctx.record_attr("photo.state", "cmd_next");
            }
            "prev" => {
                if let Some(ref album) = self.album {
                    if album.header.count > 1 {
                        self.current_index =
                            (self.current_index + album.header.count - 1) % album.header.count;
                    }
                }
                ctx.record_attr("photo.state", "cmd_prev");
            }
            "refresh" => {
                ctx.record_attr("photo.state", "cmd_refresh");
            }
            "calibrate" => {
                ctx.record_attr("photo.state", "cmd_calibrate");
                self.record_album_attrs(ctx);
                let epd_start = now_us();
                board.panel().show_4gray_stream(|rel, dst| {
                    fill_calibration_4gray_chunk(rel, dst);
                    Ok(())
                })?;
                ctx.feed_watchdog();
                board.panel().sleep()?;
                let epd_end = now_us();
                ctx.record_span("epd.photo_calibrate", "epd_refresh", epd_start, epd_end);
                ctx.feed_watchdog();
                self.displayed = true;
                self.last_switch_us = now_us();
                return Ok(StepOutput {
                    sensor_us: 0,
                    compute_us: 0,
                    epd_refresh_us: u32::try_from(epd_end.saturating_sub(epd_start))
                        .unwrap_or(u32::MAX),
                    battery_mv: 0,
                    flags: 0,
                    post_burst_delay_ms: 0,
                });
            }
            other => anyhow::bail!("unknown photo command: {other}"),
        }

        self.record_album_attrs(ctx);
        let epd_us = self.display_current(board, ctx)?;
        self.displayed = true;
        self.last_switch_us = now_us();
        Ok(StepOutput {
            sensor_us: 0,
            compute_us: 0,
            epd_refresh_us: epd_us,
            battery_mv: 0,
            flags: 0,
            post_burst_delay_ms: 0,
        })
    }
}

impl PhotoApp {
    fn record_album_attrs(&self, ctx: &mut StepContext<'_>) {
        if let Some(ref album) = self.album {
            ctx.record_attr("photo.mode", album.header.mode.as_str());
            ctx.record_attr("photo.count", &album.header.count.to_string());
            ctx.record_attr("photo.index", &self.current_index.to_string());
            ctx.record_attr("photo.interval_s", &album.header.interval_secs.to_string());
        } else {
            ctx.record_attr("photo.mode", "empty");
            ctx.record_attr("photo.count", "0");
            ctx.record_attr("photo.index", "0");
            ctx.record_attr("photo.interval_s", "0");
        }
    }

    fn display_current<B: Board + HasEpd75>(
        &self,
        board: &mut B,
        ctx: &mut StepContext<'_>,
    ) -> Result<u32> {
        let epd_start = now_us();
        let span_name = match &self.album {
            Some(album) => {
                let base_offset = album
                    .header
                    .frame_offset(self.current_index)
                    .ok_or_else(|| anyhow!("photo index {} out of range", self.current_index))?;
                let part = album.partition;
                info!(
                    "photo: rendering {}/{} (mode={}, flash_offset={base_offset})",
                    self.current_index + 1,
                    album.header.count,
                    album.header.mode.as_str()
                );
                let read_at = |rel: usize, dst: &mut [u8]| -> Result<()> {
                    // SAFETY: `part` is valid and `base_offset + rel + dst.len()` is verified
                    // within `album.header.total_bytes() <= (*part).size`.
                    let err = unsafe {
                        esp_partition_read(
                            part,
                            base_offset + rel,
                            dst.as_mut_ptr().cast(),
                            dst.len(),
                        )
                    };
                    if err != ESP_OK {
                        return Err(anyhow!("esp_partition_read err={err}"));
                    }
                    Ok(())
                };
                match album.header.mode {
                    PhotoMode::Bw1Bit => {
                        board.panel().show_bw_stream(read_at)?;
                        "epd.photo_bw"
                    }
                    PhotoMode::Gray4 => {
                        board.panel().show_4gray_stream(read_at)?;
                        "epd.photo_4gray"
                    }
                }
            }
            None => {
                let placeholder = render_empty_placeholder();
                board.panel().show_frame_awake(&placeholder)?;
                "epd.photo_placeholder"
            }
        };
        ctx.feed_watchdog();
        board.panel().sleep()?;
        let epd_end = now_us();
        ctx.record_span(span_name, "epd_refresh", epd_start, epd_end);
        ctx.feed_watchdog();
        Ok(u32::try_from(epd_end.saturating_sub(epd_start)).unwrap_or(u32::MAX))
    }
}

/// Inspect the inactive OTA partition for a valid `MCUP` photo album and verify its CRC32.
fn load_album_from_inactive_slot() -> Option<LoadedAlbum> {
    // SAFETY: queries ESP-IDF's partition table for the inactive OTA partition.
    let part = unsafe { esp_ota_get_next_update_partition(core::ptr::null()) };
    if part.is_null() {
        warn!("photo: esp_ota_get_next_update_partition returned null");
        return None;
    }

    let mut hdr_bytes = [0u8; PHOTO_HEADER_LEN];
    // SAFETY: `part` is valid and at least `PHOTO_HEADER_LEN` bytes.
    let err =
        unsafe { esp_partition_read(part, 0, hdr_bytes.as_mut_ptr().cast(), hdr_bytes.len()) };
    if err != ESP_OK {
        warn!("photo: header read failed err={err}");
        return None;
    }

    let header = match PhotoAlbumHeader::parse(&hdr_bytes) {
        Ok(h) => h,
        Err(msg) => {
            info!("photo: inactive slot does not contain a photo album ({msg})");
            return None;
        }
    };

    let part_size = unsafe { (*part).size as usize };
    if header.total_bytes() > part_size {
        warn!(
            "photo: album {}B exceeds inactive partition {}B",
            header.total_bytes(),
            part_size
        );
        return None;
    }

    let mut hasher = Crc32Hasher::new();
    let mut buf = [0u8; 4096];
    let payload_len = header.payload_bytes();
    let mut offset = 0usize;
    while offset < payload_len {
        let len = (payload_len - offset).min(buf.len());
        // SAFETY: `PHOTO_HEADER_LEN + offset + len <= header.total_bytes() <= part_size`.
        let err = unsafe {
            esp_partition_read(
                part,
                PHOTO_HEADER_LEN + offset,
                buf.as_mut_ptr().cast(),
                len,
            )
        };
        if err != ESP_OK {
            warn!("photo: payload read failed at offset {offset} err={err}");
            return None;
        }
        hasher.update(&buf[..len]);
        offset += len;
        if offset % (64 * 1024) == 0 {
            feed_task_watchdog();
        }
    }

    let actual_crc = hasher.finalize();
    if actual_crc != header.payload_crc32 {
        warn!(
            "photo: payload crc32 mismatch: got {actual_crc:#010x}, want {:#010x}",
            header.payload_crc32
        );
        return None;
    }

    Some(LoadedAlbum {
        partition: part,
        header,
    })
}
