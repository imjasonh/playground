//! Wire format, cycle/phase accumulator, e-paper benchmark helpers, and OTLP
//! JSON builder for the multi-MCU `mcu-lab` firmware crate.
//!
//! Each board measures discrete execution phases in microseconds (`sensor`,
//! `compute`, `epd_refresh`, and `radio`), packs a 24-byte little-endian
//! payload (with its `board_id` in `flags` bits 4..7) into a BLE Manufacturer
//! Specific Data (`0xFF`) advertising frame, and broadcasts a burst. The
//! Playground **MCU Lab** iOS experiment scans for company ID `0xFFFF`,
//! deduplicates frames per device by `seq`, renders a live performance and
//! power budget dashboard, and forwards OTLP/HTTP JSON metrics and traces to
//! the OpenTelemetry collector.

/// Advertised GAP short name (placed in scan response when present).
pub const DEVICE_NAME: &str = "XIAO-C3";

/// On-wire / log identifier for the XIAO benchmark app. Bump when the binary packet layout changes.
pub const FIRMWARE_ID: &str = "xiao-esp32c3/0.1";

/// On-wire / log identifier for the universal base OTA + OTel bootstrap firmware.
pub const BASE_FIRMWARE_ID: &str = "mcu-lab-base/0.1";

/// Bluetooth SIG test / internal-use company identifier (`0xFFFF`).
pub const COMPANY_ID: u16 = 0xFFFF;

/// Binary payload version in [`AdvMetrics`].
pub const PROTOCOL_VERSION: u8 = 1;

/// Size of the packed [`AdvMetrics`] payload in bytes (excluding the 2-byte company ID).
pub const PAYLOAD_LEN: usize = 24;

/// Size of the manufacturer data field in bytes (2-byte company ID + 24-byte payload).
pub const MFG_DATA_LEN: usize = 2 + PAYLOAD_LEN;

/// Full legacy BLE advertising PDU payload length (3-byte Flags AD + 28-byte Manufacturer AD).
pub const ADV_PACKET_LEN: usize = 31;

/// Flag bit 0: this wake resumed from deep sleep (`ESP_RST_DEEPSLEEP`).
pub const FLAG_DEEP_SLEEP_WAKE: u8 = 1 << 0;

/// Flag bit 1: an e-paper display is attached (vs. simulated SPI + LUT refresh timing).
pub const FLAG_EPD_ATTACHED: u8 = 1 << 1;

/// Flag bit 2: the e-paper update on this wake was a partial refresh (vs. full refresh).
pub const FLAG_EPD_PARTIAL: u8 = 1 << 2;

/// Flag bit 3: last reset was a brownout (`ESP_RST_BROWNOUT`).
pub const FLAG_BROWNOUT_RESET: u8 = 1 << 3;

/// Board ID encoded in `flags` bits 4..7 (0 = legacy XIAO ESP32-C3).
pub const BOARD_XIAO_ESP32C3: u8 = 1;
/// Waveshare e-Paper ESP32 Driver Board (classic ESP32 Xtensa + 7.5″ 800×480 UC8179).
pub const BOARD_WAVESHARE_EPD75: u8 = 2;

/// ESP-IDF `esp_image_header_t.chip_id` for classic ESP32 (Xtensa LX6).
pub const CHIP_ID_ESP32: u16 = 0x0000;
/// ESP-IDF `esp_image_header_t.chip_id` for ESP32-C3 (RISC-V).
pub const CHIP_ID_ESP32C3: u16 = 0x0005;

/// Static hardware board descriptor (independent of which [`App`] is running on it).
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub struct BoardSpec {
    pub board_id: u8,
    pub board: &'static str,
    pub chip: &'static str,
    pub gap_name: &'static str,
    pub chip_id: u16,
    pub cpu_mhz: u64,
    /// Minimum battery voltage (mV) required to accept an OTA `BEGIN` command (`0` disables check).
    pub min_ota_battery_mv: u16,
}

/// Encode `board_id` (0..=15) into the upper nibble of `AdvMetrics.flags`.
pub const fn encode_board_flags(board_id: u8) -> u8 {
    (board_id & 0x0F) << 4
}

/// Decode `board_id` from the upper nibble of `AdvMetrics.flags`.
pub const fn decode_board_id(flags: u8) -> u8 {
    (flags >> 4) & 0x0F
}

/// Validate the first chunk of an ESP-IDF application image (`esp_image_header_t`):
/// byte 0 must be `0xE9` (`ESP_IMAGE_HEADER_MAGIC`) and bytes 12..14 (little-endian
/// `chip_id`) must match `expected_chip_id` so cross-chip BLE OTA is rejected before flash write.
pub fn validate_esp_image_header(chunk: &[u8], expected_chip_id: u16) -> Result<(), String> {
    if chunk.is_empty() {
        return Err("empty first OTA chunk".to_string());
    }
    if chunk[0] != 0xE9 {
        return Err(format!(
            "invalid ESP-IDF image header byte {:#04x}",
            chunk[0]
        ));
    }
    if chunk.len() >= 14 {
        let got = u16::from_le_bytes([chunk[12], chunk[13]]);
        if got != expected_chip_id {
            return Err(format!(
                "chip_id mismatch: image={got:#06x}, device={expected_chip_id:#06x}"
            ));
        }
    }
    Ok(())
}

/// Custom BLE GATT service UUID (128-bit) for on-demand firmware OTA updates from the iPhone.
pub const OTA_SERVICE_UUID: &str = "4fafc301-1fb5-459e-8fcc-c5c9c331914b";

/// Write characteristic: iPhone → MCU OTA control (`BEGIN <size> <sha256>`, `COMMIT`, `ABORT`).
pub const OTA_CONTROL_UUID: &str = "beb5483e-36e1-4688-b7f5-ea07361bc301";

/// Write-without-response characteristic: iPhone → MCU raw or framed firmware binary chunks.
pub const OTA_DATA_UUID: &str = "beb5483e-36e1-4688-b7f5-ea07361bc302";

/// Read + notify characteristic: MCU → iPhone OTA status line (`IDLE`, `READY`, `PROGRESS`, `OK`, `ERR`).
pub const OTA_STATUS_UUID: &str = "1a3c0001-36e1-4688-b7f5-ea07361bc303";

/// Read + notify characteristic: MCU → iPhone latest wake sub-phase spans & profiling JSON (chunked if > 480 B).
pub const PROFILE_CHAR_UUID: &str = "1a3c0002-36e1-4688-b7f5-ea07361bc303";

/// Read + notify + write characteristic: MCU → iPhone chunked flash coredump ELF (`CLEAR` write erases flash).
pub const COREDUMP_CHAR_UUID: &str = "1a3c0003-36e1-4688-b7f5-ea07361bc303";

/// Size of each OTA partition slot (`ota_0` / `ota_1`) in `partitions.csv` (1.875 MiB, 64 KiB-aligned).
pub const OTA_SLOT_BYTES: u32 = 0x1E_0000;

/// Typical small SPI e-paper width in pixels (1.54″ / 2.13″ class, 200×200 = 5,000 bytes packed 1-bit).
pub const EPD_WIDTH: usize = 200;

/// Typical small SPI e-paper height in pixels.
pub const EPD_HEIGHT: usize = 200;

/// Packed 1-bit framebuffer size for a 200×200 e-paper panel (5,000 bytes).
pub const EPD_FRAME_BYTES: usize = (EPD_WIDTH * EPD_HEIGHT) / 8;

/// Simulated BUSY hold duration for a partial e-paper LUT refresh (320 ms) when no panel is wired.
pub const EPD_PARTIAL_REFRESH_SIM_US: u32 = 320_000;

/// Simulated BUSY hold duration for a full e-paper LUT refresh (1,850 ms) when no panel is wired.
pub const EPD_FULL_REFRESH_SIM_US: u32 = 1_850_000;

/// 24-byte profiling telemetry payload packed into BLE Manufacturer Specific Data (`0xFF`).
///
/// All multi-byte integers are encoded in little-endian order on the wire:
///
/// | Offset | Size | Field | Description |
/// |--------|------|-------|-------------|
/// | 0 | 1 | `seq` | Monotonic sequence number (wraps at 255) for burst deduplication |
/// | 1 | 1 | `flags` | Bitfield: `FLAG_DEEP_SLEEP_WAKE`, `FLAG_EPD_ATTACHED`, `FLAG_EPD_PARTIAL`, `FLAG_BROWNOUT_RESET` |
/// | 2 | 4 | `wake_count` | Cumulative wakes since cold power-on (stored in RTC slow RAM) |
/// | 6 | 4 | `sensor_us` | Sensor / ADC read phase duration in microseconds |
/// | 10 | 4 | `compute_us` | Compute / filtering / 1-bit framebuffer render duration in microseconds |
/// | 14 | 4 | `epd_refresh_us` | E-paper SPI transfer + BUSY refresh wait duration in microseconds |
/// | 18 | 4 | `radio_us` | BLE advertising active duration from the previous wake in microseconds |
/// | 22 | 2 | `battery_mv` | Battery voltage in millivolts |
#[derive(Clone, Copy, Debug, Default, PartialEq, Eq)]
pub struct AdvMetrics {
    pub seq: u8,
    pub flags: u8,
    pub wake_count: u32,
    pub sensor_us: u32,
    pub compute_us: u32,
    pub epd_refresh_us: u32,
    pub radio_us: u32,
    pub battery_mv: u16,
}

impl AdvMetrics {
    /// Total active awake duration across all four measured phases in microseconds.
    pub fn total_active_us(&self) -> u64 {
        u64::from(self.sensor_us)
            + u64::from(self.compute_us)
            + u64::from(self.epd_refresh_us)
            + u64::from(self.radio_us)
    }

    /// Estimated energy consumed by this wake cycle in microjoules (µJ) at 3.7 V,
    /// using typical XIAO ESP32C3 current profiles:
    /// - Sensor + CPU active: ~28 mA
    /// - Compute (160 MHz RISC-V core active): ~32 mA
    /// - E-paper SPI + booster refresh: ~38 mA
    /// - BLE TX burst: ~85 mA
    pub fn estimated_energy_uj(&self) -> u64 {
        let v_mv = if self.battery_mv > 0 {
            u64::from(self.battery_mv)
        } else {
            3700
        };
        // Power (mW) = V(mV) * I(mA) / 1000. Energy (µJ) = Power(mW) * Duration(µs) / 1000.
        let microamp_seconds = u64::from(self.sensor_us) * 28
            + u64::from(self.compute_us) * 32
            + u64::from(self.epd_refresh_us) * 38
            + u64::from(self.radio_us) * 85;
        (microamp_seconds * v_mv) / 1_000_000
    }
}

/// Accumulates phase durations across a wake cycle and persists state across deep sleep.
#[derive(Clone, Copy, Debug, Default, PartialEq, Eq)]
pub struct PhaseAccumulator {
    pub seq: u8,
    pub wake_count: u32,
    pub last_radio_us: u32,
    pub total_sensor_us: u64,
    pub total_compute_us: u64,
    pub total_epd_refresh_us: u64,
    pub total_radio_us: u64,
}

impl PhaseAccumulator {
    pub const fn new() -> Self {
        Self {
            seq: 0,
            wake_count: 0,
            last_radio_us: 0,
            total_sensor_us: 0,
            total_compute_us: 0,
            total_epd_refresh_us: 0,
            total_radio_us: 0,
        }
    }

    /// Record a completed wake cycle's phases and build the [`AdvMetrics`] packet to broadcast.
    pub fn record_wake(
        &mut self,
        sensor_us: u32,
        compute_us: u32,
        epd_refresh_us: u32,
        battery_mv: u16,
        flags: u8,
    ) -> AdvMetrics {
        self.seq = self.seq.wrapping_add(1);
        self.wake_count = self.wake_count.saturating_add(1);
        self.total_sensor_us = self.total_sensor_us.saturating_add(u64::from(sensor_us));
        self.total_compute_us = self.total_compute_us.saturating_add(u64::from(compute_us));
        self.total_epd_refresh_us = self
            .total_epd_refresh_us
            .saturating_add(u64::from(epd_refresh_us));

        AdvMetrics {
            seq: self.seq,
            flags,
            wake_count: self.wake_count,
            sensor_us,
            compute_us,
            epd_refresh_us,
            radio_us: self.last_radio_us,
            battery_mv,
        }
    }

    /// Record the duration of the BLE advertising burst just before entering deep sleep,
    /// so the next wake reports the exact radio active time.
    pub fn record_radio_tx(&mut self, radio_us: u32) {
        self.last_radio_us = radio_us;
        self.total_radio_us = self.total_radio_us.saturating_add(u64::from(radio_us));
    }
}

/// Encode [`AdvMetrics`] into its 24-byte little-endian payload.
pub fn encode_metrics(m: &AdvMetrics) -> [u8; PAYLOAD_LEN] {
    let mut out = [0u8; PAYLOAD_LEN];
    out[0] = m.seq;
    out[1] = m.flags;
    out[2..6].copy_from_slice(&m.wake_count.to_le_bytes());
    out[6..10].copy_from_slice(&m.sensor_us.to_le_bytes());
    out[10..14].copy_from_slice(&m.compute_us.to_le_bytes());
    out[14..18].copy_from_slice(&m.epd_refresh_us.to_le_bytes());
    out[18..22].copy_from_slice(&m.radio_us.to_le_bytes());
    out[22..24].copy_from_slice(&m.battery_mv.to_le_bytes());
    out
}

/// Decode a 24-byte little-endian payload into [`AdvMetrics`].
pub fn decode_metrics(bytes: &[u8]) -> Option<AdvMetrics> {
    if bytes.len() != PAYLOAD_LEN {
        return None;
    }
    let seq = bytes[0];
    let flags = bytes[1];
    let wake_count = u32::from_le_bytes(bytes[2..6].try_into().ok()?);
    let sensor_us = u32::from_le_bytes(bytes[6..10].try_into().ok()?);
    let compute_us = u32::from_le_bytes(bytes[10..14].try_into().ok()?);
    let epd_refresh_us = u32::from_le_bytes(bytes[14..18].try_into().ok()?);
    let radio_us = u32::from_le_bytes(bytes[18..22].try_into().ok()?);
    let battery_mv = u16::from_le_bytes(bytes[22..24].try_into().ok()?);

    Some(AdvMetrics {
        seq,
        flags,
        wake_count,
        sensor_us,
        compute_us,
        epd_refresh_us,
        radio_us,
        battery_mv,
    })
}

/// Encode the 26-byte Manufacturer Specific Data value (2-byte company ID + 24-byte payload).
///
/// This is the slice passed to `BLEAdvertisementData::manufacturer_data` on ESP-IDF and
/// delivered by CoreBluetooth under `CBAdvertisementDataManufacturerDataKey`.
pub fn encode_mfg_data(m: &AdvMetrics) -> [u8; MFG_DATA_LEN] {
    let mut out = [0u8; MFG_DATA_LEN];
    out[0..2].copy_from_slice(&COMPANY_ID.to_le_bytes());
    out[2..MFG_DATA_LEN].copy_from_slice(&encode_metrics(m));
    out
}

/// Decode a 26-byte Manufacturer Specific Data buffer (`0xFFFF` company ID + 24-byte payload).
pub fn decode_mfg_data(bytes: &[u8]) -> Option<AdvMetrics> {
    if bytes.len() != MFG_DATA_LEN {
        return None;
    }
    let company = u16::from_le_bytes(bytes[0..2].try_into().ok()?);
    if company != COMPANY_ID {
        return None;
    }
    decode_metrics(&bytes[2..MFG_DATA_LEN])
}

/// Encode a full 31-byte raw BLE legacy advertising PDU payload:
/// - `[0..3]`: Flags AD (`[0x02, 0x01, 0x06]`)
/// - `[3..31]`: Manufacturer Specific Data AD (`[27, 0xFF, 0xFF, 0xFF, ...24B payload...]`)
pub fn encode_adv_packet(m: &AdvMetrics) -> [u8; ADV_PACKET_LEN] {
    let mut out = [0u8; ADV_PACKET_LEN];
    out[0..3].copy_from_slice(&[0x02, 0x01, 0x06]);
    out[3] = (1 + MFG_DATA_LEN) as u8; // 27
    out[4] = 0xFF;
    out[5..ADV_PACKET_LEN].copy_from_slice(&encode_mfg_data(m));
    out
}

/// Decode a 31-byte raw BLE legacy advertising PDU payload produced by [`encode_adv_packet`].
pub fn decode_adv_packet(bytes: &[u8]) -> Option<AdvMetrics> {
    if bytes.len() != ADV_PACKET_LEN {
        return None;
    }
    if bytes[0..3] != [0x02, 0x01, 0x06] {
        return None;
    }
    if bytes[3] != (1 + MFG_DATA_LEN) as u8 || bytes[4] != 0xFF {
        return None;
    }
    decode_mfg_data(&bytes[5..ADV_PACKET_LEN])
}

/// Format a human-readable single-line status summary for serial / USB-JTAG logs.
pub fn format_status_line(m: &AdvMetrics) -> String {
    format!(
        "seq={} wake={} sensor_us={} compute_us={} epd_us={} radio_us={} batt_mv={} flags={:#04x}",
        m.seq,
        m.wake_count,
        m.sensor_us,
        m.compute_us,
        m.epd_refresh_us,
        m.radio_us,
        m.battery_mv,
        m.flags
    )
}

/// Parse a serial status line produced by [`format_status_line`].
pub fn parse_status_line(raw: &str) -> Option<AdvMetrics> {
    let raw = raw.trim();
    if raw.is_empty() {
        return None;
    }
    let mut seq = None;
    let mut wake_count = None;
    let mut sensor_us = None;
    let mut compute_us = None;
    let mut epd_refresh_us = None;
    let mut radio_us = None;
    let mut battery_mv = None;
    let mut flags = None;

    for part in raw.split_whitespace() {
        if let Some(v) = part.strip_prefix("seq=") {
            seq = Some(v.parse().ok()?);
        } else if let Some(v) = part.strip_prefix("wake=") {
            wake_count = Some(v.parse().ok()?);
        } else if let Some(v) = part.strip_prefix("sensor_us=") {
            sensor_us = Some(v.parse().ok()?);
        } else if let Some(v) = part.strip_prefix("compute_us=") {
            compute_us = Some(v.parse().ok()?);
        } else if let Some(v) = part.strip_prefix("epd_us=") {
            epd_refresh_us = Some(v.parse().ok()?);
        } else if let Some(v) = part.strip_prefix("radio_us=") {
            radio_us = Some(v.parse().ok()?);
        } else if let Some(v) = part.strip_prefix("batt_mv=") {
            battery_mv = Some(v.parse().ok()?);
        } else if let Some(v) = part.strip_prefix("flags=") {
            let hex = v.strip_prefix("0x").or_else(|| v.strip_prefix("0X"))?;
            flags = Some(u8::from_str_radix(hex, 16).ok()?);
        }
    }

    Some(AdvMetrics {
        seq: seq?,
        flags: flags?,
        wake_count: wake_count?,
        sensor_us: sensor_us?,
        compute_us: compute_us?,
        epd_refresh_us: epd_refresh_us?,
        radio_us: radio_us?,
        battery_mv: battery_mv?,
    })
}

/// Format [`AdvMetrics`] into a valid OTLP/HTTP v1 JSON metrics payload (`application/json`).
///
/// The iOS forwarder and host tests share this schema:
/// - `mcu.wake.count` (gauge)
/// - `mcu.phase.duration_us` (gauge with `phase` attribute: `sensor`, `compute`, `epd_refresh`, `radio`)
/// - `mcu.battery_mv` (gauge)
/// - `mcu.ble.rssi` (gauge)
pub fn format_otlp_json(device_id: &str, m: &AdvMetrics, rssi: i32, time_unix_nano: u64) -> String {
    let ts = time_unix_nano.to_string();
    let escaped_device_id = escape_json_str(device_id);
    let service_name = match decode_board_id(m.flags) {
        BOARD_WAVESHARE_EPD75 => "waveshare-epd75",
        _ => "xiao-esp32c3",
    };
    format!(
        concat!(
            r#"{{"resourceMetrics":[{{"resource":{{"attributes":["#,
            r#"{{"key":"service.name","value":{{"stringValue":"{service_name}"}}}},"#,
            r#"{{"key":"device.id","value":{{"stringValue":"{device_id}"}}}}"#,
            r#"]}},"scopeMetrics":[{{"metrics":["#,
            r#"{{"name":"mcu.wake.count","gauge":{{"dataPoints":[{{"asInt":"{wake_count}","timeUnixNano":"{ts}"}}]}}}},"#,
            r#"{{"name":"mcu.phase.duration_us","gauge":{{"dataPoints":["#,
            r#"{{"asInt":"{sensor_us}","timeUnixNano":"{ts}","attributes":[{{"key":"phase","value":{{"stringValue":"sensor"}}}}]}},"#,
            r#"{{"asInt":"{compute_us}","timeUnixNano":"{ts}","attributes":[{{"key":"phase","value":{{"stringValue":"compute"}}}}]}},"#,
            r#"{{"asInt":"{epd_us}","timeUnixNano":"{ts}","attributes":[{{"key":"phase","value":{{"stringValue":"epd_refresh"}}}}]}},"#,
            r#"{{"asInt":"{radio_us}","timeUnixNano":"{ts}","attributes":[{{"key":"phase","value":{{"stringValue":"radio"}}}}]}}"#,
            r#"]}}}},"#,
            r#"{{"name":"mcu.battery_mv","gauge":{{"dataPoints":[{{"asInt":"{battery_mv}","timeUnixNano":"{ts}"}}]}}}},"#,
            r#"{{"name":"mcu.ble.rssi","gauge":{{"dataPoints":[{{"asInt":"{rssi}","timeUnixNano":"{ts}"}}]}}}}"#,
            r#"]}}]}}]}}"#
        ),
        service_name = service_name,
        device_id = escaped_device_id,
        wake_count = m.wake_count,
        sensor_us = m.sensor_us,
        compute_us = m.compute_us,
        epd_us = m.epd_refresh_us,
        radio_us = m.radio_us,
        battery_mv = m.battery_mv,
        rssi = rssi,
        ts = ts,
    )
}

fn escape_json_str(s: &str) -> String {
    let mut out = String::with_capacity(s.len());
    for c in s.chars() {
        match c {
            '"' => out.push_str("\\\""),
            '\\' => out.push_str("\\\\"),
            c if c.is_control() => {}
            other => out.push(other),
        }
    }
    out
}

/// Deterministic integer-only sensor filter benchmark for the RISC-V ESP32-C3 (which has no FPU).
///
/// Runs a 64-sample fixed-point Exponential Moving Average (EMA) and median-of-3 spike filter
/// over synthetic ADC readings so the `sensor` and `compute` phase timers capture real CPU cycles.
pub fn simulate_sensor_filter(seed: u32, samples: usize) -> u16 {
    let mut state = seed.wrapping_add(0x9E37_79B9);
    let mut ema_mv: u32 = 3850;
    let mut prev1: u32 = 3850;
    let mut prev2: u32 = 3850;

    for _ in 0..samples.max(1) {
        // xorshift32
        state ^= state << 13;
        state ^= state >> 17;
        state ^= state << 5;
        let noise = (state & 0x7F) as i32 - 64; // -64..+63 mV
        let sample = (3850i32 + noise).clamp(3200, 4200) as u32;

        // Median of 3 (prev2, prev1, sample)
        let median = median3(prev2, prev1, sample);
        prev2 = prev1;
        prev1 = sample;

        // Fixed-point EMA: alpha = 1/8
        ema_mv = ((ema_mv * 7) + median + 4) >> 3;
    }

    ema_mv as u16
}

fn median3(a: u32, b: u32, c: u32) -> u32 {
    if a > b {
        if b > c {
            b
        } else if a > c {
            c
        } else {
            a
        }
    } else if a > c {
        a
    } else if b > c {
        c
    } else {
        b
    }
}

/// Render a deterministic 1-bit e-paper status tile into `buf` (e.g. [`EPD_FRAME_BYTES`] = 5,000 bytes)
/// and return the byte checksum.
///
/// This exercises the exact bit-packing, dirty-window XOR diffing, and glyph blitting that
/// a real SPI e-paper update performs during the `compute` phase on the ESP32-C3.
pub fn simulate_epd_frame(buf: &mut [u8], wake_count: u32, battery_mv: u16, partial: bool) -> u32 {
    let fill = if partial { 0xFFu8 } else { 0xAAu8 };
    buf.fill(fill);

    let stride = EPD_WIDTH / 8;
    let mut checksum: u32 = 0;

    // Draw a status border and synthetic progress bars proportional to wake_count and battery_mv.
    let bar_cols = ((wake_count as usize % EPD_WIDTH) / 8).min(stride);
    let batt_cols = (((battery_mv.saturating_sub(3000) as usize) * stride) / 1200).min(stride);

    for y in 0..EPD_HEIGHT {
        let row_start = y * stride;
        if row_start + stride > buf.len() {
            break;
        }
        // Top / bottom border
        if !(2..EPD_HEIGHT - 2).contains(&y) {
            for b in &mut buf[row_start..row_start + stride] {
                *b = 0x00;
            }
        } else if (16..32).contains(&y) {
            // Wake progress bar
            for b in &mut buf[row_start..row_start + bar_cols] {
                *b ^= 0xF0;
            }
        } else if (48..64).contains(&y) {
            // Battery gauge bar
            for b in &mut buf[row_start..row_start + batt_cols] {
                *b = 0x00;
            }
        }
    }

    for &b in buf.iter() {
        checksum = checksum.wrapping_mul(16777619) ^ u32::from(b);
    }
    checksum
}

/// Human-readable ESP-IDF `esp_reset_reason_t` name.
pub fn reset_reason_name(code: i32) -> &'static str {
    match code {
        1 => "POWERON",
        3 => "SW",
        4 => "PANIC",
        5 => "INT_WDT",
        6 => "TASK_WDT",
        7 => "WDT",
        8 => "DEEPSLEEP",
        9 => "BROWNOUT",
        10 => "SDIO",
        11 => "USB",
        12 => "JTAG",
        _ => "UNKNOWN",
    }
}

/// Control command written by the iPhone to [`OTA_CONTROL_UUID`].
#[derive(Clone, Debug, PartialEq, Eq)]
pub enum OtaCommand {
    /// Erase and open the inactive OTA partition for `size` bytes with expected lowercase hex `sha256`.
    Begin { size: u32, sha256: String },
    /// Finalize the OTA image, verify the SHA-256 digest, switch the boot partition, and reboot.
    Commit,
    /// Cancel an in-progress OTA transfer.
    Abort,
}

/// Status notification sent by the MCU on [`OTA_STATUS_UUID`].
#[derive(Clone, Debug, PartialEq, Eq)]
pub enum OtaStatus {
    Idle,
    Ready { total: u32, offset: u32 },
    Progress { written: u32, total: u32 },
    Ok { sha256: String },
    Error { message: String },
}

/// Parse an OTA control command string from the iPhone.
pub fn parse_ota_command(raw: &str) -> Option<OtaCommand> {
    let parts: Vec<&str> = raw.split_whitespace().collect();
    if parts.is_empty() {
        return None;
    }
    let head = parts[0].to_ascii_uppercase();
    match head.as_str() {
        "COMMIT" if parts.len() == 1 => Some(OtaCommand::Commit),
        "ABORT" if parts.len() == 1 => Some(OtaCommand::Abort),
        "BEGIN" if parts.len() == 3 => {
            let size: u32 = parts[1].parse().ok()?;
            if size == 0 || size > OTA_SLOT_BYTES {
                return None;
            }
            let sha = parts[2]
                .strip_prefix("sha256:")
                .unwrap_or(parts[2])
                .to_ascii_lowercase();
            if sha.len() != 64 || !sha.chars().all(|c| c.is_ascii_hexdigit()) {
                return None;
            }
            Some(OtaCommand::Begin { size, sha256: sha })
        }
        _ => None,
    }
}

/// Encode an [`OtaCommand`] into its wire string.
pub fn encode_ota_command(cmd: &OtaCommand) -> String {
    match cmd {
        OtaCommand::Begin { size, sha256 } => format!("BEGIN {size} {sha256}"),
        OtaCommand::Commit => "COMMIT".to_string(),
        OtaCommand::Abort => "ABORT".to_string(),
    }
}

/// Format an [`OtaStatus`] line for the notify characteristic.
pub fn format_ota_status(status: &OtaStatus) -> String {
    match status {
        OtaStatus::Idle => "IDLE".to_string(),
        OtaStatus::Ready { total, offset: 0 } => format!("READY total={total}"),
        OtaStatus::Ready { total, offset } => format!("READY total={total} offset={offset}"),
        OtaStatus::Progress { written, total } => {
            format!("PROGRESS written={written} total={total}")
        }
        OtaStatus::Ok { sha256 } => format!("OK sha256={sha256}"),
        OtaStatus::Error { message } => format!("ERR {message}"),
    }
}

/// Parse an [`OtaStatus`] line from the notify characteristic.
pub fn parse_ota_status(raw: &str) -> Option<OtaStatus> {
    let raw = raw.trim();
    if raw == "IDLE" {
        return Some(OtaStatus::Idle);
    }
    if let Some(msg) = raw.strip_prefix("ERR ") {
        return Some(OtaStatus::Error {
            message: msg.trim().to_string(),
        });
    }
    if let Some(rest) = raw.strip_prefix("READY ") {
        let mut total = None;
        let mut offset = 0u32;
        for part in rest.split_whitespace() {
            if let Some(t) = part.strip_prefix("total=") {
                total = Some(t.parse().ok()?);
            } else if let Some(o) = part.strip_prefix("offset=") {
                offset = o.parse().ok()?;
            }
        }
        return Some(OtaStatus::Ready {
            total: total?,
            offset,
        });
    }
    if let Some(rest) = raw.strip_prefix("OK ") {
        let sha256 = rest.trim().strip_prefix("sha256=")?.to_ascii_lowercase();
        if sha256.len() != 64 || !sha256.chars().all(|c| c.is_ascii_hexdigit()) {
            return None;
        }
        return Some(OtaStatus::Ok { sha256 });
    }
    if let Some(rest) = raw.strip_prefix("PROGRESS ") {
        let mut written = None;
        let mut total = None;
        for part in rest.split_whitespace() {
            if let Some(w) = part.strip_prefix("written=") {
                written = Some(w.parse().ok()?);
            } else if let Some(t) = part.strip_prefix("total=") {
                total = Some(t.parse().ok()?);
            }
        }
        return Some(OtaStatus::Progress {
            written: written?,
            total: total?,
        });
    }
    None
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn metrics_encode_decode_round_trip() {
        let m = AdvMetrics {
            seq: 42,
            flags: FLAG_DEEP_SLEEP_WAKE | FLAG_EPD_PARTIAL,
            wake_count: 1_024,
            sensor_us: 1_450,
            compute_us: 3_820,
            epd_refresh_us: 320_500,
            radio_us: 152_000,
            battery_mv: 3_910,
        };
        let bytes = encode_metrics(&m);
        assert_eq!(bytes.len(), PAYLOAD_LEN);
        assert_eq!(decode_metrics(&bytes), Some(m));
    }

    #[test]
    fn mfg_data_round_trip_and_company_id_validation() {
        let m = AdvMetrics {
            seq: 7,
            flags: FLAG_DEEP_SLEEP_WAKE,
            wake_count: 19,
            sensor_us: 900,
            compute_us: 2_100,
            epd_refresh_us: 1_850_000,
            radio_us: 148_000,
            battery_mv: 4_050,
        };
        let mfg = encode_mfg_data(&m);
        assert_eq!(mfg.len(), MFG_DATA_LEN);
        assert_eq!(mfg[0], 0xFF);
        assert_eq!(mfg[1], 0xFF);
        assert_eq!(decode_mfg_data(&mfg), Some(m));

        let mut bad_company = mfg;
        bad_company[0] = 0x4C; // Apple
        bad_company[1] = 0x00;
        assert_eq!(decode_mfg_data(&bad_company), None);
        assert_eq!(decode_mfg_data(&mfg[..10]), None);
    }

    #[test]
    fn adv_packet_is_31_bytes_and_round_trips() {
        let m = AdvMetrics {
            seq: 255,
            flags: FLAG_EPD_ATTACHED | FLAG_EPD_PARTIAL,
            wake_count: 99_999,
            sensor_us: 1_200,
            compute_us: 4_500,
            epd_refresh_us: 310_000,
            radio_us: 150_000,
            battery_mv: 3_720,
        };
        let pkt = encode_adv_packet(&m);
        assert_eq!(pkt.len(), ADV_PACKET_LEN);
        assert_eq!(&pkt[0..3], &[0x02, 0x01, 0x06]);
        assert_eq!(pkt[3], 27);
        assert_eq!(pkt[4], 0xFF);
        assert_eq!(decode_adv_packet(&pkt), Some(m));
    }

    #[test]
    fn phase_accumulator_tracks_wakes_and_previous_radio_tx() {
        let mut acc = PhaseAccumulator::new();
        let first = acc.record_wake(1_000, 2_000, 320_000, 3_950, 0);
        assert_eq!(first.seq, 1);
        assert_eq!(first.wake_count, 1);
        assert_eq!(first.radio_us, 0);

        acc.record_radio_tx(151_200);
        let second = acc.record_wake(1_100, 2_200, 320_000, 3_945, FLAG_DEEP_SLEEP_WAKE);
        assert_eq!(second.seq, 2);
        assert_eq!(second.wake_count, 2);
        assert_eq!(second.radio_us, 151_200);
        assert_eq!(acc.total_sensor_us, 2_100);
        assert_eq!(acc.total_compute_us, 4_200);
        assert_eq!(acc.total_epd_refresh_us, 640_000);
        assert_eq!(acc.total_radio_us, 151_200);
    }

    #[test]
    fn status_line_round_trip() {
        let m = AdvMetrics {
            seq: 12,
            flags: FLAG_DEEP_SLEEP_WAKE | FLAG_EPD_PARTIAL,
            wake_count: 12,
            sensor_us: 1_340,
            compute_us: 4_120,
            epd_refresh_us: 320_000,
            radio_us: 149_500,
            battery_mv: 3_880,
        };
        let line = format_status_line(&m);
        assert_eq!(
            line,
            "seq=12 wake=12 sensor_us=1340 compute_us=4120 epd_us=320000 radio_us=149500 batt_mv=3880 flags=0x05"
        );
        assert_eq!(parse_status_line(&line), Some(m));
    }

    #[test]
    fn otlp_json_contains_all_phases_and_attributes() {
        let m = AdvMetrics {
            seq: 3,
            flags: FLAG_DEEP_SLEEP_WAKE,
            wake_count: 15,
            sensor_us: 1_100,
            compute_us: 3_400,
            epd_refresh_us: 320_000,
            radio_us: 150_000,
            battery_mv: 3_890,
        };
        let json = format_otlp_json("xiao-c3-01", &m, -58, 1_700_000_000_000_000_000);
        assert!(json.contains(r#""service.name","value":{"stringValue":"xiao-esp32c3"}"#));
        assert!(json.contains(r#""device.id","value":{"stringValue":"xiao-c3-01"}"#));
        assert!(json.contains(r#""name":"mcu.wake.count""#));
        assert!(json.contains(r#""name":"mcu.phase.duration_us""#));
        assert!(json.contains(r#""stringValue":"sensor""#));
        assert!(json.contains(r#""stringValue":"compute""#));
        assert!(json.contains(r#""stringValue":"epd_refresh""#));
        assert!(json.contains(r#""stringValue":"radio""#));
        assert!(json.contains(r#""name":"mcu.battery_mv""#));
        assert!(json.contains(r#""name":"mcu.ble.rssi""#));
        assert!(json.contains(r#""asInt":"-58""#));
    }

    #[test]
    fn sensor_and_epd_benchmarks_are_deterministic() {
        let v1 = simulate_sensor_filter(1, 64);
        let v2 = simulate_sensor_filter(1, 64);
        assert_eq!(v1, v2);
        assert!((3200..=4200).contains(&v1));

        let mut frame = vec![0u8; EPD_FRAME_BYTES];
        let c1 = simulate_epd_frame(&mut frame, 10, v1, true);
        let c2 = simulate_epd_frame(&mut frame, 10, v1, false);
        assert_ne!(c1, c2);
    }

    #[test]
    fn energy_and_total_active_us() {
        let m = AdvMetrics {
            seq: 1,
            flags: 0,
            wake_count: 1,
            sensor_us: 1_000,
            compute_us: 4_000,
            epd_refresh_us: 320_000,
            radio_us: 150_000,
            battery_mv: 3_700,
        };
        assert_eq!(m.total_active_us(), 475_000);
        assert!(m.estimated_energy_uj() > 50_000);
    }

    #[test]
    fn ota_command_and_status_round_trip() {
        let sha = "a".repeat(64);
        let begin = OtaCommand::Begin {
            size: 384_000,
            sha256: sha.clone(),
        };
        assert_eq!(parse_ota_command(&encode_ota_command(&begin)), Some(begin));
        assert_eq!(
            parse_ota_command(&format!("begin 384000 sha256:{sha}")),
            Some(OtaCommand::Begin {
                size: 384_000,
                sha256: sha.clone(),
            })
        );
        assert_eq!(
            parse_ota_command(&encode_ota_command(&OtaCommand::Commit)),
            Some(OtaCommand::Commit)
        );
        assert_eq!(
            parse_ota_command(&encode_ota_command(&OtaCommand::Abort)),
            Some(OtaCommand::Abort)
        );
        assert_eq!(parse_ota_command("BEGIN 0 aaaa"), None);
        assert_eq!(parse_ota_command("BEGIN 99999999 aaaa"), None);

        for st in [
            OtaStatus::Idle,
            OtaStatus::Ready {
                total: 384_000,
                offset: 0,
            },
            OtaStatus::Ready {
                total: 384_000,
                offset: 65_536,
            },
            OtaStatus::Progress {
                written: 65_536,
                total: 384_000,
            },
            OtaStatus::Ok { sha256: sha },
            OtaStatus::Error {
                message: "sha256 mismatch".to_string(),
            },
        ] {
            let line = format_ota_status(&st);
            assert_eq!(parse_ota_status(&line), Some(st), "{line}");
        }
    }

    #[test]
    fn wake_profile_recorder_and_json_format() {
        let mut rec = SpanRecorder::new(10_000);
        rec.record("boot.init", "wake", 10_000, 10_450);
        rec.record("epd.spi_transfer", "epd_refresh", 12_000, 14_800);
        rec.record("epd.busy_wait", "epd_refresh", 14_800, 46_800);

        let profile = WakeProfile {
            wake_count: 7,
            seq: 7,
            board: "waveshare-epd-75".to_string(),
            chip: "esp32".to_string(),
            app: "epd-maze".to_string(),
            git_sha: "a".repeat(40),
            build_id: "b".repeat(40),
            free_heap_bytes: 210_944,
            min_free_heap_bytes: 198_400,
            stack_high_water_bytes: 3_072,
            cpu_cycles: 7_420_000,
            spans: rec.into_spans(),
            pc_samples: vec![
                PcSample {
                    pc: 0x400d_1a40,
                    hits: 14,
                },
                PcSample {
                    pc: 0x4200_3c18,
                    hits: 5,
                },
            ],
        };
        let json = format_wake_profile_json(&profile);
        assert!(json.contains(r#""wake":7"#));
        assert!(json.contains(r#""board":"waveshare-epd-75""#));
        assert!(json.contains(r#""chip":"esp32""#));
        assert!(json.contains(r#""app":"epd-maze""#));
        assert!(json.contains(&format!(r#""git_sha":"{}""#, "a".repeat(40))));
        assert!(json.contains(&format!(r#""build_id":"{}""#, "b".repeat(40))));
        assert!(json.contains(r#""free_heap":210944"#));
        assert!(json.contains(r#""min_heap":198400"#));
        assert!(json.contains(r#""stack_hw":3072"#));
        assert!(json.contains(r#""cycles":7420000"#));
        assert!(json.contains(
            r#""name":"epd.busy_wait","parent":"epd_refresh","start_us":4800,"dur_us":32000"#
        ));
        assert!(json.contains(r#""pc":"0x400d1a40","hits":14"#));
    }

    #[test]
    fn pc_histogram_filters_invalid_addrs_and_sorts_hotspots() {
        assert!(is_esp_code_addr(0x4200_1a40)); // ESP32-C3 Flash XIP IROM
        assert!(is_esp_code_addr(0x4038_0100)); // ESP32-C3 IRAM
        assert!(is_esp_code_addr(0x400D_1a40)); // ESP32 Xtensa Flash IROM
        assert!(is_esp_code_addr(0x4008_1000)); // ESP32 Xtensa IRAM
        assert!(is_esp_code_addr(0x4000_0400)); // ROM
        assert!(!is_esp_code_addr(0x0000_0000));
        assert!(!is_esp_code_addr(0x3FC8_1000)); // DRAM (not executable)

        let mut hist = PcHistogram::new();
        hist.record(0x3FC8_1000); // ignored
        hist.record(0x4200_3c18);
        hist.record(0x400D_1a40);
        hist.record(0x400D_1a40);
        hist.record(0x400D_1a40);
        hist.record(0x4200_3c18);

        let top = hist.top_samples(2);
        assert_eq!(
            top,
            vec![
                PcSample {
                    pc: 0x400D_1a40,
                    hits: 3,
                },
                PcSample {
                    pc: 0x4200_3c18,
                    hits: 2,
                },
            ]
        );
    }

    #[test]
    fn board_flags_and_esp_image_chip_id_validation() {
        let flags = FLAG_DEEP_SLEEP_WAKE | encode_board_flags(BOARD_WAVESHARE_EPD75);
        assert_eq!(decode_board_id(flags), BOARD_WAVESHARE_EPD75);
        assert_eq!(flags & FLAG_DEEP_SLEEP_WAKE, FLAG_DEEP_SLEEP_WAKE);

        let mut esp32_hdr = [0u8; 24];
        esp32_hdr[0] = 0xE9;
        esp32_hdr[12..14].copy_from_slice(&CHIP_ID_ESP32.to_le_bytes());
        assert!(validate_esp_image_header(&esp32_hdr, CHIP_ID_ESP32).is_ok());
        assert!(validate_esp_image_header(&esp32_hdr, CHIP_ID_ESP32C3).is_err());

        let mut c3_hdr = [0u8; 24];
        c3_hdr[0] = 0xE9;
        c3_hdr[12..14].copy_from_slice(&CHIP_ID_ESP32C3.to_le_bytes());
        assert!(validate_esp_image_header(&c3_hdr, CHIP_ID_ESP32C3).is_ok());
        assert!(validate_esp_image_header(&c3_hdr, CHIP_ID_ESP32).is_err());

        c3_hdr[0] = 0x00;
        assert!(validate_esp_image_header(&c3_hdr, CHIP_ID_ESP32C3).is_err());
    }
}

/// Returns true if `pc` lies inside ESP32 or ESP32-C3 executable instruction memory
/// (Flash XIP IROM, IRAM, or internal ROM).
pub const fn is_esp_code_addr(pc: u32) -> bool {
    (pc >= 0x4200_0000 && pc < 0x4400_0000) // ESP32-C3 Flash XIP
        || (pc >= 0x4037_C000 && pc < 0x403E_0000) // ESP32-C3 IRAM
        || (pc >= 0x400D_0000 && pc < 0x4040_0000) // ESP32 Xtensa Flash IROM
        || (pc >= 0x4008_0000 && pc < 0x400A_0000) // ESP32 Xtensa IRAM
        || (pc >= 0x4000_0000 && pc < 0x4006_0000) // Internal ROM
}

/// Fixed-size zero-allocation PC sample histogram used by the 1 kHz profiler timer.
#[derive(Debug, Clone)]
pub struct PcHistogram {
    pcs: [u32; 64],
    hits: [u16; 64],
    len: usize,
}

impl Default for PcHistogram {
    fn default() -> Self {
        Self::new()
    }
}

impl PcHistogram {
    pub const fn new() -> Self {
        Self {
            pcs: [0; 64],
            hits: [0; 64],
            len: 0,
        }
    }

    /// Record a sampled PC address (aligned to 4 bytes). Ignores non-code addresses.
    pub fn record(&mut self, pc: u32) {
        if !is_esp_code_addr(pc) {
            return;
        }
        let aligned = pc & !0x3;
        for i in 0..self.len {
            if self.pcs[i] == aligned {
                self.hits[i] = self.hits[i].saturating_add(1);
                return;
            }
        }
        if self.len < self.pcs.len() {
            self.pcs[self.len] = aligned;
            self.hits[self.len] = 1;
            self.len += 1;
        }
    }

    /// Return up to `limit` top hotspots sorted descending by hit count.
    pub fn top_samples(&self, limit: usize) -> Vec<PcSample> {
        let mut out: Vec<PcSample> = (0..self.len)
            .map(|i| PcSample {
                pc: self.pcs[i],
                hits: self.hits[i],
            })
            .collect();
        out.sort_by(|a, b| b.hits.cmp(&a.hits).then_with(|| a.pc.cmp(&b.pc)));
        out.truncate(limit);
        out
    }
}

/// A single sub-phase timing span recorded on the MCU relative to wake start.
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct ProfileSpan {
    pub name: String,
    pub parent: String,
    pub start_us: u32,
    pub duration_us: u32,
}

/// A sampled program counter hotspot (`pc` address + sample hit count).
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub struct PcSample {
    pub pc: u32,
    pub hits: u16,
}

/// Detailed per-wake profiling snapshot served over BLE GATT (`PROFILE_CHAR_UUID`).
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct WakeProfile {
    pub wake_count: u32,
    pub seq: u8,
    pub board: String,
    pub chip: String,
    pub app: String,
    pub git_sha: String,
    pub build_id: String,
    pub free_heap_bytes: u32,
    pub min_free_heap_bytes: u32,
    pub stack_high_water_bytes: u32,
    pub cpu_cycles: u64,
    pub spans: Vec<ProfileSpan>,
    pub pc_samples: Vec<PcSample>,
}

/// Lightweight microsecond span recorder anchored to the start of a wake cycle.
#[derive(Debug, Default)]
pub struct SpanRecorder {
    wake_start_us: u64,
    spans: Vec<ProfileSpan>,
}

impl SpanRecorder {
    pub fn new(wake_start_us: u64) -> Self {
        Self {
            wake_start_us,
            spans: Vec::with_capacity(12),
        }
    }

    pub fn record(&mut self, name: &str, parent: &str, start_us: u64, end_us: u64) {
        let rel_start =
            u32::try_from(start_us.saturating_sub(self.wake_start_us)).unwrap_or(u32::MAX);
        let dur = u32::try_from(end_us.saturating_sub(start_us)).unwrap_or(u32::MAX);
        self.spans.push(ProfileSpan {
            name: name.to_string(),
            parent: parent.to_string(),
            start_us: rel_start,
            duration_us: dur,
        });
    }

    pub fn into_spans(self) -> Vec<ProfileSpan> {
        self.spans
    }
}

/// Serialize a [`WakeProfile`] as compact JSON for BLE GATT transfer (`PROFILE_CHAR_UUID`).
pub fn format_wake_profile_json(p: &WakeProfile) -> String {
    let mut out = String::with_capacity(512);
    out.push_str(&format!(
        r#"{{"v":1,"wake":{},"seq":{},"#,
        p.wake_count, p.seq
    ));
    if !p.board.is_empty() {
        out.push_str(&format!(r#""board":"{}","#, escape_json_str(&p.board)));
    }
    if !p.chip.is_empty() {
        out.push_str(&format!(r#""chip":"{}","#, escape_json_str(&p.chip)));
    }
    if !p.app.is_empty() {
        out.push_str(&format!(r#""app":"{}","#, escape_json_str(&p.app)));
    }
    if !p.git_sha.is_empty() {
        out.push_str(&format!(r#""git_sha":"{}","#, escape_json_str(&p.git_sha)));
    }
    if !p.build_id.is_empty() {
        out.push_str(&format!(
            r#""build_id":"{}","#,
            escape_json_str(&p.build_id)
        ));
    }
    out.push_str(&format!(
        r#""free_heap":{},"min_heap":{},"stack_hw":{},"cycles":{},"spans":["#,
        p.free_heap_bytes, p.min_free_heap_bytes, p.stack_high_water_bytes, p.cpu_cycles,
    ));
    for (idx, sp) in p.spans.iter().enumerate() {
        if idx > 0 {
            out.push(',');
        }
        out.push_str(&format!(
            r#"{{"name":"{}","parent":"{}","start_us":{},"dur_us":{}}}"#,
            escape_json_str(&sp.name),
            escape_json_str(&sp.parent),
            sp.start_us,
            sp.duration_us,
        ));
    }
    out.push_str(r#"],"pcs":["#);
    for (idx, s) in p.pc_samples.iter().enumerate() {
        if idx > 0 {
            out.push(',');
        }
        out.push_str(&format!(r#"{{"pc":"0x{:08x}","hits":{}}}"#, s.pc, s.hits));
    }
    out.push_str("]}");
    out
}

/// Standard IEEE 802.3 CRC32 (polynomial `0xEDB88320`).
pub fn crc32(data: &[u8]) -> u32 {
    let mut crc: u32 = 0xFFFF_FFFF;
    for &byte in data {
        crc ^= u32::from(byte);
        for _ in 0..8 {
            let mask = (crc & 1).wrapping_neg();
            crc = (crc >> 1) ^ (0xEDB8_8320 & mask);
        }
    }
    !crc
}

/// Magic tag identifying a valid [`RtcState`] envelope in `.rtc.data`.
pub const RTC_STATE_MAGIC: u32 = 0x4D43_554C; // "MCUL"

/// Crash-loop threshold: if a `PENDING_VERIFY` image crashes this many times in a
/// row without completing `self_test()`, trigger immediate bootloader rollback.
pub const MAX_CRASH_STREAK: u8 = 3;

/// CRC32-protected retained state placed in `.rtc.data` so brownout-corrupted RTC RAM
/// resets cleanly instead of propagating garbage counters.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
#[repr(C)]
pub struct RtcState {
    pub magic: u32,
    pub accumulator: PhaseAccumulator,
    pub crash_streak: u8,
    pub reserved: [u8; 3],
    pub checksum: u32,
}

impl Default for RtcState {
    fn default() -> Self {
        Self::new()
    }
}

impl RtcState {
    pub const fn new() -> Self {
        Self {
            magic: RTC_STATE_MAGIC,
            accumulator: PhaseAccumulator::new(),
            crash_streak: 0,
            reserved: [0; 3],
            checksum: 0,
        }
    }

    fn compute_crc(&self) -> u32 {
        let mut buf = [0u8; 48];
        buf[0..4].copy_from_slice(&self.magic.to_le_bytes());
        buf[4] = self.accumulator.seq;
        buf[5] = self.crash_streak;
        buf[6..10].copy_from_slice(&self.accumulator.wake_count.to_le_bytes());
        buf[10..14].copy_from_slice(&self.accumulator.last_radio_us.to_le_bytes());
        buf[14..22].copy_from_slice(&self.accumulator.total_sensor_us.to_le_bytes());
        buf[22..30].copy_from_slice(&self.accumulator.total_compute_us.to_le_bytes());
        buf[30..38].copy_from_slice(&self.accumulator.total_epd_refresh_us.to_le_bytes());
        buf[38..46].copy_from_slice(&self.accumulator.total_radio_us.to_le_bytes());
        crc32(&buf[..46])
    }

    /// Validate the magic tag and CRC32. If invalid (e.g., cold boot or brownout),
    /// reset to a clean state and return `false`.
    pub fn validate_or_reset(&mut self) -> bool {
        if self.magic == RTC_STATE_MAGIC && self.checksum == self.compute_crc() {
            return true;
        }
        *self = Self::new();
        self.seal();
        false
    }

    /// Recompute and store the CRC32 after mutating fields.
    pub fn seal(&mut self) {
        self.magic = RTC_STATE_MAGIC;
        self.checksum = self.compute_crc();
    }
}

/// Magic header for framed resumable OTA data chunks on [`OTA_DATA_UUID`].
///
/// Format: `[b'O', b'T', offset: u32 LE, crc32: u32 LE, payload...]`
pub const OTA_CHUNK_MAGIC: [u8; 2] = *b"OT";

/// Header size in bytes for a framed OTA data chunk.
pub const OTA_CHUNK_HEADER_LEN: usize = 10;

/// Decoded framed OTA data chunk.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub struct OtaChunkFrame<'a> {
    pub offset: u32,
    pub crc32: u32,
    pub payload: &'a [u8],
}

/// Encode an offset + CRC32 framed OTA chunk for [`OTA_DATA_UUID`].
pub fn encode_ota_chunk_frame(offset: u32, payload: &[u8]) -> Vec<u8> {
    let mut out = Vec::with_capacity(OTA_CHUNK_HEADER_LEN + payload.len());
    out.extend_from_slice(&OTA_CHUNK_MAGIC);
    out.extend_from_slice(&offset.to_le_bytes());
    out.extend_from_slice(&crc32(payload).to_le_bytes());
    out.extend_from_slice(payload);
    out
}

/// Decode and CRC32-verify a framed OTA chunk.
///
/// Returns `Ok(Some(frame))` if the buffer starts with [`OTA_CHUNK_MAGIC`] and passes CRC32,
/// `Ok(None)` if the buffer does not carry the framed magic (legacy v1 raw chunk), or
/// `Err(reason)` if the frame is truncated or fails CRC32 verification.
pub fn decode_ota_chunk_frame(raw: &[u8]) -> Result<Option<OtaChunkFrame<'_>>, String> {
    if raw.len() < 2 || raw[0..2] != OTA_CHUNK_MAGIC {
        return Ok(None);
    }
    if raw.len() < OTA_CHUNK_HEADER_LEN {
        return Err(format!("truncated OTA frame ({} bytes)", raw.len()));
    }
    let offset = u32::from_le_bytes([raw[2], raw[3], raw[4], raw[5]]);
    let expected_crc = u32::from_le_bytes([raw[6], raw[7], raw[8], raw[9]]);
    let payload = &raw[OTA_CHUNK_HEADER_LEN..];
    let actual_crc = crc32(payload);
    if actual_crc != expected_crc {
        return Err(format!(
            "chunk crc32 mismatch at offset {offset}: got {actual_crc:#010x}, want {expected_crc:#010x}"
        ));
    }
    Ok(Some(OtaChunkFrame {
        offset,
        crc32: expected_crc,
        payload,
    }))
}

/// Magic header for chunked BLE GATT blob transfers ([`PROFILE_CHAR_UUID`] and [`COREDUMP_CHAR_UUID`]).
///
/// Format: `[b'M', b'C', index: u16 LE, total: u16 LE, payload...]`
pub const BLOB_FRAME_MAGIC: [u8; 2] = *b"MC";

/// Header size in bytes for a chunked BLE blob frame.
pub const BLOB_FRAME_HEADER_LEN: usize = 6;

/// Split `data` into BLE GATT frames with 6-byte headers (`"MC"`, `index`, `total`).
pub fn encode_blob_frames(data: &[u8], max_payload_per_frame: usize) -> Vec<Vec<u8>> {
    let chunk_size = max_payload_per_frame.max(1);
    if data.is_empty() {
        let mut frame = Vec::with_capacity(BLOB_FRAME_HEADER_LEN);
        frame.extend_from_slice(&BLOB_FRAME_MAGIC);
        frame.extend_from_slice(&0u16.to_le_bytes());
        frame.extend_from_slice(&1u16.to_le_bytes());
        return vec![frame];
    }
    let total_chunks = data.len().div_ceil(chunk_size);
    let total = u16::try_from(total_chunks).unwrap_or(u16::MAX);
    let mut frames = Vec::with_capacity(total_chunks);
    for (idx, chunk) in data.chunks(chunk_size).enumerate() {
        if idx >= usize::from(u16::MAX) {
            break;
        }
        let mut frame = Vec::with_capacity(BLOB_FRAME_HEADER_LEN + chunk.len());
        frame.extend_from_slice(&BLOB_FRAME_MAGIC);
        frame.extend_from_slice(&(idx as u16).to_le_bytes());
        frame.extend_from_slice(&total.to_le_bytes());
        frame.extend_from_slice(chunk);
        frames.push(frame);
    }
    frames
}

/// Decode a single chunked BLE blob frame. Returns `(index, total, payload)` if valid.
pub fn decode_blob_frame(raw: &[u8]) -> Option<(u16, u16, &[u8])> {
    if raw.len() < BLOB_FRAME_HEADER_LEN || raw[0..2] != BLOB_FRAME_MAGIC {
        return None;
    }
    let idx = u16::from_le_bytes([raw[2], raw[3]]);
    let total = u16::from_le_bytes([raw[4], raw[5]]);
    if total == 0 || idx >= total {
        return None;
    }
    Some((idx, total, &raw[BLOB_FRAME_HEADER_LEN..]))
}

/// Reassembles sequential [`encode_blob_frames`] packets back into the original byte buffer.
#[derive(Debug, Default)]
pub struct BlobReassembler {
    total: u16,
    received: Vec<Option<Vec<u8>>>,
    count: usize,
}

impl BlobReassembler {
    pub fn new() -> Self {
        Self::default()
    }

    /// Push a frame. Returns `Some(complete_bytes)` once all `total` frames have arrived.
    pub fn push(&mut self, raw: &[u8]) -> Option<Vec<u8>> {
        let (idx, total, payload) = decode_blob_frame(raw)?;
        if self.total != total {
            self.total = total;
            self.received = vec![None; usize::from(total)];
            self.count = 0;
        }
        let slot = &mut self.received[usize::from(idx)];
        if slot.is_none() {
            *slot = Some(payload.to_vec());
            self.count += 1;
        }
        if self.count == usize::from(self.total) {
            let mut out = Vec::new();
            for part in self.received.drain(..).flatten() {
                out.extend_from_slice(&part);
            }
            self.total = 0;
            self.count = 0;
            return Some(out);
        }
        None
    }
}

#[cfg(test)]
mod hardening_tests {
    use super::*;

    #[test]
    fn crc32_matches_standard_ieee_vector() {
        assert_eq!(crc32(b"123456789"), 0xCBF4_3926);
        assert_eq!(crc32(b""), 0x0000_0000);
    }

    #[test]
    fn rtc_state_validates_and_recovers_from_corruption() {
        let mut rtc = RtcState::new();
        assert!(!rtc.validate_or_reset()); // unsealed initial struct resets & seals
        assert!(rtc.validate_or_reset());

        rtc.accumulator.record_wake(100, 200, 300, 3850, 0);
        rtc.crash_streak = 2;
        rtc.seal();
        assert!(rtc.validate_or_reset());
        assert_eq!(rtc.accumulator.wake_count, 1);
        assert_eq!(rtc.crash_streak, 2);

        // Flip a bit to simulate brownout corruption
        rtc.accumulator.wake_count ^= 0x0001_0000;
        assert!(!rtc.validate_or_reset());
        assert_eq!(rtc.accumulator.wake_count, 0);
        assert_eq!(rtc.crash_streak, 0);
        assert!(rtc.validate_or_reset());
    }

    #[test]
    fn ota_chunk_frame_round_trip_and_crc_rejection() {
        let payload = b"hello firmware bytes";
        let framed = encode_ota_chunk_frame(4096, payload);
        let decoded = decode_ota_chunk_frame(&framed).unwrap().unwrap();
        assert_eq!(decoded.offset, 4096);
        assert_eq!(decoded.payload, payload);

        let mut corrupted = framed.clone();
        *corrupted.last_mut().unwrap() ^= 0xFF;
        assert!(decode_ota_chunk_frame(&corrupted).is_err());

        // Legacy raw chunk starting with ESP-IDF 0xE9 magic returns Ok(None)
        let raw = [0xE9, 0x00, 0x01, 0x02];
        assert_eq!(decode_ota_chunk_frame(&raw), Ok(None));
    }

    #[test]
    fn blob_frames_round_trip_through_reassembler() {
        let data: Vec<u8> = (0..1200).map(|i| (i % 251) as u8).collect();
        let frames = encode_blob_frames(&data, 470);
        assert_eq!(frames.len(), 3);

        let mut reasm = BlobReassembler::new();
        assert!(reasm.push(&frames[0]).is_none());
        assert!(reasm.push(&frames[2]).is_none()); // out-of-order tolerated
        let assembled = reasm.push(&frames[1]).expect("complete");
        assert_eq!(assembled, data);
    }
}
