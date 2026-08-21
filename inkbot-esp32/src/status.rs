//! Bottom-of-panel error status line.
//!
//! The 7.5″ panel is the only debug surface once the device is in the field, so
//! messages pack Wi-Fi / fetch / crash context into a few 6×10 rows. When
//! nothing is wrong the overlay is a no-op — the image keeps the full 800×480.

use anyhow::Error as AnyhowError;
use embedded_graphics::{
    draw_target::DrawTarget,
    geometry::{OriginDimensions, Point, Size},
    mono_font::{ascii::FONT_6X10, MonoTextStyle},
    pixelcolor::BinaryColor,
    prelude::*,
    text::{Baseline, Text},
};
use serde::{Deserialize, Serialize};

use crate::panel::{FRAME_BYTES, PANEL_HEIGHT, PANEL_WIDTH};

/// Matches the HTTP `User-Agent` and `firmware` telemetry field.
pub const FIRMWARE_ID: &str = "inkbot-esp32/0.4";

/// Glyph width of `FONT_6X10` (includes the 1 px gap).
const GLYPH_W: u32 = 6;
/// Glyph height of `FONT_6X10`.
const GLYPH_H: u32 = 10;
const PAD_X: u32 = 4;
const PAD_TOP: u32 = 2;
const PAD_BOT: u32 = 2;
const SEP_H: u32 = 1;
const LINE_GAP: u32 = 1;

/// Columns that fit in the status bar with a 4 px left margin.
pub const STATUS_MAX_COLS: usize = ((PANEL_WIDTH - PAD_X) / GLYPH_W) as usize;
/// Rows of 6×10 text drawn into the bar.
pub const STATUS_MAX_LINES: usize = 3;

/// Height in pixels of a status bar that shows `lines` text rows (0 if none).
pub fn status_bar_height(lines: usize) -> u32 {
    if lines == 0 {
        return 0;
    }
    let n = lines.min(STATUS_MAX_LINES) as u32;
    SEP_H + PAD_TOP + n * GLYPH_H + n.saturating_sub(1) * LINE_GAP + PAD_BOT
}

/// Wi-Fi association / DHCP failure.
#[derive(Debug, Clone, PartialEq, Eq, Serialize, Deserialize)]
pub struct WifiStatus {
    pub ssid: String,
    pub step: String,
    pub cause: String,
    pub attempt: u32,
    pub attempts: u32,
    pub heap: u32,
    pub heap_min: u32,
    pub heap_largest: u32,
    pub uptime_secs: u64,
    /// `wifi_err_reason_t` from the last STA disconnect, if known.
    pub disconnect_reason: Option<u32>,
}

/// Catalog or framebuffer HTTP failure.
#[derive(Debug, Clone, PartialEq, Eq, Serialize, Deserialize)]
pub struct FetchStatus {
    pub op: String,
    pub url: String,
    pub http_status: Option<u16>,
    pub cause: String,
    pub attempt: u32,
    pub attempts: u32,
    pub bytes_read: Option<usize>,
    pub heap: u32,
    pub heap_min: u32,
    pub heap_largest: u32,
    pub uptime_secs: u64,
    pub ip: Option<String>,
}

/// Abnormal reset / panic captured at boot.
#[derive(Debug, Clone, PartialEq, Eq, Serialize, Deserialize)]
pub struct CrashStatus {
    pub reset_code: i32,
    pub panic_message: Option<String>,
    pub last_op: Option<String>,
    pub heap: u32,
    pub heap_min: u32,
    pub heap_largest: u32,
}

/// Combined on-screen error state. All-`None` renders as no overlay.
#[derive(Debug, Clone, Default, PartialEq, Eq)]
pub struct StatusReport {
    pub wifi: Option<WifiStatus>,
    pub fetch: Option<FetchStatus>,
    pub crash: Option<CrashStatus>,
}

impl StatusReport {
    pub fn is_empty(&self) -> bool {
        self.wifi.is_none() && self.fetch.is_none() && self.crash.is_none()
    }

    /// Multi-line status text, or `None` when the panel should stay full-image.
    pub fn render(&self) -> Option<String> {
        let mut lines: Vec<String> = Vec::new();
        if let Some(w) = &self.wifi {
            lines.extend(w.lines());
        }
        if let Some(f) = &self.fetch {
            lines.extend(f.lines());
        }
        if let Some(c) = &self.crash {
            lines.extend(c.lines());
        }
        if lines.is_empty() {
            return None;
        }
        Some(wrap_lines(&lines, STATUS_MAX_COLS, STATUS_MAX_LINES).join("\n"))
    }
}

/// JSON payload POSTed to the Worker `POST /device`.
#[derive(Debug, Clone, PartialEq, Eq, Serialize, Deserialize)]
pub struct DeviceTelemetry {
    pub firmware: String,
    pub uptime_secs: u64,
    pub reset_code: i32,
    pub reset_name: String,
    pub heap: u32,
    pub heap_min: u32,
    pub heap_largest: u32,
    #[serde(skip_serializing_if = "Option::is_none")]
    pub ip: Option<String>,
    #[serde(skip_serializing_if = "Option::is_none")]
    pub ssid: Option<String>,
    #[serde(skip_serializing_if = "Option::is_none")]
    pub current_image: Option<String>,
    #[serde(skip_serializing_if = "Option::is_none")]
    pub last_op: Option<String>,
    #[serde(skip_serializing_if = "Option::is_none")]
    pub error: Option<String>,
    #[serde(skip_serializing_if = "Option::is_none")]
    pub wifi: Option<WifiStatus>,
    #[serde(skip_serializing_if = "Option::is_none")]
    pub fetch: Option<FetchStatus>,
    #[serde(skip_serializing_if = "Option::is_none")]
    pub crash: Option<CrashStatus>,
    pub panel_has_status: bool,
    pub posts_ok: u32,
    pub posts_fail: u32,
    #[serde(skip_serializing_if = "Option::is_none")]
    pub last_post_error: Option<String>,
    /// Wall clock after SNTP; omitted if NTP has not synced.
    #[serde(skip_serializing_if = "Option::is_none")]
    pub unix_secs: Option<i64>,
    #[serde(skip_serializing_if = "Option::is_none")]
    pub rssi: Option<i32>,
    #[serde(skip_serializing_if = "Option::is_none")]
    pub gateway: Option<String>,
    #[serde(skip_serializing_if = "Option::is_none")]
    pub dns: Option<String>,
    #[serde(skip_serializing_if = "Option::is_none")]
    pub last_ok_uptime_secs: Option<u64>,
    #[serde(skip_serializing_if = "Option::is_none")]
    pub last_ok_op: Option<String>,
    /// Last FETCH/WIFI failure kept until a POST succeeds, so a CONNECT
    /// outage is still visible after HTTPS recovers (or after a reboot).
    #[serde(skip_serializing_if = "Option::is_none")]
    pub last_incident: Option<LastIncident>,
    pub dhcp_renews: u32,
    pub reconnects_ok: u32,
    pub reconnects_fail: u32,
    #[serde(skip_serializing_if = "Option::is_none")]
    pub last_refresh: Option<String>,
    #[serde(skip_serializing_if = "Option::is_none")]
    pub last_refresh_uptime: Option<u64>,
}

/// Compact outage record: NVS + `POST /device` after the radio recovers.
#[derive(Debug, Clone, PartialEq, Eq, Serialize, Deserialize)]
pub struct LastIncident {
    pub kind: String,
    pub uptime_secs: u64,
    #[serde(skip_serializing_if = "Option::is_none")]
    pub unix_secs: Option<i64>,
    #[serde(skip_serializing_if = "Option::is_none")]
    pub ip: Option<String>,
    #[serde(skip_serializing_if = "Option::is_none")]
    pub op: Option<String>,
    pub error: String,
    #[serde(skip_serializing_if = "Option::is_none")]
    pub rssi: Option<i32>,
    #[serde(skip_serializing_if = "Option::is_none")]
    pub gateway: Option<String>,
}

/// Radio / clock fields captured with a FETCH or WIFI overlay.
#[derive(Debug, Clone, Default, PartialEq, Eq)]
pub struct IncidentContext {
    pub uptime_secs: u64,
    pub unix_secs: Option<i64>,
    pub ip: Option<String>,
    pub op: Option<String>,
    pub rssi: Option<i32>,
    pub gateway: Option<String>,
}

impl LastIncident {
    pub fn from_status(kind: &str, status: &StatusReport, ctx: IncidentContext) -> Option<Self> {
        let error = status.render()?;
        Some(Self {
            kind: kind.to_string(),
            uptime_secs: ctx.uptime_secs,
            unix_secs: ctx.unix_secs,
            ip: ctx.ip,
            op: ctx.op,
            error,
            rssi: ctx.rssi,
            gateway: ctx.gateway,
        })
    }
}

impl DeviceTelemetry {
    #[allow(clippy::too_many_arguments)]
    pub fn from_parts(
        status: &StatusReport,
        uptime_secs: u64,
        reset_code: i32,
        heap: u32,
        heap_min: u32,
        heap_largest: u32,
        ip: Option<String>,
        ssid: Option<String>,
        current_image: Option<String>,
        last_op: Option<String>,
        panel_has_status: bool,
        posts_ok: u32,
        posts_fail: u32,
        last_post_error: Option<String>,
    ) -> Self {
        Self {
            firmware: FIRMWARE_ID.to_string(),
            uptime_secs,
            reset_code,
            reset_name: reset_reason_name(reset_code).to_string(),
            heap,
            heap_min,
            heap_largest,
            ip,
            ssid,
            current_image,
            last_op,
            error: status.render(),
            wifi: status.wifi.clone(),
            fetch: status.fetch.clone(),
            crash: status.crash.clone(),
            panel_has_status,
            posts_ok,
            posts_fail,
            last_post_error,
            unix_secs: None,
            rssi: None,
            gateway: None,
            dns: None,
            last_ok_uptime_secs: None,
            last_ok_op: None,
            last_incident: None,
            dhcp_renews: 0,
            reconnects_ok: 0,
            reconnects_fail: 0,
            last_refresh: None,
            last_refresh_uptime: None,
        }
    }
}

/// When to POST `/device`: boot, error text change, queued incident, or interval.
pub fn should_post_status(
    secret_configured: bool,
    force: bool,
    error_changed: bool,
    secs_since_post: u64,
    status_secs: u64,
) -> bool {
    if !secret_configured {
        return false;
    }
    force || error_changed || secs_since_post >= status_secs
}

/// Force a POST after Wi-Fi recovery so `last_incident` reaches the Worker
/// even if the retry succeeded and the panel overlay was cleared.
pub fn incident_needs_post(incident_unposted: bool, recovered: bool) -> bool {
    incident_unposted || recovered
}

impl WifiStatus {
    fn lines(&self) -> Vec<String> {
        let mut head = format!(
            "WIFI ERR step={} try={}/{} ssid={} 2.4GHz up={}s",
            self.step, self.attempt, self.attempts, self.ssid, self.uptime_secs
        );
        if let Some(code) = self.disconnect_reason {
            match wifi_reason_name(code) {
                Some(name) => {
                    head.push_str(&format!(" disc={name}({code})"));
                }
                None => head.push_str(&format!(" disc={code}")),
            }
        }
        vec![
            head,
            format!(
                "{} {}",
                self.cause,
                format_heap(self.heap, self.heap_min, self.heap_largest)
            ),
        ]
    }
}

impl FetchStatus {
    fn lines(&self) -> Vec<String> {
        let mut head = format!(
            "FETCH ERR {} {} up={}s try={}/{}",
            self.op,
            shorten_url(&self.url, 48),
            self.uptime_secs,
            self.attempt,
            self.attempts
        );
        if let Some(st) = self.http_status {
            head.push_str(&format!(" HTTP {st}"));
        }
        if let Some(n) = self.bytes_read {
            head.push_str(&format!(" bytes={n}"));
        }
        if let Some(ip) = &self.ip {
            head.push_str(&format!(" ip={ip}"));
        }
        vec![
            head,
            format!(
                "{} {}",
                self.cause,
                format_heap(self.heap, self.heap_min, self.heap_largest)
            ),
        ]
    }
}

impl CrashStatus {
    fn lines(&self) -> Vec<String> {
        let name = reset_reason_name(self.reset_code);
        let mut head = format!("CRASH {name} ({})", self.reset_code);
        if let Some(op) = &self.last_op {
            head.push_str(" last=");
            head.push_str(op);
        }
        head.push(' ');
        head.push_str(&format_heap(self.heap, self.heap_min, self.heap_largest));
        let mut out = vec![head];
        let mut detail = reset_reason_hint(self.reset_code).to_string();
        if let Some(panic) = &self.panic_message {
            if !detail.is_empty() {
                detail.push_str(" | ");
            }
            detail.push_str("panic=");
            detail.push_str(panic);
        }
        if !detail.is_empty() {
            out.push(detail);
        }
        out
    }
}

fn format_heap(free: u32, min: u32, largest: u32) -> String {
    format!("heap={free} min={min} big={largest}")
}

/// Prefer the path when a URL is too long for one field.
pub fn shorten_url(url: &str, max: usize) -> String {
    if url.chars().count() <= max {
        return url.to_string();
    }
    let path = url
        .find("://")
        .and_then(|i| url[i + 3..].find('/').map(|j| &url[i + 3 + j..]))
        .unwrap_or(url);
    if path.chars().count() <= max {
        return path.to_string();
    }
    let chars: Vec<char> = path.chars().collect();
    let keep = max.saturating_sub(3);
    let mut s: String = chars[chars.len() - keep..].iter().collect();
    s.insert_str(0, "...");
    s
}

/// Flatten an `anyhow` chain into one panel-sized cause string.
pub fn format_error_chain(err: &AnyhowError) -> String {
    let mut out = String::new();
    for (i, cause) in err.chain().enumerate() {
        if i > 0 {
            out.push_str(" | ");
        }
        out.push_str(&cause.to_string());
        if out.len() > 240 {
            out.truncate(237);
            out.push_str("...");
            break;
        }
    }
    out
}

/// Wrap already-built lines to `cols`, then keep at most `max_lines`.
pub fn wrap_lines(lines: &[String], cols: usize, max_lines: usize) -> Vec<String> {
    if cols == 0 || max_lines == 0 {
        return Vec::new();
    }
    let mut out: Vec<String> = Vec::new();
    for line in lines {
        out.extend(wrap_one(line, cols));
    }
    if out.len() > max_lines {
        out.truncate(max_lines);
        let last = &mut out[max_lines - 1];
        let count = last.chars().count();
        if count + 3 > cols {
            let keep = cols.saturating_sub(3);
            *last = last.chars().take(keep).collect();
        }
        last.push_str("...");
    }
    out
}

fn wrap_one(s: &str, cols: usize) -> Vec<String> {
    let chars: Vec<char> = s.chars().collect();
    if chars.is_empty() {
        return vec![String::new()];
    }
    chars.chunks(cols).map(|c| c.iter().collect()).collect()
}

/// `esp_reset_reason_t` names (ESP-IDF). Unknown codes stay `"OTHER"`.
pub fn reset_reason_name(code: i32) -> &'static str {
    match code {
        0 => "UNKNOWN",
        1 => "POWERON",
        2 => "EXT",
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
        13 => "EFUSE",
        14 => "PWR_GLITCH",
        15 => "CPU_LOCKUP",
        _ => "OTHER",
    }
}

/// Resets that should paint a crash line (not a normal power-on / button).
pub fn reset_is_abnormal(code: i32) -> bool {
    matches!(code, 0 | 3 | 4 | 5 | 6 | 7 | 9 | 14 | 15)
}

/// True when the panel should show a crash line for this reset.
///
/// `ESP_RST_SW` (3) after an intentional OTA reboot (`last_op` starts
/// with `ota:`) is expected and is not a crash.
pub fn crash_after_reset(code: i32, last_op: Option<&str>) -> bool {
    if code == 3 && last_op.is_some_and(|op| op.starts_with("ota:")) {
        return false;
    }
    reset_is_abnormal(code)
}

/// Short field-debug hint for an abnormal reset. Empty for normal boots.
pub fn reset_reason_hint(code: i32) -> &'static str {
    match code {
        0 => "reset reason lost",
        3 => "esp_restart/SW reset (main returned or abort)",
        4 => "Rust/IDF panic; see panic= if present",
        5 => "interrupt watchdog: hung in ISR/wifi",
        6 => "task watchdog: hung in wifi/http/display",
        7 => "other watchdog timeout",
        9 => "5V sagged on Wi-Fi TX; use >=1A supply + short cable",
        14 => "power glitch detector",
        15 => "CPU lockup",
        _ => "",
    }
}

/// Common `wifi_err_reason_t` values from ESP-IDF.
pub fn wifi_reason_name(code: u32) -> Option<&'static str> {
    Some(match code {
        1 => "UNSPECIFIED",
        2 => "AUTH_EXPIRE",
        3 => "AUTH_LEAVE",
        4 => "ASSOC_EXPIRE",
        5 => "ASSOC_TOOMANY",
        8 => "ASSOC_LEAVE",
        15 => "4WAY_HANDSHAKE_TIMEOUT",
        200 => "BEACON_TIMEOUT",
        201 => "NO_AP_FOUND",
        202 => "AUTH_FAIL",
        203 => "ASSOC_FAIL",
        204 => "HANDSHAKE_TIMEOUT",
        205 => "CONNECTION_FAIL",
        210 => "NO_AP_FOUND_IN_RSSI_THRESHOLD",
        211 => "NO_AP_FOUND_IN_AUTHMODE_THRESHOLD",
        212 => "NO_AP_FOUND_W_COMPATIBLE_SECURITY",
        _ => return None,
    })
}

/// Compact panic text for RTC / the crash line (`msg @file:line`).
pub fn format_panic_message(msg: &str, file: &str, line: u32) -> String {
    let file = file.rsplit('/').next().unwrap_or(file);
    let mut s = format!("{msg} @{file}:{line}");
    const MAX: usize = 160;
    if s.chars().count() > MAX {
        s = s.chars().take(MAX - 3).collect();
        s.push_str("...");
    }
    s
}

/// Paint `text` into a white bar at the bottom of a packed 1-bit frame.
///
/// `text` is pre-wrapped (`\n` separated). Empty text leaves `frame` unchanged
/// so a healthy device never loses image rows.
pub fn overlay_status_line(frame: &mut [u8], text: &str) -> Result<(), String> {
    if frame.len() != FRAME_BYTES {
        return Err(format!(
            "framebuffer must be {FRAME_BYTES} bytes, got {}",
            frame.len()
        ));
    }
    if text.is_empty() {
        return Ok(());
    }
    let lines: Vec<&str> = text.lines().collect();
    let n = lines.len().min(STATUS_MAX_LINES);
    if n == 0 {
        return Ok(());
    }
    let bar_h = status_bar_height(n);
    let y0 = PANEL_HEIGHT - bar_h;
    let row_bytes = (PANEL_WIDTH / 8) as usize;
    let start = y0 as usize * row_bytes;
    frame[start..].fill(0xff);
    // 1 px black separator so a white image still shows the bar edge.
    let sep_end = start + row_bytes;
    frame[start..sep_end].fill(0x00);

    let mut target = PackedFrame { buf: frame };
    let style = MonoTextStyle::new(&FONT_6X10, BinaryColor::On);
    let mut y = y0 as i32 + SEP_H as i32 + PAD_TOP as i32;
    for line in lines.iter().take(n) {
        let t = Text::with_baseline(line, Point::new(PAD_X as i32, y), style, Baseline::Top);
        let _ = t.draw(&mut target);
        y += GLYPH_H as i32 + LINE_GAP as i32;
    }
    Ok(())
}

/// Packed 1-bit DrawTarget matching the panel (`MSB first`, `1 = white`).
/// `BinaryColor::On` is black ink (clears the bit).
struct PackedFrame<'a> {
    buf: &'a mut [u8],
}

impl OriginDimensions for PackedFrame<'_> {
    fn size(&self) -> Size {
        Size::new(PANEL_WIDTH, PANEL_HEIGHT)
    }
}

impl DrawTarget for PackedFrame<'_> {
    type Color = BinaryColor;
    type Error = core::convert::Infallible;

    fn draw_iter<I>(&mut self, pixels: I) -> Result<(), Self::Error>
    where
        I: IntoIterator<Item = Pixel<Self::Color>>,
    {
        let row_bytes = (PANEL_WIDTH / 8) as usize;
        for Pixel(point, color) in pixels {
            if point.x < 0 || point.y < 0 {
                continue;
            }
            let x = point.x as u32;
            let y = point.y as u32;
            if x >= PANEL_WIDTH || y >= PANEL_HEIGHT {
                continue;
            }
            let i = y as usize * row_bytes + (x as usize) / 8;
            let bit = 0x80u8 >> (x % 8);
            if color == BinaryColor::On {
                self.buf[i] &= !bit;
            } else {
                self.buf[i] |= bit;
            }
        }
        Ok(())
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn empty_report_renders_nothing() {
        assert!(StatusReport::default().is_empty());
        assert_eq!(StatusReport::default().render(), None);
    }

    #[test]
    fn overlay_empty_text_does_not_touch_frame() {
        let mut frame = vec![0x00u8; FRAME_BYTES];
        overlay_status_line(&mut frame, "").unwrap();
        assert!(frame.iter().all(|b| *b == 0));
    }

    #[test]
    fn overlay_rejects_wrong_size() {
        let mut frame = vec![0u8; 16];
        assert!(overlay_status_line(&mut frame, "x").is_err());
    }

    #[test]
    fn overlay_paints_only_the_bottom_bar() {
        let mut frame = vec![0x00u8; FRAME_BYTES];
        overlay_status_line(&mut frame, "WIFI ERR").unwrap();
        let bar_h = status_bar_height(1);
        let row_bytes = (PANEL_WIDTH / 8) as usize;
        let start = (PANEL_HEIGHT - bar_h) as usize * row_bytes;
        assert!(
            frame[..start].iter().all(|b| *b == 0),
            "image rows above the bar must stay untouched"
        );
        assert!(
            frame[start..start + row_bytes].iter().all(|b| *b == 0),
            "separator row should be black"
        );
        let text_rows = &frame[start + row_bytes..];
        assert!(
            text_rows.iter().any(|b| *b != 0),
            "bar should contain white background"
        );
        assert!(
            text_rows.iter().any(|b| *b != 0xff),
            "bar should contain black glyph pixels"
        );
    }

    #[test]
    fn overlay_three_lines_uses_taller_bar() {
        assert!(status_bar_height(3) > status_bar_height(1));
        let mut frame = vec![0xAAu8; FRAME_BYTES];
        overlay_status_line(&mut frame, "one\ntwo\nthree").unwrap();
        let bar_h = status_bar_height(3);
        let row_bytes = (PANEL_WIDTH / 8) as usize;
        let start = (PANEL_HEIGHT - bar_h) as usize * row_bytes;
        assert!(frame[..start].iter().all(|b| *b == 0xAA));
    }

    #[test]
    fn wifi_render_includes_ssid_step_heap_and_2ghz() {
        let r = StatusReport {
            wifi: Some(WifiStatus {
                ssid: "CafeNet".into(),
                step: "connect".into(),
                cause: "ESP_ERR_TIMEOUT (0x107)".into(),
                attempt: 5,
                attempts: 5,
                heap: 12345,
                heap_min: 8000,
                heap_largest: 9000,
                uptime_secs: 12,
                disconnect_reason: Some(201),
            }),
            ..Default::default()
        };
        let text = r.render().expect("wifi error should render");
        assert!(text.contains("WIFI ERR"));
        assert!(text.contains("step=connect"));
        assert!(text.contains("ssid=CafeNet"));
        assert!(text.contains("2.4GHz"));
        assert!(text.contains("try=5/5"));
        assert!(text.contains("NO_AP_FOUND(201)"));
        assert!(text.contains("ESP_ERR_TIMEOUT"));
        assert!(text.contains("heap=12345"));
        assert!(text.contains("min=8000"));
        assert!(text.contains("big=9000"));
        assert!(!text.to_lowercase().contains("no error"));
    }

    #[test]
    fn fetch_render_includes_url_http_and_ip() {
        let r = StatusReport {
            fetch: Some(FetchStatus {
                op: "catalog".into(),
                url: "https://inkbot.example.workers.dev/".into(),
                http_status: Some(502),
                cause: "GET / -> HTTP 502".into(),
                attempt: 3,
                attempts: 3,
                bytes_read: Some(0),
                heap: 11111,
                heap_min: 4000,
                heap_largest: 48000,
                uptime_secs: 90,
                ip: Some("192.168.1.20".into()),
            }),
            ..Default::default()
        };
        let text = r.render().expect("fetch error should render");
        assert!(text.contains("FETCH ERR"));
        assert!(text.contains("catalog"));
        assert!(text.contains("HTTP 502"));
        assert!(text.contains("ip=192.168.1.20"));
        assert!(text.contains("bytes=0"));
        assert!(text.contains("big=48000"));
    }

    #[test]
    fn crash_render_brownout_hint_and_last_op() {
        let r = StatusReport {
            crash: Some(CrashStatus {
                reset_code: 9,
                panic_message: None,
                last_op: Some("wifi-connect".into()),
                heap: 1000,
                heap_min: 500,
                heap_largest: 800,
            }),
            ..Default::default()
        };
        let text = r.render().expect("crash should render");
        assert!(text.contains("CRASH BROWNOUT (9)"));
        assert!(text.contains("last=wifi-connect"));
        assert!(text.contains("5V sagged"));
        assert!(text.contains(">=1A"));
    }

    #[test]
    fn crash_render_includes_panic_message() {
        let r = StatusReport {
            crash: Some(CrashStatus {
                reset_code: 4,
                panic_message: Some("index out of bounds @main.rs:88".into()),
                last_op: Some("GET /latest.bin".into()),
                heap: 20000,
                heap_min: 10000,
                heap_largest: 15000,
            }),
            ..Default::default()
        };
        let text = r.render().unwrap();
        assert!(text.contains("CRASH PANIC (4)"));
        assert!(text.contains("panic=index out of bounds @main.rs:88"));
        assert!(text.contains("last=GET /latest.bin"));
    }

    #[test]
    fn wifi_reason_names_cover_common_sta_failures() {
        assert_eq!(wifi_reason_name(201), Some("NO_AP_FOUND"));
        assert_eq!(wifi_reason_name(202), Some("AUTH_FAIL"));
        assert_eq!(wifi_reason_name(204), Some("HANDSHAKE_TIMEOUT"));
        assert_eq!(wifi_reason_name(99), None);
    }

    #[test]
    fn poweron_is_not_abnormal() {
        assert!(!reset_is_abnormal(1));
        assert!(!reset_is_abnormal(2));
        assert!(reset_is_abnormal(4));
        assert!(reset_is_abnormal(9));
        assert_eq!(reset_reason_name(4), "PANIC");
        assert_eq!(reset_reason_name(6), "TASK_WDT");
        assert!(reset_is_abnormal(3));
        assert!(!crash_after_reset(3, Some("ota:reboot")));
        assert!(crash_after_reset(3, Some("GET /latest.bin")));
        assert!(crash_after_reset(4, Some("ota:reboot")));
    }

    #[test]
    fn wrap_lines_truncates_to_max_and_marks_overflow() {
        let lines = vec!["aaaa".into(), "bbbb".into(), "cccc".into(), "dddd".into()];
        let out = wrap_lines(&lines, 4, 3);
        assert_eq!(out.len(), 3);
        assert!(out[2].ends_with("..."));
    }

    #[test]
    fn wrap_one_splits_long_url() {
        let long = "a".repeat(STATUS_MAX_COLS + 10);
        let out = wrap_lines(&[long], STATUS_MAX_COLS, STATUS_MAX_LINES);
        assert_eq!(out.len(), 2);
        assert_eq!(out[0].len(), STATUS_MAX_COLS);
        assert_eq!(out[1].len(), 10);
    }

    #[test]
    fn shorten_url_keeps_path() {
        let u = "https://inkbot.example.workers.dev/some-long-image-name.bin";
        let s = shorten_url(u, 24);
        assert!(s.contains(".bin"), "{s}");
        assert!(s.chars().count() <= 24);
    }

    #[test]
    fn format_panic_strips_path_and_caps_length() {
        let s = format_panic_message("boom", "/home/me/src/main.rs", 42);
        assert_eq!(s, "boom @main.rs:42");
        let long = format_panic_message(&"x".repeat(200), "lib.rs", 1);
        assert!(long.chars().count() <= 160);
        assert!(long.ends_with("..."));
    }

    #[test]
    fn format_error_chain_joins_causes() {
        let err = anyhow::anyhow!("http read").context("GET /foo.bin");
        let s = format_error_chain(&err);
        assert!(s.contains("GET /foo.bin"));
        assert!(s.contains("http read"));
        assert!(s.contains(" | "));
    }

    #[test]
    fn combined_wifi_and_crash_fits_max_lines() {
        let r = StatusReport {
            wifi: Some(WifiStatus {
                ssid: "x".into(),
                step: "dhcp".into(),
                cause: "wait_netif_up timeout".into(),
                attempt: 5,
                attempts: 5,
                heap: 1,
                heap_min: 1,
                heap_largest: 1,
                uptime_secs: 8,
                disconnect_reason: None,
            }),
            crash: Some(CrashStatus {
                reset_code: 9,
                panic_message: None,
                last_op: Some("wifi-dhcp".into()),
                heap: 1,
                heap_min: 1,
                heap_largest: 1,
            }),
            ..Default::default()
        };
        let text = r.render().unwrap();
        assert!(text.lines().count() <= STATUS_MAX_LINES);
        assert!(text.contains("WIFI ERR"));
        // Crash may be truncated to "..." on the last line, but WIFI is first.
        assert!(text.contains("WIFI ERR") || text.contains("CRASH"));
    }

    #[test]
    fn should_post_status_gates_on_secret_and_triggers() {
        assert!(!should_post_status(false, true, true, 10_000, 900));
        assert!(should_post_status(true, true, false, 0, 900));
        assert!(should_post_status(true, false, true, 0, 900));
        assert!(should_post_status(true, false, false, 900, 900));
        assert!(!should_post_status(true, false, false, 899, 900));
    }

    #[test]
    fn incident_needs_post_after_recovery_or_unposted() {
        assert!(incident_needs_post(true, false));
        assert!(incident_needs_post(false, true));
        assert!(!incident_needs_post(false, false));
    }

    #[test]
    fn telemetry_json_includes_error_and_skips_empty_optionals() {
        let status = StatusReport {
            crash: Some(CrashStatus {
                reset_code: 4,
                panic_message: Some("boom @main.rs:1".into()),
                last_op: Some("GET /".into()),
                heap: 1,
                heap_min: 1,
                heap_largest: 1,
            }),
            ..Default::default()
        };
        let mut t = DeviceTelemetry::from_parts(
            &status,
            12,
            4,
            100,
            50,
            80,
            Some("10.0.0.2".into()),
            Some("CafeNet".into()),
            Some("foo".into()),
            Some("GET /".into()),
            true,
            3,
            1,
            None,
        );
        t.unix_secs = Some(1_700_000_000);
        t.rssi = Some(-62);
        t.last_incident = LastIncident::from_status(
            "fetch",
            &status,
            IncidentContext {
                uptime_secs: 12,
                unix_secs: Some(1_700_000_000),
                ip: Some("10.0.0.2".into()),
                op: Some("GET /".into()),
                rssi: Some(-62),
                gateway: Some("10.0.0.1".into()),
            },
        );
        let v = serde_json::to_value(&t).unwrap();
        assert_eq!(v["firmware"], FIRMWARE_ID);
        assert_eq!(v["reset_name"], "PANIC");
        assert!(v["error"].as_str().unwrap().contains("CRASH PANIC"));
        assert!(v.get("last_post_error").is_none());
        assert_eq!(v["unix_secs"], 1_700_000_000);
        assert_eq!(v["rssi"], -62);
        assert_eq!(v["last_incident"]["kind"], "fetch");
        assert_eq!(v["dhcp_renews"], 0);
        assert!(v["crash"]["panic_message"]
            .as_str()
            .unwrap()
            .contains("boom"));
        assert!(v.is_object());
    }

    #[test]
    fn last_incident_from_fetch_status() {
        let status = StatusReport {
            fetch: Some(FetchStatus {
                op: "catalog".into(),
                url: "https://inkbot.example.workers.dev/".into(),
                http_status: None,
                cause: "ESP_ERR_HTTP_CONNECT".into(),
                attempt: 3,
                attempts: 3,
                bytes_read: None,
                heap: 170000,
                heap_min: 99000,
                heap_largest: 110000,
                uptime_secs: 86370,
                ip: Some("10.10.19.35".into()),
            }),
            ..Default::default()
        };
        let inc = LastIncident::from_status(
            "fetch",
            &status,
            IncidentContext {
                uptime_secs: 86370,
                unix_secs: Some(1_700_000_000),
                ip: Some("10.10.19.35".into()),
                op: Some("GET /".into()),
                rssi: Some(-62),
                gateway: Some("10.10.19.1".into()),
            },
        )
        .expect("fetch overlay should become an incident");
        assert_eq!(inc.kind, "fetch");
        assert!(inc.error.contains("ESP_ERR_HTTP_CONNECT"));
        assert_eq!(inc.rssi, Some(-62));
        let v = serde_json::to_value(&inc).unwrap();
        assert!(v.get("http_status").is_none());
    }

    #[test]
    fn last_incident_none_when_healthy() {
        assert!(LastIncident::from_status(
            "fetch",
            &StatusReport::default(),
            IncidentContext {
                uptime_secs: 1,
                ..Default::default()
            },
        )
        .is_none());
    }
}
