//! Shared wire format for the Playground BLE GATT service.
//!
//! The iOS experiment encodes and parses the same UTF-8 text. Commands are
//! case-insensitive. Status is a single line of `key=value` fields.

/// Advertised GAP name. iOS filters on the service UUID, not this string.
pub const DEVICE_NAME: &str = "PlaygroundBLE";

/// Custom GATT service UUID (128-bit).
pub const SERVICE_UUID: &str = "4fafc201-1fb5-459e-8fcc-c5c9c331914b";

/// Write characteristic: iPhone → ESP32 command text.
pub const COMMAND_UUID: &str = "beb5483e-36e1-4688-b7f5-ea07361b26a6";

/// Read + notify characteristic: ESP32 → iPhone status line.
pub const STATUS_UUID: &str = "1a3c0001-36e1-4688-b7f5-ea07361b26a6";

/// On-wire / log identifier. Bump when the GATT contract changes.
pub const FIRMWARE_ID: &str = "esp32-ble/0.1";

/// Shortest blink period the firmware accepts.
pub const MIN_BLINK_MS: u32 = 50;

/// Longest blink period the firmware accepts (60 seconds).
pub const MAX_BLINK_MS: u32 = 60_000;

/// A command the iPhone writes to the command characteristic.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum Command {
    /// Drive the LED on and cancel blinking.
    LedOn,
    /// Drive the LED off and cancel blinking.
    LedOff,
    /// Blink with a full on+off period of `period_ms`.
    Blink { period_ms: u32 },
    /// Cancel blinking and leave the LED in its current state.
    Stop,
}

/// Latest device status, notified on the status characteristic.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct Status {
    pub led_on: bool,
    pub blink_ms: u32,
    pub uptime_s: u32,
    pub heap_free: Option<u32>,
    pub last_command: String,
}

/// Mutable LED / blink bookkeeping shared by the GATT write path and the loop.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct DeviceState {
    pub led_on: bool,
    pub blink_period_ms: Option<u32>,
    pub last_command: String,
}

impl Default for DeviceState {
    /// Boot blinking at 1 s so the board is visible before the first write.
    fn default() -> Self {
        Self {
            led_on: true,
            blink_period_ms: Some(1_000),
            last_command: String::new(),
        }
    }
}

impl DeviceState {
    /// Apply a parsed command.
    pub fn apply(&mut self, command: Command) {
        match command {
            Command::LedOn => {
                self.led_on = true;
                self.blink_period_ms = None;
            }
            Command::LedOff => {
                self.led_on = false;
                self.blink_period_ms = None;
            }
            Command::Blink { period_ms } => {
                self.led_on = true;
                self.blink_period_ms = Some(period_ms);
            }
            Command::Stop => {
                self.blink_period_ms = None;
            }
        }
        self.last_command = encode_command(command);
    }

    /// Physical LED level at `elapsed_ms` after boot.
    pub fn physical_led_on(&self, elapsed_ms: u64) -> bool {
        match self.blink_period_ms {
            Some(period) if period >= 2 => {
                let half = u64::from(period) / 2;
                (elapsed_ms / half) % 2 == 0
            }
            _ => self.led_on,
        }
    }

    /// Snapshot for [`format_status`].
    pub fn to_status(&self, elapsed_ms: u64, heap_free: Option<u32>) -> Status {
        Status {
            led_on: self.physical_led_on(elapsed_ms),
            blink_ms: self.blink_period_ms.unwrap_or(0),
            uptime_s: u32::try_from(elapsed_ms / 1000).unwrap_or(u32::MAX),
            heap_free,
            last_command: self.last_command.clone(),
        }
    }
}

/// Parse a command written by the iPhone.
pub fn parse_command(raw: &str) -> Option<Command> {
    let parts: Vec<&str> = raw.split_whitespace().collect();
    if parts.is_empty() {
        return None;
    }
    let head = parts[0].to_ascii_lowercase();
    match head.as_str() {
        "on" => return Some(Command::LedOn),
        "off" => return Some(Command::LedOff),
        "stop" if parts.len() == 1 => return Some(Command::Stop),
        "led" if parts.len() == 2 => {
            let arg = parts[1].to_ascii_lowercase();
            return match arg.as_str() {
                "on" => Some(Command::LedOn),
                "off" => Some(Command::LedOff),
                _ => None,
            };
        }
        "blink" => return parse_blink(&parts[1..]),
        _ => {}
    }
    None
}

fn parse_blink(args: &[&str]) -> Option<Command> {
    if args.is_empty() {
        return None;
    }
    let mut tokens: Vec<String> = args.iter().map(|s| s.to_ascii_lowercase()).collect();
    if tokens[0] == "every" {
        tokens.remove(0);
    }
    if tokens.len() != 1 {
        return None;
    }
    let period_ms = parse_period(&tokens[0])?;
    if !(MIN_BLINK_MS..=MAX_BLINK_MS).contains(&period_ms) {
        return None;
    }
    Some(Command::Blink { period_ms })
}

fn parse_period(token: &str) -> Option<u32> {
    if let Some(ms) = token.strip_suffix("ms") {
        if ms.is_empty() || !ms.chars().all(|c| c.is_ascii_digit()) {
            return None;
        }
        return ms.parse().ok();
    }
    let secs = token.strip_suffix('s').unwrap_or(token);
    parse_seconds(secs)
}

fn parse_seconds(s: &str) -> Option<u32> {
    if let Some((whole_s, frac_s)) = s.split_once('.') {
        if whole_s.is_empty() || !whole_s.chars().all(|c| c.is_ascii_digit()) {
            return None;
        }
        if frac_s.is_empty() || !frac_s.chars().all(|c| c.is_ascii_digit()) {
            return None;
        }
        let whole: u32 = whole_s.parse().ok()?;
        let mut frac: String = frac_s.chars().take(3).collect();
        while frac.len() < 3 {
            frac.push('0');
        }
        let frac_ms: u32 = frac.parse().ok()?;
        whole.checked_mul(1000)?.checked_add(frac_ms)
    } else {
        if s.is_empty() || !s.chars().all(|c| c.is_ascii_digit()) {
            return None;
        }
        let whole: u32 = s.parse().ok()?;
        whole.checked_mul(1000)
    }
}

/// Canonical command text written by the iOS presets.
pub fn encode_command(command: Command) -> String {
    match command {
        Command::LedOn => "led on".to_string(),
        Command::LedOff => "led off".to_string(),
        Command::Stop => "stop".to_string(),
        Command::Blink { period_ms } => format!("blink {}", format_seconds(period_ms)),
    }
}

fn format_seconds(period_ms: u32) -> String {
    let whole = period_ms / 1000;
    let frac = period_ms % 1000;
    if frac == 0 {
        return whole.to_string();
    }
    let mut frac_s = format!("{frac:03}");
    while frac_s.ends_with('0') {
        frac_s.pop();
    }
    format!("{whole}.{frac_s}")
}

/// Encode a status line for the notify characteristic.
pub fn format_status(status: &Status) -> String {
    let led = if status.led_on { "on" } else { "off" };
    match status.heap_free {
        Some(heap) => format!(
            "led={led} blink_ms={} uptime_s={} heap={heap} last={}",
            status.blink_ms, status.uptime_s, status.last_command
        ),
        None => format!(
            "led={led} blink_ms={} uptime_s={} last={}",
            status.blink_ms, status.uptime_s, status.last_command
        ),
    }
}

/// Parse a status line from the notify characteristic.
pub fn parse_status(raw: &str) -> Option<Status> {
    let raw = raw.trim();
    if raw.is_empty() {
        return None;
    }
    let (prefix, last_command) = match raw.split_once(" last=") {
        Some((prefix, last)) => (prefix, last.to_string()),
        None => (raw, String::new()),
    };
    let mut led_on = None;
    let mut blink_ms = None;
    let mut uptime_s = None;
    let mut heap_free = None;
    for part in prefix.split_whitespace() {
        if let Some(value) = part.strip_prefix("led=") {
            led_on = Some(value == "on");
        } else if let Some(value) = part.strip_prefix("blink_ms=") {
            blink_ms = Some(value.parse().ok()?);
        } else if let Some(value) = part.strip_prefix("uptime_s=") {
            uptime_s = Some(value.parse().ok()?);
        } else if let Some(value) = part.strip_prefix("heap=") {
            heap_free = Some(value.parse().ok()?);
        }
    }
    Some(Status {
        led_on: led_on?,
        blink_ms: blink_ms?,
        uptime_s: uptime_s?,
        heap_free,
        last_command,
    })
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn parse_led_aliases() {
        assert_eq!(parse_command("led on"), Some(Command::LedOn));
        assert_eq!(parse_command("LED ON"), Some(Command::LedOn));
        assert_eq!(parse_command("on"), Some(Command::LedOn));
        assert_eq!(parse_command("led off"), Some(Command::LedOff));
        assert_eq!(parse_command("off"), Some(Command::LedOff));
        assert_eq!(parse_command("stop"), Some(Command::Stop));
    }

    #[test]
    fn parse_blink_forms() {
        assert_eq!(
            parse_command("blink 1"),
            Some(Command::Blink { period_ms: 1000 })
        );
        assert_eq!(
            parse_command("blink 1s"),
            Some(Command::Blink { period_ms: 1000 })
        );
        assert_eq!(
            parse_command("blink every 1s"),
            Some(Command::Blink { period_ms: 1000 })
        );
        assert_eq!(
            parse_command("blink 0.5"),
            Some(Command::Blink { period_ms: 500 })
        );
        assert_eq!(
            parse_command("blink 500ms"),
            Some(Command::Blink { period_ms: 500 })
        );
        assert_eq!(
            parse_command("blink 2s"),
            Some(Command::Blink { period_ms: 2000 })
        );
    }

    #[test]
    fn reject_bad_commands() {
        assert_eq!(parse_command(""), None);
        assert_eq!(parse_command("blink"), None);
        assert_eq!(parse_command("blink 0"), None);
        assert_eq!(parse_command("blink 0.01"), None);
        assert_eq!(parse_command("blink 120s"), None);
        assert_eq!(parse_command("led"), None);
        assert_eq!(parse_command("led blink"), None);
        assert_eq!(parse_command("wave"), None);
    }

    #[test]
    fn encode_round_trip() {
        for command in [
            Command::LedOn,
            Command::LedOff,
            Command::Stop,
            Command::Blink { period_ms: 1000 },
            Command::Blink { period_ms: 500 },
            Command::Blink { period_ms: 250 },
        ] {
            let encoded = encode_command(command);
            assert_eq!(parse_command(&encoded), Some(command), "{encoded}");
        }
    }

    #[test]
    fn default_state_blinks() {
        let state = DeviceState::default();
        assert_eq!(state.blink_period_ms, Some(1000));
        assert!(state.physical_led_on(0));
        assert!(!state.physical_led_on(500));
    }

    #[test]
    fn apply_blink_then_stop() {
        let mut state = DeviceState::default();
        state.apply(Command::Blink { period_ms: 1000 });
        assert_eq!(state.blink_period_ms, Some(1000));
        assert!(state.physical_led_on(0));
        assert!(!state.physical_led_on(500));
        assert!(state.physical_led_on(1000));
        state.apply(Command::Stop);
        assert_eq!(state.blink_period_ms, None);
        assert!(state.led_on);
        assert!(state.physical_led_on(500));
    }

    #[test]
    fn led_off_cancels_blink() {
        let mut state = DeviceState::default();
        state.apply(Command::Blink { period_ms: 1000 });
        state.apply(Command::LedOff);
        assert_eq!(state.blink_period_ms, None);
        assert!(!state.led_on);
        assert!(!state.physical_led_on(0));
    }

    #[test]
    fn status_round_trip_with_heap() {
        let status = Status {
            led_on: true,
            blink_ms: 1000,
            uptime_s: 12,
            heap_free: Some(185_432),
            last_command: "led on".to_string(),
        };
        let line = format_status(&status);
        assert_eq!(
            line,
            "led=on blink_ms=1000 uptime_s=12 heap=185432 last=led on"
        );
        assert_eq!(parse_status(&line), Some(status));
    }

    #[test]
    fn status_round_trip_without_heap() {
        let status = Status {
            led_on: false,
            blink_ms: 0,
            uptime_s: 3,
            heap_free: None,
            last_command: String::new(),
        };
        let line = format_status(&status);
        assert_eq!(line, "led=off blink_ms=0 uptime_s=3 last=");
        assert_eq!(parse_status(&line), Some(status));
    }

    #[test]
    fn device_state_status_snapshot() {
        let mut state = DeviceState::default();
        state.apply(Command::Blink { period_ms: 1000 });
        let status = state.to_status(1500, Some(99));
        assert!(!status.led_on);
        assert_eq!(status.blink_ms, 1000);
        assert_eq!(status.uptime_s, 1);
        assert_eq!(status.last_command, "blink 1");
        assert_eq!(status.heap_free, Some(99));
    }

    #[test]
    fn uuid_literals_are_stable() {
        assert_eq!(SERVICE_UUID, "4fafc201-1fb5-459e-8fcc-c5c9c331914b");
        assert_eq!(COMMAND_UUID, "beb5483e-36e1-4688-b7f5-ea07361b26a6");
        assert_eq!(STATUS_UUID, "1a3c0001-36e1-4688-b7f5-ea07361b26a6");
        assert_eq!(DEVICE_NAME, "PlaygroundBLE");
    }
}
