//! Wall-clock formatting for API responses.
//!
//! Internal state keeps epoch milliseconds (cheap, timezone-free); JSON APIs
//! expose RFC 3339 UTC strings. No chrono/`time` dependency — only UTC with
//! millisecond precision is needed.

/// Format Unix epoch milliseconds as RFC 3339 UTC (`2026-07-11T14:28:00.123Z`).
pub fn rfc3339_ms(ms: i64) -> String {
    let secs = ms.div_euclid(1000);
    let millis = ms.rem_euclid(1000) as u32;
    let (y, mo, d, h, mi, s) = civil_utc(secs);
    format!("{y:04}-{mo:02}-{d:02}T{h:02}:{mi:02}:{s:02}.{millis:03}Z")
}

/// Unix seconds → (year, month, day, hour, minute, second) in UTC.
///
/// Civil-from-days after Howard Hinnant
/// (<http://howardhinnant.github.io/date_algorithms.html>).
fn civil_utc(secs: i64) -> (i32, u32, u32, u32, u32, u32) {
    let days = secs.div_euclid(86_400);
    let tod = secs.rem_euclid(86_400) as u32;
    let h = tod / 3600;
    let mi = (tod % 3600) / 60;
    let s = tod % 60;

    // Shift epoch from 1970-01-01 to the algorithmic era starting 0000-03-01.
    let z = days + 719_468;
    let era = if z >= 0 { z } else { z - 146_096 } / 146_097;
    let doe = (z - era * 146_097) as u32; // [0, 146096]
    let yoe = (doe - doe / 1460 + doe / 36524 - doe / 146_096) / 365; // [0, 399]
    let y = (yoe as i64 + era * 400) as i32;
    let doy = doe - (365 * yoe + yoe / 4 - yoe / 100); // [0, 365]
    let mp = (5 * doy + 2) / 153; // [0, 11]
    let d = doy - (153 * mp + 2) / 5 + 1; // [1, 31]
    let m = if mp < 10 { mp + 3 } else { mp - 9 }; // [1, 12]
    let y = if m <= 2 { y + 1 } else { y };
    (y, m, d, h, mi, s)
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn epoch_zero() {
        assert_eq!(rfc3339_ms(0), "1970-01-01T00:00:00.000Z");
    }

    #[test]
    fn known_instant() {
        // 2026-07-11T14:28:00.000Z
        assert_eq!(rfc3339_ms(1_783_780_080_000), "2026-07-11T14:28:00.000Z");
    }

    #[test]
    fn millis_and_negative() {
        assert_eq!(rfc3339_ms(1_001), "1970-01-01T00:00:01.001Z");
        assert_eq!(rfc3339_ms(-1), "1969-12-31T23:59:59.999Z");
    }
}
