//! RFC 3339 timestamps as Sigstore trusted roots write them.

/// Seconds since the Unix epoch for an RFC 3339 UTC time such as
/// `2025-04-16T00:00:00Z` or `2025-04-16T00:00:00.000Z`.
pub fn rfc3339(text: &str) -> Result<u64, String> {
    let bad = || format!("not an RFC 3339 UTC time: {text}");
    let t = text.strip_suffix('Z').ok_or_else(bad)?;
    let (date, clock) = t.split_once('T').ok_or_else(bad)?;
    let clock = clock.split('.').next().ok_or_else(bad)?;
    let num = |s: &str| s.parse::<u64>().map_err(|_| bad());
    let d: Vec<&str> = date.split('-').collect();
    let c: Vec<&str> = clock.split(':').collect();
    if d.len() != 3 || c.len() != 3 {
        return Err(bad());
    }
    let (y, m, day) = (num(d[0])?, num(d[1])?, num(d[2])?);
    let (hh, mm, ss) = (num(c[0])?, num(c[1])?, num(c[2])?);
    if !(1..=12).contains(&m) || !(1..=31).contains(&day) || hh > 23 || mm > 59 || ss > 60 {
        return Err(bad());
    }
    Ok(days_from_civil(y, m, day) * 86_400 + hh * 3_600 + mm * 60 + ss)
}

/// Days since 1970-01-01 for a proleptic Gregorian date in or after 1970.
pub fn days_from_civil(y: u64, m: u64, d: u64) -> u64 {
    let y = if m <= 2 { y - 1 } else { y };
    let era = y / 400;
    let yoe = y - era * 400;
    let mp = (m + 9) % 12;
    let doy = (153 * mp + 2) / 5 + d - 1;
    let doe = yoe * 365 + yoe / 4 - yoe / 100 + doy;
    era * 146_097 + doe - 719_468
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn parses_trusted_root_times() {
        assert_eq!(rfc3339("1970-01-01T00:00:00Z"), Ok(0));
        assert_eq!(rfc3339("2025-06-12T12:02:16Z"), Ok(1_749_729_736));
        assert_eq!(rfc3339("2022-12-31T23:59:59.999Z"), Ok(1_672_531_199));
        assert!(rfc3339("2025-06-12T12:02:16+01:00").is_err());
    }
}
