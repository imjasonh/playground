//! `UTCTime` and `GeneralizedTime` in the forms `docs/formats.md` allows.
//!
//! Both parsers return seconds since the Unix epoch. Times before 1970 have
//! no such value, so they are rejected.

use crate::error::Error;

/// The first year a time can have.
const FIRST_YEAR: u32 = 1970;
/// Days from 0000-03-01 to 1970-01-01 in the proleptic Gregorian calendar.
const EPOCH_DAYS: u64 = 719_468;
/// Days in a 400-year Gregorian cycle.
const DAYS_PER_ERA: u64 = 146_097;

/// Reads `N` ASCII decimal digits from the front of `input`.
fn digits<const N: usize>(input: &mut &[u8]) -> Result<u32, Error> {
    let (chunk, rest) = input.split_first_chunk::<N>().ok_or(Error::BadTime)?;
    *input = rest;
    let mut value: u32 = 0;
    for &b in chunk {
        let digit = b
            .checked_sub(b'0')
            .filter(|d| *d <= 9)
            .ok_or(Error::BadTime)?;
        value = value
            .checked_mul(10)
            .and_then(|v| v.checked_add(u32::from(digit)))
            .ok_or(Error::Overflow)?;
    }
    Ok(value)
}

fn is_leap_year(year: u32) -> bool {
    year.is_multiple_of(4) && (!year.is_multiple_of(100) || year.is_multiple_of(400))
}

fn days_in_month(year: u32, month: u32) -> u32 {
    match month {
        1 | 3 | 5 | 7 | 8 | 10 | 12 => 31,
        4 | 6 | 9 | 11 => 30,
        2 if is_leap_year(year) => 29,
        2 => 28,
        _ => 0,
    }
}

/// Days from 1970-01-01 to the given date, which must be valid and in 1970 or
/// later. This is Howard Hinnant's `days_from_civil`.
fn days_from_civil(year: u32, month: u32, day: u32) -> Option<u64> {
    let year = u64::from(year);
    let month = u64::from(month);
    let day = u64::from(day);
    let y = if month <= 2 {
        year.checked_sub(1)?
    } else {
        year
    };
    let era = y.checked_div(400)?;
    let year_of_era = y.checked_rem(400)?;
    let shifted_month = if month > 2 {
        month.checked_sub(3)?
    } else {
        month.checked_add(9)?
    };
    let day_of_year = shifted_month
        .checked_mul(153)?
        .checked_add(2)?
        .checked_div(5)?
        .checked_add(day)?
        .checked_sub(1)?;
    let day_of_era = year_of_era
        .checked_mul(365)?
        .checked_add(year_of_era.checked_div(4)?)?
        .checked_sub(year_of_era.checked_div(100)?)?
        .checked_add(day_of_year)?;
    era.checked_mul(DAYS_PER_ERA)?
        .checked_add(day_of_era)?
        .checked_sub(EPOCH_DAYS)
}

/// Reads `MMDDHHMMSS` after a year and returns the seconds since the epoch.
fn date_time(year: u32, input: &mut &[u8]) -> Result<u64, Error> {
    let month = digits::<2>(input)?;
    let day = digits::<2>(input)?;
    let hour = digits::<2>(input)?;
    let minute = digits::<2>(input)?;
    let second = digits::<2>(input)?;
    let valid = year >= FIRST_YEAR
        && (1..=12).contains(&month)
        && day >= 1
        && day <= days_in_month(year, month)
        && hour <= 23
        && minute <= 59
        && second <= 59;
    if !valid {
        return Err(Error::BadTime);
    }
    let days = days_from_civil(year, month, day).ok_or(Error::Overflow)?;
    let seconds = u64::from(hour)
        .checked_mul(3600)
        .and_then(|s| s.checked_add(u64::from(minute).checked_mul(60)?))
        .and_then(|s| s.checked_add(u64::from(second)))
        .ok_or(Error::Overflow)?;
    days.checked_mul(86_400)
        .and_then(|d| d.checked_add(seconds))
        .ok_or(Error::Overflow)
}

/// Parses the contents of a `UTCTime`, `YYMMDDHHMMSSZ`, and returns seconds
/// since the Unix epoch.
///
/// Years 50 through 99 are 1950 through 1999, and 00 through 49 are 2000
/// through 2049. Years before 1970 are rejected.
pub fn utc_time(content: &[u8]) -> Result<u64, Error> {
    let mut rest = content;
    let yy = digits::<2>(&mut rest)?;
    let century = if yy >= 50 { 1900 } else { 2000 };
    let year = yy.checked_add(century).ok_or(Error::Overflow)?;
    let t = date_time(year, &mut rest)?;
    if rest != b"Z" {
        return Err(Error::BadTime);
    }
    Ok(t)
}

/// Parses the contents of a `GeneralizedTime` and returns seconds since the
/// Unix epoch.
///
/// The accepted forms are `YYYYMMDDHHMMSSZ` and `YYYYMMDDHHMMSS.fZ`, where the
/// fraction has one or more digits and doesn't end in `0`. The fraction is
/// dropped. Years before 1970 are rejected.
pub fn generalized_time(content: &[u8]) -> Result<u64, Error> {
    let mut rest = content;
    let year = digits::<4>(&mut rest)?;
    let t = date_time(year, &mut rest)?;
    match rest.split_first() {
        Some((b'Z', [])) => Ok(t),
        Some((b'.', fraction_and_zone)) => match fraction_and_zone.split_last() {
            Some((b'Z', fraction))
                if fraction.iter().all(u8::is_ascii_digit)
                    && fraction.last().is_some_and(|&d| d != b'0') =>
            {
                Ok(t)
            }
            _ => Err(Error::BadTime),
        },
        _ => Err(Error::BadTime),
    }
}

#[cfg(test)]
#[allow(clippy::arithmetic_side_effects, clippy::indexing_slicing)]
mod tests {
    use super::*;

    #[test]
    fn converts_known_times() {
        assert_eq!(generalized_time(b"19700101000000Z"), Ok(0));
        assert_eq!(utc_time(b"700101000000Z"), Ok(0));
        assert_eq!(generalized_time(b"20000229120000Z"), Ok(951_825_600));
        assert_eq!(utc_time(b"000229120000Z"), Ok(951_825_600));
        assert_eq!(utc_time(b"250612120216Z"), Ok(1_749_729_736));
        assert_eq!(generalized_time(b"20250612120216Z"), Ok(1_749_729_736));
        assert_eq!(generalized_time(b"19991231235959Z"), Ok(946_684_799));
        assert_eq!(utc_time(b"991231235959Z"), Ok(946_684_799));
        assert_eq!(utc_time(b"491231235959Z"), Ok(2_524_607_999));
        assert_eq!(generalized_time(b"21000301000000Z"), Ok(4_107_542_400));
    }

    #[test]
    fn drops_fractions() {
        assert_eq!(generalized_time(b"20250612120216.5Z"), Ok(1_749_729_736));
        assert_eq!(generalized_time(b"20250612120216.123Z"), Ok(1_749_729_736));
        assert_eq!(generalized_time(b"20250612120216.10Z"), Err(Error::BadTime));
        assert_eq!(generalized_time(b"20250612120216.0Z"), Err(Error::BadTime));
        assert_eq!(generalized_time(b"20250612120216.Z"), Err(Error::BadTime));
        assert_eq!(generalized_time(b"20250612120216.1aZ"), Err(Error::BadTime));
        assert_eq!(generalized_time(b"20250612120216,5Z"), Err(Error::BadTime));
    }

    #[test]
    fn rejects_invalid_dates() {
        assert_eq!(generalized_time(b"20230229000000Z"), Err(Error::BadTime));
        assert_eq!(generalized_time(b"21000229000000Z"), Err(Error::BadTime));
        assert_eq!(generalized_time(b"20241301000000Z"), Err(Error::BadTime));
        assert_eq!(utc_time(b"241301000000Z"), Err(Error::BadTime));
        assert_eq!(generalized_time(b"20240001000000Z"), Err(Error::BadTime));
        assert_eq!(generalized_time(b"20240100000000Z"), Err(Error::BadTime));
        assert_eq!(generalized_time(b"20240431000000Z"), Err(Error::BadTime));
        assert_eq!(generalized_time(b"20240101240000Z"), Err(Error::BadTime));
        assert_eq!(generalized_time(b"20240101006000Z"), Err(Error::BadTime));
        assert_eq!(generalized_time(b"20240101000060Z"), Err(Error::BadTime));
    }

    #[test]
    fn rejects_years_before_the_epoch() {
        assert_eq!(utc_time(b"691231235959Z"), Err(Error::BadTime));
        assert_eq!(utc_time(b"500101000000Z"), Err(Error::BadTime));
        assert_eq!(generalized_time(b"19691231235959Z"), Err(Error::BadTime));
    }

    #[test]
    fn rejects_malformed_text() {
        assert_eq!(utc_time(b"250612120216"), Err(Error::BadTime));
        assert_eq!(generalized_time(b"20250612120216"), Err(Error::BadTime));
        assert_eq!(utc_time(b"250612120216z"), Err(Error::BadTime));
        assert_eq!(generalized_time(b"20250612120216z"), Err(Error::BadTime));
        assert_eq!(utc_time(b"2506121202a6Z"), Err(Error::BadTime));
        assert_eq!(generalized_time(b"2025061212021 Z"), Err(Error::BadTime));
        assert_eq!(utc_time(b"250612120216ZZ"), Err(Error::BadTime));
        assert_eq!(utc_time(b"2506121202Z"), Err(Error::BadTime));
        assert_eq!(utc_time(b"250612120216+0000"), Err(Error::BadTime));
        assert_eq!(utc_time(b"20250612120216Z"), Err(Error::BadTime));
        assert_eq!(generalized_time(b"250612120216Z"), Err(Error::BadTime));
        assert_eq!(generalized_time(b""), Err(Error::BadTime));
        assert_eq!(generalized_time(b"+0250612120216Z"), Err(Error::BadTime));
    }
}
