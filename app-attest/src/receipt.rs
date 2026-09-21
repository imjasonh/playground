//! Parse App Attest receipt attributes (PKCS #7 / ASN.1, App Store shape).
//!
//! Apple documents these fields in "Assessing fraud risk":
//! 6 = receipt type (`ATTEST` or `RECEIPT`), 17 = risk metric, 19 = not-before.
//! Only a server-refreshed `RECEIPT` includes field 17.

use std::collections::BTreeMap;

use der_parser::ber::BerObjectContent;
use der_parser::parse_der;

use crate::error::Error;

const FIELD_TYPE: u64 = 6;
const FIELD_RISK_METRIC: u64 = 17;
const FIELD_NOT_BEFORE: u64 = 19;

/// Fields extracted from a receipt payload.
#[derive(Debug, Clone, PartialEq, Eq, Default)]
pub struct ReceiptFields {
    pub receipt_type: Option<String>,
    pub risk_metric: Option<u32>,
    pub not_before_unix: Option<u64>,
}

/// Walk a PKCS #7 receipt (or a bare attribute SET) and read known fields.
pub fn parse(bytes: &[u8]) -> Result<ReceiptFields, Error> {
    if bytes.is_empty() {
        return Err(Error::Attestation("receipt is empty"));
    }
    let (_, obj) = parse_der(bytes).map_err(|_| Error::Attestation("receipt is not DER"))?;
    let mut attrs = BTreeMap::new();
    collect_attributes(&obj, &mut attrs);
    if attrs.is_empty() {
        return Err(Error::Attestation("receipt has no attributes"));
    }
    Ok(ReceiptFields {
        receipt_type: attrs.get(&FIELD_TYPE).and_then(|v| text(v)),
        risk_metric: attrs.get(&FIELD_RISK_METRIC).and_then(|v| metric(v)),
        not_before_unix: attrs.get(&FIELD_NOT_BEFORE).and_then(|v| apple_date(v)),
    })
}

fn collect_attributes(obj: &der_parser::der::DerObject<'_>, out: &mut BTreeMap<u64, Vec<u8>>) {
    match &obj.content {
        BerObjectContent::Sequence(seq) if is_receipt_attribute(seq) => {
            if let Some(typ) = integer(&seq[0]) {
                if let Some(value) = octet_string(&seq[2]) {
                    out.insert(typ, value);
                }
            }
        }
        BerObjectContent::Sequence(seq) | BerObjectContent::Set(seq) => {
            for child in seq {
                collect_attributes(child, out);
            }
        }
        BerObjectContent::Tagged(_, _, inner) | BerObjectContent::Optional(Some(inner)) => {
            collect_attributes(inner, out);
        }
        BerObjectContent::Unknown(any) => {
            if let Ok((_, inner)) = parse_der(any.data) {
                collect_attributes(&inner, out);
            }
        }
        _ => {
            if let Ok(bytes) = obj.as_slice() {
                if let Ok((_, inner)) = parse_der(bytes) {
                    collect_attributes(&inner, out);
                }
            }
        }
    }
}

fn is_receipt_attribute(seq: &[der_parser::der::DerObject<'_>]) -> bool {
    seq.len() == 3 && integer(&seq[0]).is_some() && octet_string(&seq[2]).is_some()
}

fn integer(obj: &der_parser::der::DerObject<'_>) -> Option<u64> {
    obj.as_u64().ok()
}

fn octet_string(obj: &der_parser::der::DerObject<'_>) -> Option<Vec<u8>> {
    match &obj.content {
        BerObjectContent::OctetString(bytes) => Some(bytes.to_vec()),
        _ => obj.as_slice().ok().map(<[u8]>::to_vec),
    }
}

fn text(bytes: &[u8]) -> Option<String> {
    let s = std::str::from_utf8(bytes).ok()?.trim();
    if s.is_empty() {
        None
    } else {
        Some(s.to_string())
    }
}

fn metric(bytes: &[u8]) -> Option<u32> {
    text(bytes)?.parse().ok()
}

fn apple_date(bytes: &[u8]) -> Option<u64> {
    let s = text(bytes)?;
    if let Ok(n) = s.parse::<u64>() {
        return Some(n);
    }
    parse_iso8601(&s)
}

/// Parse `2020-07-22T14:40:38.819Z` (Apple's receipt date form) as Unix seconds.
fn parse_iso8601(s: &str) -> Option<u64> {
    let s = s.trim().trim_end_matches('Z');
    let (date, rest) = s.split_once('T')?;
    let mut d = date.split('-');
    let year: i64 = d.next()?.parse().ok()?;
    let month: u32 = d.next()?.parse().ok()?;
    let day: u32 = d.next()?.parse().ok()?;
    let time = rest.split('.').next()?;
    let mut t = time.split(':');
    let hour: u32 = t.next()?.parse().ok()?;
    let min: u32 = t.next()?.parse().ok()?;
    let sec: u32 = t.next()?.parse().ok()?;
    days_from_civil(year, month, day).map(|days| {
        days.saturating_mul(86400)
            .saturating_add(i64::from(hour) * 3600)
            .saturating_add(i64::from(min) * 60)
            .saturating_add(i64::from(sec)) as u64
    })
}

/// Howard Hinnant's days-from-civil, Unix epoch.
fn days_from_civil(year: i64, month: u32, day: u32) -> Option<i64> {
    if !(1..=12).contains(&month) || !(1..=31).contains(&day) {
        return None;
    }
    let y = if month <= 2 { year - 1 } else { year };
    let era = y.div_euclid(400);
    let yoe = y.rem_euclid(400);
    let mp = if month > 2 { month - 3 } else { month + 9 };
    let doy = (153 * i64::from(mp) + 2) / 5 + i64::from(day) - 1;
    let doe = yoe * 365 + yoe / 4 - yoe / 100 + doy;
    Some(era * 146097 + doe - 719468)
}

/// Encode a bare attribute SET for tests (not a full PKCS #7 wrapper).
pub fn encode_attribute_set(fields: &[(u64, &[u8])]) -> Vec<u8> {
    let mut inner = Vec::new();
    for (typ, value) in fields {
        inner.extend(encode_attribute(*typ, value));
    }
    let mut out = Vec::new();
    out.push(0x31);
    out.extend(der_len(inner.len()));
    out.extend(inner);
    out
}

fn encode_attribute(typ: u64, value: &[u8]) -> Vec<u8> {
    let mut body = Vec::new();
    body.extend(encode_integer(typ));
    body.extend(encode_integer(1));
    body.push(0x04);
    body.extend(der_len(value.len()));
    body.extend_from_slice(value);
    let mut out = Vec::new();
    out.push(0x30);
    out.extend(der_len(body.len()));
    out.extend(body);
    out
}

fn encode_integer(n: u64) -> Vec<u8> {
    let mut bytes = n.to_be_bytes().to_vec();
    while bytes.len() > 1 && bytes[0] == 0 && bytes[1] < 0x80 {
        bytes.remove(0);
    }
    if bytes[0] >= 0x80 {
        bytes.insert(0, 0);
    }
    let mut out = vec![0x02];
    out.extend(der_len(bytes.len()));
    out.extend(bytes);
    out
}

fn der_len(len: usize) -> Vec<u8> {
    if len < 0x80 {
        vec![len as u8]
    } else if len <= 0xff {
        vec![0x81, len as u8]
    } else {
        vec![0x82, (len >> 8) as u8, len as u8]
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn parses_receipt_fields() {
        let der = encode_attribute_set(&[
            (6, b"RECEIPT"),
            (17, b"5"),
            (19, b"2020-07-22T14:40:38.819Z"),
        ]);
        let fields = parse(&der).unwrap();
        assert_eq!(fields.receipt_type.as_deref(), Some("RECEIPT"));
        assert_eq!(fields.risk_metric, Some(5));
        assert_eq!(fields.not_before_unix, Some(1_595_428_838));
    }

    #[test]
    fn iso_date_known_instant() {
        assert_eq!(parse_iso8601("2020-06-22T14:40:08Z"), Some(1_592_836_808));
    }
}
