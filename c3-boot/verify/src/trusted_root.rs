//! Reads the keys a slot check uses from Sigstore's `trusted_root.json`,
//! after [`crate::tuf`] has checked its digest.
//!
//! The result is the [`TrustRoot`] that [`crate::sigstore::verify`] takes,
//! with the compiled-in identity policy:
//!
//! - each certificate authority whose first certificate has a P-384 key
//!   becomes a Fulcio intermediate with that certificate's subject;
//! - each transparency log with an Ed25519 key becomes a log key whose
//!   origin is the log's base URL without `https://` and trailing slashes;
//! - each timestamp authority whose first certificate has a P-384 key
//!   becomes a TSA signer whose `SignerIdentifier` is that certificate's
//!   issuer and serial number.
//!
//! Each window is the entry's `validFor` intersected with the validity of
//! every certificate in its chain. Entries with other key types are
//! skipped, because the slot check can't use them. Certificates in the
//! trusted root aren't checked against each other: TUF vouches for them.

use crate::der::CONTEXT_0;
use crate::der::Der;
use crate::der::INTEGER;
use crate::der::OID;
use crate::der::SEQUENCE;
use crate::error::Error;
use crate::json::Mode;
use crate::json::Value;
use crate::trustroot::FulcioIntermediate;
use crate::trustroot::LogKey;
use crate::trustroot::MAX_FULCIO;
use crate::trustroot::MAX_LOGS;
use crate::trustroot::MAX_TSAS;
use crate::trustroot::P384_POINT_LEN;
use crate::trustroot::Policy;
use crate::trustroot::TrustRoot;
use crate::trustroot::TsaSigner;
use crate::trustroot::Window;
use crate::tuf::TufError;
use crate::x509::read_time;

/// The media type `trusted_root.json` must declare.
pub const MEDIA_TYPE: &[u8] = b"application/vnd.dev.sigstore.trustedroot+json;version=0.1";
/// The most certificates an entry's chain can hold.
pub const MAX_CHAIN: usize = 4;

/// `id-ecPublicKey`, 1.2.840.10045.2.1.
const EC_PUBLIC_KEY: &[u8] = &[0x2a, 0x86, 0x48, 0xce, 0x3d, 0x02, 0x01];
/// `secp384r1`, 1.3.132.0.34.
const SECP384R1: &[u8] = &[0x2b, 0x81, 0x04, 0x00, 0x22];
/// The DER `SubjectPublicKeyInfo` of an Ed25519 key, up to the key.
const ED25519_SPKI_PREFIX: [u8; 12] = [
    0x30, 0x2a, 0x30, 0x05, 0x06, 0x03, 0x2b, 0x65, 0x70, 0x03, 0x21, 0x00,
];

/// The bytes `extract` needs in its buffer for a trusted root of `len`
/// bytes: room for every certificate it decodes and every `SignerIdentifier`
/// it builds.
pub fn buffer_len(len: usize) -> usize {
    len.saturating_mul(2).saturating_add(64)
}

/// The parts of a certificate that the trusted root's entries use.
#[derive(Clone, Copy, Debug)]
struct Cert<'a> {
    /// The whole serial number `INTEGER`.
    serial: &'a [u8],
    /// The whole issuer `Name`.
    issuer: &'a [u8],
    /// The whole subject `Name`.
    subject: &'a [u8],
    window: Window,
    /// The subject's key, if it is a P-384 point on the curve.
    p384: Option<&'a [u8; P384_POINT_LEN]>,
}

/// The P-384 point in a `SubjectPublicKeyInfo`, if it holds one on the
/// curve.
fn p384_key(spki: &[u8]) -> Option<&[u8; P384_POINT_LEN]> {
    let mut outer = Der::new(spki);
    let mut seq = outer.sequence().ok()?;
    outer.finish().ok()?;
    let (algorithm, params) = seq.algorithm().ok()?;
    let curve_ok = params.is_some_and(|p| p.tag == OID && p.content == SECP384R1);
    if algorithm != EC_PUBLIC_KEY || !curve_ok {
        return None;
    }
    let point: &[u8; P384_POINT_LEN] = seq.bit_string().ok()?.try_into().ok()?;
    seq.finish().ok()?;
    c3_crypto::p384_public_key_ok(point).then_some(point)
}

/// Reads the fields of an X.509 certificate that the entries use. The
/// certificate must be three DER elements in a `SEQUENCE`; the
/// `tbsCertificate` must hold the optional version, the serial number,
/// signature algorithm, issuer, validity, subject, and key, in that order,
/// and may hold anything after them.
fn parse_cert(der: &[u8]) -> Result<Cert<'_>, Error> {
    let mut input = Der::new(der);
    let mut certificate = input.sequence()?;
    input.finish()?;
    let tbs = certificate.element(SEQUENCE)?;
    certificate.element(SEQUENCE)?;
    certificate.bit_string()?;
    certificate.finish()?;

    let mut t = Der::new(tbs.content);
    t.optional(CONTEXT_0)?;
    let serial = t.element(INTEGER)?.raw;
    t.element(SEQUENCE)?;
    let issuer = t.element(SEQUENCE)?.raw;
    let mut validity = t.sequence()?;
    let not_before = read_time(&mut validity)?;
    let not_after = read_time(&mut validity)?;
    validity.finish()?;
    let subject = t.element(SEQUENCE)?.raw;
    let spki = t.element(SEQUENCE)?.raw;
    Ok(Cert {
        serial,
        issuer,
        subject,
        window: Window {
            not_before,
            not_after,
        },
        p384: p384_key(spki),
    })
}

/// A `validFor` object: `start` and an optional `end`, which defaults to the
/// last representable second.
fn valid_for(v: Value<'_>) -> Result<Window, TufError> {
    let not_before = crate::time::rfc3339(v.field(b"start")?.str()?)?;
    let not_after = match v.get(b"end")? {
        Some(end) => crate::time::rfc3339(end.str()?)?,
        None => u64::MAX,
    };
    Ok(Window {
        not_before,
        not_after,
    })
}

fn intersect(a: Window, b: Window) -> Window {
    Window {
        not_before: a.not_before.max(b.not_before),
        not_after: a.not_after.min(b.not_after),
    }
}

/// Splits the first `n` bytes off `free` and returns them.
fn take<'a>(free: &mut &'a mut [u8], n: usize) -> Result<&'a mut [u8], Error> {
    let (head, tail) = core::mem::take(free)
        .split_at_mut_checked(n)
        .ok_or(Error::ScratchTooSmall)?;
    *free = tail;
    Ok(head)
}

/// Decodes base64 `text` into the front of `free` and splits it off.
fn decode<'a>(text: &[u8], free: &mut &'a mut [u8]) -> Result<&'a [u8], Error> {
    let n = crate::base64::decode_into(text, free)?;
    Ok(take(free, n)?)
}

/// Reads an entry's certificate chain and `validFor`, and returns its first
/// certificate and the intersected window.
fn read_chain<'a>(
    entry: Value<'_>,
    free: &mut &'a mut [u8],
) -> Result<(Cert<'a>, Window), TufError> {
    let mut window = valid_for(entry.field(b"validFor")?)?;
    let mut certs = entry
        .field(b"certChain")?
        .field(b"certificates")?
        .elements()?;
    let mut first = None;
    for _ in 0..MAX_CHAIN {
        let Some(c) = certs.next_element()? else {
            break;
        };
        let der = decode(c.field(b"rawBytes")?.str()?, free)?;
        let cert = parse_cert(der)?;
        window = intersect(window, cert.window);
        first = first.or(Some(cert));
    }
    if certs.next_element()?.is_some() {
        return Err(TufError::Schema);
    }
    Ok((first.ok_or(TufError::Schema)?, window))
}

/// Writes the DER `SEQUENCE` of `parts` into the front of `free` and splits
/// it off.
fn der_sequence<'a>(parts: [&[u8]; 2], free: &mut &'a mut [u8]) -> Result<&'a [u8], Error> {
    let [a, b] = parts;
    let len = a.len().checked_add(b.len()).ok_or(Error::Overflow)?;
    let len16 = u16::try_from(len).map_err(|_| Error::OutOfRange)?;
    let [hi, lo] = len16.to_be_bytes();
    let mut header = [0x30, hi, lo, 0];
    let header: &[u8] = match len16 {
        0..0x80 => {
            header[1] = lo;
            header.get(..2).ok_or(Error::Overflow)?
        }
        0x80..0x100 => {
            header = [0x30, 0x81, lo, 0];
            header.get(..3).ok_or(Error::Overflow)?
        }
        _ => {
            header = [0x30, 0x82, hi, lo];
            &header
        }
    };
    let total = header.len().checked_add(len).ok_or(Error::Overflow)?;
    let out = take(free, total)?;
    let (h, rest) = out
        .split_at_mut_checked(header.len())
        .ok_or(Error::Overflow)?;
    let (x, y) = rest.split_at_mut_checked(a.len()).ok_or(Error::Overflow)?;
    h.copy_from_slice(header);
    x.copy_from_slice(a);
    y.copy_from_slice(b);
    Ok(out)
}

/// Reports whether any two of the listed items have equal keys under `key`.
fn has_duplicates<T, K: PartialEq>(items: &[Option<T>], key: impl Fn(&T) -> K) -> bool {
    let listed = items.iter().map_while(Option::as_ref);
    for (i, a) in listed.clone().enumerate() {
        let ka = key(a);
        if listed
            .clone()
            .skip(i.saturating_add(1))
            .any(|b| key(b) == ka)
        {
            return true;
        }
    }
    false
}

/// Stores `item` in the next free entry of `list`.
fn push<T>(list: &mut [Option<T>], count: &mut usize, item: T) -> Result<(), Error> {
    *list.get_mut(*count).ok_or(Error::OutOfRange)? = Some(item);
    *count = count.checked_add(1).ok_or(Error::Overflow)?;
    Ok(())
}

/// Reads a log entry's Ed25519 key, origin, and window, or `None` if its
/// key isn't Ed25519.
fn log_key<'a>(tlog: Value<'a>, free: &mut &'a mut [u8]) -> Result<Option<LogKey<'a>>, TufError> {
    let key = tlog.field(b"publicKey")?;
    if key.field(b"keyDetails")?.str()? != b"PKIX_ED25519" {
        return Ok(None);
    }
    let spki = decode(key.field(b"rawBytes")?.str()?, free)?;
    let public_key: &[u8; 32] = spki
        .strip_prefix(&ED25519_SPKI_PREFIX)
        .and_then(|k| k.try_into().ok())
        .ok_or(Error::BadKey)?;
    if !c3_crypto::ed25519_public_key_ok(public_key) {
        return Err(Error::BadKey.into());
    }
    let url = tlog.field(b"baseUrl")?.str()?;
    let mut origin = url.strip_prefix(b"https://").ok_or(TufError::Schema)?;
    while let Some(trimmed) = origin.strip_suffix(b"/") {
        origin = trimmed;
    }
    if origin.is_empty() || !origin.iter().all(|b| (0x20..=0x7e).contains(b)) {
        return Err(TufError::Schema);
    }
    Ok(Some(LogKey {
        origin,
        public_key,
        window: valid_for(key.field(b"validFor")?)?,
    }))
}

/// Reads the Sigstore keys from `json`, a `trusted_root.json` whose digest
/// the caller has verified, and returns them with `policy`.
///
/// Decoded certificates and built `SignerIdentifier`s are stored in `buf`,
/// which must hold at least [`buffer_len`] of `json.len()` bytes.
pub fn extract<'a>(
    json: &'a [u8],
    policy: Policy<'a>,
    buf: &'a mut [u8],
) -> Result<TrustRoot<'a>, TufError> {
    if buf.len() < buffer_len(json.len()) {
        return Err(Error::ScratchTooSmall.into());
    }
    let mut free = buf;
    let root = crate::json::parse(json, Mode::Strict)?;
    if root.field(b"mediaType")?.str()? != MEDIA_TYPE {
        return Err(TufError::Schema);
    }

    let mut fulcio = [None; MAX_FULCIO];
    let mut count = 0usize;
    let mut cas = root.field(b"certificateAuthorities")?.elements()?;
    while let Some(ca) = cas.next_element()? {
        let (first, window) = read_chain(ca, &mut free)?;
        if let Some(public_key) = first.p384 {
            let entry = FulcioIntermediate {
                subject: first.subject,
                public_key,
                window,
            };
            push(&mut fulcio, &mut count, entry)?;
        }
    }

    let mut logs = [None; MAX_LOGS];
    let mut count = 0usize;
    let mut tlogs = root.field(b"tlogs")?.elements()?;
    while let Some(tlog) = tlogs.next_element()? {
        if let Some(entry) = log_key(tlog, &mut free)? {
            push(&mut logs, &mut count, entry)?;
        }
    }

    let mut tsas = [None; MAX_TSAS];
    let mut count = 0usize;
    let mut authorities = root.field(b"timestampAuthorities")?.elements()?;
    while let Some(tsa) = authorities.next_element()? {
        let (first, window) = read_chain(tsa, &mut free)?;
        if let Some(public_key) = first.p384 {
            let signer_id = der_sequence([first.issuer, first.serial], &mut free)?;
            let entry = TsaSigner {
                signer_id,
                public_key,
                window,
            };
            push(&mut tsas, &mut count, entry)?;
        }
    }

    let duplicated = has_duplicates(&fulcio, |f| f.subject)
        || has_duplicates(&fulcio, |f| f.public_key)
        || has_duplicates(&logs, |l| l.origin)
        || has_duplicates(&logs, |l| l.public_key)
        || has_duplicates(&tsas, |t| t.signer_id)
        || has_duplicates(&tsas, |t| t.public_key);
    if duplicated {
        return Err(Error::DuplicateKey.into());
    }
    Ok(TrustRoot::from_parts(fulcio, logs, tsas, policy))
}
