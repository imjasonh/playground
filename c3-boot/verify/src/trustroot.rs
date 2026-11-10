//! The trust-root blob: the Sigstore keys and identity policy a slot uses.

use crate::chain::MAX_LEVEL;
use crate::chain::Tip;
use crate::error::Error;
use crate::keys::check_signatures;
use crate::keys::read_signatures;
use crate::reader::Reader;

/// The domain-separation string for blob signatures.
pub const BLOB_DOMAIN: &[u8] = b"c3-boot trust root v1";
/// The most Fulcio intermediates a blob can list.
pub const MAX_FULCIO: usize = 4;
/// The most log keys a blob can list.
pub const MAX_LOGS: usize = 8;
/// The most TSA signers a blob can list.
pub const MAX_TSAS: usize = 4;
/// The length of an uncompressed SEC1 P-384 point.
pub const P384_POINT_LEN: usize = 97;

/// An inclusive validity window, in seconds since the Unix epoch.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub struct Window {
    /// The first second the key is valid.
    pub not_before: u64,
    /// The last second the key is valid.
    pub not_after: u64,
}

impl Window {
    /// Reports whether `t` is inside the window.
    pub fn contains(&self, t: u64) -> bool {
        self.not_before <= t && t <= self.not_after
    }
}

/// A Fulcio intermediate that may sign leaf certificates.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub struct FulcioIntermediate<'a> {
    /// The intermediate's subject name, DER.
    pub subject: &'a [u8],
    /// The intermediate's P-384 public key, uncompressed SEC1.
    pub public_key: &'a [u8; P384_POINT_LEN],
    /// When the intermediate may be used.
    pub window: Window,
}

/// A transparency log key that may sign checkpoints.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub struct LogKey<'a> {
    /// The log's origin string.
    pub origin: &'a [u8],
    /// The log's Ed25519 public key.
    pub public_key: &'a [u8; 32],
    /// When the key may be used.
    pub window: Window,
}

/// A timestamp authority signer.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub struct TsaSigner<'a> {
    /// The DER `SignerIdentifier` a token's `SignerInfo` must contain.
    pub signer_id: &'a [u8],
    /// The TSA's P-384 public key, uncompressed SEC1.
    pub public_key: &'a [u8; P384_POINT_LEN],
    /// When the signer may be used.
    pub window: Window,
}

/// The values the Fulcio leaf's extensions must equal exactly.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub struct Policy<'a> {
    /// Issuer (V2), `1.3.6.1.4.1.57264.1.8`.
    pub issuer: &'a [u8],
    /// Build Signer URI, `1.3.6.1.4.1.57264.1.9`.
    pub build_signer_uri: &'a [u8],
    /// Source Repository Identifier, `1.3.6.1.4.1.57264.1.15`.
    pub repository_id: &'a [u8],
    /// Source Repository Owner Identifier, `1.3.6.1.4.1.57264.1.17`.
    pub owner_id: &'a [u8],
    /// Build Trigger, `1.3.6.1.4.1.57264.1.20`.
    pub trigger: &'a [u8],
}

/// A parsed blob whose structure has been checked but whose signatures have
/// not.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub struct TrustRoot<'a> {
    /// The blob's level.
    pub level: u8,
    fulcio: [Option<FulcioIntermediate<'a>>; MAX_FULCIO],
    logs: [Option<LogKey<'a>>; MAX_LOGS],
    tsas: [Option<TsaSigner<'a>>; MAX_TSAS],
    /// The identity policy.
    pub policy: Policy<'a>,
    body: &'a [u8],
    signatures: &'a [u8],
}

impl<'a> TrustRoot<'a> {
    /// The Fulcio intermediates the blob lists.
    pub fn fulcio(&self) -> impl Iterator<Item = &FulcioIntermediate<'a>> {
        self.fulcio.iter().map_while(Option::as_ref)
    }

    /// The log keys the blob lists.
    pub fn logs(&self) -> impl Iterator<Item = &LogKey<'a>> {
        self.logs.iter().map_while(Option::as_ref)
    }

    /// The TSA signers the blob lists.
    pub fn tsas(&self) -> impl Iterator<Item = &TsaSigner<'a>> {
        self.tsas.iter().map_while(Option::as_ref)
    }
}

fn read_window(r: &mut Reader<'_>) -> Result<Window, Error> {
    let not_before = r.u64()?;
    let not_after = r.u64()?;
    if not_before > not_after {
        return Err(Error::OutOfRange);
    }
    Ok(Window {
        not_before,
        not_after,
    })
}

fn read_p384_point<'a>(r: &mut Reader<'a>) -> Result<&'a [u8; P384_POINT_LEN], Error> {
    let point = r.array::<P384_POINT_LEN>()?;
    match point.first() {
        Some(0x04) => Ok(point),
        _ => Err(Error::OutOfRange),
    }
}

/// Reads a string with a length prefix, two bytes when `wide` is set and one
/// byte otherwise, and a length from 1 through `max`. When `printable` is set,
/// every byte must be printable ASCII.
fn read_string<'a>(
    r: &mut Reader<'a>,
    wide: bool,
    max: usize,
    printable: bool,
) -> Result<&'a [u8], Error> {
    let len = if wide {
        usize::from(r.u16()?)
    } else {
        usize::from(r.u8()?)
    };
    if len == 0 || len > max {
        return Err(Error::OutOfRange);
    }
    let s = r.bytes(len)?;
    if printable && !s.iter().all(|b| (0x20..=0x7e).contains(b)) {
        return Err(Error::NotPrintable);
    }
    Ok(s)
}

fn read_count(r: &mut Reader<'_>, max: usize) -> Result<usize, Error> {
    let count = usize::from(r.u8()?);
    if count == 0 || count > max {
        return Err(Error::OutOfRange);
    }
    Ok(count)
}

/// Reports whether any two items have equal keys under `key`.
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

/// Parses a blob and checks its structure. The level rules that involve the
/// chain, the image, and eFuse are in [`crate::level`].
pub fn parse(bytes: &[u8]) -> Result<TrustRoot<'_>, Error> {
    let mut r = Reader::new(bytes);
    r.magic(b"C3TR")?;
    r.version_1()?;
    r.u32()?;
    let level = r.u8()?;
    if level > MAX_LEVEL {
        return Err(Error::BadLevel);
    }
    r.reserved(1)?;

    let mut fulcio = [None; MAX_FULCIO];
    let count = read_count(&mut r, MAX_FULCIO)?;
    for slot in fulcio.iter_mut().take(count) {
        let subject = read_string(&mut r, true, 512, false)?;
        let public_key = read_p384_point(&mut r)?;
        let window = read_window(&mut r)?;
        *slot = Some(FulcioIntermediate {
            subject,
            public_key,
            window,
        });
    }

    let mut logs = [None; MAX_LOGS];
    let count = read_count(&mut r, MAX_LOGS)?;
    for slot in logs.iter_mut().take(count) {
        let origin = read_string(&mut r, false, 128, true)?;
        let public_key = r.array::<32>()?;
        if !c3_crypto::ed25519_public_key_ok(public_key) {
            return Err(Error::BadKey);
        }
        let window = read_window(&mut r)?;
        *slot = Some(LogKey {
            origin,
            public_key,
            window,
        });
    }

    let mut tsas = [None; MAX_TSAS];
    let count = read_count(&mut r, MAX_TSAS)?;
    for slot in tsas.iter_mut().take(count) {
        let signer_id = read_string(&mut r, true, 512, false)?;
        let public_key = read_p384_point(&mut r)?;
        let window = read_window(&mut r)?;
        *slot = Some(TsaSigner {
            signer_id,
            public_key,
            window,
        });
    }

    let policy = Policy {
        issuer: read_string(&mut r, true, 512, true)?,
        build_signer_uri: read_string(&mut r, true, 512, true)?,
        repository_id: read_string(&mut r, true, 512, true)?,
        owner_id: read_string(&mut r, true, 512, true)?,
        trigger: read_string(&mut r, true, 512, true)?,
    };
    let body = r.since(0)?;
    let signatures = read_signatures(&mut r)?;
    r.finish()?;

    let duplicated = has_duplicates(&fulcio, |f| f.subject)
        || has_duplicates(&fulcio, |f| f.public_key)
        || has_duplicates(&logs, |l| l.origin)
        || has_duplicates(&logs, |l| l.public_key)
        || has_duplicates(&tsas, |t| t.signer_id)
        || has_duplicates(&tsas, |t| t.public_key);
    if duplicated {
        return Err(Error::DuplicateKey);
    }

    Ok(TrustRoot {
        level,
        fulcio,
        logs,
        tsas,
        policy,
        body,
        signatures,
    })
}

/// Checks the blob's signatures against the chain's tip.
///
/// `scratch` must hold the blob body plus the domain string and a zero byte;
/// 4,120 bytes is enough for any blob.
pub fn verify(root: &TrustRoot<'_>, tip: &Tip<'_>, scratch: &mut [u8]) -> Result<(), Error> {
    check_signatures(root.signatures, &tip.keys, BLOB_DOMAIN, root.body, scratch)
}

#[cfg(test)]
#[allow(clippy::arithmetic_side_effects, clippy::indexing_slicing)]
pub(crate) mod tests {
    use super::*;
    use crate::keys::KeySet;
    use crate::keys::tests::public_keys;
    use crate::keys::tests::sign_entries;

    fn string(out: &mut Vec<u8>, s: &[u8]) {
        out.extend_from_slice(&(s.len() as u16).to_le_bytes());
        out.extend_from_slice(s);
    }

    fn window(out: &mut Vec<u8>, a: u64, b: u64) {
        out.extend_from_slice(&a.to_le_bytes());
        out.extend_from_slice(&b.to_le_bytes());
    }

    /// The unsigned body of a blob at `level` with one entry of each kind.
    pub(crate) fn body(level: u8) -> Vec<u8> {
        let mut out = b"C3TR".to_vec();
        out.extend_from_slice(&1u16.to_le_bytes());
        out.extend_from_slice(&7u32.to_le_bytes());
        out.push(level);
        out.push(0);
        out.push(1);
        string(&mut out, b"\x30\x00");
        out.push(0x04);
        out.extend_from_slice(&[1u8; 96]);
        window(&mut out, 100, 200);
        out.push(1);
        out.push(14);
        out.extend_from_slice(b"log.example.dv");
        out.extend_from_slice(&public_keys(&[30]));
        window(&mut out, 100, 200);
        out.push(1);
        string(&mut out, b"\x30\x01\x00");
        out.push(0x04);
        out.extend_from_slice(&[3u8; 96]);
        window(&mut out, 100, 200);
        for s in [
            &b"https://token.actions.githubusercontent.com"[..],
            b"https://github.com/o/r/.github/workflows/release.yml@refs/heads/main",
            b"123",
            b"456",
            b"push",
        ] {
            string(&mut out, s);
        }
        out
    }

    pub(crate) fn blob(level: u8, signer_seeds: &[u8], indexes: &[u8]) -> Vec<u8> {
        let b = body(level);
        let mut out = b.clone();
        out.extend_from_slice(&sign_entries(signer_seeds, indexes, BLOB_DOMAIN, &b));
        out
    }

    fn run(bytes: &[u8], signer_seeds: &[u8]) -> Result<u8, Error> {
        let keys = public_keys(signer_seeds);
        let tip = Tip {
            keys: KeySet::new(&keys)?,
            level: 0,
        };
        let root = parse(bytes)?;
        let mut scratch = [0u8; 4120];
        verify(&root, &tip, &mut scratch)?;
        Ok(root.level)
    }

    #[test]
    fn accepts_signed_blob() {
        let bytes = blob(3, &[1, 2, 3], &[0, 1]);
        assert_eq!(run(&bytes, &[1, 2, 3]), Ok(3));
        let root = parse(&bytes).unwrap();
        assert_eq!(root.logs().count(), 1);
        assert_eq!(root.policy.trigger, b"push");
        assert!(root.fulcio().next().unwrap().window.contains(150));
    }

    #[test]
    fn rejects_wrong_signers_and_tampering() {
        let bytes = blob(3, &[1, 2, 3], &[0, 1]);
        assert_eq!(run(&bytes, &[4, 5, 6]), Err(Error::BadSignature));
        let mut tampered = bytes.clone();
        tampered[10] = 4;
        assert_eq!(run(&tampered, &[1, 2, 3]), Err(Error::BadSignature));
    }

    #[test]
    fn link_signature_is_not_a_blob_signature() {
        let b = body(3);
        let mut bytes = b.clone();
        bytes.extend_from_slice(&sign_entries(
            &[1, 2],
            &[0, 1],
            crate::chain::LINK_DOMAIN,
            &b,
        ));
        assert_eq!(run(&bytes, &[1, 2]), Err(Error::BadSignature));
    }

    #[test]
    fn rejects_structural_errors() {
        let good = blob(3, &[1, 2], &[0, 1]);
        assert_eq!(parse(&blob(17, &[1, 2], &[0, 1])), Err(Error::BadLevel));
        let mut bad = good.clone();
        bad.push(0);
        assert_eq!(parse(&bad), Err(Error::TrailingBytes));
        let mut bad = good.clone();
        bad[11] = 1;
        assert_eq!(parse(&bad), Err(Error::NonzeroReserved));
        let mut bad = good.clone();
        bad[12] = 0;
        assert_eq!(parse(&bad), Err(Error::OutOfRange));
        let mut bad = body(3);
        let at = bad.iter().position(|&b| b == b'l').unwrap();
        bad[at] = 0x07;
        bad.extend_from_slice(&sign_entries(&[1, 2], &[0, 1], BLOB_DOMAIN, &bad.clone()));
        assert_eq!(parse(&bad), Err(Error::NotPrintable));
    }

    #[test]
    fn rejects_duplicate_log_origin() {
        let b = body(3);
        let logs_at = 12 + 118;
        assert_eq!(b[logs_at], 1);
        let entry = b[logs_at + 1..logs_at + 64].to_vec();
        let mut second = entry.clone();
        second[15..47].copy_from_slice(&public_keys(&[31]));
        let mut bad = b[..logs_at].to_vec();
        bad.push(2);
        bad.extend_from_slice(&entry);
        bad.extend_from_slice(&second);
        bad.extend_from_slice(&b[logs_at + 64..]);
        bad.extend_from_slice(&sign_entries(&[1, 2], &[0, 1], BLOB_DOMAIN, &bad.clone()));
        assert_eq!(parse(&bad), Err(Error::DuplicateKey));
    }

    #[test]
    fn rejects_unusable_log_key() {
        let mut bad = body(3);
        let key_at = 12 + 118 + 1 + 1 + 14;
        let mut identity = [0u8; 32];
        identity[0] = 1;
        bad[key_at..key_at + 32].copy_from_slice(&identity);
        bad.extend_from_slice(&sign_entries(&[1, 2], &[0, 1], BLOB_DOMAIN, &bad.clone()));
        assert_eq!(parse(&bad), Err(Error::BadKey));
    }

    #[test]
    fn rejects_inverted_window_and_compressed_point() {
        let mut bad = body(3);
        let at = 12 + 1 + 2 + 2 + 97;
        bad[at..at + 8].copy_from_slice(&300u64.to_le_bytes());
        bad.extend_from_slice(&sign_entries(&[1, 2], &[0, 1], BLOB_DOMAIN, &bad.clone()));
        assert_eq!(parse(&bad), Err(Error::OutOfRange));
        let mut bad = body(3);
        bad[12 + 1 + 2 + 2] = 0x02;
        bad.extend_from_slice(&sign_entries(&[1, 2], &[0, 1], BLOB_DOMAIN, &bad.clone()));
        assert_eq!(parse(&bad), Err(Error::OutOfRange));
    }
}
