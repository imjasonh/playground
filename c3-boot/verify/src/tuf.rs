//! Sigstore's TUF metadata: the root rotation chain and the targets role
//! that lists `trusted_root.json`.
//!
//! This follows the TUF specification's client workflow (sections 5.3 and
//! 5.6) for the parts a device without a clock or writable state can check:
//!
//! - Each new root has a version one more than the trusted root's, and is
//!   signed by a threshold of the trusted root's root keys and a threshold
//!   of its own.
//! - `targets.json` is signed by a threshold of the final root's targets
//!   keys, and lists `trusted_root.json` with its length and SHA-256 digest.
//!
//! The device doesn't check the snapshot and timestamp roles, which protect
//! against freeze and mix-and-match attacks on clients that have a clock and
//! remember what they saw. Expiry is checked against the TSA's signed time
//! instead, in [`crate::tuf_slot`].
//!
//! Signatures cover the canonical JSON of the `signed` object. Metadata
//! documents must be canonical JSON as a whole, so those bytes are the
//! `signed` value's bytes in the document, and nothing is re-encoded.

use crate::error::Error;
use crate::json::Mode;
use crate::json::Value;
use crate::reader::Reader;

/// Why a TUF check rejected its input.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum TufError {
    /// A document isn't JSON in the profile `json` requires, or isn't
    /// canonical JSON where TUF requires it.
    Json,
    /// A field is missing, has the wrong type, or has a value the profile
    /// doesn't allow.
    Schema,
    /// A root's version isn't one more than the version of the root before
    /// it.
    Version,
    /// Fewer distinct keys than the role's threshold signed.
    Threshold,
    /// `targets.json` doesn't list `trusted_root.json` with its length and
    /// digest.
    Target,
    /// The signed time is after the root or targets metadata expired.
    Expired,
    /// The TUF part couldn't be read from where it's stored.
    Read,
    /// A check shared with the other slot formats failed.
    Check(Error),
}

impl From<Error> for TufError {
    fn from(e: Error) -> Self {
        TufError::Check(e)
    }
}

/// The most keys a role can list.
pub const MAX_ROLE_KEYS: usize = 8;
/// The longest key ID a role can list.
pub const MAX_KEYID_LEN: usize = 64;
/// The most new roots one slot can carry.
pub const MAX_ROOTS: usize = 64;
/// The longest document in the TUF part: a root, `targets.json`, or
/// `trusted_root.json`.
pub const MAX_DOC_LEN: u32 = 10_240;
/// The longest TUF part: room for [`MAX_ROOTS`] roots of 5,600 bytes and
/// the other documents, rounded up to a 64 KiB multiple.
pub const MAX_TUF_LEN: u32 = 0x6_0000;
/// The magic number of the TUF part of a slot.
pub const TUF_MAGIC: &[u8; 4] = b"C3TU";
const TUF_VERSION: u16 = 2;
/// The length of the TUF part's header: the magic, version, and root count.
const HEADER_LEN: u32 = 8;
/// The target that holds Sigstore's trusted root.
pub const TRUSTED_ROOT_TARGET: &[u8] = b"trusted_root.json";

const PEM_HEADER: &[u8] = b"-----BEGIN PUBLIC KEY-----\n";
const PEM_FOOTER: &[u8] = b"-----END PUBLIC KEY-----\n";
/// The DER `SubjectPublicKeyInfo` of a P-256 key, up to the point.
const P256_SPKI_PREFIX: [u8; 26] = [
    0x30, 0x59, 0x30, 0x13, 0x06, 0x07, 0x2a, 0x86, 0x48, 0xce, 0x3d, 0x02, 0x01, 0x06, 0x08, 0x2a,
    0x86, 0x48, 0xce, 0x3d, 0x03, 0x01, 0x07, 0x03, 0x42, 0x00,
];
/// The DER `SubjectPublicKeyInfo` of a P-384 key, up to the point.
const P384_SPKI_PREFIX: [u8; 23] = [
    0x30, 0x76, 0x30, 0x10, 0x06, 0x07, 0x2a, 0x86, 0x48, 0xce, 0x3d, 0x02, 0x01, 0x06, 0x05, 0x2b,
    0x81, 0x04, 0x00, 0x22, 0x03, 0x62, 0x00,
];

/// A TUF public key of a type the device can verify.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum Key {
    /// `ecdsa-sha2-nistp256`: an uncompressed SEC1 point.
    P256([u8; 65]),
    /// `ecdsa-sha2-nistp384`: an uncompressed SEC1 point.
    P384([u8; 97]),
    /// `ed25519`.
    Ed25519([u8; 32]),
}

fn hex_value(c: u8) -> Option<u8> {
    match c {
        b'0'..=b'9' => c.checked_sub(b'0'),
        b'a'..=b'f' => c.checked_sub(b'a').and_then(|v| v.checked_add(10)),
        _ => None,
    }
}

/// Decodes lowercase hex into `out` and returns the bytes written.
fn hex_decode<'o>(text: &[u8], out: &'o mut [u8]) -> Option<&'o [u8]> {
    let (pairs, rest) = text.as_chunks::<2>();
    if !rest.is_empty() {
        return None;
    }
    let dst = out.get_mut(..pairs.len())?;
    for (o, [hi, lo]) in dst.iter_mut().zip(pairs) {
        *o = (hex_value(*hi)? << 4) | hex_value(*lo)?;
    }
    Some(dst)
}

/// Lowercase hex of a SHA-256 digest.
fn hex_digest(digest: &[u8; 32]) -> [u8; 64] {
    const DIGITS: &[u8; 16] = b"0123456789abcdef";
    let mut out = [0u8; 64];
    for (pair, b) in out.as_chunks_mut::<2>().0.iter_mut().zip(digest) {
        let hi = DIGITS.get(usize::from(b >> 4)).copied().unwrap_or(0);
        let lo = DIGITS.get(usize::from(b & 0x0f)).copied().unwrap_or(0);
        *pair = [hi, lo];
    }
    out
}

/// The DER `SubjectPublicKeyInfo` in a PEM `PUBLIC KEY` block: the text
/// between the header and footer lines without its line feeds, decoded as
/// base64.
fn pem_spki<'o>(pem: &[u8], out: &'o mut [u8; 128]) -> Option<&'o [u8]> {
    let body = pem.strip_prefix(PEM_HEADER)?.strip_suffix(PEM_FOOTER)?;
    let mut text = [0u8; 192];
    let mut len = 0usize;
    for &b in body.iter().filter(|&&b| b != b'\n') {
        *text.get_mut(len)? = b;
        len = len.checked_add(1)?;
    }
    let n = crate::base64::decode_into(text.get(..len)?, out).ok()?;
    out.get(..n)
}

/// Decodes a TUF key object, or returns `None` if its type or scheme isn't
/// one the device verifies or its fields don't decode. A key that doesn't
/// decode can't count toward a threshold.
pub fn decode_key(key: Value<'_>) -> Option<Key> {
    let keytype = key.field(b"keytype").ok()?.str().ok()?;
    let scheme = key.field(b"scheme").ok()?.str().ok()?;
    let public = key
        .field(b"keyval")
        .ok()?
        .field(b"public")
        .ok()?
        .str()
        .ok()?;
    let mut buf = [0u8; 128];
    match (keytype, scheme) {
        (b"ecdsa" | b"ecdsa-sha2-nistp256", b"ecdsa-sha2-nistp256") => {
            let point = pem_spki(public, &mut buf)?.strip_prefix(&P256_SPKI_PREFIX)?;
            Some(Key::P256(point.try_into().ok()?))
        }
        (b"ecdsa" | b"ecdsa-sha2-nistp384", b"ecdsa-sha2-nistp384") => {
            let point = pem_spki(public, &mut buf)?.strip_prefix(&P384_SPKI_PREFIX)?;
            Some(Key::P384(point.try_into().ok()?))
        }
        (b"ed25519", b"ed25519") => {
            Some(Key::Ed25519(hex_decode(public, &mut buf)?.try_into().ok()?))
        }
        _ => None,
    }
}

/// Reports whether `sig`, lowercase hex, is `key`'s signature over
/// `message`. ECDSA signatures are DER and sign the message's SHA-256 or
/// SHA-384 digest; Ed25519 signatures are the 64-byte RFC 8032 form.
pub fn signature_valid(key: &Key, message: &[u8], sig: &[u8]) -> bool {
    let mut buf = [0u8; 128];
    let Some(sig) = hex_decode(sig, &mut buf) else {
        return false;
    };
    match key {
        Key::P256(point) => match crate::der::ecdsa_signature::<32>(sig) {
            Ok((r, s)) => {
                c3_crypto::p256_verify_prehash(point, &c3_crypto::sha256(message), &r, &s)
            }
            Err(_) => false,
        },
        Key::P384(point) => match crate::der::ecdsa_signature::<48>(sig) {
            Ok((r, s)) => {
                c3_crypto::p384_verify_prehash(point, &c3_crypto::sha384(message), &r, &s)
            }
            Err(_) => false,
        },
        Key::Ed25519(public) => match <&[u8; 64]>::try_from(sig) {
            Ok(sig) => c3_crypto::ed25519_verify(public, message, sig),
            Err(_) => false,
        },
    }
}

/// A metadata document whose structure and type have been checked but whose
/// signatures have not.
#[derive(Clone, Copy, Debug)]
pub struct Metadata<'a> {
    /// The `signed` object.
    pub signed: Value<'a>,
    signatures: Value<'a>,
}

impl<'a> Metadata<'a> {
    /// The signature with key ID `keyid`, if there is one.
    fn signature(&self, keyid: &[u8]) -> Result<Option<&'a [u8]>, TufError> {
        let mut sigs = self.signatures.elements()?;
        while let Some(s) = sigs.next_element()? {
            if s.field(b"keyid")?.str()? == keyid {
                return Ok(Some(s.field(b"sig")?.str()?));
            }
        }
        Ok(None)
    }
}

/// Parses a canonical JSON metadata document: an object with exactly the
/// members `signatures` and `signed`, where `signed._type` is `kind` and
/// every signature has a string `keyid` and `sig`, with no key ID twice.
pub fn parse_metadata<'a>(doc: &'a [u8], kind: &[u8]) -> Result<Metadata<'a>, TufError> {
    let top = crate::json::parse(doc, Mode::Canonical)?;
    let mut members = top.members()?;
    let (k1, signatures) = members.next_member()?.ok_or(TufError::Schema)?;
    let (k2, signed) = members.next_member()?.ok_or(TufError::Schema)?;
    if k1 != b"signatures" || k2 != b"signed" || members.next_member()?.is_some() {
        return Err(TufError::Schema);
    }
    if signed.field(b"_type")?.str()? != kind {
        return Err(TufError::Schema);
    }
    let mut sigs = signatures.elements()?;
    while let Some(s) = sigs.next_element()? {
        let keyid = s.field(b"keyid")?.str()?;
        s.field(b"sig")?.str()?;
        let mut later = sigs.clone();
        while let Some(other) = later.next_element()? {
            if other.field(b"keyid")?.str()? == keyid {
                return Err(TufError::Schema);
            }
        }
    }
    Ok(Metadata { signed, signatures })
}

/// A role's threshold and keys, read from a root so that later checks don't
/// need the root's bytes.
#[derive(Clone, Copy, Debug)]
pub struct RoleKeys {
    threshold: u64,
    listed: usize,
    ids: [[u8; MAX_KEYID_LEN]; MAX_ROLE_KEYS],
    id_lens: [usize; MAX_ROLE_KEYS],
    /// Each listed key, or `None` if it doesn't decode.
    keys: [Option<Key>; MAX_ROLE_KEYS],
}

impl RoleKeys {
    /// Reads `role` from `root`, a root's `signed` object. A role lists at
    /// most [`MAX_ROLE_KEYS`] key IDs of at most [`MAX_KEYID_LEN`] bytes, and
    /// its threshold is at least 1.
    pub fn read(root: Value<'_>, role: &[u8]) -> Result<Self, TufError> {
        let role = root.field(b"roles")?.field(role)?;
        let threshold = role.field(b"threshold")?.u64()?;
        if threshold == 0 {
            return Err(TufError::Schema);
        }
        let keys = root.field(b"keys")?;
        keys.members()?;
        let mut out = RoleKeys {
            threshold,
            listed: 0,
            ids: [[0; MAX_KEYID_LEN]; MAX_ROLE_KEYS],
            id_lens: [0; MAX_ROLE_KEYS],
            keys: [None; MAX_ROLE_KEYS],
        };
        let mut ids = role.field(b"keyids")?.elements()?;
        while let Some(id) = ids.next_element()? {
            let id = id.str()?;
            let i = out.listed;
            let dst = out.ids.get_mut(i).ok_or(TufError::Schema)?;
            dst.get_mut(..id.len())
                .ok_or(TufError::Schema)?
                .copy_from_slice(id);
            *out.id_lens.get_mut(i).ok_or(TufError::Schema)? = id.len();
            *out.keys.get_mut(i).ok_or(TufError::Schema)? = keys.get(id)?.and_then(decode_key);
            out.listed = i.checked_add(1).ok_or(TufError::Schema)?;
        }
        Ok(out)
    }

    /// Reports whether at least the threshold of distinct listed keys signed
    /// `meta`. A listed key counts when it decodes, `meta` has a signature
    /// with its key ID, and that signature verifies over the `signed` bytes.
    /// Keys with equal values count once.
    pub fn met(&self, meta: &Metadata<'_>) -> Result<bool, TufError> {
        let message = meta.signed.bytes();
        let mut counted = [0usize; MAX_ROLE_KEYS];
        let mut count = 0usize;
        for i in 0..self.listed {
            let Some(Some(key)) = self.keys.get(i) else {
                continue;
            };
            let len = self.id_lens.get(i).copied().unwrap_or(0);
            let id = self
                .ids
                .get(i)
                .and_then(|id| id.get(..len))
                .ok_or(TufError::Schema)?;
            let Some(sig) = meta.signature(id)? else {
                continue;
            };
            let seen = counted
                .get(..count)
                .ok_or(TufError::Schema)?
                .iter()
                .any(|&j| self.keys.get(j) == Some(&Some(*key)));
            if seen || !signature_valid(key, message, sig) {
                continue;
            }
            *counted.get_mut(count).ok_or(TufError::Schema)? = i;
            count = count.checked_add(1).ok_or(TufError::Schema)?;
        }
        Ok(u64::try_from(count).map_err(|_| TufError::Schema)? >= self.threshold)
    }
}

/// Reports whether `meta` is signed by at least the threshold of distinct
/// keys that `delegator`, a root's `signed` object, lists for `role`.
pub fn threshold_met(
    meta: &Metadata<'_>,
    delegator: Value<'_>,
    role: &[u8],
) -> Result<bool, TufError> {
    RoleKeys::read(delegator, role)?.met(meta)
}

/// A root whose structure has been checked.
#[derive(Clone, Copy, Debug)]
pub struct Root<'a> {
    /// The root's metadata.
    pub meta: Metadata<'a>,
    /// `signed.version`, at least 1.
    pub version: u64,
}

/// Parses a root metadata document.
pub fn parse_root(doc: &[u8]) -> Result<Root<'_>, TufError> {
    let meta = parse_metadata(doc, b"root")?;
    let version = meta.signed.field(b"version")?.u64()?;
    if version == 0 {
        return Err(TufError::Schema);
    }
    Ok(Root { meta, version })
}

/// Where the verifier reads a slot's TUF part from.
pub trait Source {
    /// Fills `out` with the bytes that start `offset` bytes into the TUF
    /// part, or returns `false` if they can't be read.
    fn read(&mut self, offset: u32, out: &mut [u8]) -> bool;
}

impl Source for &[u8] {
    fn read(&mut self, offset: u32, out: &mut [u8]) -> bool {
        let Ok(start) = usize::try_from(offset) else {
            return false;
        };
        match start
            .checked_add(out.len())
            .and_then(|end| self.get(start..end))
        {
            Some(src) => {
                out.copy_from_slice(src);
                true
            }
            None => false,
        }
    }
}

/// The index of a TUF part: the number of roots and the length of each
/// document, the roots first, then `targets.json` and `trusted_root.json`.
#[derive(Clone, Copy, Debug)]
pub struct Index {
    roots: usize,
    lengths: [u32; MAX_ROOTS + 2],
}

impl Index {
    /// The number of new roots.
    pub fn roots(&self) -> usize {
        self.roots
    }

    /// The offset and length of document `i`: root `i` for `i` below
    /// [`Index::roots`], then `targets.json`, then `trusted_root.json`.
    pub fn doc(&self, i: usize) -> Result<(u32, u32), Error> {
        let count = self.roots.checked_add(2).ok_or(Error::Overflow)?;
        let index_len = u32::try_from(count.checked_mul(4).ok_or(Error::Overflow)?)
            .map_err(|_| Error::Overflow)?;
        let mut offset = HEADER_LEN.checked_add(index_len).ok_or(Error::Overflow)?;
        for len in self.lengths.get(..i).ok_or(Error::OutOfRange)? {
            offset = offset.checked_add(*len).ok_or(Error::Overflow)?;
        }
        let len = self
            .lengths
            .get(..count)
            .and_then(|l| l.get(i))
            .ok_or(Error::OutOfRange)?;
        Ok((offset, *len))
    }
}

/// Reads and checks the header and index of a TUF part `part_len` bytes
/// long: the magic `C3TU`, version 2, the number of roots as a 2-byte
/// count of at most [`MAX_ROOTS`], then a 4-byte length for each root,
/// `targets.json`, and `trusted_root.json`, each from 1 to
/// [`MAX_DOC_LEN`]. The documents follow the index in that order with
/// nothing between or after them, and the part is at most
/// [`MAX_TUF_LEN`] bytes. Integers are little endian.
pub fn read_index<S: Source>(src: &mut S, part_len: u32) -> Result<Index, TufError> {
    if part_len > MAX_TUF_LEN {
        return Err(Error::OutOfRange.into());
    }
    let mut head = [0u8; 8];
    if !src.read(0, &mut head) {
        return Err(TufError::Read);
    }
    let mut r = Reader::new(&head);
    r.magic(TUF_MAGIC)?;
    if r.u16()? != TUF_VERSION {
        return Err(Error::BadVersion.into());
    }
    let roots = usize::from(r.u16()?);
    if roots > MAX_ROOTS {
        return Err(Error::OutOfRange.into());
    }
    let count = roots.checked_add(2).ok_or(Error::Overflow)?;
    let mut raw = [0u8; 4 * (MAX_ROOTS + 2)];
    let raw = raw
        .get_mut(..count.checked_mul(4).ok_or(Error::Overflow)?)
        .ok_or(Error::Overflow)?;
    if part_len < HEADER_LEN {
        return Err(Error::Truncated.into());
    }
    if !src.read(HEADER_LEN, raw) {
        return Err(TufError::Read);
    }
    let mut index = Index {
        roots,
        lengths: [0; MAX_ROOTS + 2],
    };
    let mut r = Reader::new(raw);
    for len in index.lengths.get_mut(..count).ok_or(Error::Overflow)? {
        *len = r.u32()?;
        if *len == 0 || *len > MAX_DOC_LEN {
            return Err(Error::OutOfRange.into());
        }
    }
    let (offset, len) = index.doc(count.checked_sub(1).ok_or(Error::Overflow)?)?;
    let end = offset.checked_add(len).ok_or(Error::Overflow)?;
    if end > part_len {
        return Err(Error::Truncated.into());
    }
    if end < part_len {
        return Err(Error::TrailingBytes.into());
    }
    Ok(index)
}

/// Reads document `i` of the part into the start of `buf`.
fn read_doc<'b, S: Source>(
    src: &mut S,
    index: &Index,
    i: usize,
    buf: &'b mut [u8],
) -> Result<&'b [u8], TufError> {
    let (offset, len) = index.doc(i)?;
    let len = usize::try_from(len).map_err(|_| Error::Overflow)?;
    let dst = buf.get_mut(..len).ok_or(Error::ScratchTooSmall)?;
    if !src.read(offset, dst) {
        return Err(TufError::Read);
    }
    Ok(dst)
}

/// What verified TUF metadata establishes.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub struct Verified {
    /// The final root's version.
    pub root_version: u64,
    /// The earlier of the final root's and `targets.json`'s expiry times, in
    /// seconds since the Unix epoch.
    pub expires: u64,
}

fn expires(meta: &Metadata<'_>) -> Result<u64, TufError> {
    Ok(crate::time::rfc3339(meta.signed.field(b"expires")?.str()?)?)
}

/// Verifies the TUF part of a slot, `part_len` bytes read from `src`, from
/// the pinned root: the root chain, `targets.json` under the final root, and
/// `trusted_root.json` against its entry in `targets.json`. Returns what the
/// metadata establishes and `trusted_root.json`, which is left at the start
/// of `buf`.
///
/// The documents are read into `buf` one at a time, so `buf` needs room for
/// the longest one, at most [`MAX_DOC_LEN`] bytes, however many roots the
/// part holds. Only the threshold and keys of the trusted root's root role,
/// and of the final root's targets role, are kept between documents.
pub fn verify<'b, S: Source>(
    pinned: &[u8],
    src: &mut S,
    part_len: u32,
    buf: &'b mut [u8],
) -> Result<(Verified, &'b [u8]), TufError> {
    let index = read_index(src, part_len)?;
    let roots = index.roots();
    let pinned = parse_root(pinned)?;
    let mut version = pinned.version;
    // The trusted root's root role. A malformed role fails the chain only
    // when another root follows it.
    let mut trusted = RoleKeys::read(pinned.meta.signed, b"root");
    let mut targets_role = RoleKeys::read(pinned.meta.signed, b"targets");
    let mut root_expires = expires(&pinned.meta);
    for i in 0..roots {
        let next = parse_root(read_doc(src, &index, i, buf)?)?;
        if Some(next.version) != version.checked_add(1) {
            return Err(TufError::Version);
        }
        if !trusted?.met(&next.meta)? {
            return Err(TufError::Threshold);
        }
        let own = RoleKeys::read(next.meta.signed, b"root")?;
        if !own.met(&next.meta)? {
            return Err(TufError::Threshold);
        }
        if i.checked_add(1) == Some(roots) {
            targets_role = RoleKeys::read(next.meta.signed, b"targets");
            root_expires = expires(&next.meta);
        }
        version = next.version;
        trusted = Ok(own);
    }
    let root_expires = root_expires?;

    let targets = parse_metadata(read_doc(src, &index, roots, buf)?, b"targets")?;
    if !targets_role?.met(&targets)? {
        return Err(TufError::Threshold);
    }
    let targets_expires = expires(&targets)?;
    let entry = targets
        .signed
        .field(b"targets")?
        .get(TRUSTED_ROOT_TARGET)?
        .ok_or(TufError::Target)?;
    let length = entry.field(b"length")?.u64()?;
    let sha256: Option<[u8; 64]> = entry
        .field(b"hashes")?
        .field(b"sha256")?
        .str()?
        .try_into()
        .ok();

    let trusted_root = read_doc(
        src,
        &index,
        roots.checked_add(1).ok_or(Error::Overflow)?,
        buf,
    )?;
    let actual = hex_digest(&c3_crypto::sha256(trusted_root));
    let length_ok = usize::try_from(length).is_ok_and(|l| l == trusted_root.len());
    if !length_ok || sha256 != Some(actual) {
        return Err(TufError::Target);
    }
    let verified = Verified {
        root_version: version,
        expires: root_expires.min(targets_expires),
    };
    Ok((verified, trusted_root))
}

#[cfg(test)]
#[allow(clippy::arithmetic_side_effects, clippy::indexing_slicing)]
mod tests {
    use super::*;

    fn value(doc: &str) -> Value<'_> {
        crate::json::parse(doc.as_bytes(), Mode::Strict).unwrap()
    }

    #[test]
    fn hex_is_lowercase_and_even() {
        let mut buf = [0u8; 4];
        assert_eq!(hex_decode(b"00ff7a", &mut buf), Some(&[0, 0xff, 0x7a][..]));
        assert_eq!(hex_decode(b"", &mut buf), Some(&[][..]));
        assert_eq!(hex_decode(b"0F", &mut buf), None);
        assert_eq!(hex_decode(b"0", &mut buf), None);
        assert_eq!(hex_decode(b"0000000000", &mut buf), None);
        assert_eq!(&hex_digest(&[0xab; 32])[..4], b"abab");
    }

    #[test]
    fn decodes_ed25519_keys_only_in_full() {
        let public = "11".repeat(32);
        let doc = format!(
            r#"{{"keytype":"ed25519","scheme":"ed25519","keyval":{{"public":"{public}"}}}}"#
        );
        assert_eq!(decode_key(value(&doc)), Some(Key::Ed25519([0x11; 32])));
        let short = doc.replace(&public, &"11".repeat(31));
        assert_eq!(decode_key(value(&short)), None);
        let rsa = doc.replace(r#""keytype":"ed25519""#, r#""keytype":"rsa""#);
        assert_eq!(decode_key(value(&rsa)), None);
        let mismatched = doc.replace(r#""scheme":"ed25519""#, r#""scheme":"ecdsa-sha2-nistp256""#);
        assert_eq!(decode_key(value(&mismatched)), None);
    }

    #[test]
    fn pem_needs_its_header_and_footer() {
        let mut out = [0u8; 128];
        let pem = b"-----BEGIN PUBLIC KEY-----\nAAEC\nAw==\n-----END PUBLIC KEY-----\n";
        assert_eq!(pem_spki(pem, &mut out), Some(&[0, 1, 2, 3][..]));
        assert_eq!(pem_spki(&pem[1..], &mut out), None);
        assert_eq!(pem_spki(&pem[..pem.len() - 1], &mut out), None);
    }

    fn part(roots: &[&[u8]], targets: &[u8], trusted: &[u8]) -> Vec<u8> {
        let mut tuf = TUF_MAGIC.to_vec();
        tuf.extend_from_slice(&TUF_VERSION.to_le_bytes());
        tuf.extend_from_slice(&(roots.len() as u16).to_le_bytes());
        let docs: Vec<&[u8]> = roots.iter().copied().chain([targets, trusted]).collect();
        for doc in &docs {
            tuf.extend_from_slice(&(doc.len() as u32).to_le_bytes());
        }
        for doc in &docs {
            tuf.extend_from_slice(doc);
        }
        tuf
    }

    fn index(tuf: &[u8]) -> Result<Index, TufError> {
        read_index(&mut &tuf[..], tuf.len() as u32)
    }

    #[test]
    fn index_locates_each_document() {
        let tuf = part(&[b"ab", b"cde"], b"{}", b"x");
        let index = index(&tuf).unwrap();
        assert_eq!(index.roots(), 2);
        let docs: Vec<&[u8]> = (0..4)
            .map(|i| {
                let (offset, len) = index.doc(i).unwrap();
                &tuf[offset as usize..][..len as usize]
            })
            .collect();
        assert_eq!(docs, [&b"ab"[..], b"cde", b"{}", b"x"]);
        assert_eq!(index.doc(4), Err(Error::OutOfRange));
    }

    #[test]
    fn index_limits_roots_and_lengths() {
        let tuf = part(&[], b"{}", b"x");
        assert!(index(&tuf).is_ok());
        let mut version = tuf.clone();
        version[4] = 1;
        assert_eq!(index(&version).unwrap_err(), Error::BadVersion.into());
        let many = part(&vec![&b"r"[..]; MAX_ROOTS + 1], b"{}", b"x");
        assert_eq!(index(&many).unwrap_err(), Error::OutOfRange.into());
        assert!(index(&part(&vec![&b"r"[..]; MAX_ROOTS], b"{}", b"x")).is_ok());
        let empty = part(&[], b"", b"x");
        assert_eq!(index(&empty).unwrap_err(), Error::OutOfRange.into());
        let long = vec![b' '; MAX_DOC_LEN as usize + 1];
        assert_eq!(
            index(&part(&[], &long, b"x")).unwrap_err(),
            Error::OutOfRange.into()
        );
        assert_eq!(
            index(&tuf[..tuf.len() - 1]).unwrap_err(),
            Error::Truncated.into()
        );
        let mut trailing = tuf.clone();
        trailing.push(0);
        assert_eq!(index(&trailing).unwrap_err(), Error::TrailingBytes.into());
        assert_eq!(
            read_index(&mut &tuf[..], MAX_TUF_LEN + 1).unwrap_err(),
            Error::OutOfRange.into()
        );
        assert_eq!(read_index(&mut &tuf[..4], 4).unwrap_err(), TufError::Read);
    }
}
