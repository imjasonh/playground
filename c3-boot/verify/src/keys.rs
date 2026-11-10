//! Ed25519 key sets and threshold signatures over domain-separated messages.

use crate::error::Error;
use crate::reader::Reader;

/// The most keys a key set can hold.
pub const MAX_KEYS: usize = 4;
/// The fewest distinct signatures a link or blob needs.
pub const THRESHOLD: usize = 2;
/// The length of one signature entry: a key index and a signature.
const SIGNATURE_ENTRY_LEN: usize = 65;

/// A set of one to [`MAX_KEYS`] distinct Ed25519 public keys.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub struct KeySet<'a> {
    keys: &'a [u8],
}

impl<'a> KeySet<'a> {
    /// Wraps `keys`, the concatenation of one to four distinct 32-byte keys,
    /// each a usable Ed25519 public key.
    pub fn new(keys: &'a [u8]) -> Result<Self, Error> {
        let (chunks, rest) = keys.as_chunks::<32>();
        if !rest.is_empty() || chunks.is_empty() || chunks.len() > MAX_KEYS {
            return Err(Error::OutOfRange);
        }
        for (i, a) in chunks.iter().enumerate() {
            if !c3_crypto::ed25519_public_key_ok(a) {
                return Err(Error::BadKey);
            }
            if chunks.iter().skip(i.saturating_add(1)).any(|b| a == b) {
                return Err(Error::DuplicateKey);
            }
        }
        Ok(KeySet { keys })
    }

    /// The number of keys in the set.
    pub fn len(&self) -> usize {
        self.keys.as_chunks::<32>().0.len()
    }

    /// Reports whether the set has no keys. A checked set never does.
    pub fn is_empty(&self) -> bool {
        self.keys.is_empty()
    }

    /// The key at `index`, if there is one.
    pub fn key(&self, index: usize) -> Option<&'a [u8; 32]> {
        self.keys.as_chunks::<32>().0.get(index)
    }
}

/// Reads a key set: a 1-byte count followed by that many keys.
pub(crate) fn read_key_set<'a>(r: &mut Reader<'a>) -> Result<KeySet<'a>, Error> {
    let count = usize::from(r.u8()?);
    if count == 0 || count > MAX_KEYS {
        return Err(Error::OutOfRange);
    }
    let len = count.checked_mul(32).ok_or(Error::Overflow)?;
    KeySet::new(r.bytes(len)?)
}

/// Reads a signature list: a 1-byte count from [`THRESHOLD`] through
/// [`MAX_KEYS`], then that many 65-byte entries.
pub(crate) fn read_signatures<'a>(r: &mut Reader<'a>) -> Result<&'a [u8], Error> {
    let count = usize::from(r.u8()?);
    if !(THRESHOLD..=MAX_KEYS).contains(&count) {
        return Err(Error::OutOfRange);
    }
    let len = count
        .checked_mul(SIGNATURE_ENTRY_LEN)
        .ok_or(Error::Overflow)?;
    r.bytes(len)
}

/// Writes `prefix`, a zero byte, and `body` into `scratch`, and returns that
/// message.
fn domain_message<'s>(
    prefix: &[u8],
    body: &[u8],
    scratch: &'s mut [u8],
) -> Result<&'s [u8], Error> {
    let prefix_end = prefix.len();
    let body_start = prefix_end.checked_add(1).ok_or(Error::Overflow)?;
    let end = body_start.checked_add(body.len()).ok_or(Error::Overflow)?;
    let out = scratch.get_mut(..end).ok_or(Error::ScratchTooSmall)?;
    let (head, tail) = out.split_at_mut(prefix_end);
    head.copy_from_slice(prefix);
    let (zero, rest) = tail.split_first_mut().ok_or(Error::ScratchTooSmall)?;
    *zero = 0;
    rest.copy_from_slice(body);
    Ok(out)
}

/// Checks that every entry in `signatures` is a valid signature by a distinct
/// key of `signers` over `prefix`, a zero byte, and `body`.
///
/// Key indexes must be strictly increasing and less than the set's size, so
/// no key counts twice. `signatures` comes from [`read_signatures`], so it has
/// at least [`THRESHOLD`] entries.
pub(crate) fn check_signatures(
    signatures: &[u8],
    signers: &KeySet<'_>,
    prefix: &[u8],
    body: &[u8],
    scratch: &mut [u8],
) -> Result<(), Error> {
    let (entries, rest) = signatures.as_chunks::<SIGNATURE_ENTRY_LEN>();
    if !rest.is_empty() || entries.len() < THRESHOLD {
        return Err(Error::OutOfRange);
    }
    let message = domain_message(prefix, body, scratch)?;
    let mut next_allowed = 0usize;
    for entry in entries {
        let (&[index], signature) = entry.split_first_chunk::<1>().ok_or(Error::Truncated)?;
        let index = usize::from(index);
        if index < next_allowed {
            return Err(Error::BadKeyIndex);
        }
        let key = signers.key(index).ok_or(Error::BadKeyIndex)?;
        let signature: &[u8; 64] = signature.try_into().map_err(|_| Error::Truncated)?;
        if !c3_crypto::ed25519_verify(key, message, signature) {
            return Err(Error::BadSignature);
        }
        next_allowed = index.checked_add(1).ok_or(Error::Overflow)?;
    }
    Ok(())
}

#[cfg(test)]
#[allow(clippy::arithmetic_side_effects, clippy::indexing_slicing)]
pub(crate) mod tests {
    use super::*;
    use ed25519_dalek::Signer;
    use ed25519_dalek::SigningKey;

    pub(crate) fn signing_key(seed: u8) -> SigningKey {
        SigningKey::from_bytes(&[seed; 32])
    }

    pub(crate) fn public_keys(seeds: &[u8]) -> Vec<u8> {
        seeds
            .iter()
            .flat_map(|&s| signing_key(s).verifying_key().to_bytes())
            .collect()
    }

    /// Signs `prefix || 0 || body` with the keys at `indexes` of `seeds`.
    pub(crate) fn sign_entries(
        seeds: &[u8],
        indexes: &[u8],
        prefix: &[u8],
        body: &[u8],
    ) -> Vec<u8> {
        let mut message = prefix.to_vec();
        message.push(0);
        message.extend_from_slice(body);
        let mut out = vec![indexes.len() as u8];
        for &i in indexes {
            out.push(i);
            out.extend_from_slice(&signing_key(seeds[usize::from(i)]).sign(&message).to_bytes());
        }
        out
    }

    #[test]
    fn key_set_rules() {
        assert!(KeySet::new(&public_keys(&[1, 2])).is_ok());
        assert_eq!(KeySet::new(&public_keys(&[1, 1])), Err(Error::DuplicateKey));
        assert_eq!(KeySet::new(&[]), Err(Error::OutOfRange));
        assert_eq!(
            KeySet::new(&public_keys(&[1, 2, 3, 4, 5])),
            Err(Error::OutOfRange)
        );
        assert_eq!(KeySet::new(&[0u8; 33]), Err(Error::OutOfRange));
        let mut identity = [0u8; 32];
        identity[0] = 1;
        assert_eq!(KeySet::new(&identity), Err(Error::BadKey));
    }

    fn check(seeds: &[u8], entries: &[u8], body: &[u8]) -> Result<(), Error> {
        let keys = public_keys(seeds);
        let set = KeySet::new(&keys)?;
        let mut r = Reader::new(entries);
        let sigs = read_signatures(&mut r)?;
        r.finish()?;
        let mut scratch = [0u8; 256];
        check_signatures(sigs, &set, b"test v1", body, &mut scratch)
    }

    #[test]
    fn accepts_threshold_signatures() {
        let entries = sign_entries(&[1, 2, 3], &[0, 2], b"test v1", b"body");
        assert_eq!(check(&[1, 2, 3], &entries, b"body"), Ok(()));
    }

    #[test]
    fn rejects_one_signature_and_repeats() {
        let one = sign_entries(&[1, 2, 3], &[1], b"test v1", b"body");
        assert_eq!(check(&[1, 2, 3], &one, b"body"), Err(Error::OutOfRange));
        let repeat = sign_entries(&[1, 2, 3], &[1, 1], b"test v1", b"body");
        assert_eq!(check(&[1, 2, 3], &repeat, b"body"), Err(Error::BadKeyIndex));
        let backward = sign_entries(&[1, 2, 3], &[2, 0], b"test v1", b"body");
        assert_eq!(
            check(&[1, 2, 3], &backward, b"body"),
            Err(Error::BadKeyIndex)
        );
    }

    #[test]
    fn rejects_out_of_range_index_and_wrong_domain() {
        let mut entries = sign_entries(&[1, 2, 3], &[0, 1], b"test v1", b"body");
        entries[66] = 3;
        assert_eq!(
            check(&[1, 2, 3], &entries, b"body"),
            Err(Error::BadKeyIndex)
        );
        let other = sign_entries(&[1, 2, 3], &[0, 1], b"other v1", b"body");
        assert_eq!(check(&[1, 2, 3], &other, b"body"), Err(Error::BadSignature));
        let ok = sign_entries(&[1, 2, 3], &[0, 1], b"test v1", b"body");
        assert_eq!(check(&[1, 2, 3], &ok, b"bodz"), Err(Error::BadSignature));
    }

    #[test]
    fn rejects_small_scratch() {
        let keys = public_keys(&[1, 2]);
        let set = KeySet::new(&keys).unwrap();
        let entries = sign_entries(&[1, 2], &[0, 1], b"test v1", b"body");
        let mut scratch = [0u8; 8];
        assert_eq!(
            check_signatures(&entries[1..], &set, b"test v1", b"body", &mut scratch),
            Err(Error::ScratchTooSmall)
        );
    }
}
