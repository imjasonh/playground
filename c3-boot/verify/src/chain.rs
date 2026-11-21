//! The key-set chain from the genesis keys to the set that signs the
//! trust-root blob.

use crate::error::Error;
use crate::keys::KeySet;
use crate::keys::check_signatures;
use crate::keys::read_key_set;
use crate::keys::read_signatures;
use crate::reader::Reader;

/// The most links a chain can have.
pub const MAX_LINKS: usize = 16;
/// The highest level a link can have.
pub const MAX_LEVEL: u8 = 16;
/// The domain-separation string for link signatures.
pub const LINK_DOMAIN: &[u8] = b"c3-boot chain link v1";

/// One link: a level and the key set it authorizes.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub struct Link<'a> {
    /// The link's level, 1 through [`MAX_LEVEL`].
    pub level: u8,
    /// The key set this link authorizes.
    pub keys: KeySet<'a>,
    body: &'a [u8],
    signatures: &'a [u8],
}

/// A parsed chain whose structure has been checked but whose signatures have
/// not.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub struct Chain<'a> {
    links: [Option<Link<'a>>; MAX_LINKS],
}

impl<'a> Chain<'a> {
    /// The chain's links, in order.
    pub fn links(&self) -> impl Iterator<Item = &Link<'a>> {
        self.links.iter().map_while(Option::as_ref)
    }
}

/// Parses a chain and checks its structure: the header, link count, levels
/// strictly increasing from 1 through 16, distinct keys in each set, and the
/// signature count of each link.
pub fn parse(bytes: &[u8]) -> Result<Chain<'_>, Error> {
    let mut r = Reader::new(bytes);
    r.magic(b"C3KC")?;
    r.version_1()?;
    let count = usize::from(r.u8()?);
    if count > MAX_LINKS {
        return Err(Error::OutOfRange);
    }
    r.reserved(1)?;

    let mut links = [None; MAX_LINKS];
    let mut previous_level = 0u8;
    for slot in links.iter_mut().take(count) {
        let start = r.position();
        let level = r.u8()?;
        if level <= previous_level || level > MAX_LEVEL {
            return Err(Error::BadLevel);
        }
        let keys = read_key_set(&mut r)?;
        let body = r.since(start)?;
        let signatures = read_signatures(&mut r)?;
        *slot = Some(Link {
            level,
            keys,
            body,
            signatures,
        });
        previous_level = level;
    }
    r.finish()?;
    Ok(Chain { links })
}

/// The key set and level at the end of a verified chain.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub struct Tip<'a> {
    /// The key set that must sign the trust-root blob.
    pub keys: KeySet<'a>,
    /// The last link's level, or 0 for an empty chain.
    pub level: u8,
}

/// Checks every link's signatures against the previous key set, starting
/// from `genesis`, and returns the chain's tip.
///
/// `scratch` must hold the longest link body plus the domain string and a
/// zero byte; 160 bytes is enough.
pub fn verify<'a>(
    chain: &Chain<'a>,
    genesis: KeySet<'a>,
    scratch: &mut [u8],
) -> Result<Tip<'a>, Error> {
    let mut tip = Tip {
        keys: genesis,
        level: 0,
    };
    for link in chain.links() {
        check_signatures(link.signatures, &tip.keys, LINK_DOMAIN, link.body, scratch)?;
        tip = Tip {
            keys: link.keys,
            level: link.level,
        };
    }
    Ok(tip)
}

#[cfg(test)]
#[allow(clippy::arithmetic_side_effects, clippy::indexing_slicing)]
pub(crate) mod tests {
    use super::*;
    use crate::keys::tests::public_keys;
    use crate::keys::tests::sign_entries;

    /// Encodes a link at `level` naming `new_seeds`, signed by `indexes` of
    /// `signer_seeds`.
    pub(crate) fn link(
        level: u8,
        new_seeds: &[u8],
        signer_seeds: &[u8],
        indexes: &[u8],
    ) -> Vec<u8> {
        let mut body = vec![level, new_seeds.len() as u8];
        body.extend_from_slice(&public_keys(new_seeds));
        let mut out = body.clone();
        out.extend_from_slice(&sign_entries(signer_seeds, indexes, LINK_DOMAIN, &body));
        out
    }

    pub(crate) fn chain(links: &[Vec<u8>]) -> Vec<u8> {
        let mut out = b"C3KC".to_vec();
        out.extend_from_slice(&1u16.to_le_bytes());
        out.push(links.len() as u8);
        out.push(0);
        for l in links {
            out.extend_from_slice(l);
        }
        out
    }

    const GENESIS: [u8; 4] = [1, 2, 3, 4];

    fn run(bytes: &[u8]) -> Result<(usize, u8), Error> {
        let genesis_keys = public_keys(&GENESIS);
        let genesis = KeySet::new(&genesis_keys)?;
        let parsed = parse(bytes)?;
        let mut scratch = [0u8; 160];
        let tip = verify(&parsed, genesis, &mut scratch)?;
        Ok((tip.keys.len(), tip.level))
    }

    #[test]
    fn empty_chain_ends_at_genesis() {
        assert_eq!(run(&chain(&[])), Ok((4, 0)));
    }

    #[test]
    fn accepts_two_rotations() {
        let l1 = link(2, &[10, 11, 12], &GENESIS, &[0, 3]);
        let l2 = link(5, &[20, 21], &[10, 11, 12], &[1, 2]);
        assert_eq!(run(&chain(&[l1, l2])), Ok((2, 5)));
    }

    #[test]
    fn rejects_link_signed_by_its_own_set() {
        let l1 = link(2, &[10, 11, 12], &[10, 11, 12], &[0, 1]);
        assert_eq!(run(&chain(&[l1])), Err(Error::BadSignature));
    }

    #[test]
    fn rejects_non_increasing_levels() {
        let l1 = link(3, &[10, 11], &GENESIS, &[0, 1]);
        let l2 = link(3, &[20, 21], &[10, 11], &[0, 1]);
        assert_eq!(run(&chain(&[l1, l2])), Err(Error::BadLevel));
        let l0 = link(0, &[10, 11], &GENESIS, &[0, 1]);
        assert_eq!(run(&chain(&[l0])), Err(Error::BadLevel));
        let l17 = link(17, &[10, 11], &GENESIS, &[0, 1]);
        assert_eq!(run(&chain(&[l17])), Err(Error::BadLevel));
    }

    #[test]
    fn rejects_trailing_bytes_and_bad_count() {
        let mut bytes = chain(&[link(1, &[10, 11], &GENESIS, &[0, 1])]);
        bytes.push(0);
        assert_eq!(run(&bytes), Err(Error::TrailingBytes));
        let mut bytes = chain(&[]);
        bytes[6] = 17;
        assert_eq!(run(&bytes), Err(Error::OutOfRange));
    }

    #[test]
    fn rejects_tampered_key() {
        let mut l1 = link(2, &[10, 11], &GENESIS, &[0, 1]);
        l1[2] ^= 1;
        assert_eq!(run(&chain(&[l1])), Err(Error::BadSignature));
    }
}
