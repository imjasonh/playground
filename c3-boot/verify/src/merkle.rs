//! RFC 6962 Merkle tree hashing and RFC 9162 inclusion proofs.

use crate::error::Error;

/// The most hashes an inclusion proof can have, for trees of up to 2^64
/// leaves.
pub const MAX_PROOF_HASHES: usize = 64;

/// The RFC 6962 hash of an interior node.
fn node_hash(left: &[u8; 32], right: &[u8; 32]) -> [u8; 32] {
    c3_crypto::sha256_parts(&[&[0x01], left, right])
}

/// Computes the root that an inclusion proof implies, following RFC 9162
/// section 2.1.3.2.
///
/// `proof` is the concatenation of the audit path's 32-byte hashes, from the
/// leaf toward the root. Fails if `index` isn't below `size` or if the proof
/// has the wrong number of hashes for that position.
pub fn root_from_inclusion(
    index: u64,
    size: u64,
    leaf_hash: &[u8; 32],
    proof: &[u8],
) -> Result<[u8; 32], Error> {
    let (hashes, rest) = proof.as_chunks::<32>();
    if !rest.is_empty() || hashes.len() > MAX_PROOF_HASHES || index >= size {
        return Err(Error::BadProof);
    }
    let mut f = index;
    let mut s = size.checked_sub(1).ok_or(Error::BadProof)?;
    let mut r = *leaf_hash;
    for p in hashes {
        if s == 0 {
            return Err(Error::BadProof);
        }
        if f & 1 == 1 || f == s {
            r = node_hash(p, &r);
            while f & 1 == 0 && f != 0 {
                f >>= 1;
                s >>= 1;
            }
        } else {
            r = node_hash(&r, p);
        }
        f >>= 1;
        s >>= 1;
    }
    if s != 0 {
        return Err(Error::BadProof);
    }
    Ok(r)
}

#[cfg(test)]
#[allow(clippy::arithmetic_side_effects, clippy::indexing_slicing)]
mod tests {
    use super::*;

    fn leaf(i: u8) -> [u8; 32] {
        c3_crypto::sha256_parts(&[&[0x00], &[i]])
    }

    /// The RFC 6962 root of leaves `lo..hi`.
    fn root(lo: usize, hi: usize) -> [u8; 32] {
        let n = hi - lo;
        if n == 1 {
            return leaf(lo as u8);
        }
        let mut k = 1;
        while k * 2 < n {
            k *= 2;
        }
        node_hash(&root(lo, lo + k), &root(lo + k, hi))
    }

    /// The RFC 6962 audit path for leaf `m` in leaves `lo..hi`.
    fn path(m: usize, lo: usize, hi: usize) -> Vec<u8> {
        let n = hi - lo;
        if n == 1 {
            return Vec::new();
        }
        let mut k = 1;
        while k * 2 < n {
            k *= 2;
        }
        let mut out;
        if m < k {
            out = path(m, lo, lo + k);
            out.extend_from_slice(&root(lo + k, hi));
        } else {
            out = path(m - k, lo + k, hi);
            out.extend_from_slice(&root(lo, lo + k));
        }
        out
    }

    #[test]
    fn every_leaf_of_small_trees() {
        for size in 1..=17usize {
            for m in 0..size {
                let proof = path(m, 0, size);
                let got = root_from_inclusion(m as u64, size as u64, &leaf(m as u8), &proof);
                assert_eq!(got, Ok(root(0, size)), "size {size} leaf {m}");
            }
        }
    }

    #[test]
    fn rejects_wrong_shapes() {
        let proof = path(3, 0, 8);
        assert_eq!(
            root_from_inclusion(8, 8, &leaf(3), &proof),
            Err(Error::BadProof)
        );
        let mut long = proof.clone();
        long.extend_from_slice(&[0u8; 32]);
        assert_eq!(
            root_from_inclusion(3, 8, &leaf(3), &long),
            Err(Error::BadProof)
        );
        assert_eq!(
            root_from_inclusion(3, 8, &leaf(3), &proof[..64]),
            Err(Error::BadProof)
        );
        assert_eq!(
            root_from_inclusion(3, 8, &leaf(3), &proof[..65]),
            Err(Error::BadProof)
        );
        assert_ne!(root_from_inclusion(3, 8, &leaf(4), &proof), Ok(root(0, 8)));
        assert_ne!(root_from_inclusion(2, 8, &leaf(3), &proof), Ok(root(0, 8)));
    }
}
