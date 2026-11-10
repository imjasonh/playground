//! SHA-2 digests in software.
//!
//! The SHA accelerator is never used on the verification path, so every
//! digest a security decision depends on comes from this module. `sha2` is a
//! provisional backend until phase 0 picks the implementation phase 7 proves.

use sha2::Digest;

/// An incremental SHA-256 computation, for data read from flash in pieces.
#[derive(Clone, Default)]
pub struct Sha256(sha2::Sha256);

impl Sha256 {
    /// Starts a new digest.
    pub fn new() -> Self {
        Sha256(sha2::Sha256::new())
    }

    /// Adds `data` to the digest.
    pub fn update(&mut self, data: &[u8]) {
        self.0.update(data);
    }

    /// Finishes the digest.
    pub fn finish(self) -> [u8; 32] {
        self.0.finalize().into()
    }
}

/// The SHA-256 digest of `data`.
pub fn sha256(data: &[u8]) -> [u8; 32] {
    sha2::Sha256::digest(data).into()
}

/// The SHA-256 digest of `parts`, concatenated.
pub fn sha256_parts(parts: &[&[u8]]) -> [u8; 32] {
    let mut h = sha2::Sha256::new();
    for part in parts {
        h.update(part);
    }
    h.finalize().into()
}

/// The SHA-384 digest of `data`.
pub fn sha384(data: &[u8]) -> [u8; 48] {
    sha2::Sha384::digest(data).into()
}

#[cfg(test)]
#[allow(clippy::indexing_slicing, clippy::arithmetic_side_effects)]
mod tests {
    use super::*;

    fn hex(bytes: &[u8]) -> String {
        bytes.iter().map(|b| format!("{b:02x}")).collect()
    }

    #[test]
    fn nist_vectors() {
        assert_eq!(
            hex(&sha256(b"abc")),
            "ba7816bf8f01cfea414140de5dae2223b00361a396177a9cb410ff61f20015ad"
        );
        assert_eq!(
            hex(&sha384(b"abc")),
            "cb00753f45a35e8bb5a03d699ac65007272c32ab0eded1631a8b605a43ff5bed8086072ba1e7cc2358baeca134c825a7"
        );
    }

    #[test]
    fn incremental_matches_one_shot() {
        let mut h = Sha256::new();
        h.update(b"ab");
        h.update(b"c");
        assert_eq!(h.finish(), sha256(b"abc"));
        assert_eq!(sha256_parts(&[b"a", b"", b"bc"]), sha256(b"abc"));
    }
}
