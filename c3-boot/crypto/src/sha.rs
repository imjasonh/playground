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

    /// FIPS 180-4's examples, plus the empty message and a million `a`s, for
    /// the compact compression functions the build selects.
    #[test]
    fn fips_180_4_examples() {
        let two = b"abcdbcdecdefdefgefghfghighijhijkijkljklmklmnlmnomnopnopq";
        let long: &[u8] = b"abcdefghbcdefghicdefghijdefghijkefghijklfghijklmghijklmnhijklmnoijklmnopjklmnopqklmnopqrlmnopqrsmnopqrstnopqrstu";
        let million = [b'a'; 1_000_000];
        let sha512 = |m: &[u8]| hex(&sha2::Sha512::digest(m));
        assert_eq!(
            hex(&sha256(b"")),
            "e3b0c44298fc1c149afbf4c8996fb92427ae41e4649b934ca495991b7852b855"
        );
        assert_eq!(
            hex(&sha256(two)),
            "248d6a61d20638b8e5c026930c3e6039a33ce45964ff2167f6ecedd419db06c1"
        );
        assert_eq!(
            hex(&sha256(&million)),
            "cdc76e5c9914fb9281a1c7e284d73e67f1809a48a497200e046d39ccc7112cd0"
        );
        assert_eq!(
            hex(&sha384(long)),
            "09330c33f71147e83d192fc782cd1b4753111b173b3b05d22fa08086e3b0f712fcc7c71a557e2db966c3e9fa91746039"
        );
        assert_eq!(
            sha512(b""),
            "cf83e1357eefb8bdf1542850d66d8007d620e4050b5715dc83f4a921d36ce9ce47d0d13c5d85f2b0ff8318d2877eec2f63b931bd47417a81a538327af927da3e"
        );
        assert_eq!(
            sha512(b"abc"),
            "ddaf35a193617abacc417349ae20413112e6fa4e89a97ea20a9eeee64b55d39a2192992a274fc1a836ba3c23a3feebbd454d4423643ce80e2a9ac94fa54ca49f"
        );
        assert_eq!(
            sha512(long),
            "8e959b75dae313da8cf4f72814fc143f8f7779c6eb9f7fa17299aeadb6889018501d289e4900f7e4331b99dec4b5433ac7d329eeb6dd26545e96e55b874be909"
        );
        assert_eq!(
            sha512(&million),
            "e718483d0ce769644e2e42c7bc15b4638e1f98b13b2044285632a803afa973ebde0ff244877ea60a4cb0432ce577c31beb009c5c2c49aa2e4eadb217ad8cc09b"
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
