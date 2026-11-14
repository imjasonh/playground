//! Signs and hashes random inputs, mutates some of the results, checks each
//! with `c3-crypto`, and prints one line per input with the result.
//! `c3-boot-proofs`'s `sigstore-check` reads the same lines, checks them
//! with the Lean specifications of SHA-384, ECDSA, and Ed25519, and must
//! print identical lines.
//!
//! The lines are:
//!
//! - `sha384 HEX | HEX`
//! - `p256 KEY DIGEST R S | 1` or `| 0`, from `p256_verify_prehash`
//! - `p384 KEY DIGEST R S | 1` or `| 0`, from `p384_verify_prehash`
//! - `ed25519 KEY MESSAGE SIGNATURE | 1` or `| 0`, from `ed25519_verify`
//!
//! where an empty `HEX` is `-`.

// A host-side test generator, not device code: its arithmetic and indexing
// work on values it chose itself.
#![allow(clippy::arithmetic_side_effects, clippy::indexing_slicing)]

use std::io::BufWriter;
use std::io::Write;

use ed25519_dalek::Signer;
use p256::ecdsa::signature::hazmat::PrehashSigner;

const CASES: usize = 120;

struct Rng(u64);

impl Rng {
    fn next(&mut self) -> u64 {
        self.0 ^= self.0 << 13;
        self.0 ^= self.0 >> 7;
        self.0 ^= self.0 << 17;
        self.0
    }

    fn below(&mut self, n: u64) -> u64 {
        self.next() % n
    }

    fn bytes(&mut self, n: usize) -> Vec<u8> {
        (0..n).map(|_| self.next() as u8).collect()
    }

    /// Flips a random bit of `v`.
    fn flip(&mut self, v: &mut [u8]) {
        if !v.is_empty() {
            let i = self.below(v.len() as u64) as usize;
            v[i] ^= 1 << self.below(8);
        }
    }
}

fn hex(b: &[u8]) -> String {
    if b.is_empty() {
        "-".to_string()
    } else {
        b.iter().map(|x| format!("{x:02x}")).collect()
    }
}

/// A digest for a P-256 or P-384 signature: SHA-256, SHA-384, or an odd
/// length.
fn digest(rng: &mut Rng) -> Vec<u8> {
    let len = rng.below(40) as usize;
    let msg = rng.bytes(len);
    match rng.below(4) {
        0 => c3_crypto::sha256(&msg).to_vec(),
        1 => c3_crypto::sha384(&msg).to_vec(),
        _ => {
            let n = 1 + rng.below(70) as usize;
            rng.bytes(n)
        }
    }
}

/// Changes one of the key, digest, `r`, or `s`, or sets `r` or `s` to an
/// edge value, or leaves all four alone.
fn mutate(rng: &mut Rng, parts: &mut [Vec<u8>; 4], order: &[u8]) {
    match rng.below(8) {
        0 => rng.flip(&mut parts[0]),
        1 => rng.flip(&mut parts[1]),
        2 => rng.flip(&mut parts[2]),
        3 => rng.flip(&mut parts[3]),
        4 => {
            let i = 2 + rng.below(2) as usize;
            parts[i] = match rng.below(3) {
                0 => vec![0; order.len()],
                1 => order.to_vec(),
                _ => {
                    let mut v = order.to_vec();
                    let last = v.len() - 1;
                    v[last] -= 1;
                    v
                }
            };
        }
        _ => {}
    }
}

fn main() {
    let mut out = BufWriter::new(std::io::stdout().lock());
    let mut rng = Rng(0x4352_5950_544f_2131);
    let p256_order: [u8; 32] = [
        0xff, 0xff, 0xff, 0xff, 0x00, 0x00, 0x00, 0x00, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff,
        0xff, 0xbc, 0xe6, 0xfa, 0xad, 0xa7, 0x17, 0x9e, 0x84, 0xf3, 0xb9, 0xca, 0xc2, 0xfc, 0x63,
        0x25, 0x51,
    ];
    let p384_order: [u8; 48] = [
        0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff,
        0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xc7, 0x63, 0x4d, 0x81, 0xf4, 0x37,
        0x2d, 0xdf, 0x58, 0x1a, 0x0d, 0xb2, 0x48, 0xb0, 0xa7, 0x7a, 0xec, 0xec, 0x19, 0x6a, 0xcc,
        0xc5, 0x29, 0x73,
    ];

    for _ in 0..CASES {
        let n = rng.below(300) as usize;
        let msg = rng.bytes(n);
        writeln!(
            out,
            "sha384 {} | {}",
            hex(&msg),
            hex(&c3_crypto::sha384(&msg))
        )
        .unwrap();
    }

    let mut done = 0;
    while done < CASES {
        let Ok(k) = p256::ecdsa::SigningKey::from_slice(&rng.bytes(32)) else {
            continue;
        };
        let d = digest(&mut rng);
        let Ok(sig): Result<p256::ecdsa::Signature, _> = k.sign_prehash(&d) else {
            continue;
        };
        let (r, s) = sig.split_bytes();
        let pt = k.verifying_key().to_sec1_point(false).as_bytes().to_vec();
        let mut parts = [pt, d, r.to_vec(), s.to_vec()];
        mutate(&mut rng, &mut parts, &p256_order);
        let [pt, d, r, s] = &parts;
        let ok = c3_crypto::p256_verify_prehash(
            &pt[..].try_into().unwrap(),
            d,
            &r[..].try_into().unwrap(),
            &s[..].try_into().unwrap(),
        );
        writeln!(
            out,
            "p256 {} {} {} {} | {}",
            hex(pt),
            hex(d),
            hex(r),
            hex(s),
            u8::from(ok)
        )
        .unwrap();
        done += 1;
    }

    let mut done = 0;
    while done < CASES {
        let Ok(k) = p384::ecdsa::SigningKey::from_slice(&rng.bytes(48)) else {
            continue;
        };
        let d = digest(&mut rng);
        let Ok(sig): Result<p384::ecdsa::Signature, _> = k.sign_prehash(&d) else {
            continue;
        };
        let (r, s) = sig.split_bytes();
        let pt = k.verifying_key().to_sec1_point(false).as_bytes().to_vec();
        let mut parts = [pt, d, r.to_vec(), s.to_vec()];
        mutate(&mut rng, &mut parts, &p384_order);
        let [pt, d, r, s] = &parts;
        let ok = c3_crypto::p384_verify_prehash(
            &pt[..].try_into().unwrap(),
            d,
            &r[..].try_into().unwrap(),
            &s[..].try_into().unwrap(),
        );
        writeln!(
            out,
            "p384 {} {} {} {} | {}",
            hex(pt),
            hex(d),
            hex(r),
            hex(s),
            u8::from(ok)
        )
        .unwrap();
        done += 1;
    }

    let group_order: [u8; 32] = [
        0xed, 0xd3, 0xf5, 0x5c, 0x1a, 0x63, 0x12, 0x58, 0xd6, 0x9c, 0xf7, 0xa2, 0xde, 0xf9, 0xde,
        0x14, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00,
        0x00, 0x10,
    ];
    let mut identity = [0u8; 32];
    identity[0] = 1;
    for _ in 0..CASES {
        let seed: [u8; 32] = rng.bytes(32).try_into().unwrap();
        let k = ed25519_dalek::SigningKey::from_bytes(&seed);
        let n = rng.below(100) as usize;
        let mut msg = rng.bytes(n);
        let mut sig = k.sign(&msg).to_bytes().to_vec();
        let mut key = k.verifying_key().to_bytes().to_vec();
        match rng.below(10) {
            0 => rng.flip(&mut key),
            1 => rng.flip(&mut msg),
            2 => rng.flip(&mut sig),
            3 => {
                // S + L: the same scalar, not reduced.
                let mut carry = 0u16;
                for i in 0..32 {
                    let v = u16::from(sig[32 + i]) + u16::from(group_order[i]) + carry;
                    sig[32 + i] = v as u8;
                    carry = v >> 8;
                }
            }
            4 => sig[..32].copy_from_slice(&identity),
            5 => key.copy_from_slice(&identity),
            6 => key[31] |= 0x80,
            _ => {}
        }
        let ok = c3_crypto::ed25519_verify(
            &key[..].try_into().unwrap(),
            &msg,
            &sig[..].try_into().unwrap(),
        );
        writeln!(
            out,
            "ed25519 {} {} {} | {}",
            hex(&key),
            hex(&msg),
            hex(&sig),
            u8::from(ok)
        )
        .unwrap();
    }
}
