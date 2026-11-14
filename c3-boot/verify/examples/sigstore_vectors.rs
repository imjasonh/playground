//! Builds inputs for the parts of the Sigstore check, valid and mutated,
//! runs each through `c3-verify`, and prints one line per input with the
//! result. `c3-boot-proofs`'s `sigstore-check` reads the same lines, runs
//! the Lean specification, and must print identical lines.
//!
//! The lines are:
//!
//! - `b64e HEX | HEX`, the bytes and their `base64::encode_to` text
//! - `b64d HEX | ok HEX` or `| err`, text and `base64::decode_into`'s bytes
//! - `utc HEX | ok N` or `| err`, from `time::utc_time`
//! - `gen HEX | ok N` or `| err`, from `time::generalized_time`
//! - `bundle HEX | ok HEX HEX N HEX HEX HEX` or `| err`, from `bundle::parse`
//! - `rekor HEX HEX HEX | HEX`, from `rekor::entry_leaf_hash`
//!
//! where an empty `HEX` is `-`.

// A host-side test generator, not device code: its arithmetic and indexing
// work on values it chose itself.
#![allow(clippy::arithmetic_side_effects, clippy::indexing_slicing)]

use std::io::BufWriter;
use std::io::Write;

use base64::Engine;
use base64::engine::general_purpose::STANDARD;
use c3_verify::base64::Sink;

const CASES: usize = 4_000;

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

    /// `v` with one byte changed, inserted, or removed, or `v` itself.
    fn mutate(&mut self, v: &[u8], alphabet: &[u8]) -> Vec<u8> {
        let mut v = v.to_vec();
        let pick = |r: &mut Rng| alphabet[r.below(alphabet.len() as u64) as usize];
        match self.below(4) {
            0 if !v.is_empty() => {
                let i = self.below(v.len() as u64) as usize;
                v[i] = pick(self);
            }
            1 => {
                let i = self.below(v.len() as u64 + 1) as usize;
                let c = pick(self);
                v.insert(i, c);
            }
            2 if !v.is_empty() => {
                let i = self.below(v.len() as u64) as usize;
                v.remove(i);
            }
            _ => {}
        }
        v
    }
}

fn hex(b: &[u8]) -> String {
    if b.is_empty() {
        "-".to_string()
    } else {
        b.iter().map(|x| format!("{x:02x}")).collect()
    }
}

struct Text(Vec<u8>);

impl Sink for Text {
    fn write(&mut self, bytes: &[u8]) {
        self.0.extend_from_slice(bytes);
    }
}

/// The certificate, signature, and digest of every conformance bundle.
fn conformance() -> Vec<[Vec<u8>; 3]> {
    let dir = concat!(env!("CARGO_MANIFEST_DIR"), "/../testdata/conformance");
    let mut out = Vec::new();
    let mut entries: Vec<_> = std::fs::read_dir(dir).unwrap().map(|e| e.unwrap().path()).collect();
    entries.sort();
    for path in entries {
        let Ok(text) = std::fs::read_to_string(path.join("bundle.sigstore.json")) else {
            continue;
        };
        let bundle: serde_json::Value = serde_json::from_str(&text).unwrap();
        let b64 = |v: &serde_json::Value| v.as_str().map(|s| STANDARD.decode(s).unwrap());
        let cert = b64(&bundle["verificationMaterial"]["certificate"]["rawBytes"]);
        let sig = b64(&bundle["messageSignature"]["signature"]);
        let digest = b64(&bundle["messageSignature"]["messageDigest"]["digest"]);
        if let (Some(c), Some(s), Some(d)) = (cert, sig, digest) {
            out.push([c, s, d]);
        }
    }
    out
}

fn container(fields: &[&[u8]; 6]) -> Vec<u8> {
    let mut out = b"C3BN".to_vec();
    out.extend_from_slice(&1u16.to_le_bytes());
    for f in fields {
        out.extend_from_slice(&(f.len() as u32).to_le_bytes());
        out.extend_from_slice(f);
    }
    out
}

fn main() {
    let mut out = BufWriter::new(std::io::stdout().lock());
    let mut rng = Rng(0x5167_5354_4f52_4521);
    let alphabet = b"ABCDEFGHIJKLMNOPQRSTUVWXYZabcdefghijklmnopqrstuvwxyz0123456789+/=-_ \n";
    let real = conformance();

    for _ in 0..CASES {
        let len = rng.below(40) as usize;
        let data = rng.bytes(len);
        let mut text = Text(Vec::new());
        c3_verify::base64::encode_to(&data, &mut text);
        writeln!(out, "b64e {} | {}", hex(&data), hex(&text.0)).unwrap();
        let input = if rng.below(3) == 0 { text.0 } else { rng.mutate(&text.0, alphabet) };
        let mut buf = [0u8; 64];
        let r = match c3_verify::base64::decode_into(&input, &mut buf) {
            Ok(n) => format!("ok {}", hex(&buf[..n])),
            Err(_) => "err".to_string(),
        };
        writeln!(out, "b64d {} | {r}", hex(&input)).unwrap();
    }

    let digits = b"0123456789Z.+-";
    for i in 0..CASES {
        let year = 1940 + rng.below(140);
        let month = rng.below(14);
        let day = rng.below(33);
        let base = format!(
            "{:04}{:02}{:02}{:02}{:02}{:02}",
            year,
            month,
            day,
            rng.below(25),
            rng.below(61),
            rng.below(61)
        );
        let frac = match rng.below(4) {
            0 => format!(".{}", rng.below(1000)),
            1 => ".".to_string(),
            _ => String::new(),
        };
        let gen_text = format!("{base}{frac}Z").into_bytes();
        let gen_in = if i % 3 == 0 { rng.mutate(&gen_text, digits) } else { gen_text };
        let r = match c3_verify::time::generalized_time(&gen_in) {
            Ok(t) => format!("ok {t}"),
            Err(_) => "err".to_string(),
        };
        writeln!(out, "gen {} | {r}", hex(&gen_in)).unwrap();
        let utc_text = format!("{}Z", &base[2..]).into_bytes();
        let utc_in = if i % 3 == 0 { rng.mutate(&utc_text, digits) } else { utc_text };
        let r = match c3_verify::time::utc_time(&utc_in) {
            Ok(t) => format!("ok {t}"),
            Err(_) => "err".to_string(),
        };
        writeln!(out, "utc {} | {r}", hex(&utc_in)).unwrap();
    }

    for i in 0..CASES {
        let [cert, sig, digest] = &real[i % real.len()];
        let n = rng.below(4) as usize;
        let extra = usize::from(rng.below(8) == 0);
        let proof = rng.bytes(32 * n + extra);
        let index = rng.next().to_le_bytes();
        let mut fields: [&[u8]; 6] = [cert, sig, &index, &proof, b"checkpoint\n", b"tsr"];
        let empty: &[u8] = &[];
        if rng.below(10) == 0 {
            fields[rng.below(6) as usize] = empty;
        }
        let mut bytes = container(&fields);
        if rng.below(3) == 0 {
            let all: Vec<u8> = (0..=255).collect();
            bytes = rng.mutate(&bytes, &all);
        }
        let r = match c3_verify::bundle::parse(&bytes) {
            Ok(b) => format!(
                "ok {} {} {} {} {} {}",
                hex(b.leaf_certificate),
                hex(b.image_signature),
                b.log_index,
                hex(b.inclusion_proof),
                hex(b.checkpoint),
                hex(b.timestamp)
            ),
            Err(_) => "err".to_string(),
        };
        writeln!(out, "bundle {} | {r}", hex(&bytes)).unwrap();
        let d: Vec<u8> = if rng.below(2) == 0 { digest.clone() } else { rng.bytes(32) };
        let d: [u8; 32] = d.try_into().unwrap();
        let s = &sig[..sig.len() - rng.below(3) as usize];
        let h = c3_verify::rekor::entry_leaf_hash(&d, s, cert);
        writeln!(out, "rekor {} {} {} | {}", hex(&d), hex(s), hex(cert), hex(&h)).unwrap();
    }
}
