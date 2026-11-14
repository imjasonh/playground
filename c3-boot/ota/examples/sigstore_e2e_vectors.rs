//! Runs the Sigstore conformance cases, and mutations of them, through the
//! parts of `c3_verify::sigstore::verify`, and prints one line per input
//! with the result. `c3-boot-proofs`'s `sigstore-check` reads the same
//! lines, runs the Lean specification, and must print identical lines.
//!
//! Each case's trusted root becomes a trust-root blob signed with the
//! development genesis keys, with the conformance beacon's identity as the
//! policy, as `tests/conformance.rs` builds it. The lines are:
//!
//! - `checkpoint TEXT ROOT | ok ORIGIN SIZE HASH` or `| err`, from
//!   `checkpoint::verify`
//!
//! where `TEXT`, `ORIGIN`, and `HASH` are hex, and `ROOT` lists the parsed
//! root's keys and policy: four `/`-separated sections, each a
//! `;`-separated list of `.`-separated fields. The Fulcio, log, and TSA
//! sections hold `NAME.KEY.NOT_BEFORE.NOT_AFTER` entries, and the policy
//! section holds one entry of five fields.

// A host-side test generator, not device code: its arithmetic and indexing
// work on values it chose itself.
#![allow(clippy::arithmetic_side_effects, clippy::indexing_slicing)]

use std::fs;
use std::io::BufWriter;
use std::io::Write;
use std::path::Path;

use c3_ota::blob::TrustRootSpec;
use c3_ota::blob::signed_blob;
use c3_ota::container::from_bundle_json;
use c3_ota::keys::read_signing_key;
use c3_verify::trustroot::TrustRoot;

const DATA: &str = concat!(env!("CARGO_MANIFEST_DIR"), "/../testdata");
const MUTATIONS: usize = 60;

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
}

fn hex(b: &[u8]) -> String {
    if b.is_empty() {
        "-".to_string()
    } else {
        b.iter().map(|x| format!("{x:02x}")).collect()
    }
}

fn policy() -> [String; 5] {
    [
        "https://token.actions.githubusercontent.com".into(),
        "https://github.com/sigstore-conformance/extremely-dangerous-public-oidc-beacon/.github/workflows/extremely-dangerous-oidc-beacon.yml@refs/heads/main".into(),
        "632596897".into(),
        "131804563".into(),
        "workflow_dispatch".into(),
    ]
}

fn root_token(root: &TrustRoot<'_>) -> String {
    let entry = |name: &[u8], key: &[u8], w: c3_verify::trustroot::Window| {
        format!("{}.{}.{}.{}", hex(name), hex(key), w.not_before, w.not_after)
    };
    let fulcio: Vec<String> = root
        .fulcio()
        .map(|f| entry(f.subject, f.public_key, f.window))
        .collect();
    let logs: Vec<String> = root
        .logs()
        .map(|l| entry(l.origin, l.public_key, l.window))
        .collect();
    let tsas: Vec<String> = root
        .tsas()
        .map(|t| entry(t.signer_id, t.public_key, t.window))
        .collect();
    let p = &root.policy;
    let policy = [p.issuer, p.build_signer_uri, p.repository_id, p.owner_id, p.trigger]
        .iter()
        .map(|s| hex(s))
        .collect::<Vec<_>>()
        .join(".");
    format!("{}/{}/{}/{}", fulcio.join(";"), logs.join(";"), tsas.join(";"), policy)
}

/// A mutation of a checkpoint note: a changed, inserted, or removed byte,
/// a duplicated or dropped line, or a truncation.
fn mutate(rng: &mut Rng, text: &[u8]) -> Vec<u8> {
    let mut v = text.to_vec();
    let lines: Vec<&[u8]> = text.split_inclusive(|&b| b == b'\n').collect();
    match rng.below(6) {
        0 => {
            let i = rng.below(v.len() as u64) as usize;
            v[i] = [b'\n', b' ', b'0', b'A', b'=', 0xE2][rng.below(6) as usize];
        }
        1 => {
            let i = rng.below(v.len() as u64) as usize;
            v.remove(i);
        }
        2 => {
            let i = rng.below(lines.len() as u64) as usize;
            v = lines.iter().take(i + 1).chain(lines.iter().skip(i)).flat_map(|l| l.iter().copied()).collect();
        }
        3 => {
            let i = rng.below(lines.len() as u64) as usize;
            v = lines
                .iter()
                .enumerate()
                .filter(|(j, _)| *j != i)
                .flat_map(|(_, l)| l.iter().copied())
                .collect();
        }
        4 => v.truncate(rng.below(v.len() as u64) as usize),
        _ => {
            let i = rng.below(v.len() as u64) as usize;
            v[i] ^= 1 << rng.below(8);
        }
    }
    v
}

fn main() {
    let mut out = BufWriter::new(std::io::stdout().lock());
    let mut rng = Rng(0x4532_4556_4543_5452);
    let k1 = read_signing_key(&format!("{DATA}/keys/genesis-dev-1.seed")).unwrap();
    let k2 = read_signing_key(&format!("{DATA}/keys/genesis-dev-2.seed")).unwrap();
    let base = Path::new(DATA).join("conformance");
    let mut dirs: Vec<_> = fs::read_dir(&base).unwrap().map(|e| e.unwrap().path()).collect();
    dirs.sort();
    for dir in dirs.iter().filter(|d| d.is_dir()) {
        let bundle_json = fs::read_to_string(dir.join("bundle.sigstore.json")).unwrap();
        let root_json = fs::read_to_string(dir.join("trusted_root.json")).unwrap();
        let Ok(container) = from_bundle_json(&bundle_json, None) else {
            continue;
        };
        let Ok(spec) = TrustRootSpec::from_trusted_root(&root_json, 0, policy()) else {
            continue;
        };
        let blob = signed_blob(&spec, &[(0, &k1), (1, &k2)]).unwrap();
        let root = c3_verify::trustroot::parse(&blob).unwrap();
        let bundle = c3_verify::bundle::parse(&container).unwrap();
        let token = root_token(&root);
        let mut texts = vec![bundle.checkpoint.to_vec()];
        for _ in 0..MUTATIONS {
            let t = mutate(&mut rng, bundle.checkpoint);
            texts.push(t);
        }
        for text in texts {
            let r = match c3_verify::checkpoint::verify(&text, &root) {
                Ok(c) => format!("ok {} {} {}", hex(c.log.origin), c.size, hex(&c.root)),
                Err(_) => "err".to_string(),
            };
            writeln!(out, "checkpoint {} {token} | {r}", hex(&text)).unwrap();
        }
    }
}
