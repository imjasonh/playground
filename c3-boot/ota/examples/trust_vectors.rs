//! Builds random key-set chains and trust-root blobs with real Ed25519
//! signatures, checks each with `c3-verify`, and prints one line per case
//! with the verdict. `c3-boot-proofs`'s `trust-check` reads the same lines,
//! evaluates the Lean specification, and must print identical lines.
//!
//! A line is `trust links=L;L blob=LEVEL/SIGS sv=N e=N | VERDICT`, where a
//! link `L` is `LEVEL/KEYS/SIGS`, `KEYS` are key IDs joined by `.`, and each
//! signature in `SIGS` is `INDEX:SIGNER:MESSAGE`, with a `!` suffix when the
//! signature is corrupted. `MESSAGE` is the index of the link it covers, or
//! `b` for the blob. The genesis keys are IDs 0 through 3.

use std::fmt::Write as _;
use std::io::BufWriter;
use std::io::Write as _;

use c3_ota::blob::TrustRootSpec;
use c3_verify::chain::LINK_DOMAIN;
use c3_verify::keys::KeySet;
use c3_verify::trustroot::BLOB_DOMAIN;
use ed25519_dalek::Signer;
use ed25519_dalek::SigningKey;

const CASES: usize = 20_000;
const KEYS: u8 = 8;

/// A small deterministic generator, so every run prints the same cases.
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

    fn chance(&mut self, percent: u64) -> bool {
        self.below(100) < percent
    }
}

/// A signature entry before signing: which index it claims, which key
/// signs, which message it covers (`None` for the blob), and whether to
/// corrupt it.
struct Entry {
    index: u8,
    signer: u8,
    message: Option<usize>,
    corrupt: bool,
}

/// An honest signature list from `signers` over `own`, then, for about a
/// third of lists, one fault.
fn entries(rng: &mut Rng, signers: &[u8], own: Option<usize>, links: usize) -> Vec<Entry> {
    let mut indexes: Vec<u8> = (0..signers.len() as u8)
        .filter(|_| rng.chance(70))
        .collect();
    while indexes.len() < 2.min(signers.len()) {
        let i = rng.below(signers.len() as u64) as u8;
        if !indexes.contains(&i) {
            indexes.push(i);
        }
    }
    indexes.sort_unstable();
    let mut list: Vec<Entry> = indexes
        .iter()
        .map(|&index| Entry {
            index,
            signer: signers[usize::from(index)],
            message: own,
            corrupt: false,
        })
        .collect();
    if list.is_empty() || !rng.chance(35) {
        return list;
    }
    let at = rng.below(list.len() as u64) as usize;
    match rng.below(7) {
        0 => list[at].corrupt = true,
        1 => list[at].signer = rng.below(u64::from(KEYS)) as u8,
        2 => {
            list[at].message = if links > 0 && rng.chance(50) {
                Some(rng.below(links as u64) as usize)
            } else {
                None
            }
        }
        3 => {
            let e = &list[at];
            let copy = Entry {
                index: e.index,
                signer: e.signer,
                message: e.message,
                corrupt: false,
            };
            list.insert(at, copy);
        }
        4 => list[at].index = signers.len() as u8 + rng.below(2) as u8,
        5 => list.truncate(1),
        _ => {
            if list.len() > 1 {
                list.swap(0, 1);
            }
        }
    }
    list.truncate(4);
    list
}

fn describe(entries: &[Entry]) -> String {
    let mut out = String::new();
    for (i, e) in entries.iter().enumerate() {
        if i > 0 {
            out.push(',');
        }
        let message = e.message.map_or_else(|| "b".to_string(), |m| m.to_string());
        let _ = write!(out, "{}:{}:{}", e.index, e.signer, message);
        if e.corrupt {
            out.push('!');
        }
    }
    out
}

fn sign(entries: &[Entry], keys: &[SigningKey], messages: &[Vec<u8>], blob: &[u8]) -> Vec<u8> {
    let mut out = vec![entries.len() as u8];
    for e in entries {
        let message = e.message.map_or(blob, |m| messages[m].as_slice());
        let mut sig = keys[usize::from(e.signer)].sign(message).to_bytes();
        if e.corrupt {
            sig[7] ^= 0x40;
        }
        out.push(e.index);
        out.extend_from_slice(&sig);
    }
    out
}

fn domain_message(domain: &[u8], body: &[u8]) -> Vec<u8> {
    let mut m = domain.to_vec();
    m.push(0);
    m.extend_from_slice(body);
    m
}

fn main() -> std::io::Result<()> {
    let keys: Vec<SigningKey> = (0..KEYS)
        .map(|i| SigningKey::from_bytes(&[i + 1; 32]))
        .collect();
    let public: Vec<[u8; 32]> = keys.iter().map(|k| k.verifying_key().to_bytes()).collect();
    let genesis_bytes: Vec<u8> = public[..4].concat();
    let genesis = KeySet::new(&genesis_bytes).expect("distinct genesis keys");
    let root_json = include_str!("../../release/trusted_root.json");
    let policy = [
        "https://token.actions.githubusercontent.com".to_string(),
        "https://github.com/o/r/.github/workflows/c3-release.yml@refs/heads/main".to_string(),
        "1".to_string(),
        "2".to_string(),
        "push".to_string(),
    ];
    let mut spec = TrustRootSpec::from_trusted_root(root_json, 0, policy)
        .expect("the pinned trusted root converts");
    let mut rng = Rng(0x0C3B_0071);
    let mut scratch = vec![0u8; 4_120];
    let mut out = BufWriter::new(std::io::stdout().lock());

    for _ in 0..CASES {
        let link_count = rng.below(4) as usize;
        let mut level = 0u8;
        let mut signers: Vec<u8> = (0..4).collect();
        let mut bodies = Vec::new();
        let mut link_keys = Vec::new();
        let mut link_entries = Vec::new();
        for i in 0..link_count {
            level = if rng.chance(4) {
                rng.below(18) as u8
            } else {
                (level + 1 + rng.below(3) as u8).min(17)
            };
            let n = if rng.chance(5) {
                1
            } else {
                2 + rng.below(3) as usize
            };
            let duplicate = rng.chance(4);
            let mut ks: Vec<u8> = Vec::new();
            while ks.len() < n {
                let k = rng.below(u64::from(KEYS)) as u8;
                if !ks.contains(&k) {
                    ks.push(k);
                }
            }
            if duplicate && ks.len() > 1 {
                ks[1] = ks[0];
            }
            let mut body = vec![level, ks.len() as u8];
            for &k in &ks {
                body.extend_from_slice(&public[usize::from(k)]);
            }
            link_entries.push(entries(&mut rng, &signers, Some(i), link_count));
            bodies.push(body);
            signers = ks.clone();
            link_keys.push(ks);
        }
        let blob_level = if rng.chance(8) {
            rng.below(18) as u8
        } else {
            (level + rng.below(3) as u8).min(17)
        };
        let blob_entries = entries(&mut rng, &signers, None, link_count);
        let sv = if rng.chance(8) {
            rng.below(18) as u8
        } else {
            blob_level
        };
        let efuse = if rng.chance(10) {
            rng.below(18) as u8
        } else {
            rng.below(u64::from(blob_level) + 1) as u8
        };

        let messages: Vec<Vec<u8>> = bodies
            .iter()
            .map(|b| domain_message(LINK_DOMAIN, b))
            .collect();
        spec.level = blob_level;
        let blob_body = spec.encode_body().expect("the blob body encodes");
        let blob_message = domain_message(BLOB_DOMAIN, &blob_body);

        let mut chain = b"C3KC".to_vec();
        chain.extend_from_slice(&1u16.to_le_bytes());
        chain.push(link_count as u8);
        chain.push(0);
        for (body, es) in bodies.iter().zip(&link_entries) {
            chain.extend_from_slice(body);
            chain.extend_from_slice(&sign(es, &keys, &messages, &blob_message));
        }
        let mut blob = blob_body.clone();
        blob.extend_from_slice(&sign(&blob_entries, &keys, &messages, &blob_message));

        let accepted = c3_verify::chain::parse(&chain)
            .and_then(|c| c3_verify::chain::verify(&c, genesis, &mut scratch))
            .and_then(|tip| {
                let root = c3_verify::trustroot::parse(&blob)?;
                c3_verify::trustroot::verify(&root, &tip, &mut scratch)?;
                c3_verify::level::check_slot(tip.level, root.level, sv, efuse)
            })
            .is_ok();

        let links = if link_count == 0 {
            "-".to_string()
        } else {
            link_keys
                .iter()
                .zip(&link_entries)
                .zip(&bodies)
                .map(|((ks, es), body)| {
                    let ids: Vec<String> = ks.iter().map(u8::to_string).collect();
                    format!("{}/{}/{}", body[0], ids.join("."), describe(es))
                })
                .collect::<Vec<_>>()
                .join(";")
        };
        writeln!(
            out,
            "trust links={links} blob={blob_level}/{} sv={sv} e={efuse} | {}",
            describe(&blob_entries),
            u8::from(accepted)
        )?;
    }
    out.flush()
}
