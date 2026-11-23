//! Named inputs for the TUF checks, shared by the tests, which compare each
//! with its expected verdict, and the `tuf_vectors` example, which prints
//! `c3-verify`'s verdicts for `c3-boot-proofs`' `tuf-check` to compare with
//! the Lean specification.
//!
//! The real cases use Sigstore's metadata in `testdata/tuf/`. The synthetic
//! cases sign metadata with test keys, and the accept cases put that
//! metadata around the fakestore release in `testdata/mutation/`.

use std::fs;

use serde_json::Value;
use serde_json::json;

use crate::tuf::TestKey;
use crate::tuf::canonical;
use crate::tuf::canonical_value;
use crate::tuf::container;
use crate::tuf::root_signed;
use crate::tuf::sign_metadata;
use crate::tuf::targets_signed;

/// The directory of the test data.
pub const TESTDATA: &str = concat!(env!("CARGO_MANIFEST_DIR"), "/../testdata");

/// The release identity that the fakestore bundle in `testdata/mutation/`
/// satisfies: issuer, Build Signer URI, repository ID, owner ID, and
/// trigger.
pub const POLICY: [&str; 5] = [
    "https://token.actions.githubusercontent.com",
    "https://github.com/imjasonh/playground/.github/workflows/c3-release.yml@refs/heads/main",
    "1234",
    "5678",
    "push",
];

/// What a case checks.
pub enum Input {
    /// Parses a JSON document in the strict or canonical profile.
    Json {
        /// Whether the document must be canonical JSON.
        canonical: bool,
        /// The document.
        doc: Vec<u8>,
    },
    /// Verifies the TUF part of a slot from a pinned root.
    Tuf {
        /// The pinned root.
        pinned: Vec<u8>,
        /// The TUF part.
        tuf: Vec<u8>,
    },
    /// Reads the keys from a `trusted_root.json`.
    Trusted {
        /// The trusted root.
        json: Vec<u8>,
    },
    /// Checks a whole slot with [`POLICY`].
    Accept {
        /// The eFuse level.
        level: u8,
        /// The image.
        image: Vec<u8>,
        /// The bundle container.
        bundle: Vec<u8>,
        /// The TUF part.
        tuf: Vec<u8>,
        /// The pinned root.
        pinned: Vec<u8>,
    },
}

/// One named input and whether the device should accept it.
pub struct Case {
    /// A name with no spaces.
    pub name: String,
    /// What to check.
    pub input: Input,
    /// Whether the check should pass, or `None` for random inputs that only
    /// the differential check judges.
    pub expect: Option<bool>,
}

fn case(name: &str, input: Input, ok: bool) -> Case {
    Case {
        name: name.to_string(),
        input,
        expect: Some(ok),
    }
}

fn read(path: &str) -> Vec<u8> {
    fs::read(format!("{TESTDATA}/{path}")).unwrap_or_else(|e| panic!("{path}: {e}"))
}

/// A small deterministic generator, so every run builds the same cases.
struct Rng(u64);

impl Rng {
    fn next(&mut self) -> u64 {
        self.0 ^= self.0 << 13;
        self.0 ^= self.0 >> 7;
        self.0 ^= self.0 << 17;
        self.0
    }

    fn below(&mut self, n: usize) -> usize {
        (self.next() % n as u64) as usize
    }
}

const JSON_CASES: usize = 3_000;
const ALPHABET: &[u8] = b"{}[]:,\" \n\t\r\\0123456789-.etruefalsnul\x01\x7fab";

fn random_value(rng: &mut Rng, depth: usize, out: &mut Vec<u8>) {
    let ws = |rng: &mut Rng, out: &mut Vec<u8>| {
        if rng.below(4) == 0 {
            out.push(b" \n\t\r"[rng.below(4)]);
        }
    };
    let kind = if depth >= 18 {
        rng.below(4)
    } else {
        rng.below(7)
    };
    match kind {
        0 => out.extend_from_slice(
            ["0", "7", "42", "100", "true", "false", "null"][rng.below(7)].as_bytes(),
        ),
        1 => out.extend_from_slice(b"9999999999999999999"),
        2 | 3 => {
            out.push(b'"');
            for _ in 0..rng.below(4) {
                out.push(b"ab\n z"[rng.below(5)]);
            }
            out.push(b'"');
        }
        4 | 5 => {
            out.push(b'{');
            let keys = [&b"a"[..], b"b", b"ab", b"", b"_t"];
            let mut start = rng.below(keys.len());
            for i in 0..rng.below(4) {
                if i > 0 {
                    out.push(b',');
                }
                ws(rng, out);
                out.push(b'"');
                out.extend_from_slice(keys[start % keys.len()]);
                out.push(b'"');
                ws(rng, out);
                out.push(b':');
                ws(rng, out);
                random_value(rng, depth + 1, out);
                ws(rng, out);
                start += 1 + rng.below(2);
            }
            out.push(b'}');
        }
        _ => {
            out.push(b'[');
            for i in 0..rng.below(4) {
                if i > 0 {
                    out.push(b',');
                }
                ws(rng, out);
                random_value(rng, depth + 1, out);
                ws(rng, out);
            }
            out.push(b']');
        }
    }
}

fn json_cases(cases: &mut Vec<Case>) {
    let fixed: &[(&str, &[u8], bool, bool)] = &[
        ("empty", b"", false, false),
        ("zero", b"0", true, true),
        ("leading_zero", b"01", false, false),
        ("negative", b"-1", false, false),
        ("fraction", b"1.5", false, false),
        ("nineteen_digits", b"9999999999999999999", true, true),
        ("twenty_digits", b"10000000000000000000", false, false),
        ("escape", b"\"a\\nb\"", false, false),
        ("raw_newline", b"\"a\nb\"", true, false),
        ("control", b"\"a\x01b\"", true, false),
        ("sorted", b"{\"a\":1,\"b\":2}", true, true),
        ("unsorted", b"{\"b\":1,\"a\":2}", false, true),
        ("duplicate", b"{\"a\":1,\"a\":2}", false, false),
        ("prefix_keys", b"{\"a\":1,\"ab\":2}", true, true),
        ("whitespace", b" { \"a\" : [ 1 , 2 ] } ", false, true),
        ("trailing_comma", b"[1,]", false, false),
        ("trailing_bytes", b"{}x", false, false),
        ("two_values", b"1 2", false, false),
        ("depth_16", b"[[[[[[[[[[[[[[[[]]]]]]]]]]]]]]]]", true, true),
        (
            "depth_17",
            b"[[[[[[[[[[[[[[[[[]]]]]]]]]]]]]]]]]",
            false,
            false,
        ),
        ("unclosed", b"[1,[2]", false, false),
        ("bare_key", b"{a:1}", false, false),
        ("literal_case", b"True", false, false),
        ("utf8", "\"\u{e9}\"".as_bytes(), true, true),
    ];
    for &(name, doc, canonical_ok, strict_ok) in fixed {
        let doc = doc.to_vec();
        cases.push(case(
            &format!("json_canonical_{name}"),
            Input::Json {
                canonical: true,
                doc: doc.clone(),
            },
            canonical_ok,
        ));
        cases.push(case(
            &format!("json_strict_{name}"),
            Input::Json {
                canonical: false,
                doc,
            },
            strict_ok,
        ));
    }
    let mut rng = Rng(0x7f4a_7c15_9e37_79b9);
    for i in 0..JSON_CASES {
        let mut doc = Vec::new();
        random_value(&mut rng, 0, &mut doc);
        for _ in 0..rng.below(3) {
            let at = rng.below(doc.len() + 1);
            match rng.below(3) {
                0 => doc.insert(at, ALPHABET[rng.below(ALPHABET.len())]),
                1 if at < doc.len() => {
                    doc.remove(at);
                }
                _ if at < doc.len() => doc[at] = ALPHABET[rng.below(ALPHABET.len())],
                _ => {}
            }
        }
        cases.push(Case {
            name: format!("json_random_{i}"),
            input: Input::Json {
                canonical: i % 2 == 0,
                doc,
            },
            expect: None,
        });
    }
}

fn real_root(v: u64) -> Vec<u8> {
    canonical(&read(&format!("tuf/{v}.root.json"))).expect("canonical root")
}

fn real_cases(cases: &mut Vec<Case>) {
    let targets = canonical(&read("tuf/targets.json")).expect("canonical targets");
    let trusted = read("tuf/trusted_root.json");
    let roots = |from: u64, to: u64| (from..=to).map(real_root).collect::<Vec<_>>();
    let tuf = |pinned: u64, roots: Vec<Vec<u8>>, targets: &[u8], trusted: &[u8]| Input::Tuf {
        pinned: real_root(pinned),
        tuf: container(&roots, targets, trusted),
    };
    cases.push(case(
        "real_5_to_16",
        tuf(5, roots(6, 16), &targets, &trusted),
        true,
    ));
    cases.push(case(
        "real_14_to_16",
        tuf(14, roots(15, 16), &targets, &trusted),
        true,
    ));
    cases.push(case(
        "real_16",
        tuf(16, Vec::new(), &targets, &trusted),
        true,
    ));
    let mut gap = roots(10, 16);
    gap.remove(2);
    cases.push(case(
        "real_version_gap",
        tuf(9, gap, &targets, &trusted),
        false,
    ));
    cases.push(case(
        "real_stale_targets",
        tuf(5, roots(6, 8), &targets, &trusted),
        false,
    ));
    cases.push(case(
        "real_replayed_root",
        tuf(16, vec![real_root(16)], &targets, &trusted),
        false,
    ));
    let pretty = read("tuf/16.root.json");
    cases.push(case(
        "real_pretty_root",
        tuf(15, vec![pretty], &targets, &trusted),
        false,
    ));
    let mut changed = trusted.clone();
    let at = changed.len() / 2;
    changed[at] ^= 1;
    cases.push(case(
        "real_trusted_root_changed",
        tuf(16, Vec::new(), &targets, &changed),
        false,
    ));
    let mut longer = trusted.clone();
    longer.push(b'\n');
    cases.push(case(
        "real_trusted_root_longer",
        tuf(16, Vec::new(), &targets, &longer),
        false,
    ));
    let mut tampered = targets.clone();
    let at = tampered
        .windows(9)
        .position(|w| w == b"\"version\"")
        .expect("targets has a version");
    tampered[at + 10] = b'9';
    cases.push(case(
        "real_targets_changed",
        tuf(16, Vec::new(), &tampered, &trusted),
        false,
    ));
    for (name, path) in [
        ("release", "../release/trusted_root.json"),
        ("mutation", "mutation/trusted_root.json"),
    ] {
        let json = read(path);
        cases.push(case(
            &format!("trusted_{name}"),
            Input::Trusted { json },
            true,
        ));
    }
    for entry in fs::read_dir(format!("{TESTDATA}/conformance")).expect("conformance dir") {
        let dir = entry.expect("conformance entry").path();
        let path = dir.join("trusted_root.json");
        if let Ok(json) = fs::read(&path) {
            let name = dir.file_name().unwrap_or_default().to_string_lossy();
            let input = Input::Trusted { json };
            cases.push(case(&format!("trusted_conformance_{name}"), input, true));
        }
    }
}

fn append<const N: usize>(array: &mut Value, items: [Value; N]) {
    if let Some(a) = array.as_array_mut() {
        a.extend(items);
    }
}

fn remove(object: &mut Value, key: &str) {
    if let Some(o) = object.as_object_mut() {
        o.remove(key);
    }
}

fn edit_trusted(name: &str, ok: bool, edit: impl FnOnce(&mut Value)) -> Case {
    let mut v: Value =
        serde_json::from_slice(&read("../release/trusted_root.json")).expect("trusted root");
    edit(&mut v);
    let json = serde_json::to_vec_pretty(&v).expect("encodes");
    case(&format!("trusted_{name}"), Input::Trusted { json }, ok)
}

fn trusted_cases(cases: &mut Vec<Case>) {
    let ed25519_small_order = "MCowBQYDK2VwAyEAAQAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAA=";
    cases.extend([
        edit_trusted("media_type", false, |v| {
            v["mediaType"] = json!("application/json");
        }),
        edit_trusted("no_tlogs", false, |v| {
            remove(v, "tlogs");
        }),
        edit_trusted("no_cas", true, |v| {
            v["certificateAuthorities"] = json!([]);
        }),
        edit_trusted("log_http", false, |v| {
            v["tlogs"][1]["baseUrl"] = json!("http://log2025-1.rekor.sigstore.dev");
        }),
        edit_trusted("log_trailing_slashes", true, |v| {
            v["tlogs"][1]["baseUrl"] = json!("https://log2025-1.rekor.sigstore.dev//");
        }),
        edit_trusted("log_empty_origin", false, |v| {
            v["tlogs"][1]["baseUrl"] = json!("https:///");
        }),
        edit_trusted("log_small_order", false, |v| {
            v["tlogs"][1]["publicKey"]["rawBytes"] = json!(ed25519_small_order);
        }),
        edit_trusted("log_duplicate", false, |v| {
            let log = v["tlogs"][1].clone();
            append(&mut v["tlogs"], [log]);
        }),
        edit_trusted("log_end", true, |v| {
            v["tlogs"][1]["publicKey"]["validFor"]["end"] = json!("2030-01-01T00:00:00.5Z");
        }),
        edit_trusted("log_bad_time", false, |v| {
            v["tlogs"][1]["publicKey"]["validFor"]["start"] = json!("2025-09-23 00:00:00Z");
        }),
        edit_trusted("ca_duplicate", false, |v| {
            let ca = v["certificateAuthorities"][1].clone();
            append(&mut v["certificateAuthorities"], [ca]);
        }),
        edit_trusted("ca_empty_chain", false, |v| {
            v["certificateAuthorities"][1]["certChain"]["certificates"] = json!([]);
        }),
        edit_trusted("ca_long_chain", false, |v| {
            let c = &mut v["certificateAuthorities"][1]["certChain"]["certificates"];
            let first = c[0].clone();
            append(c, [first.clone(), first.clone(), first]);
        }),
        edit_trusted("ca_chain_of_four", true, |v| {
            let c = &mut v["certificateAuthorities"][1]["certChain"]["certificates"];
            let first = c[0].clone();
            append(c, [first.clone(), first]);
        }),
        edit_trusted("ca_bad_base64", false, |v| {
            let raw =
                &mut v["certificateAuthorities"][1]["certChain"]["certificates"][0]["rawBytes"];
            let text = raw.as_str().unwrap_or_default().replace('=', "");
            *raw = json!(text);
        }),
        edit_trusted("ca_not_der", false, |v| {
            v["certificateAuthorities"][1]["certChain"]["certificates"][0]["rawBytes"] =
                json!("MAA=");
        }),
        edit_trusted("tsa_duplicate", false, |v| {
            let tsa = v["timestampAuthorities"][0].clone();
            append(&mut v["timestampAuthorities"], [tsa]);
        }),
        edit_trusted("tsa_no_valid_for", false, |v| {
            remove(&mut v["timestampAuthorities"][0], "validFor");
        }),
    ]);
}

/// The synthetic keys: P-256, P-384, and Ed25519 keys from distinct seeds.
fn keys() -> Vec<TestKey> {
    vec![
        TestKey::p256(1),
        TestKey::p384(2),
        TestKey::ed25519(3),
        TestKey::ed25519(4),
        TestKey::p256(5),
        TestKey::p384(6),
        TestKey::ed25519(7),
        TestKey::p256(8),
    ]
}

const FAR: &str = "2099-01-01T00:00:00Z";

/// A synthetic TUF setup: root v1 with keys 0, 1, 2 (threshold 2) signing
/// roots and keys 5, 6 (threshold 1) signing targets; root v2 rotating to
/// keys 3, 4, 7 (threshold 2); and targets signed by key 6.
struct Synth {
    k: Vec<TestKey>,
    trusted: Vec<u8>,
}

impl Synth {
    fn new() -> Self {
        Synth {
            k: keys(),
            trusted: read("mutation/trusted_root.json"),
        }
    }

    fn ks(&self, ids: &[usize]) -> Vec<&TestKey> {
        ids.iter().map(|&i| &self.k[i]).collect()
    }

    fn root_value(&self, version: u64, root: &[usize], threshold: u64) -> Value {
        root_signed(
            version,
            FAR,
            (&self.ks(root), threshold),
            (&self.ks(&[5, 6]), 1),
        )
    }

    fn v1(&self) -> Value {
        self.root_value(1, &[0, 1, 2], 2)
    }

    fn v2(&self) -> Value {
        self.root_value(2, &[3, 4, 7], 2)
    }

    fn sign(&self, signed: &Value, ids: &[usize]) -> Vec<u8> {
        sign_metadata(signed, &self.ks(ids)).expect("signs")
    }

    fn pinned(&self) -> Vec<u8> {
        self.sign(&self.v1(), &[])
    }

    fn targets(&self) -> Vec<u8> {
        self.sign(&targets_signed(1, FAR, &self.trusted), &[6])
    }

    fn good_v2(&self) -> Vec<u8> {
        self.sign(&self.v2(), &[0, 2, 3, 7])
    }

    fn tuf(&self, roots: Vec<Vec<u8>>, targets: Vec<u8>) -> Input {
        Input::Tuf {
            pinned: self.pinned(),
            tuf: container(&roots, &targets, &self.trusted),
        }
    }
}

/// Builds a metadata document from `signed` and explicit signature entries.
fn with_signatures(signed: &Value, signatures: Vec<Value>) -> Vec<u8> {
    canonical_value(&json!({"signatures": signatures, "signed": signed})).expect("canonical")
}

fn synthetic_cases(cases: &mut Vec<Case>) {
    let s = Synth::new();
    let v2 = s.v2();
    let message = canonical_value(&v2).expect("canonical");
    let sig = |i: usize| json!({"keyid": s.k[i].keyid(), "sig": s.k[i].sign(&message)});
    let mut add = |name: &str, input: Input, ok: bool| {
        cases.push(case(&format!("synthetic_{name}"), input, ok));
    };

    add("no_rotation", s.tuf(Vec::new(), s.targets()), true);
    add("rotation", s.tuf(vec![s.good_v2()], s.targets()), true);
    add(
        "rotation_old_below_threshold",
        s.tuf(vec![s.sign(&v2, &[0, 3, 7])], s.targets()),
        false,
    );
    add(
        "rotation_new_below_threshold",
        s.tuf(vec![s.sign(&v2, &[0, 1, 3])], s.targets()),
        false,
    );
    add(
        "rotation_unsigned_by_old",
        s.tuf(vec![s.sign(&v2, &[3, 4, 7])], s.targets()),
        false,
    );
    add(
        "rotation_p384_and_ed25519",
        s.tuf(vec![s.sign(&v2, &[1, 2, 4, 7])], s.targets()),
        true,
    );
    let v3 = s.root_value(3, &[0], 1);
    add(
        "two_rotations",
        s.tuf(vec![s.good_v2(), s.sign(&v3, &[3, 4, 0])], s.targets()),
        true,
    );
    add(
        "rotation_skips_version",
        s.tuf(vec![s.sign(&v3, &[0, 1, 2])], s.targets()),
        false,
    );
    let v1_again = s.v1();
    add(
        "rotation_same_version",
        s.tuf(vec![s.sign(&v1_again, &[0, 1, 2])], s.targets()),
        false,
    );

    let corrupt = |mut v: Value| {
        let text = v["sig"].as_str().unwrap_or_default().to_string();
        let flipped = if text.ends_with('0') { "1" } else { "0" };
        v["sig"] = json!(format!("{}{flipped}", &text[..text.len() - 1]));
        v
    };
    add(
        "bad_signature_counted_out",
        s.tuf(
            vec![with_signatures(
                &v2,
                vec![corrupt(sig(0)), sig(2), sig(3), sig(7)],
            )],
            s.targets(),
        ),
        false,
    );
    add(
        "bad_signature_spare",
        s.tuf(
            vec![with_signatures(
                &v2,
                vec![corrupt(sig(1)), sig(0), sig(2), sig(3), sig(7)],
            )],
            s.targets(),
        ),
        true,
    );
    let empty = |i: usize| json!({"keyid": s.k[i].keyid(), "sig": ""});
    add(
        "empty_signature",
        s.tuf(
            vec![with_signatures(
                &v2,
                vec![empty(1), sig(0), sig(2), sig(3), sig(7)],
            )],
            s.targets(),
        ),
        true,
    );
    add(
        "duplicate_keyid",
        s.tuf(
            vec![with_signatures(
                &v2,
                vec![sig(0), sig(0), sig(2), sig(3), sig(7)],
            )],
            s.targets(),
        ),
        false,
    );
    add(
        "unknown_keyid_signature",
        s.tuf(
            vec![with_signatures(
                &v2,
                vec![
                    json!({"keyid": "00", "sig": "00"}),
                    sig(0),
                    sig(2),
                    sig(3),
                    sig(7),
                ],
            )],
            s.targets(),
        ),
        true,
    );
    add(
        "signature_extra_field",
        s.tuf(
            vec![with_signatures(
                &v2,
                vec![
                    json!({"keyid": s.k[0].keyid(), "sig": s.k[0].sign(&message), "x": 1}),
                    sig(2),
                    sig(3),
                    sig(7),
                ],
            )],
            s.targets(),
        ),
        true,
    );
    add(
        "signature_missing_sig",
        s.tuf(
            vec![with_signatures(
                &v2,
                vec![
                    json!({"keyid": s.k[1].keyid()}),
                    sig(0),
                    sig(2),
                    sig(3),
                    sig(7),
                ],
            )],
            s.targets(),
        ),
        false,
    );

    // The same key under two key IDs counts once.
    let mut v2_alias = s.v2();
    let alias = "aa".repeat(32);
    v2_alias["keys"][&alias] = s.k[3].key_json();
    v2_alias["roles"]["root"]["keyids"] = json!([s.k[3].keyid(), alias]);
    let msg = canonical_value(&v2_alias).expect("canonical");
    let signed_as = |i: usize, id: String| json!({"keyid": id, "sig": s.k[i].sign(&msg)});
    let alias_sigs = vec![
        signed_as(0, s.k[0].keyid()),
        signed_as(2, s.k[2].keyid()),
        signed_as(3, s.k[3].keyid()),
        signed_as(3, alias),
    ];
    add(
        "same_key_two_ids",
        s.tuf(vec![with_signatures(&v2_alias, alias_sigs)], s.targets()),
        false,
    );

    let mut unknown_type = s.v1();
    unknown_type["keys"][s.k[0].keyid()]["keytype"] = json!("rsa");
    let v2_types = s.v2();
    let pinned = s.sign(&unknown_type, &[]);
    let typed = |signers: &[usize]| Input::Tuf {
        pinned: pinned.clone(),
        tuf: container(&[s.sign(&v2_types, signers)], &s.targets(), &s.trusted),
    };
    add("unknown_key_type_ignored", typed(&[1, 2, 3, 4]), true);
    add("unknown_key_type_not_counted", typed(&[0, 1, 3, 4]), false);

    let mut nine = s.v1();
    let ids: Vec<String> = (0..9).map(|i| format!("{i:02x}")).collect();
    nine["roles"]["root"]["keyids"] = json!(ids);
    let pinned_nine = s.sign(&nine, &[]);
    add(
        "nine_root_keys",
        Input::Tuf {
            pinned: pinned_nine,
            tuf: container(&[s.good_v2()], &s.targets(), &s.trusted),
        },
        false,
    );
    let mut zero = s.v1();
    zero["roles"]["root"]["threshold"] = json!(0);
    add(
        "zero_threshold",
        Input::Tuf {
            pinned: s.sign(&zero, &[]),
            tuf: container(&[s.good_v2()], &s.targets(), &s.trusted),
        },
        false,
    );
    let mut zero_version = s.v1();
    zero_version["version"] = json!(0);
    add(
        "zero_version",
        Input::Tuf {
            pinned: s.sign(&zero_version, &[]),
            tuf: container(&[], &s.targets(), &s.trusted),
        },
        false,
    );
    let mut wrong_type = s.v2();
    wrong_type["_type"] = json!("targets");
    add(
        "rotation_wrong_type",
        s.tuf(vec![s.sign(&wrong_type, &[0, 2, 3, 7])], s.targets()),
        false,
    );
    let extra = canonical_value(&json!({
        "extra": 1,
        "signatures": [],
        "signed": s.v1(),
    }))
    .expect("canonical");
    add(
        "extra_top_member",
        Input::Tuf {
            pinned: extra,
            tuf: container(&[], &s.targets(), &s.trusted),
        },
        false,
    );

    add(
        "targets_unsigned",
        s.tuf(Vec::new(), s.sign(&targets_signed(1, FAR, &s.trusted), &[])),
        false,
    );
    add(
        "targets_signed_by_root_key",
        s.tuf(
            Vec::new(),
            s.sign(&targets_signed(1, FAR, &s.trusted), &[0]),
        ),
        false,
    );
    add(
        "targets_signed_by_new_root_key",
        s.tuf(
            vec![s.good_v2()],
            s.sign(&targets_signed(1, FAR, &s.trusted), &[7]),
        ),
        false,
    );
    let mut no_entry = targets_signed(1, FAR, &s.trusted);
    no_entry["targets"] = json!({"other.json": no_entry["targets"]["trusted_root.json"].clone()});
    add(
        "targets_no_entry",
        s.tuf(Vec::new(), s.sign(&no_entry, &[6])),
        false,
    );
    let mut upper = targets_signed(1, FAR, &s.trusted);
    let digest = upper["targets"]["trusted_root.json"]["hashes"]["sha256"]
        .as_str()
        .unwrap_or_default()
        .to_uppercase();
    upper["targets"]["trusted_root.json"]["hashes"]["sha256"] = json!(digest);
    add(
        "targets_uppercase_digest",
        s.tuf(Vec::new(), s.sign(&upper, &[6])),
        false,
    );
    let mut wrong_len = targets_signed(1, FAR, &s.trusted);
    wrong_len["targets"]["trusted_root.json"]["length"] = json!(s.trusted.len() + 1);
    add(
        "targets_wrong_length",
        s.tuf(Vec::new(), s.sign(&wrong_len, &[6])),
        false,
    );
    let bad_expiry = targets_signed(1, "2099-01-01", &s.trusted);
    add(
        "targets_bad_expiry",
        s.tuf(Vec::new(), s.sign(&bad_expiry, &[6])),
        false,
    );

    let too_many: Vec<Vec<u8>> = (2..=34)
        .map(|v| s.sign(&s.root_value(v, &[0, 1, 2], 2), &[0, 1, 2]))
        .collect();
    add(
        "thirty_three_roots",
        s.tuf(too_many.clone(), s.targets()),
        false,
    );
    let max = too_many[..32].to_vec();
    add("thirty_two_roots", s.tuf(max, s.targets()), true);

    let good = container(&[s.good_v2()], &s.targets(), &s.trusted);
    let mut short = good.clone();
    short.pop();
    add(
        "container_truncated",
        Input::Tuf {
            pinned: s.pinned(),
            tuf: short,
        },
        false,
    );
    let mut trailing = good.clone();
    trailing.push(0);
    add(
        "container_trailing",
        Input::Tuf {
            pinned: s.pinned(),
            tuf: trailing,
        },
        false,
    );
    let mut magic = good;
    magic[0] = b'X';
    add(
        "container_magic",
        Input::Tuf {
            pinned: s.pinned(),
            tuf: magic,
        },
        false,
    );
}

fn accept_cases(cases: &mut Vec<Case>) {
    let s = Synth::new();
    let image = read("mutation/image.bin");
    let json = String::from_utf8(read("mutation/bundle.sigstore.json")).expect("UTF-8");
    let bundle = crate::container::from_bundle_json(&json, Some(&c3_crypto::sha256(&image)))
        .expect("bundle container");
    let accept = |level: u8, tuf: Vec<u8>, image: &[u8]| Input::Accept {
        level,
        image: image.to_vec(),
        bundle: bundle.clone(),
        tuf,
        pinned: s.pinned(),
    };
    let good = container(&[s.good_v2()], &s.targets(), &s.trusted);
    let mut add = |name: &str, input: Input, ok: bool| {
        cases.push(case(&format!("accept_{name}"), input, ok));
    };
    add("ok", accept(0, good.clone(), &image), true);
    let sv = c3_verify::image::parse(&image, image.len() as u32)
        .map(|h| h.security_version)
        .unwrap_or(0);
    add("at_level", accept(sv, good.clone(), &image), true);
    add("below_level", accept(sv + 1, good.clone(), &image), false);
    let mut other_image = image.clone();
    let last = other_image.len() - 1;
    other_image[last] ^= 1;
    add("other_image", accept(0, good.clone(), &other_image), false);
    let expired = s.sign(&targets_signed(1, "2021-01-01T00:00:00Z", &s.trusted), &[6]);
    add(
        "expired_targets",
        accept(0, container(&[s.good_v2()], &expired, &s.trusted), &image),
        false,
    );
    let mut old_root = s.v2();
    old_root["expires"] = json!("2021-01-01T00:00:00Z");
    let old = s.sign(&old_root, &[0, 2, 3, 7]);
    add(
        "expired_root",
        accept(0, container(&[old], &s.targets(), &s.trusted), &image),
        false,
    );
    let release = read("../release/trusted_root.json");
    let other_targets = s.sign(&targets_signed(1, FAR, &release), &[6]);
    add(
        "other_trusted_root",
        accept(
            0,
            container(&[s.good_v2()], &other_targets, &release),
            &image,
        ),
        false,
    );
    add(
        "bad_tuf",
        accept(
            0,
            container(&[s.sign(&s.v2(), &[3])], &s.targets(), &s.trusted),
            &image,
        ),
        false,
    );
}

/// Every case, in a fixed order.
pub fn cases() -> Vec<Case> {
    let mut cases = Vec::new();
    json_cases(&mut cases);
    real_cases(&mut cases);
    trusted_cases(&mut cases);
    synthetic_cases(&mut cases);
    accept_cases(&mut cases);
    cases
}

fn hex(bytes: &[u8]) -> String {
    if bytes.is_empty() {
        return "-".to_string();
    }
    bytes.iter().map(|b| format!("{b:02x}")).collect()
}

fn entries<T>(items: impl Iterator<Item = T>, f: impl Fn(T) -> String) -> String {
    let list: Vec<String> = items.map(f).collect();
    if list.is_empty() {
        "-".to_string()
    } else {
        list.join(",")
    }
}

impl Input {
    /// The input as `c3-boot-proofs`' `tuf-check` reads it: a kind, then
    /// its fields, with byte strings in lowercase hex and `-` for an empty
    /// one.
    pub fn describe(&self) -> String {
        match self {
            Input::Json { canonical, doc } => {
                let mode = if *canonical { "canonical" } else { "strict" };
                format!("json {mode} {}", hex(doc))
            }
            Input::Tuf { pinned, tuf } => format!("tuf {} {}", hex(pinned), hex(tuf)),
            Input::Trusted { json } => format!("trusted {}", hex(json)),
            Input::Accept {
                level,
                image,
                bundle,
                tuf,
                pinned,
            } => format!(
                "accept {level} {} {} {} {}",
                hex(image),
                hex(bundle),
                hex(tuf),
                hex(pinned)
            ),
        }
    }

    /// `c3-verify`'s verdict: `err`, or `ok` and what the check returned.
    pub fn verdict(&self) -> String {
        match self {
            Input::Json { canonical, doc } => {
                let mode = if *canonical {
                    c3_verify::json::Mode::Canonical
                } else {
                    c3_verify::json::Mode::Strict
                };
                match c3_verify::json::parse(doc, mode) {
                    Ok(_) => "ok".to_string(),
                    Err(_) => "err".to_string(),
                }
            }
            Input::Tuf { pinned, tuf } => match crate::tuf::verify(pinned, tuf) {
                Ok(v) => format!("ok {} {}", v.root_version, v.expires),
                Err(_) => "err".to_string(),
            },
            Input::Trusted { json } => {
                let policy = c3_verify::trustroot::Policy {
                    issuer: b"",
                    build_signer_uri: b"",
                    repository_id: b"",
                    owner_id: b"",
                    trigger: b"",
                };
                let mut buf = vec![0u8; c3_verify::trusted_root::buffer_len(json.len())];
                match c3_verify::trusted_root::extract(json, policy, &mut buf) {
                    Ok(root) => format!(
                        "ok fulcio={} logs={} tsas={}",
                        entries(root.fulcio(), |f| format!(
                            "{}/{}/{}/{}",
                            hex(f.subject),
                            hex(f.public_key),
                            f.window.not_before,
                            f.window.not_after
                        )),
                        entries(root.logs(), |l| format!(
                            "{}/{}/{}/{}",
                            hex(l.origin),
                            hex(l.public_key),
                            l.window.not_before,
                            l.window.not_after
                        )),
                        entries(root.tsas(), |t| format!(
                            "{}/{}/{}/{}",
                            hex(t.signer_id),
                            hex(t.public_key),
                            t.window.not_before,
                            t.window.not_after
                        )),
                    ),
                    Err(_) => "err".to_string(),
                }
            }
            Input::Accept {
                level,
                image,
                bundle,
                tuf,
                pinned,
            } => {
                let policy = POLICY.map(String::from);
                match crate::tuf::accept(image, bundle, tuf, pinned, &policy, *level) {
                    Ok(a) => format!("ok {} {}", a.level, a.signed_time),
                    Err(_) => "err".to_string(),
                }
            }
        }
    }
}
