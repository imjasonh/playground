//! Changes each byte of a valid slot and checks that no change alters the
//! outcome.
//!
//! The slot holds a 40-byte image signed by fakestore
//! (`testdata/mutation/`) and a TUF part with no new roots, a `targets.json`
//! from the development TUF repository, and fakestore's trusted root. Every
//! byte the manifest points to is changed once, flipping one bit.
//!
//! A changed manifest, image, or TUF part must be rejected. A changed
//! bundle must be rejected, except inside the timestamp authority's embedded
//! certificate, which nothing reads; a change there must give the same
//! result.

use std::fs;
use std::path::Path;

use base64::Engine;
use base64::engine::general_purpose::STANDARD;

use c3_ota::container::from_bundle_json;
use c3_ota::slot;
use c3_ota::tuf;

const ROOT: &str = concat!(env!("CARGO_MANIFEST_DIR"), "/../testdata");

fn valid_slot() -> Vec<u8> {
    let image = fs::read(format!("{ROOT}/mutation/image.bin")).unwrap();
    let bundle_json = fs::read_to_string(format!("{ROOT}/mutation/bundle.sigstore.json")).unwrap();
    let root_json = fs::read_to_string(format!("{ROOT}/mutation/trusted_root.json")).unwrap();
    let container = from_bundle_json(&bundle_json, Some(&c3_crypto::sha256(&image))).unwrap();
    let keys = tuf::DevKeys::read(Path::new(&format!("{ROOT}/keys"))).unwrap();
    let targets = keys
        .targets(1, root_json.as_bytes(), tuf::DEV_EXPIRES)
        .unwrap();
    let tuf_part = tuf::package(&[], &targets, root_json.as_bytes()).unwrap();
    slot::assemble(&image, &container, &tuf_part).unwrap()
}

fn pinned() -> Vec<u8> {
    fs::read(format!("{ROOT}/keys/tuf-dev-root.json")).unwrap()
}

fn policy() -> [String; 5] {
    c3_ota::policy::parse(&fs::read_to_string(format!("{ROOT}/keys/dev-policy")).unwrap()).unwrap()
}

/// The slot range of the timestamp authority's certificate, which the
/// timestamp token in `bundle` embeds.
fn embedded_tsa_certificate(
    slot_bytes: &[u8],
    bundle: std::ops::Range<usize>,
) -> std::ops::Range<usize> {
    let root: serde_json::Value = serde_json::from_str(
        &fs::read_to_string(format!("{ROOT}/mutation/trusted_root.json")).unwrap(),
    )
    .unwrap();
    let raw = root["timestampAuthorities"][0]["certChain"]["certificates"][0]["rawBytes"]
        .as_str()
        .unwrap();
    let der = STANDARD.decode(raw).unwrap();
    let matches: Vec<usize> = slot_bytes[bundle.clone()]
        .windows(der.len())
        .enumerate()
        .filter(|(_, w)| *w == der.as_slice())
        .map(|(i, _)| bundle.start + i)
        .collect();
    assert_eq!(
        matches.len(),
        1,
        "the bundle embeds the TSA certificate once"
    );
    matches[0]..matches[0] + der.len()
}

#[test]
fn no_single_byte_change_alters_the_outcome() {
    let slot_bytes = valid_slot();
    let (pinned, policy) = (pinned(), policy());
    let expected =
        slot::verify(&slot_bytes, &pinned, &policy, 0).expect("the unchanged slot is accepted");

    let manifest =
        c3_verify::manifest::parse(&slot_bytes[..c3_verify::manifest::MANIFEST_LEN]).unwrap();
    let range = |p: c3_verify::manifest::Part| p.offset as usize..(p.offset + p.length) as usize;
    let parts = [
        ("manifest", 0..c3_verify::manifest::MANIFEST_LEN, false),
        ("image", range(manifest.image), false),
        ("bundle", range(manifest.bundle), true),
        ("tuf", range(manifest.tuf), false),
    ];

    let mut changed = slot_bytes.clone();
    let mut tried = 0;
    let mut ignored = Vec::new();
    let mut failures = Vec::new();
    for (name, bytes, may_ignore) in parts.clone() {
        for at in bytes {
            let bit = 1u8 << (at % 8);
            changed[at] ^= bit;
            match slot::verify(&changed, &pinned, &policy, 0) {
                Err(_) => {}
                Ok(got) if may_ignore && got == expected => ignored.push(at),
                Ok(got) => failures.push(format!("{name} byte {at:#x} bit {bit:#04x}: {got:?}")),
            }
            changed[at] ^= bit;
            tried += 1;
        }
    }
    assert!(
        failures.is_empty(),
        "{} of {tried} changes were accepted:\n{}",
        failures.len(),
        failures.join("\n")
    );
    // The only bytes nothing checks are the timestamp authority's embedded
    // certificate: the device finds the signer by the issuer and serial
    // number in the trusted root and verifies with the trusted root's key.
    let tsa_cert = embedded_tsa_certificate(&slot_bytes, range(manifest.bundle));
    assert!(
        ignored.iter().all(|at| tsa_cert.contains(at)),
        "bundle changes outside the TSA certificate {tsa_cert:x?} were ignored: {ignored:x?}"
    );
    assert!(
        !ignored.is_empty(),
        "the TSA certificate's bytes are now checked; update this test"
    );

    // Bytes outside the parts the manifest names are never read, so changing
    // them changes nothing.
    let covered = |at: usize| parts.iter().any(|(_, r, _)| r.contains(&at));
    let padding: Vec<usize> = (0..slot_bytes.len())
        .filter(|&at| !covered(at))
        .step_by(997)
        .collect();
    assert!(padding.len() > 50, "too few padding bytes sampled");
    for at in padding {
        changed[at] ^= 0x01;
        assert_eq!(
            slot::verify(&changed, &pinned, &policy, 0),
            Ok(expected),
            "padding byte {at:#x}"
        );
        changed[at] ^= 0x01;
    }
}
