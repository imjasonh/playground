//! Changes each byte of a valid slot and checks that no change alters the
//! outcome.
//!
//! The slot holds a 40-byte image signed by fakestore
//! (`testdata/mutation/`), an empty chain, and a level 0 trust-root blob for
//! fakestore's trusted root, signed by the development genesis keys. Every
//! byte the manifest points to is changed once, flipping one bit.
//!
//! A changed manifest, image, chain, or blob must be rejected. A changed
//! bundle must be rejected, except inside the timestamp authority's embedded
//! certificate, which nothing reads; a change there must give the same
//! result.

use std::fs;

use base64::Engine;
use base64::engine::general_purpose::STANDARD;

use c3_ota::blob::TrustRootSpec;
use c3_ota::blob::chain;
use c3_ota::blob::signed_blob;
use c3_ota::container::from_bundle_json;
use c3_ota::keys::read_signing_key;
use c3_ota::slot;

const ROOT: &str = concat!(env!("CARGO_MANIFEST_DIR"), "/../testdata");

fn valid_slot() -> Vec<u8> {
    let image = fs::read(format!("{ROOT}/mutation/image.bin")).unwrap();
    let bundle_json = fs::read_to_string(format!("{ROOT}/mutation/bundle.sigstore.json")).unwrap();
    let root_json = fs::read_to_string(format!("{ROOT}/mutation/trusted_root.json")).unwrap();
    let container = from_bundle_json(&bundle_json, Some(&c3_crypto::sha256(&image))).unwrap();
    let policy = [
        "https://token.actions.githubusercontent.com".into(),
        "https://github.com/imjasonh/playground/.github/workflows/c3-release.yml@refs/heads/main"
            .into(),
        "1234".into(),
        "5678".into(),
        "push".into(),
    ];
    let spec = TrustRootSpec::from_trusted_root(&root_json, 0, policy).unwrap();
    let k1 = read_signing_key(&format!("{ROOT}/keys/genesis-dev-1.seed")).unwrap();
    let k2 = read_signing_key(&format!("{ROOT}/keys/genesis-dev-2.seed")).unwrap();
    let blob = signed_blob(&spec, &[(0, &k1), (1, &k2)]).unwrap();
    slot::assemble(&image, &container, &chain(&[]).unwrap(), &blob).unwrap()
}

fn genesis() -> [u8; 128] {
    fs::read(format!("{ROOT}/keys/genesis-dev.pub"))
        .unwrap()
        .try_into()
        .unwrap()
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
    let genesis = genesis();
    let expected = slot::verify(&slot_bytes, &genesis, 0).expect("the unchanged slot is accepted");

    let manifest =
        c3_verify::manifest::parse(&slot_bytes[..c3_verify::manifest::MANIFEST_LEN]).unwrap();
    let range = |p: c3_verify::manifest::Part| p.offset as usize..(p.offset + p.length) as usize;
    let parts = [
        ("manifest", 0..c3_verify::manifest::MANIFEST_LEN, false),
        ("image", range(manifest.image), false),
        ("bundle", range(manifest.bundle), true),
        ("chain", range(manifest.chain), false),
        ("blob", range(manifest.blob), false),
    ];

    let mut changed = slot_bytes.clone();
    let mut tried = 0;
    let mut ignored = Vec::new();
    let mut failures = Vec::new();
    for (name, bytes, may_ignore) in parts.clone() {
        for at in bytes {
            let bit = 1u8 << (at % 8);
            changed[at] ^= bit;
            match slot::verify(&changed, &genesis, 0) {
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
    // number in the blob and verifies with the blob's key.
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
            slot::verify(&changed, &genesis, 0),
            Ok(expected),
            "padding byte {at:#x}"
        );
        changed[at] ^= 0x01;
    }
}
