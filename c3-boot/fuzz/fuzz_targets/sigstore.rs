//! Fuzzes the bundle container and the Sigstore checks behind it: the leaf
//! certificate, the timestamp token, the checkpoint, and the inclusion
//! proof, against a fixed trust root built from the mutation-test fixtures.

#![no_main]

use std::sync::OnceLock;

use c3_ota::blob::TrustRootSpec;
use c3_ota::blob::signed_blob;
use c3_ota::keys::read_signing_key;
use libfuzzer_sys::fuzz_target;

const ROOT: &str = concat!(env!("CARGO_MANIFEST_DIR"), "/../testdata");

fn blob() -> &'static [u8] {
    static BLOB: OnceLock<Vec<u8>> = OnceLock::new();
    BLOB.get_or_init(|| {
        let json = std::fs::read_to_string(format!("{ROOT}/mutation/trusted_root.json"))
            .expect("the fixture trusted root exists");
        let policy = [
            "https://token.actions.githubusercontent.com".to_string(),
            "https://github.com/imjasonh/playground/.github/workflows/c3-release.yml@refs/heads/main"
                .to_string(),
            "1234".to_string(),
            "5678".to_string(),
            "push".to_string(),
        ];
        let spec = TrustRootSpec::from_trusted_root(&json, 0, policy).expect("the root converts");
        let k1 = read_signing_key(&format!("{ROOT}/keys/genesis-dev-1.seed")).expect("seed 1");
        let k2 = read_signing_key(&format!("{ROOT}/keys/genesis-dev-2.seed")).expect("seed 2");
        signed_blob(&spec, &[(0, &k1), (1, &k2)]).expect("the blob signs")
    })
}

fn image_digest() -> &'static [u8; 32] {
    static DIGEST: OnceLock<[u8; 32]> = OnceLock::new();
    DIGEST.get_or_init(|| {
        let image = std::fs::read(format!("{ROOT}/mutation/image.bin"))
            .expect("the fixture image exists");
        c3_crypto::sha256(&image)
    })
}

fuzz_target!(|data: &[u8]| {
    let Ok(root) = c3_verify::trustroot::parse(blob()) else {
        return;
    };
    let Ok(bundle) = c3_verify::bundle::parse(data) else {
        return;
    };
    let _ = c3_verify::x509::parse_leaf(bundle.leaf_certificate);
    let _ = c3_verify::tsa::parse_timestamp(bundle.timestamp);
    let _ = c3_verify::checkpoint::verify(bundle.checkpoint, &root);
    // The seed bundle signs the fixture image, so mutations of it reach the
    // checks after the image signature.
    let _ = c3_verify::sigstore::verify(&bundle, &root, image_digest());
});
