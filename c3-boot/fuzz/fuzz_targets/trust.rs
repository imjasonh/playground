//! Fuzzes key-set chain and trust-root blob parsing and verification
//! against the development genesis keys. The first two bytes give the
//! chain's length; the rest is the chain, then the blob.

#![no_main]

use c3_verify::keys::KeySet;
use libfuzzer_sys::fuzz_target;

const GENESIS: &[u8; 128] = include_bytes!("../../testdata/keys/genesis-dev.pub");

fuzz_target!(|data: &[u8]| {
    let Some((len, rest)) = data.split_first_chunk::<2>() else {
        return;
    };
    let split = usize::from(u16::from_le_bytes(*len)).min(rest.len());
    let (chain, blob) = rest.split_at(split);
    let mut scratch = [0u8; 4_120];
    let Ok(genesis) = KeySet::new(GENESIS) else {
        return;
    };
    let Ok(chain) = c3_verify::chain::parse(chain) else {
        return;
    };
    let Ok(tip) = c3_verify::chain::verify(&chain, genesis, &mut scratch) else {
        return;
    };
    if let Ok(root) = c3_verify::trustroot::parse(blob) {
        let _ = c3_verify::trustroot::verify(&root, &tip, &mut scratch);
    }
});
