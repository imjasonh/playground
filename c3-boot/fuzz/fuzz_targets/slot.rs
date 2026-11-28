//! Fuzzes a whole slot through the same checks the bootloader runs, from the
//! development TUF root with fakestore's identity, at eFuse level 0.

#![no_main]

use libfuzzer_sys::fuzz_target;

const PINNED: &[u8] = include_bytes!("../../testdata/keys/tuf-dev-root.json");
const POLICY: [&str; 5] = c3_ota::tuf_cases::POLICY;

fuzz_target!(|data: &[u8]| {
    let _ = c3_ota::slot::verify(data, PINNED, &POLICY.map(String::from), 0);
});
