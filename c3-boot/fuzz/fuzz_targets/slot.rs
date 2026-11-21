//! Fuzzes a whole slot through the same checks the bootloader runs, with
//! the development genesis keys at eFuse level 0.

#![no_main]

use libfuzzer_sys::fuzz_target;

const GENESIS: &[u8; 128] = include_bytes!("../../testdata/keys/genesis-dev.pub");

fuzz_target!(|data: &[u8]| {
    let _ = c3_ota::slot::verify(data, GENESIS, 0);
});
