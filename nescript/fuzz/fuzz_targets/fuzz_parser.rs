#![no_main]

use libfuzzer_sys::fuzz_target;

fuzz_target!(|data: &[u8]| {
    // The parser must never panic — always produce an AST or diagnostics.
    if let Ok(source) = std::str::from_utf8(data) {
        let _ = nescript::parser::parse(source);
    }
});
