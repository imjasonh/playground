#![no_main]

use libfuzzer_sys::fuzz_target;

fuzz_target!(|data: &[u8]| {
    // The lexer must never panic on any input — always produce tokens or errors.
    if let Ok(source) = std::str::from_utf8(data) {
        let _ = nescript::lexer::lex(source);
    }
});
