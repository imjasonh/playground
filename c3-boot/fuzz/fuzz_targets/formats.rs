//! Fuzzes the slot manifest, image header, and boot-state record decoders.
//! The first byte picks the decoder.

#![no_main]

use libfuzzer_sys::fuzz_target;

fuzz_target!(|data: &[u8]| {
    let Some((&which, rest)) = data.split_first() else {
        return;
    };
    match which % 3 {
        0 => {
            let _ = c3_verify::manifest::parse(rest);
        }
        1 => {
            if let Some((len, header)) = rest.split_first_chunk::<4>() {
                let _ = c3_verify::image::parse(header, u32::from_le_bytes(*len));
            }
        }
        _ => {
            if let Some((a, rest)) = rest.split_first_chunk::<32>() {
                let _ = c3_verify::bootstate::decode(a);
                if let Some((b, _)) = rest.split_first_chunk::<32>() {
                    let current = c3_verify::bootstate::read(a, b);
                    let _ = c3_verify::bootstate::plan(&current.state);
                }
            }
        }
    }
});
