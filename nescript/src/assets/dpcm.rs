//! DPCM samples for the APU's delta-modulation channel.
//!
//! The DMC reads sample bytes only from `$C000-$FFFF`. A sample starts
//! on a 64-byte boundary (`$C000 + ($4012 << 6)`) and is
//! `($4013 << 4) + 1` bytes long, so the longest sample is 4081 bytes.
//! The linker stores every sample at the top of the fixed bank, below
//! the vectors and, on MMC3, below the reset stub. Playback is a
//! register write in `play_dpcm`. The audio tick does not advance it.

use crate::parser::ast::{AssetSource, Mapper, Program};
use crate::runtime::MMC3_RESET_STUB_LEN;

/// Longest sample the 8-bit length register can name.
pub const DPCM_MAX_BYTES: usize = 0xFF * 16 + 1;

/// One declared sample, after its bytes have been loaded.
#[derive(Debug, Clone)]
pub struct DpcmSample {
    pub name: String,
    pub rate: u8,
    pub looped: bool,
    pub raw: Vec<u8>,
}

/// A sample laid out in the fixed bank, with the register bytes
/// `play_dpcm` writes.
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct DpcmImage {
    pub name: String,
    /// `$4010`: rate in bits 0-3, loop in bit 6. IRQ stays clear.
    pub reg_4010: u8,
    /// `$4012`: `(address - $C000) >> 6`.
    pub reg_4012: u8,
    /// `$4013`: `(byte_len - 1) >> 4`.
    pub reg_4013: u8,
    /// Offset of the first sample byte in the 16 KB fixed bank.
    pub offset: usize,
    /// Sample bytes, padded with `$00` out to `($4013 << 4) + 1`.
    /// `$00` holds a DAC that has already reached 0.
    pub bytes: Vec<u8>,
}

/// Last fixed-bank offset a sample may use. MMC3 keeps a reset stub
/// in the bytes immediately before the vectors.
#[must_use]
pub fn fixed_bank_limit(mapper: Mapper) -> usize {
    let vectors = 0x3FFA;
    if mapper == Mapper::MMC3 {
        vectors - MMC3_RESET_STUB_LEN
    } else {
        vectors
    }
}

/// Load every `dpcm` declaration. Paths are relative to `source_dir`,
/// the same directory `@chr` and `@binary` use.
pub fn resolve_dpcm(
    program: &Program,
    source_dir: &std::path::Path,
) -> Result<Vec<DpcmSample>, String> {
    let mut out = Vec::new();
    for decl in &program.dpcm {
        let raw = match &decl.source {
            AssetSource::Inline(bytes) => bytes.clone(),
            AssetSource::Binary(path) => {
                let full = source_dir.join(path);
                std::fs::read(&full).map_err(|err| {
                    format!(
                        "dpcm '{}': failed to read {}: {err}",
                        decl.name,
                        full.display()
                    )
                })?
            }
            AssetSource::Chr(path) => {
                return Err(format!(
                    "dpcm '{}': @chr(\"{path}\") is tile data, not a DPCM sample",
                    decl.name
                ));
            }
        };
        if raw.is_empty() {
            return Err(format!("dpcm '{}' has no sample bytes", decl.name));
        }
        out.push(DpcmSample {
            name: decl.name.clone(),
            rate: decl.rate,
            looped: decl.looped,
            raw,
        });
    }
    Ok(out)
}

/// Pack samples from the top of the fixed bank downward. The first
/// declaration sits closest to the vectors. Each sample is padded to
/// a legal DMC length and then aligned down to 64 bytes.
pub fn layout_dpcm(samples: &[DpcmSample], limit: usize) -> Result<Vec<DpcmImage>, String> {
    let mut cursor = limit;
    let mut images = Vec::with_capacity(samples.len());
    for sample in samples {
        if sample.rate > 15 {
            return Err(format!(
                "dpcm '{}': rate {} is outside 0-15",
                sample.name, sample.rate
            ));
        }
        let padded = padded_len(sample.raw.len()).ok_or_else(|| {
            format!(
                "dpcm '{}' is {} bytes; a DMC sample is at most {DPCM_MAX_BYTES} bytes",
                sample.name,
                sample.raw.len()
            )
        })?;
        if padded > cursor {
            return Err(format!(
                "dpcm '{}' needs {padded} bytes and the fixed bank has {cursor} bytes left below the vectors",
                sample.name
            ));
        }
        let start = (cursor - padded) & !63;
        let mut bytes = sample.raw.clone();
        bytes.resize(padded, 0x00);
        let reg_4012 = u8::try_from(start >> 6).expect("DPCM offset fits in $4012");
        let reg_4013 = u8::try_from((padded - 1) / 16).expect("DPCM length fits in $4013");
        let reg_4010 = sample.rate | if sample.looped { 0x40 } else { 0 };
        images.push(DpcmImage {
            name: sample.name.clone(),
            reg_4010,
            reg_4012,
            reg_4013,
            offset: start,
            bytes,
        });
        cursor = start;
    }
    Ok(images)
}

/// Smallest `16 * n + 1` length that can hold `n_bytes`, or `None`
/// when that length would not fit in `$4013`.
fn padded_len(n_bytes: usize) -> Option<usize> {
    if n_bytes == 0 {
        return None;
    }
    let blocks = (n_bytes - 1).div_ceil(16);
    if blocks > 0xFF {
        return None;
    }
    Some(blocks * 16 + 1)
}

#[cfg(test)]
mod tests {
    use super::*;

    fn sample(name: &str, rate: u8, looped: bool, len: usize) -> DpcmSample {
        DpcmSample {
            name: name.to_string(),
            rate,
            looped,
            raw: vec![0xA5; len],
        }
    }

    #[test]
    fn one_byte_sample_lands_on_a_64_byte_boundary_below_the_vectors() {
        let images = layout_dpcm(&[sample("Blip", 15, false, 1)], 0x3FFA).unwrap();
        assert_eq!(images.len(), 1);
        let img = &images[0];
        assert_eq!(img.bytes.len(), 1);
        assert_eq!(img.offset % 64, 0);
        assert!(img.offset + img.bytes.len() <= 0x3FFA);
        assert_eq!(img.reg_4010, 15);
        assert_eq!(img.reg_4012, (img.offset >> 6) as u8);
        assert_eq!(img.reg_4013, 0);
        assert_eq!(
            0xC000 + (usize::from(img.reg_4012) << 6),
            0xC000 + img.offset
        );
    }

    #[test]
    fn loop_flag_sets_bit_6_and_length_pads_to_16_n_plus_1() {
        let images = layout_dpcm(&[sample("Loop", 4, true, 18)], 0x3FFA).unwrap();
        let img = &images[0];
        assert_eq!(img.reg_4010, 0x44);
        assert_eq!(img.bytes.len(), 33);
        assert_eq!(img.reg_4013, 2);
        assert!(img.bytes[18..].iter().all(|&b| b == 0));
    }

    #[test]
    fn two_samples_pack_downward_without_overlapping() {
        let images = layout_dpcm(
            &[sample("A", 1, false, 100), sample("B", 2, false, 50)],
            0x3FFA,
        )
        .unwrap();
        assert!(images[0].offset > images[1].offset);
        let a_end = images[0].offset + images[0].bytes.len();
        assert!(a_end <= 0x3FFA);
        assert!(images[1].offset + images[1].bytes.len() <= images[0].offset);
    }

    #[test]
    fn mmc3_limit_keeps_the_sample_out_of_the_reset_stub() {
        let limit = fixed_bank_limit(Mapper::MMC3);
        assert_eq!(limit, 0x3FFA - MMC3_RESET_STUB_LEN);
        let images = layout_dpcm(&[sample("Voice", 11, false, 200)], limit).unwrap();
        assert!(images[0].offset + images[0].bytes.len() <= limit);
    }

    #[test]
    fn sample_longer_than_the_length_register_is_rejected() {
        let err =
            layout_dpcm(&[sample("Huge", 15, false, DPCM_MAX_BYTES + 1)], 0x3FFA).unwrap_err();
        assert!(err.contains("4081"), "{err}");
    }

    #[test]
    fn sample_that_cannot_fit_under_the_vectors_is_rejected() {
        let err = layout_dpcm(&[sample("Wide", 8, false, 3000)], 100).unwrap_err();
        assert!(err.contains("fixed bank"), "{err}");
    }
}
