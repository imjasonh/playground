//! Pixelation and bit-plane packing, kept generic (no panel-sized constants)
//! so both can be unit-tested at a size much smaller than 800×480.

use super::Shade;

/// Expand a `logical_w`×`logical_h` grid of shades into a
/// `(logical_w*block)`×`(logical_h*block)` grid, repeating each logical
/// pixel as a `block`×`block` square, row-major.
pub fn pixelate(logical_w: usize, logical_h: usize, block: usize, logical: &[Shade]) -> Vec<Shade> {
    assert_eq!(
        logical.len(),
        logical_w * logical_h,
        "logical buffer does not match logical_w*logical_h"
    );
    assert!(block >= 1, "block must be at least 1");

    let physical_w = logical_w * block;
    let mut out = vec![Shade::White; physical_w * logical_h * block];
    for ly in 0..logical_h {
        for lx in 0..logical_w {
            let shade = logical[ly * logical_w + lx];
            for dy in 0..block {
                let py = ly * block + dy;
                let row_start = py * physical_w + lx * block;
                out[row_start..row_start + block].fill(shade);
            }
        }
    }
    out
}

/// Pack a flat shade grid into the two 1-bit `(old, new)` planes the UC8179
/// takes on `DTM1`/`DTM2`, MSB-first. `physical.len()` must be a multiple of
/// 8 (true for any panel-sized frame: `PANEL_WIDTH` is byte-aligned).
pub fn pack_4gray_planes(physical: &[Shade]) -> (Vec<u8>, Vec<u8>) {
    assert_eq!(
        physical.len() % 8,
        0,
        "shade count must be a whole number of bytes"
    );
    let bytes = physical.len() / 8;
    let mut old = vec![0u8; bytes];
    let mut new = vec![0u8; bytes];
    for (i, shade) in physical.iter().enumerate() {
        let (old_bit, new_bit) = shade.plane_bits();
        let byte = i / 8;
        let bit = 0x80u8 >> (i % 8);
        if old_bit {
            old[byte] |= bit;
        }
        if new_bit {
            new[byte] |= bit;
        }
    }
    (old, new)
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn pixelate_repeats_each_logical_pixel_as_a_block() {
        // 2×1 logical grid, block=2 -> 4×2 physical grid.
        let logical = [Shade::Black, Shade::White];
        let physical = pixelate(2, 1, 2, &logical);
        assert_eq!(physical.len(), 8);
        // Row 0: B B W W; row 1: B B W W.
        assert_eq!(
            physical,
            vec![
                Shade::Black,
                Shade::Black,
                Shade::White,
                Shade::White,
                Shade::Black,
                Shade::Black,
                Shade::White,
                Shade::White,
            ]
        );
    }

    #[test]
    fn pixelate_block_one_is_identity() {
        let logical = [Shade::Gray1, Shade::Gray2, Shade::Black, Shade::White];
        let physical = pixelate(2, 2, 1, &logical);
        assert_eq!(physical, logical);
    }

    #[test]
    #[should_panic(expected = "logical buffer does not match")]
    fn pixelate_rejects_mismatched_buffer_length() {
        let logical = [Shade::White; 3];
        let _ = pixelate(2, 2, 1, &logical);
    }

    #[test]
    fn pack_all_white_is_all_zero_planes() {
        let physical = vec![Shade::White; 16];
        let (old, new) = pack_4gray_planes(&physical);
        assert_eq!(old, vec![0u8; 2]);
        assert_eq!(new, vec![0u8; 2]);
    }

    #[test]
    fn pack_all_black_is_all_one_planes() {
        let physical = vec![Shade::Black; 16];
        let (old, new) = pack_4gray_planes(&physical);
        assert_eq!(old, vec![0xFFu8; 2]);
        assert_eq!(new, vec![0xFFu8; 2]);
    }

    #[test]
    fn pack_matches_hand_computed_bytes_for_a_mixed_row() {
        // W B G1 G2 W B G1 G2 -> old bits 0,1,1,0,0,1,1,0 = 0b01100110 = 0x66
        //                     -> new bits 0,1,0,1,0,1,0,1 = 0b01010101 = 0x55
        let row = [
            Shade::White,
            Shade::Black,
            Shade::Gray1,
            Shade::Gray2,
            Shade::White,
            Shade::Black,
            Shade::Gray1,
            Shade::Gray2,
        ];
        let (old, new) = pack_4gray_planes(&row);
        assert_eq!(old, vec![0x66]);
        assert_eq!(new, vec![0x55]);
    }

    #[test]
    fn pack_byte_count_is_pixel_count_over_eight() {
        let physical = vec![Shade::Gray1; 800 * 8];
        let (old, new) = pack_4gray_planes(&physical);
        assert_eq!(old.len(), 800);
        assert_eq!(new.len(), 800);
    }
}
