//! Turning a grid of grey targets into a grid of die choices.
//!
//! The palette a die mosaic offers is not evenly spaced — a black die can only
//! be so bright, a white die only so dark — so quantisation picks the nearest
//! available tone rather than rounding to a fixed step, and error diffusion
//! carries the leftover into cells that have not been decided yet.

/// How the leftover tone of a cell is handled.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum Dither {
    /// Snap each cell to its nearest tone; posterised, no diffusion.
    None,
    /// Floyd-Steinberg.
    Floyd,
    /// Atkinson: only 3/4 of the error is passed on, for a punchier picture.
    Atkinson,
    /// Jarvis, Judice and Ninke: wide kernel, smooth gradients.
    Jarvis,
    /// Sierra Lite: cheap and tight.
    SierraLite,
    /// Ordered 8x8 Bayer threshold; a regular, printed-looking texture.
    Bayer,
}

impl Dither {
    /// Error distribution kernel as `(dx, dy, weight)`, for the diffusing
    /// modes. `dx` is mirrored automatically on right-to-left rows.
    fn kernel(self) -> &'static [(i32, i32, f32)] {
        const S16: f32 = 1.0 / 16.0;
        const S8: f32 = 1.0 / 8.0;
        const S48: f32 = 1.0 / 48.0;
        const S4: f32 = 1.0 / 4.0;
        match self {
            Dither::None | Dither::Bayer => &[],
            Dither::Floyd => &[
                (1, 0, 7.0 * S16),
                (-1, 1, 3.0 * S16),
                (0, 1, 5.0 * S16),
                (1, 1, S16),
            ],
            Dither::Atkinson => &[
                (1, 0, S8),
                (2, 0, S8),
                (-1, 1, S8),
                (0, 1, S8),
                (1, 1, S8),
                (0, 2, S8),
            ],
            Dither::Jarvis => &[
                (1, 0, 7.0 * S48),
                (2, 0, 5.0 * S48),
                (-2, 1, 3.0 * S48),
                (-1, 1, 5.0 * S48),
                (0, 1, 7.0 * S48),
                (1, 1, 5.0 * S48),
                (2, 1, 3.0 * S48),
                (-2, 2, S48),
                (-1, 2, 3.0 * S48),
                (0, 2, 5.0 * S48),
                (1, 2, 3.0 * S48),
                (2, 2, S48),
            ],
            Dither::SierraLite => &[(1, 0, 2.0 * S4), (-1, 1, S4), (0, 1, S4)],
        }
    }
}

/// Index into a sorted tone palette, one per grid cell.
pub type Choices = Vec<usize>;

/// Quantise `grid` (row-major grey targets) against `levels`, a palette of
/// achievable greys sorted ascending. Returns the chosen level per cell.
///
/// Targets are clamped to the palette's range before the error is measured, so
/// a region darker than the darkest die cannot accumulate a debt that smears
/// across the rest of the picture.
pub fn quantize(
    grid: &[f32],
    cols: usize,
    rows: usize,
    levels: &[f32],
    mode: Dither,
    serpentine: bool,
) -> Choices {
    assert!(!levels.is_empty(), "palette must not be empty");
    assert_eq!(
        grid.len(),
        cols * rows,
        "grid does not match its dimensions"
    );

    if mode == Dither::Bayer {
        return grid
            .iter()
            .enumerate()
            .map(|(i, &v)| ordered_pick(levels, v, i % cols, i / cols))
            .collect();
    }

    let lo = levels[0];
    let hi = levels[levels.len() - 1];
    let kernel = mode.kernel();
    let mut buf = grid.to_vec();
    let mut out = vec![0usize; grid.len()];

    for y in 0..rows {
        let left_to_right = !serpentine || y % 2 == 0;
        for i in 0..cols {
            let x = if left_to_right { i } else { cols - 1 - i };
            let idx = y * cols + x;
            let target = buf[idx].clamp(lo, hi);
            let pick = nearest(levels, target);
            out[idx] = pick;

            let error = target - levels[pick];
            for &(dx, dy, weight) in kernel {
                let dx = if left_to_right { dx } else { -dx };
                let (nx, ny) = (x as i32 + dx, y as i32 + dy);
                if nx < 0 || ny < 0 || nx >= cols as i32 || ny >= rows as i32 {
                    continue;
                }
                buf[ny as usize * cols + nx as usize] += error * weight;
            }
        }
    }
    out
}

/// Index of the palette entry closest to `target`.
pub fn nearest(levels: &[f32], target: f32) -> usize {
    let mut best = 0;
    let mut best_d = f32::INFINITY;
    for (i, &level) in levels.iter().enumerate() {
        let d = (level - target).abs();
        if d < best_d {
            best_d = d;
            best = i;
        }
    }
    best
}

/// Ordered dithering: pick between the two palette entries that bracket
/// `target` using the Bayer threshold for this cell.
fn ordered_pick(levels: &[f32], target: f32, x: usize, y: usize) -> usize {
    let target = target.clamp(levels[0], levels[levels.len() - 1]);
    let upper = levels.iter().position(|&l| l >= target).unwrap_or(0);
    if upper == 0 {
        return 0;
    }
    let (lo, hi) = (levels[upper - 1], levels[upper]);
    let fraction = if hi > lo {
        (target - lo) / (hi - lo)
    } else {
        0.0
    };
    if fraction > bayer8(x, y) {
        upper
    } else {
        upper - 1
    }
}

/// 8x8 Bayer threshold in `[0, 1)`.
pub fn bayer8(x: usize, y: usize) -> f32 {
    bayer(x % 8, y % 8, 3) as f32 / 64.0
}

/// Recursive Bayer construction: each order quadruples the previous matrix and
/// offsets its quadrants by 0, 2, 3, 1.
fn bayer(x: usize, y: usize, order: u32) -> u32 {
    if order == 0 {
        return 0;
    }
    let half = 1 << (order - 1);
    let quadrant = match (x >= half, y >= half) {
        (false, false) => 0,
        (true, false) => 2,
        (false, true) => 3,
        (true, true) => 1,
    };
    4 * bayer(x % half, y % half, order - 1) + quadrant
}

#[cfg(test)]
mod tests {
    use super::*;

    const LEVELS: [f32; 4] = [0.1, 0.3, 0.7, 0.9];

    #[test]
    fn kernels_are_normalised_or_deliberately_lossy() {
        for mode in [Dither::Floyd, Dither::Jarvis, Dither::SierraLite] {
            let sum: f32 = mode.kernel().iter().map(|k| k.2).sum();
            assert!((sum - 1.0).abs() < 1e-5, "{mode:?} sums to {sum}");
        }
        let atkinson: f32 = Dither::Atkinson.kernel().iter().map(|k| k.2).sum();
        assert!((atkinson - 0.75).abs() < 1e-5);
    }

    #[test]
    fn kernels_only_push_error_into_undecided_cells() {
        for mode in [
            Dither::Floyd,
            Dither::Atkinson,
            Dither::Jarvis,
            Dither::SierraLite,
        ] {
            for &(dx, dy, _) in mode.kernel() {
                assert!(dy > 0 || (dy == 0 && dx > 0), "{mode:?} looks backwards");
            }
        }
    }

    #[test]
    fn nearest_picks_the_closest_level() {
        assert_eq!(nearest(&LEVELS, 0.0), 0);
        assert_eq!(nearest(&LEVELS, 0.29), 1);
        assert_eq!(nearest(&LEVELS, 0.51), 2);
        assert_eq!(nearest(&LEVELS, 5.0), 3);
    }

    #[test]
    fn without_dithering_every_cell_snaps_to_its_own_nearest() {
        let grid = vec![0.0, 0.31, 0.69, 1.0];
        let out = quantize(&grid, 4, 1, &LEVELS, Dither::None, false);
        assert_eq!(out, vec![0, 1, 2, 3]);
    }

    #[test]
    fn diffusion_reproduces_a_tone_the_palette_cannot_hit() {
        // 0.5 sits exactly in the palette's hole between 0.3 and 0.7.
        for mode in [
            Dither::Floyd,
            Dither::Atkinson,
            Dither::Jarvis,
            Dither::SierraLite,
            Dither::Bayer,
        ] {
            let grid = vec![0.5f32; 64 * 64];
            let out = quantize(&grid, 64, 64, &LEVELS, mode, true);
            let mean: f32 = out.iter().map(|&i| LEVELS[i]).sum::<f32>() / out.len() as f32;
            assert!((mean - 0.5).abs() < 0.02, "{mode:?} averaged {mean}");
            assert!(out.contains(&1) && out.contains(&2));
        }
    }

    #[test]
    fn diffusion_tracks_a_gradient() {
        let (cols, rows) = (64, 64);
        let grid: Vec<f32> = (0..cols * rows)
            .map(|i| (i % cols) as f32 / (cols - 1) as f32)
            .collect();
        let out = quantize(&grid, cols, rows, &LEVELS, Dither::Floyd, true);
        let column_mean =
            |c: usize| (0..rows).map(|r| LEVELS[out[r * cols + c]]).sum::<f32>() / rows as f32;
        assert!(column_mean(2) < column_mean(cols / 2));
        assert!(column_mean(cols / 2) < column_mean(cols - 3));
    }

    #[test]
    fn out_of_range_tones_do_not_smear_into_their_neighbours() {
        // A black block next to a white block: with the error clamped, the
        // white block must come out entirely white.
        let (cols, rows) = (16, 4);
        let grid: Vec<f32> = (0..cols * rows)
            .map(|i| if i % cols < 8 { -3.0 } else { 0.9 })
            .collect();
        let out = quantize(&grid, cols, rows, &LEVELS, Dither::Floyd, true);
        for r in 0..rows {
            for c in 8..cols {
                assert_eq!(out[r * cols + c], 3, "cell {c},{r} was dragged dark");
            }
        }
    }

    #[test]
    fn bayer_matrix_covers_every_threshold_once() {
        let mut seen: Vec<f32> = (0..8)
            .flat_map(|y| (0..8).map(move |x| bayer8(x, y)))
            .collect();
        seen.sort_by(|a, b| a.partial_cmp(b).unwrap());
        seen.dedup();
        assert_eq!(seen.len(), 64);
        assert!(seen.iter().all(|v| (0.0..1.0).contains(v)));
    }

    #[test]
    fn serpentine_and_raster_order_both_hit_the_average() {
        let grid = vec![0.42f32; 40 * 40];
        for serpentine in [false, true] {
            let out = quantize(&grid, 40, 40, &LEVELS, Dither::Floyd, serpentine);
            let mean: f32 = out.iter().map(|&i| LEVELS[i]).sum::<f32>() / out.len() as f32;
            assert!(
                (mean - 0.42).abs() < 0.02,
                "serpentine={serpentine}: {mean}"
            );
        }
    }
}
