use rand::Rng;
use rand_chacha::rand_core::SeedableRng;
use rand_chacha::ChaCha8Rng;

use crate::config::{Config, Pattern};
use crate::life::Grid;

/// Build generation 0 from the config's pattern and seed.
pub fn initial_grid(config: &Config) -> Grid {
    match config.pattern {
        // Default: sparse still-life garden — stable forever, so the Z-stack is
        // vertical columns face-connected to the bed (usually no supports needed).
        Pattern::Random => {
            still_life_garden(config.width, config.height, config.seed, config.density)
        }
        // Classic Bernoulli soup — chaotic, often leaves orphans after support removal.
        Pattern::Soup => soup_grid(config.width, config.height, config.seed, config.density),
        Pattern::Glider => place_pattern(config.width, config.height, &GLIDER, 1, 1),
        Pattern::Rpento => place_pattern(config.width, config.height, &R_PENTOMINO, 2, 2),
        Pattern::Blinker => place_pattern(config.width, config.height, &BLINKER, 1, 1),
        Pattern::Lwss => place_pattern(config.width, config.height, &LWSS, 1, 2),
    }
}

fn soup_grid(width: usize, height: usize, seed: u64, density: f64) -> Grid {
    let density = density.clamp(0.0, 1.0);
    let mut rng = ChaCha8Rng::seed_from_u64(seed);
    let mut grid = Grid::new(width, height);
    for y in 0..height {
        for x in 0..width {
            grid.set(x, y, rng.gen::<f64>() < density);
        }
    }
    grid
}

/// Pack still lifes with Chebyshev gap ≥ 2 between any live cells of different
/// objects (no neighbor interaction → pattern stays stable).
fn still_life_garden(width: usize, height: usize, seed: u64, density: f64) -> Grid {
    let density = density.clamp(0.0, 1.0);
    let mut rng = ChaCha8Rng::seed_from_u64(seed);
    let mut grid = Grid::new(width, height);
    // forbidden[i] = cannot place a new live cell here (near an existing one).
    let mut forbidden = vec![false; width * height];
    let target = ((width * height) as f64 * density).round() as usize;
    if target == 0 {
        return grid;
    }

    let stamps: &[&[&str]] = &[&BLOCK, &TUB, &BEEHIVE, &BOAT];
    let mut guard = 0usize;
    while grid.live_count() < target && guard < target.saturating_mul(50).max(50) {
        guard += 1;
        let stamp = stamps[rng.gen_range(0..stamps.len())];
        let sw = stamp[0].len();
        let sh = stamp.len();
        if sw > width || sh > height {
            continue;
        }
        let x0 = rng.gen_range(0..=width - sw);
        let y0 = rng.gen_range(0..=height - sh);
        if !stamp_fits(&forbidden, width, height, stamp, x0, y0) {
            continue;
        }
        paint(&mut grid, stamp, x0, y0);
        mark_forbidden(&mut forbidden, width, height, stamp, x0, y0);
    }
    grid
}

fn stamp_fits(
    forbidden: &[bool],
    width: usize,
    height: usize,
    stamp: &[&str],
    ox: usize,
    oy: usize,
) -> bool {
    for (dy, row) in stamp.iter().enumerate() {
        for (dx, ch) in row.chars().enumerate() {
            if !matches!(ch, 'O' | 'o' | 'X' | 'x' | '1' | '#' | '*') {
                continue;
            }
            let x = ox + dx;
            let y = oy + dy;
            if x >= width || y >= height || forbidden[y * width + x] {
                return false;
            }
        }
    }
    true
}

/// After placing a stamp, forbid a Chebyshev radius-2 neighborhood around every
/// live cell. That keeps distinct objects at distance ≥ 3 so they cannot share
/// a neighbor cell (distance 2 is enough to *touch* the same empty cell and
/// cause births across the gap).
fn mark_forbidden(
    forbidden: &mut [bool],
    width: usize,
    height: usize,
    stamp: &[&str],
    ox: usize,
    oy: usize,
) {
    for (dy, row) in stamp.iter().enumerate() {
        for (dx, ch) in row.chars().enumerate() {
            if !matches!(ch, 'O' | 'o' | 'X' | 'x' | '1' | '#' | '*') {
                continue;
            }
            let cx = ox + dx;
            let cy = oy + dy;
            for yy in cy.saturating_sub(2)..=(cy + 2).min(height - 1) {
                for xx in cx.saturating_sub(2)..=(cx + 2).min(width - 1) {
                    forbidden[yy * width + xx] = true;
                }
            }
        }
    }
}

fn paint(grid: &mut Grid, rows: &[&str], ox: usize, oy: usize) {
    for (dy, row) in rows.iter().enumerate() {
        for (dx, ch) in row.chars().enumerate() {
            if matches!(ch, 'O' | 'o' | 'X' | 'x' | '1' | '#' | '*') {
                let x = ox + dx;
                let y = oy + dy;
                if x < grid.width() && y < grid.height() {
                    grid.set(x, y, true);
                }
            }
        }
    }
}

/// Rows of a pattern; `O` / `x` / `1` / `#` = live, anything else = dead.
fn place_pattern(width: usize, height: usize, rows: &[&str], ox: usize, oy: usize) -> Grid {
    let mut grid = Grid::new(width, height);
    paint(&mut grid, rows, ox, oy);
    grid
}

const BLOCK: [&str; 2] = ["OO", "OO"];
const TUB: [&str; 3] = [".O.", "O.O", ".O."];
const BEEHIVE: [&str; 3] = [".OO.", "O..O", ".OO."];
const BOAT: [&str; 3] = ["OO.", "O.O", ".O."];

const GLIDER: [&str; 3] = ["010", "001", "111"];
const R_PENTOMINO: [&str; 3] = [".OO", "OO.", ".O."];
const BLINKER: [&str; 1] = ["OOO"];
const LWSS: [&str; 4] = [".O..O", "O....", "O...O", "OOOO."];

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn soup_is_deterministic() {
        let a = soup_grid(16, 16, 42, 0.35);
        let b = soup_grid(16, 16, 42, 0.35);
        assert_eq!(a, b);
        let c = soup_grid(16, 16, 43, 0.35);
        assert_ne!(a, c);
    }

    #[test]
    fn garden_is_deterministic_and_stable() {
        let g = still_life_garden(24, 24, 7, 0.25);
        assert!(g.live_count() > 0);
        assert_eq!(g.step(), g, "still-life garden must be stable");
        let g2 = still_life_garden(24, 24, 7, 0.25);
        assert_eq!(g, g2);
    }

    #[test]
    fn glider_has_five_cells() {
        let g = place_pattern(10, 10, &GLIDER, 1, 1);
        assert_eq!(g.live_count(), 5);
    }
}
