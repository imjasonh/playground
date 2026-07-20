use rand::Rng;
use rand_chacha::rand_core::SeedableRng;
use rand_chacha::ChaCha8Rng;

use crate::config::{Config, Pattern};
use crate::life::Grid;

/// Build generation 0 from the config's pattern and seed.
pub fn initial_grid(config: &Config) -> Grid {
    match config.pattern {
        Pattern::Random => random_grid(config.width, config.height, config.seed, config.density),
        Pattern::Glider => place_pattern(config.width, config.height, &GLIDER, 1, 1),
        Pattern::Rpento => place_pattern(config.width, config.height, &R_PENTOMINO, 2, 2),
        Pattern::Blinker => place_pattern(config.width, config.height, &BLINKER, 1, 1),
        Pattern::Lwss => place_pattern(config.width, config.height, &LWSS, 1, 2),
    }
}

fn random_grid(width: usize, height: usize, seed: u64, density: f64) -> Grid {
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

/// Rows of a pattern; `O` / `x` / `1` / `#` = live, anything else = dead.
fn place_pattern(width: usize, height: usize, rows: &[&str], ox: usize, oy: usize) -> Grid {
    let mut grid = Grid::new(width, height);
    for (dy, row) in rows.iter().enumerate() {
        for (dx, ch) in row.chars().enumerate() {
            let live = matches!(ch, 'O' | 'o' | 'X' | 'x' | '1' | '#' | '*');
            if !live {
                continue;
            }
            let x = ox + dx;
            let y = oy + dy;
            if x < width && y < height {
                grid.set(x, y, true);
            }
        }
    }
    grid
}

const GLIDER: [&str; 3] = ["010", "001", "111"];
const R_PENTOMINO: [&str; 3] = [".OO", "OO.", ".O."];
const BLINKER: [&str; 1] = ["OOO"];
const LWSS: [&str; 4] = [".O..O", "O....", "O...O", "OOOO."];

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn random_is_deterministic() {
        let a = random_grid(16, 16, 42, 0.35);
        let b = random_grid(16, 16, 42, 0.35);
        assert_eq!(a, b);
        let c = random_grid(16, 16, 43, 0.35);
        assert_ne!(a, c);
    }

    #[test]
    fn glider_has_five_cells() {
        let g = place_pattern(10, 10, &GLIDER, 1, 1);
        assert_eq!(g.live_count(), 5);
    }
}
