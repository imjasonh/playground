//! Backward Life search: find predecessor grids that evolve into a target.
//!
//! Used to build Z-stacks that **end** in sparse still-life ash (easy near the
//! top) while staying active earlier. Prefer **zero-birth** predecessors when
//! possible: every Life birth is a strict vertical support tip, so histories
//! that mostly shrink/die into ash stay much more supportable.

use crate::config::Config;
use crate::life::Grid;
use crate::seed::still_life_garden;
use rand::Rng;
use rand_chacha::rand_core::SeedableRng;
use rand_chacha::ChaCha8Rng;

/// Births going forward from `pred` → `target` (strict vertical tip count).
pub fn birth_count(pred: &Grid, target: &Grid) -> usize {
    let mut n = 0;
    for y in 0..target.height() {
        for x in 0..target.width() {
            if target.is_alive(x, y) && !pred.is_alive(x, y) {
                n += 1;
            }
        }
    }
    n
}

/// Deaths going forward from `pred` → `target`.
pub fn death_count(pred: &Grid, target: &Grid) -> usize {
    let mut n = 0;
    for y in 0..pred.height() {
        for x in 0..pred.width() {
            if pred.is_alive(x, y) && !target.is_alive(x, y) {
                n += 1;
            }
        }
    }
    n
}

/// Candidate spark cells: dead in `target`, within Chebyshev distance `margin`
/// of at least one live target cell.
fn spark_positions(target: &Grid, margin: isize) -> Vec<(usize, usize)> {
    let w = target.width();
    let h = target.height();
    let mut near = vec![false; w * h];
    for y in 0..h {
        for x in 0..w {
            if !target.is_alive(x, y) {
                continue;
            }
            for dy in -margin..=margin {
                for dx in -margin..=margin {
                    let nx = x as isize + dx;
                    let ny = y as isize + dy;
                    if nx < 0 || ny < 0 || nx >= w as isize || ny >= h as isize {
                        continue;
                    }
                    near[(ny as usize) * w + nx as usize] = true;
                }
            }
        }
    }
    let mut out = Vec::new();
    for y in 0..h {
        for x in 0..w {
            if near[y * w + x] && !target.is_alive(x, y) {
                out.push((x, y));
            }
        }
    }
    out
}

/// Enumerate **zero-birth** predecessors: every live target cell is already
/// alive in the predecessor (no support tips for this layer transition), and
/// optional “spark” cells die away. Returns up to `limit` grids including the
/// trivial still-life predecessor when applicable.
pub fn enumerate_zero_birth_predecessors(target: &Grid, margin: isize, limit: usize) -> Vec<Grid> {
    let w = target.width();
    let h = target.height();
    let sparks = spark_positions(target, margin);
    if sparks.len() > 22 {
        // 2^22 is getting heavy; rely on stochastic search instead.
        return stochastic_zero_birth(target, margin, limit, 0xC0FFEE);
    }

    let mut base = Grid::new(w, h);
    for y in 0..h {
        for x in 0..w {
            if target.is_alive(x, y) {
                base.set(x, y, true);
            }
        }
    }

    let mut out = Vec::new();
    let n = sparks.len();
    let max_mask = 1u32 << n.min(22);
    for mask in 0..max_mask {
        if out.len() >= limit {
            break;
        }
        let mut g = base.clone();
        for (i, &(x, y)) in sparks.iter().enumerate() {
            if (mask >> i) & 1 == 1 {
                g.set(x, y, true);
            }
        }
        if g.step() == *target {
            out.push(g);
        }
    }
    out
}

fn stochastic_zero_birth(target: &Grid, margin: isize, limit: usize, seed: u64) -> Vec<Grid> {
    let sparks = spark_positions(target, margin);
    let w = target.width();
    let h = target.height();
    let mut base = Grid::new(w, h);
    for y in 0..h {
        for x in 0..w {
            if target.is_alive(x, y) {
                base.set(x, y, true);
            }
        }
    }
    let mut out = Vec::new();
    out.push(base.clone()); // trivial
    if sparks.is_empty() {
        return out;
    }
    let mut rng = ChaCha8Rng::seed_from_u64(seed);
    for _ in 0..limit.saturating_mul(40).max(200) {
        if out.len() >= limit {
            break;
        }
        let mut g = base.clone();
        let k = rng.gen_range(1..=sparks.len().clamp(1, 8));
        for _ in 0..k {
            let &(x, y) = &sparks[rng.gen_range(0..sparks.len())];
            g.set(x, y, true);
        }
        if g.step() == *target && !out.contains(&g) {
            out.push(g);
        }
    }
    out
}

/// Pick a predecessor scoring high on: nontrivial, zero/low births, many deaths.
pub fn pick_predecessor(target: &Grid, seed: u64, prefer_zero_birth: bool) -> Option<Grid> {
    let mut rng = ChaCha8Rng::seed_from_u64(seed);
    let mut candidates = enumerate_zero_birth_predecessors(target, 2, 128);
    if candidates.len() < 2 {
        candidates.extend(enumerate_zero_birth_predecessors(target, 1, 128));
    }
    // Dedup
    candidates.sort_by(|a, b| a.cells().cmp(b.cells()));
    candidates.dedup();

    let mut best: Option<(i32, Grid)> = None;
    for g in candidates {
        if g.step() != *target {
            continue;
        }
        let births = birth_count(&g, target) as i32;
        if prefer_zero_birth && births > 0 {
            continue;
        }
        let deaths = death_count(&g, target) as i32;
        let nontrivial = (g != *target) as i32;
        let score = nontrivial * 10_000 - births * 200 + deaths * 30 - (g.live_count() as i32)
            + rng.gen_range(0..7);
        if best.as_ref().map(|(s, _)| score > *s).unwrap_or(true) {
            best = Some((score, g));
        }
    }
    best.map(|(_, g)| g)
}

/// Build a generation chain of length `depth` ending at still-life ash.
///
/// Index 0 is generation 0 (bottom / early time); `depth-1` is the ash (top).
/// Walks backward from ash, preferring zero-birth predecessors. When the
/// reverse walk stalls, pads remaining **top** layers with ash (still life) so
/// the chain stays forward-consistent — never duplicates a non-stable grid.
pub fn build_reverse_chain(width: usize, height: usize, depth: usize, seed: u64) -> Vec<Grid> {
    let density = 0.12;
    let ash = still_life_garden(width, height, seed, density);
    debug_assert_eq!(ash.step(), ash, "ash must be still life");

    // `late_to_early`: [ash, pred1, pred2, ...] while reverse-walking.
    let mut late_to_early = vec![ash.clone()];
    let mut current = ash.clone();
    for step in 0..depth.saturating_sub(1) {
        match pick_predecessor(&current, seed.wrapping_add(step as u64 * 7919 + 1), true) {
            Some(pred) if pred != current && pred.step() == current => {
                current = pred;
                late_to_early.push(current.clone());
            }
            _ => break, // no further zero-birth history
        }
    }

    late_to_early.reverse(); // early → late, ending at ash
    while late_to_early.len() < depth {
        late_to_early.push(ash.clone());
    }
    late_to_early.truncate(depth);
    late_to_early
}

/// Generation-0 grid for `--pattern reverse` (bottom of the stack).
pub fn reverse_initial_grid(config: &Config) -> Grid {
    let chain = build_reverse_chain(config.width, config.height, config.depth, config.seed);
    chain
        .into_iter()
        .next()
        .unwrap_or_else(|| Grid::new(config.width, config.height))
}

/// Full generation chain for reverse mode (length = depth).
pub fn reverse_generation_chain(config: &Config) -> Vec<Grid> {
    build_reverse_chain(config.width, config.height, config.depth, config.seed)
}

/// Paint a precomputed generation chain into a Life|Base volume.
pub fn volume_from_chain(chain: &[Grid], base_layers: usize) -> crate::volume::Volume {
    assert!(!chain.is_empty());
    let w = chain[0].width();
    let h = chain[0].height();
    let depth = chain.len();
    let mut volume = crate::volume::Volume::new(w, h, base_layers + depth);
    for z in 0..base_layers {
        for y in 0..h {
            for x in 0..w {
                volume.set(x, y, z, crate::volume::CellKind::Base);
            }
        }
    }
    for (zi, g) in chain.iter().enumerate() {
        for y in 0..h {
            for x in 0..w {
                if g.is_alive(x, y) {
                    volume.set(x, y, base_layers + zi, crate::volume::CellKind::Life);
                }
            }
        }
    }
    volume
}

#[cfg(test)]
mod tests {
    use super::*;

    fn block() -> Grid {
        let mut g = Grid::new(8, 8);
        g.set(3, 3, true);
        g.set(4, 3, true);
        g.set(3, 4, true);
        g.set(4, 4, true);
        g
    }

    #[test]
    fn block_has_zero_birth_predecessors_with_sparks() {
        let b = block();
        let preds = enumerate_zero_birth_predecessors(&b, 2, 100);
        assert!(preds.iter().any(|p| p == &b), "trivial predecessor");
        let nontrivial: Vec<_> = preds.into_iter().filter(|p| p != &b).collect();
        assert!(
            !nontrivial.is_empty(),
            "expected spark predecessors of a block"
        );
        for p in &nontrivial {
            assert_eq!(p.step(), b);
            assert_eq!(birth_count(p, &b), 0);
            assert!(death_count(p, &b) > 0);
        }
    }

    #[test]
    fn reverse_chain_is_forward_consistent() {
        let chain = build_reverse_chain(12, 12, 16, 7);
        assert_eq!(chain.len(), 16);
        for i in 0..chain.len() - 1 {
            assert_eq!(chain[i].step(), chain[i + 1], "break at generation {i}");
        }
        // Top should be still life.
        let top = chain.last().unwrap();
        assert_eq!(top.step(), *top);
    }
}
