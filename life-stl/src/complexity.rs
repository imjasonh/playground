//! Evolution “interestingness” gate: reject shapes that go quiescent too early.
//!
//! A stack that becomes a still life (or short-period oscillator) after only a
//! few generations is a boring extruded tower for most of its height. Seed
//! search / CLI exit codes treat that the same way as hard-to-remove supports.
//!
//! Still-life gardens (`Pattern::Random`) are exempt — stability is the point.

use crate::config::{ComplexityParams, Pattern};
use crate::life::Grid;
use crate::seed::initial_grid;
use crate::Config;

/// Verdict for how long a Life run stays non-quiescent.
#[derive(Debug, Clone, PartialEq)]
pub struct ComplexityReport {
    /// True when the run stays active long enough (or the pattern is exempt).
    pub ok: bool,
    /// First generation index that belongs to a still life / boring cycle
    /// (or `depth` if none appears within the stacked generations).
    pub quiescent_generation: usize,
    /// Attractor period once quiescent (`1` = still life, `2` = blinker-like,
    /// `0` = never settled inside the stack).
    pub period: usize,
    /// Distinct grids observed before the first repeat.
    pub unique_states: usize,
    /// Required quiescent generation (from depth + params).
    pub required_active_generations: usize,
    /// Human reasons when `ok` is false.
    pub reasons: Vec<String>,
}

impl Default for ComplexityReport {
    fn default() -> Self {
        Self {
            ok: true,
            quiescent_generation: 0,
            period: 0,
            unique_states: 0,
            required_active_generations: 0,
            reasons: Vec::new(),
        }
    }
}

/// Minimum generation index at which quiescence is allowed.
pub fn required_active_generations(depth: usize, params: &ComplexityParams) -> usize {
    let from_frac = (depth as f32 * params.min_active_fraction).ceil() as usize;
    params.min_active_generations.max(from_frac).min(depth)
}

/// Simulate the configured pattern and score whether it stays interesting.
pub fn analyze_complexity(config: &Config) -> ComplexityReport {
    let required = required_active_generations(config.depth, &config.complexity);
    let (quiescent, period, unique) = simulate_quiescence(config);

    // Still-life gardens are intentionally static through Z.
    if config.pattern == Pattern::Random {
        return ComplexityReport {
            ok: true,
            quiescent_generation: quiescent,
            period,
            unique_states: unique,
            required_active_generations: required,
            reasons: Vec::new(),
        };
    }

    let boring_period = period > 0 && period <= config.complexity.max_boring_period;
    let too_early = boring_period && quiescent < required;
    let mut reasons = Vec::new();
    if too_early {
        let kind = match period {
            1 => "still life",
            _ => "short-period oscillator",
        };
        reasons.push(format!(
            "pattern becomes a {kind} (period {period}) at generation {quiescent}, \
             need activity until generation ≥ {required} \
             ({:.0}% of {depth} generations, min {})",
            config.complexity.min_active_fraction * 100.0,
            config.complexity.min_active_generations,
            depth = config.depth
        ));
    }

    ComplexityReport {
        ok: !too_early,
        quiescent_generation: quiescent,
        period,
        unique_states: unique,
        required_active_generations: required,
        reasons,
    }
}

/// Walk generations until a repeat; return `(quiescent_gen, period, unique)`.
fn simulate_quiescence(config: &Config) -> (usize, usize, usize) {
    let mut grid = initial_grid(config);
    let mut seen: Vec<Grid> = vec![grid.clone()];
    for t in 1..config.depth {
        grid = grid.step();
        if let Some(prev) = seen.iter().position(|s| s == &grid) {
            let period = t - prev;
            return (prev, period, seen.len());
        }
        seen.push(grid.clone());
    }
    (config.depth, 0, seen.len())
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::config::{ComplexityParams, Pattern, SupportMode};

    fn soup_config(seed: u64, density: f64) -> Config {
        Config {
            width: 16,
            height: 16,
            depth: 24,
            seed,
            density,
            pattern: Pattern::Soup,
            mode: SupportMode::Breakaway,
            cell_mm: 4.0,
            ..Config::default()
        }
    }

    #[test]
    fn early_stable_soups_fail_complexity() {
        // Low-density soups that settle into still lifes within ~4 generations
        // must be rejected — most of the printed height would be a static tower.
        let seeds = [
            (60u64, 0.12),
            (98, 0.12),
            (262, 0.12),
            (299, 0.12),
            (415, 0.12),
            (552, 0.12),
            (51, 0.14),
            (178, 0.14),
            (920, 0.14),
            (944, 0.14),
        ];
        for (seed, density) in seeds {
            let report = analyze_complexity(&soup_config(seed, density));
            assert!(
                !report.ok,
                "seed {seed} dens={density} should fail complexity (quiescent@{})",
                report.quiescent_generation
            );
            assert!(report.quiescent_generation <= 4);
            assert_eq!(report.period, 1);
        }
    }

    #[test]
    fn blinker_fails_complexity() {
        let config = Config {
            width: 8,
            height: 8,
            depth: 24,
            pattern: Pattern::Blinker,
            ..Config::default()
        };
        let report = analyze_complexity(&config);
        assert!(!report.ok);
        assert_eq!(report.period, 2);
    }

    #[test]
    fn glider_stays_interesting_on_open_board() {
        let config = Config {
            width: 16,
            height: 16,
            depth: 24,
            pattern: Pattern::Glider,
            ..Config::default()
        };
        let report = analyze_complexity(&config);
        assert!(report.ok, "{report:?}");
        assert_eq!(report.period, 0);
        assert_eq!(report.quiescent_generation, 24);
    }

    #[test]
    fn methuselahs_outlast_a_44_gen_stack() {
        // Centered on a 44×44 board, all catalogued methuselahs stay active
        // for a full 180 mm print (44 generations at 4 mm cells).
        for pattern in [
            Pattern::Acorn,
            Pattern::Rpento,
            Pattern::Pi,
            Pattern::Bheptomino,
            Pattern::Thunderbird,
            Pattern::Bunnies,
            Pattern::Rabbits,
            Pattern::Diehard,
        ] {
            let config = Config {
                width: 44,
                height: 44,
                depth: 44,
                pattern,
                ..Config::default()
            };
            let report = analyze_complexity(&config);
            assert!(report.ok, "{pattern:?}: {report:?}");
            assert_eq!(report.period, 0, "{pattern:?} must not settle in 44 gens");
        }
    }

    #[test]
    fn still_life_garden_is_exempt() {
        let config = Config {
            width: 20,
            height: 20,
            depth: 30,
            seed: 11,
            density: 0.25,
            pattern: Pattern::Random,
            ..Config::default()
        };
        let report = analyze_complexity(&config);
        assert!(report.ok);
        assert_eq!(report.period, 1);
        assert_eq!(report.quiescent_generation, 0);
    }

    #[test]
    fn allow_boring_params_accept_early_still_life() {
        let mut config = soup_config(60, 0.12);
        config.complexity = ComplexityParams {
            min_active_generations: 0,
            min_active_fraction: 0.0,
            max_boring_period: 2,
        };
        assert!(analyze_complexity(&config).ok);
    }
}
