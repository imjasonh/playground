//! Search for seeds whose Life geometry is one piece after support removal.

use crate::config::Config;
use crate::metrics::{analyze, PrintabilityReport};
use crate::{build_life_volume, build_model, Model};

/// Outcome of trying to produce a printable model for a config/seed policy.
#[derive(Debug)]
pub struct SearchOutcome {
    pub config: Config,
    pub model: Model,
    pub report: PrintabilityReport,
    /// Seeds tried (including the successful one, if any).
    pub attempts: u32,
    /// True when every Life voxel is face-connected to the base without supports.
    pub life_self_supporting: bool,
}

/// Build + analyze one seed (includes breakaway/fused supports per config).
pub fn evaluate(config: &Config) -> Model {
    build_model(config)
}

/// Check Life self-support on the Life|Base volume only (no supports).
pub fn evaluate_life_only(config: &Config) -> PrintabilityReport {
    let volume = build_life_volume(config);
    analyze(&volume, config.cell_mm)
}

/// Find a seed whose Life sculpture is self-supporting (no orphan Life cells).
pub fn find_self_supporting(
    mut config: Config,
    max_attempts: u32,
    start_seed: u64,
) -> SearchOutcome {
    let attempts_budget = max_attempts.max(1);
    let mut attempts = 0u32;
    let mut best: Option<SearchOutcome> = None;

    let last = start_seed.saturating_add(u64::from(attempts_budget));
    for seed in start_seed..last {
        attempts += 1;
        config.seed = seed;
        let life_report = evaluate_life_only(&config);
        let supporting = life_report.life_self_supporting();
        let model = evaluate(&config);
        let outcome = SearchOutcome {
            report: model.report.clone(),
            config: config.clone(),
            model,
            attempts,
            life_self_supporting: supporting,
        };

        if supporting {
            return outcome;
        }

        let replace = match &best {
            None => true,
            Some(b) => {
                outcome.report.orphan_life_voxels < b.report.orphan_life_voxels
                    || (outcome.report.orphan_life_voxels == b.report.orphan_life_voxels
                        && outcome.report.breakaway_support_tips + outcome.report.scaffold_voxels
                            < b.report.breakaway_support_tips + b.report.scaffold_voxels)
            }
        };
        if replace {
            best = Some(outcome);
        }
    }

    let mut best = best.expect("max_attempts >= 1");
    best.attempts = attempts;
    best
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::config::{Pattern, SupportMode};

    #[test]
    fn random_garden_search_succeeds_immediately() {
        let config = Config {
            width: 20,
            height: 20,
            depth: 30,
            seed: 0,
            density: 0.25,
            pattern: Pattern::Random,
            mode: SupportMode::Breakaway,
            cell_mm: 4.0,
            ..Config::default()
        };
        let out = find_self_supporting(config, 5, 11);
        assert!(out.life_self_supporting);
        assert_eq!(out.attempts, 1);
        assert_eq!(out.config.seed, 11);
    }

    #[test]
    fn soup_search_reports_attempts_when_exhausted() {
        let config = Config {
            width: 16,
            height: 16,
            depth: 32,
            seed: 0,
            density: 0.35,
            pattern: Pattern::Soup,
            mode: SupportMode::Raw,
            cell_mm: 4.0,
            ..Config::default()
        };
        let out = find_self_supporting(config, 8, 0);
        assert_eq!(out.attempts, 8);
        assert!(!out.life_self_supporting);
    }
}
