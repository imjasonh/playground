//! Search for seeds whose supports are practically removable (and, when
//! possible, whose Life geometry is one piece after support removal).

use crate::config::{Config, Pattern, SupportMode};
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
    /// True when breakaway supports pass the removability gate (or raw mode).
    pub supports_removable: bool,
}

/// Build + analyze one seed (includes breakaway supports per config).
pub fn evaluate(config: &Config) -> Model {
    build_model(config)
}

/// Check Life self-support on the Life|Base volume only (no supports).
pub fn evaluate_life_only(config: &Config) -> PrintabilityReport {
    let volume = build_life_volume(config);
    analyze(&volume, config.cell_mm)
}

fn removability_ok(model: &Model) -> bool {
    model.support_removability.ok
}

/// Find an acceptable seed for this mode/pattern.
///
/// - **Raw**: Life must be one piece (no supports to clean up).
/// - **Breakaway + Random**: Life one piece **and** supports easy to remove.
/// - **Breakaway + Soup** (and other chaotic patterns): supports must be easy
///   to remove; Life orphans are allowed (soups rarely stay one piece).
fn candidate_succeeds(
    mode: SupportMode,
    pattern: Pattern,
    life_ok: bool,
    removal_ok: bool,
) -> bool {
    match mode {
        SupportMode::Raw => life_ok,
        SupportMode::Breakaway => match pattern {
            Pattern::Random => life_ok && removal_ok,
            _ => removal_ok,
        },
    }
}

/// Rank failed candidates: prefer removable supports, then fewer orphans, then
/// higher removal score, then fewer tips.
fn better_fallback(a: &SearchOutcome, b: &SearchOutcome) -> bool {
    let a_rem = a.supports_removable;
    let b_rem = b.supports_removable;
    if a_rem != b_rem {
        return a_rem;
    }
    let a_orph = a.report.orphan_life_voxels;
    let b_orph = b.report.orphan_life_voxels;
    if a_orph != b_orph {
        return a_orph < b_orph;
    }
    let a_score = a
        .report
        .support_removability
        .as_ref()
        .map(|r| r.score)
        .unwrap_or(0.0);
    let b_score = b
        .report
        .support_removability
        .as_ref()
        .map(|r| r.score)
        .unwrap_or(0.0);
    if (a_score - b_score).abs() > 0.5 {
        return a_score > b_score;
    }
    a.report.breakaway_support_tips < b.report.breakaway_support_tips
}

/// Find a seed that passes the printability gates for this pattern.
pub fn find_self_supporting(
    mut config: Config,
    max_attempts: u32,
    start_seed: u64,
) -> SearchOutcome {
    let attempts_budget = max_attempts.max(1);
    let mut attempts = 0u32;
    let mut best: Option<SearchOutcome> = None;
    let pattern = config.pattern;

    let last = start_seed.saturating_add(u64::from(attempts_budget));
    for seed in start_seed..last {
        attempts += 1;
        config.seed = seed;
        let life_report = evaluate_life_only(&config);
        let supporting = life_report.life_self_supporting();
        let model = evaluate(&config);
        let removable = removability_ok(&model);
        let outcome = SearchOutcome {
            report: model.report.clone(),
            config: config.clone(),
            model,
            attempts,
            life_self_supporting: supporting,
            supports_removable: removable,
        };

        if candidate_succeeds(config.mode, pattern, supporting, removable) {
            return outcome;
        }

        let replace = match &best {
            None => true,
            Some(b) => better_fallback(&outcome, b),
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
        assert!(out.supports_removable);
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
        // Raw mode: no supports → removability trivially OK, but Life orphans remain.
        assert!(out.supports_removable);
        assert!(!out.life_self_supporting);
    }
}
