//! Seed search: try seeds until one passes the gates for the configured
//! mode/pattern (see `candidate_succeeds`) — evolution stays interesting for
//! the printed height, supports (if any) are practically removable, and the
//! final piece stands on its own. Keeps the best-scoring failure as a
//! best-effort fallback when the budget is exhausted.

use crate::complexity::analyze_complexity;
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
    /// True when evolution stays active long enough (or pattern is exempt).
    pub interesting: bool,
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

fn complexity_ok(model: &Model) -> bool {
    model.complexity.ok
}

fn outcome_from(config: &Config, model: Model, attempts: u32) -> SearchOutcome {
    // Gusset mode reports causal (braced) connectivity in the model report;
    // other modes report face-only connectivity — both mean "one piece after
    // any cleanup" for their mode.
    let life_ok = model.report.life_self_supporting();
    SearchOutcome {
        interesting: complexity_ok(&model),
        supports_removable: removability_ok(&model),
        life_self_supporting: life_ok,
        report: model.report.clone(),
        config: config.clone(),
        model,
        attempts,
    }
}

/// Find an acceptable seed for this mode/pattern.
///
/// - **Raw**: Life must be one piece (no supports to clean up); still require
///   interesting evolution for non-garden patterns.
/// - **Gusset**: self-supporting by construction — Life must be one causal
///   piece (always true for real Life) and evolution must stay interesting.
/// - **Breakaway + Random**: Life one piece **and** supports easy to remove
///   (gardens are exempt from the complexity gate).
/// - **Breakaway + Soup** (and other chaotic patterns): supports must be easy
///   to remove **and** evolution must stay interesting; Life orphans are
///   allowed (these patterns rarely stay one piece).
fn candidate_succeeds(
    mode: SupportMode,
    pattern: Pattern,
    life_ok: bool,
    removal_ok: bool,
    interesting: bool,
) -> bool {
    match mode {
        SupportMode::Raw | SupportMode::Gusset => match pattern {
            Pattern::Random => life_ok,
            _ => life_ok && interesting,
        },
        SupportMode::Breakaway => match pattern {
            Pattern::Random => life_ok && removal_ok,
            _ => removal_ok && interesting,
        },
    }
}

/// Rank failed candidates: prefer interesting+removable, then interesting, then
/// removable, then fewer orphans, then higher removal score, then later
/// quiescence, then fewer tips.
fn better_fallback(a: &SearchOutcome, b: &SearchOutcome) -> bool {
    let a_both = a.supports_removable && a.interesting;
    let b_both = b.supports_removable && b.interesting;
    if a_both != b_both {
        return a_both;
    }
    if a.interesting != b.interesting {
        return a.interesting;
    }
    if a.supports_removable != b.supports_removable {
        return a.supports_removable;
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
    let a_q = a
        .report
        .complexity
        .as_ref()
        .map(|c| c.quiescent_generation)
        .unwrap_or(0);
    let b_q = b
        .report
        .complexity
        .as_ref()
        .map(|c| c.quiescent_generation)
        .unwrap_or(0);
    if a_q != b_q {
        return a_q > b_q;
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
    let mut first_boring_seed: Option<u64> = None;
    let pattern = config.pattern;
    let mode = config.mode;

    let last = start_seed.saturating_add(u64::from(attempts_budget));
    for seed in start_seed..last {
        attempts += 1;
        config.seed = seed;

        // Cheap reject: skip support routing for patterns that die into a
        // still-life tower after a few turns.
        if pattern != Pattern::Random && !analyze_complexity(&config).ok {
            if first_boring_seed.is_none() {
                first_boring_seed = Some(seed);
            }
            continue;
        }

        let model = evaluate(&config);
        let outcome = outcome_from(&config, model, attempts);

        if candidate_succeeds(
            mode,
            pattern,
            outcome.life_self_supporting,
            outcome.supports_removable,
            outcome.interesting,
        ) {
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

    if let Some(mut best) = best {
        best.attempts = attempts;
        return best;
    }

    // Every candidate failed the complexity gate — still emit a best-effort STL.
    config.seed = first_boring_seed.unwrap_or(start_seed);
    let model = evaluate(&config);
    let mut outcome = outcome_from(&config, model, attempts);
    outcome.attempts = attempts;
    outcome
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
        assert!(out.interesting);
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

    #[test]
    fn soup_search_skips_early_stable_seeds() {
        // Seed 60 dens=0.12 settles at gen 3 — must not be accepted under defaults.
        let config = Config {
            width: 16,
            height: 16,
            depth: 24,
            seed: 0,
            density: 0.12,
            pattern: Pattern::Soup,
            mode: SupportMode::Breakaway,
            cell_mm: 4.0,
            ..Config::default()
        };
        let out = find_self_supporting(config, 1, 60);
        assert!(!out.interesting);
        assert!(!out.model.complexity.ok);
        assert_eq!(out.config.seed, 60);
    }
}
