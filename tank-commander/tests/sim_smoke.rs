//! End-to-end Monte Carlo smoke tests.

use tank_commander::scenario::ScenarioKind;
use tank_commander::sim::{self, SimConfig};

#[test]
fn skirmish_batch_produces_drama_signals() {
    let result = sim::run(SimConfig {
        games: 40,
        seed: 99,
        verbose: false,
        scenario: ScenarioKind::Skirmish,
    });
    assert_eq!(result.aggregate.games, 40);
    assert_eq!(result.aggregate.scenario, "skirmish");
    assert!(result.aggregate.red_wins + result.aggregate.blue_wins + result.aggregate.draws == 40);
    assert!(result.aggregate.avg_pens > 0.5);
    assert!(result.aggregate.avg_shots > 1.0);
    assert!(!result.aggregate.suggestions.is_empty());
}

#[test]
fn squadron_batch_runs() {
    let result = sim::run(SimConfig {
        games: 20,
        seed: 13,
        verbose: false,
        scenario: ScenarioKind::Squadron,
    });
    assert_eq!(result.aggregate.games, 20);
    assert_eq!(result.aggregate.scenario, "squadron");
    assert!(result.aggregate.avg_shots > 1.0);
    assert!(result.aggregate.avg_moves > 1.0);
    assert_eq!(result.aggregate.loadout_avg_points, 0.0);
}

#[test]
fn platoon_batch_runs() {
    let result = sim::run(SimConfig {
        games: 20,
        seed: 11,
        verbose: false,
        scenario: ScenarioKind::Platoon,
    });
    assert_eq!(result.aggregate.games, 20);
    assert_eq!(result.aggregate.scenario, "platoon");
    assert!(result.aggregate.avg_shots > 1.0);
    assert!(result.aggregate.avg_moves > 1.0);
}

#[test]
fn combined_batch_runs() {
    let result = sim::run(SimConfig {
        games: 16,
        seed: 22,
        verbose: false,
        scenario: ScenarioKind::Combined,
    });
    assert_eq!(result.aggregate.games, 16);
    assert_eq!(result.aggregate.scenario, "combined");
    assert!(result.aggregate.avg_shots > 0.5);
}

#[test]
fn capture_batch_runs() {
    let result = sim::run(SimConfig {
        games: 16,
        seed: 33,
        verbose: false,
        scenario: ScenarioKind::Capture,
    });
    assert_eq!(result.aggregate.games, 16);
    assert_eq!(result.aggregate.scenario, "capture");
    assert!(result.aggregate.avg_moves > 1.0);
    // At least some games should resolve via Capture when the AI races.
    assert!(
        result.aggregate.capture_win_rate > 0.0 || result.aggregate.avg_drop_offs > 0.0,
        "expected flag play (captures or drop-offs), got capture_win_rate={} drop_offs={}",
        result.aggregate.capture_win_rate,
        result.aggregate.avg_drop_offs
    );
}
