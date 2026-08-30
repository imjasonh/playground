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
