//! End-to-end Monte Carlo smoke test.

use tank_commander::sim::{self, SimConfig};

#[test]
fn skirmish_batch_produces_drama_signals() {
    let result = sim::run(SimConfig {
        games: 40,
        seed: 99,
        verbose: false,
    });
    assert_eq!(result.aggregate.games, 40);
    assert!(result.aggregate.red_wins + result.aggregate.blue_wins + result.aggregate.draws == 40);
    // Stock AT vs armor 6 always pens on hit, so pens should appear.
    assert!(result.aggregate.avg_pens > 0.5);
    assert!(result.aggregate.avg_shots > 1.0);
    assert!(!result.aggregate.suggestions.is_empty());
}
