//! Monte Carlo runner.

use crate::ai;
use crate::game::Outcome;
use crate::metrics::{AggregateReport, GameReport, HpTrace};
use crate::scenario;
use rand::SeedableRng;
use rand_chacha::ChaCha8Rng;

pub struct SimConfig {
    pub games: u32,
    pub seed: u64,
    pub verbose: bool,
}

pub struct SimResult {
    pub reports: Vec<GameReport>,
    pub aggregate: AggregateReport,
    pub sample_events: Vec<String>,
}

pub fn run(config: SimConfig) -> SimResult {
    let mut reports = Vec::with_capacity(config.games as usize);
    let mut sample_events = Vec::new();

    for i in 0..config.games {
        let seed = config.seed.wrapping_add(u64::from(i));
        let mut rng = ChaCha8Rng::seed_from_u64(seed);
        let mut game = scenario::skirmish(&mut rng);
        let mut hp = HpTrace::default();
        hp.observe(&game);

        while matches!(game.outcome(), Outcome::InProgress) {
            ai::take_turn(&mut game, &mut rng);
            hp.observe(&game);
            // Safety valve against infinite loops if legality breaks.
            if game.activations > game.max_activations + 2 {
                break;
            }
        }

        let report = GameReport::from_game(&game, seed, &hp);
        if config.verbose && i == 0 {
            for ev in &game.events {
                sample_events.push(format!("t{} {:?}: {}", ev.turn, ev.side, ev.text));
            }
        }
        reports.push(report);
    }

    let aggregate = AggregateReport::from_games(&reports);
    SimResult {
        reports,
        aggregate,
        sample_events,
    }
}
