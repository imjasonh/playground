use rails_server::engine::ai::play_ai_turn;
use rails_server::engine::map::MapIndex;
use rails_server::engine::na_map::build_north_america_map;
use rails_server::engine::rules::{new_game, verify_invariants, PlayerSpec};
use rails_server::engine::state::{GameConfig, GameMode, TrainTier, TurnPhase};
use std::time::Instant;

struct ScenarioStats {
    label: String,
    games: usize,
    completed: usize,
    timed_out: usize,
    errors: Vec<String>,
    total_turns: u64,
    min_turns: u32,
    max_turns: u32,
    total_deliveries: u64,
    total_track_segments: u64,
    seat_wins: Vec<usize>,
    winner_upgrades_fast: usize,
    winner_upgrades_super: usize,
    events_triggered: u64,
}

fn run_scenario(
    map: &MapIndex,
    label: &str,
    mode: GameMode,
    events_enabled: bool,
    num_players: usize,
    games: usize,
    base_seed: u64,
    max_turns: u32,
) -> ScenarioStats {
    let mut stats = ScenarioStats {
        label: label.to_string(),
        games,
        completed: 0,
        timed_out: 0,
        errors: Vec::new(),
        total_turns: 0,
        min_turns: u32::MAX,
        max_turns: 0,
        total_deliveries: 0,
        total_track_segments: 0,
        seat_wins: vec![0; num_players],
        winner_upgrades_fast: 0,
        winner_upgrades_super: 0,
        events_triggered: 0,
    };

    let specs: Vec<PlayerSpec> = (0..num_players)
        .map(|i| PlayerSpec {
            name: format!("Bot {}", i + 1),
            color: None,
            is_bot: true,
        })
        .collect();

    let workers = std::thread::available_parallelism()
        .map(|n| n.get())
        .unwrap_or(4)
        .min(games.max(1));

    let chunk_size = games.div_ceil(workers);
    let partial: Vec<ScenarioStats> = std::thread::scope(|s| {
        let mut handles = Vec::new();
        for w in 0..workers {
            let start_g = w * chunk_size;
            let end_g = ((w + 1) * chunk_size).min(games);
            if start_g >= end_g {
                continue;
            }
            let specs_ref = &specs;
            handles.push(s.spawn(move || {
                let mut local = ScenarioStats {
                    label: String::new(),
                    games: end_g - start_g,
                    completed: 0,
                    timed_out: 0,
                    errors: Vec::new(),
                    total_turns: 0,
                    min_turns: u32::MAX,
                    max_turns: 0,
                    total_deliveries: 0,
                    total_track_segments: 0,
                    seat_wins: vec![0; num_players],
                    winner_upgrades_fast: 0,
                    winner_upgrades_super: 0,
                    events_triggered: 0,
                };
                for g in start_g..end_g {
                    let seed = base_seed + g as u64 * 7919;
                    let mut config = match mode {
                        GameMode::Standard => GameConfig::standard(),
                        GameMode::Fast => GameConfig::fast(),
                    };
                    config.events_enabled = events_enabled;

                    let mut state = match new_game(map, config, specs_ref, seed) {
                        Ok(st) => st,
                        Err(e) => {
                            local.errors.push(format!("game {g} init: {e}"));
                            continue;
                        }
                    };

                    let mut turn_guard = 0u32;
                    let mut failed = false;

                    while state.phase != TurnPhase::Finished && state.turn_number <= max_turns {
                        turn_guard += 1;
                        if turn_guard > max_turns * (num_players as u32 + 2) {
                            break;
                        }
                        let prev_log_seq = state.next_log_seq;
                        if let Err(e) = play_ai_turn(map, &mut state) {
                            local.errors.push(format!(
                                "game {g} (seed {seed}) turn {}: {e}",
                                state.turn_number
                            ));
                            failed = true;
                            break;
                        }
                        if let Err(inv) = verify_invariants(map, &state) {
                            local.errors.push(format!(
                                "game {g} (seed {seed}) turn {} invariant: {inv}",
                                state.turn_number
                            ));
                            failed = true;
                            break;
                        }
                        for entry in state.log.iter().rev() {
                            if entry.seq < prev_log_seq {
                                break;
                            }
                            if entry.text.starts_with("EVENT:") {
                                local.events_triggered += 1;
                            }
                        }
                    }

                    if failed {
                        continue;
                    }

                    if let Some(winner) = state.winner {
                        local.completed += 1;
                        local.seat_wins[winner as usize] += 1;
                        local.total_turns += state.turn_number as u64;
                        local.min_turns = local.min_turns.min(state.turn_number);
                        local.max_turns = local.max_turns.max(state.turn_number);
                        local.total_deliveries += state
                            .players
                            .iter()
                            .map(|p| p.deliveries_completed as u64)
                            .sum::<u64>();
                        local.total_track_segments += state.tracks.len() as u64;
                        match state.players[winner as usize].train_tier {
                            TrainTier::FastFreight | TrainTier::HeavyFreight => {
                                local.winner_upgrades_fast += 1
                            }
                            TrainTier::Superfreight => local.winner_upgrades_super += 1,
                            TrainTier::Freight => {}
                        }
                    } else {
                        local.timed_out += 1;
                    }
                }
                local
            }));
        }
        handles.into_iter().map(|h| h.join().unwrap()).collect()
    });

    for p in partial {
        stats.completed += p.completed;
        stats.timed_out += p.timed_out;
        stats.errors.extend(p.errors);
        stats.total_turns += p.total_turns;
        stats.min_turns = stats.min_turns.min(p.min_turns);
        stats.max_turns = stats.max_turns.max(p.max_turns);
        stats.total_deliveries += p.total_deliveries;
        stats.total_track_segments += p.total_track_segments;
        for (i, w) in p.seat_wins.into_iter().enumerate() {
            stats.seat_wins[i] += w;
        }
        stats.winner_upgrades_fast += p.winner_upgrades_fast;
        stats.winner_upgrades_super += p.winner_upgrades_super;
        stats.events_triggered += p.events_triggered;
    }

    stats
}

fn main() {
    let total_games: usize = std::env::args()
        .skip_while(|a| a != "--games")
        .nth(1)
        .and_then(|s| s.parse().ok())
        .unwrap_or(1000);

    let start = Instant::now();
    let map = MapIndex::new(build_north_america_map());
    println!(
        "Loaded map '{}': {} mileposts, {} cities, {} edges, {} commodities, {} cards",
        map.data.name,
        map.data.mileposts.len(),
        map.data.cities.len(),
        map.data.edges.len(),
        map.data.commodities.len(),
        map.data.deck.len(),
    );

    // Split total_games across 5 representative scenarios (2..6 players, Standard & Fast, Events On/Off).
    let per = (total_games / 5).max(1);
    let rem = total_games.saturating_sub(per * 5);

    let scenarios = [
        (
            "Standard 4P (No Events)",
            GameMode::Standard,
            false,
            4,
            per + rem,
            100_000,
            120,
        ),
        (
            "Standard 4P (Events ON)",
            GameMode::Standard,
            true,
            4,
            per,
            200_000,
            140,
        ),
        (
            "Fast 4P (No Events)",
            GameMode::Fast,
            false,
            4,
            per,
            300_000,
            100,
        ),
        (
            "Fast 2P (Events ON)",
            GameMode::Fast,
            true,
            2,
            per,
            400_000,
            110,
        ),
        (
            "Standard 6P (Events ON)",
            GameMode::Standard,
            true,
            6,
            per,
            500_000,
            140,
        ),
    ];

    let mut grand_games = 0usize;
    let mut grand_completed = 0usize;
    let mut grand_timeouts = 0usize;
    let mut grand_errors = 0usize;

    println!("\n| Scenario | Games | Completed | Timeouts | Errors | Avg Turns (Min-Max) | Avg Deliveries | Avg Tracks | Seat Win % | Events |");
    println!("|---|---:|---:|---:|---:|---:|---:|---:|---|---:|");

    let only_idx: Option<usize> = std::env::args()
        .skip_while(|a| a != "--only")
        .nth(1)
        .and_then(|s| s.parse().ok());

    for (idx, (label, mode, events, players, count, seed, max_t)) in
        scenarios.into_iter().enumerate()
    {
        if only_idx.is_some_and(|o| o != idx) {
            continue;
        }
        let s = run_scenario(&map, label, mode, events, players, count, seed, max_t);
        grand_games += s.games;
        grand_completed += s.completed;
        grand_timeouts += s.timed_out;
        grand_errors += s.errors.len();

        let avg_turns = if s.completed > 0 {
            s.total_turns as f64 / s.completed as f64
        } else {
            0.0
        };
        let avg_del = if s.completed > 0 {
            s.total_deliveries as f64 / s.completed as f64
        } else {
            0.0
        };
        let avg_trk = if s.completed > 0 {
            s.total_track_segments as f64 / s.completed as f64
        } else {
            0.0
        };
        let seat_pct: Vec<String> = s
            .seat_wins
            .iter()
            .map(|&w| {
                if s.completed > 0 {
                    format!("{:.0}%", 100.0 * w as f64 / s.completed as f64)
                } else {
                    "0%".to_string()
                }
            })
            .collect();

        println!(
            "| {} | {} | {} | {} | {} | {:.1} ({}-{}) | {:.1} | {:.0} | {} | {} |",
            s.label,
            s.games,
            s.completed,
            s.timed_out,
            s.errors.len(),
            avg_turns,
            if s.completed > 0 { s.min_turns } else { 0 },
            s.max_turns,
            avg_del,
            avg_trk,
            seat_pct.join("/"),
            s.events_triggered
        );

        for err in s.errors.iter().take(5) {
            eprintln!("  ERROR [{}]: {}", s.label, err);
        }
    }

    let elapsed = start.elapsed();
    println!(
        "\nTotal: {grand_games} games simulated in {:.2}s — {grand_completed} completed ({:.1}%), {grand_timeouts} timeouts, {grand_errors} errors/invariant violations.",
        elapsed.as_secs_f64(),
        100.0 * grand_completed as f64 / grand_games.max(1) as f64,
    );

    if grand_errors > 0 {
        std::process::exit(1);
    }
}
