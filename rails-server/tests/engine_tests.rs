use rails_server::engine::ai::play_ai_turn;
use rails_server::engine::map::{Card, CitySize, EdgeKind, MapIndex};
use rails_server::engine::na_map::build_north_america_map;
use rails_server::engine::rules::{
    apply_action, can_enter_city, connected_major_cities_count, new_game, player_build_anchors,
    player_owned_edges, verify_invariants, PlayerSpec,
};
use rails_server::engine::state::{Action, GameConfig, GameMode, TrainTier, TurnPhase};
use std::collections::{HashSet, VecDeque};

fn two_players() -> Vec<PlayerSpec> {
    vec![
        PlayerSpec {
            name: "Alice".into(),
            color: None,
            is_bot: false,
        },
        PlayerSpec {
            name: "Bob".into(),
            color: None,
            is_bot: false,
        },
    ]
}

#[test]
fn na_map_is_fully_connected_and_valid() {
    let map = MapIndex::new(build_north_america_map());
    assert!(map.data.mileposts.len() > 350, "expected full NA lattice");
    assert_eq!(map.major_city_ids.len(), 6, "classic NA has 6 major cities");
    assert!(map.data.cities.len() >= 35);
    assert!(map.data.commodities.len() >= 24);
    assert!(map.data.deck.len() >= 110);

    // Verify single connected component across all mileposts.
    let mut visited = HashSet::new();
    let mut q = VecDeque::new();
    visited.insert(0u16);
    q.push_back(0u16);
    while let Some(cur) = q.pop_front() {
        for &(nb, _) in &map.adj[cur as usize] {
            if visited.insert(nb) {
                q.push_back(nb);
            }
        }
    }
    assert_eq!(
        visited.len(),
        map.data.mileposts.len(),
        "NA map graph must be a single connected component"
    );

    // Verify rivers and inlets exist.
    assert!(
        map.data.edges.iter().any(|e| e.kind == EdgeKind::River),
        "must have river crossings"
    );
    assert!(
        map.data.edges.iter().any(|e| e.kind == EdgeKind::Inlet),
        "must have ocean inlets"
    );

    // Verify every demand card references valid city & commodity, and destination doesn't produce that commodity.
    for card in &map.data.deck {
        if let Card::Demand { demands, .. } = card {
            for d in demands {
                let city = map.city(&d.city_id).expect("valid demand city");
                assert!(map.commodity_by_id.contains_key(&d.commodity));
                assert!(
                    !city.commodities.contains(&d.commodity),
                    "city {} should not demand its own commodity {}",
                    city.name,
                    d.commodity
                );
                assert!(d.payout >= 7 && d.payout <= 48);
            }
        }
    }

    // Verify MapData serializes cleanly to JSON for the browser renderer.
    let json = serde_json::to_string(&map.data).expect("serialize MapData");
    assert!(json.len() > 10_000);
}

#[test]
fn initial_build_undo_and_budget_enforcement() {
    let map = MapIndex::new(build_north_america_map());
    let mut state = new_game(&map, GameConfig::standard(), &two_players(), 42).unwrap();
    assert_eq!(state.phase, TurnPhase::InitialBuild);
    assert_eq!(state.players[0].cash, 40);

    // Find a short build path out of Chicago toward St. Louis.
    let st_louis = map.city("st_louis").unwrap().center_mp;
    let anchors = player_build_anchors(&map, &state, 0);
    let owned = player_owned_edges(&state, 0);
    let (edges, cost) = map
        .shortest_build_path(
            &anchors,
            st_louis,
            &owned,
            &HashSet::new(),
            &HashSet::new(),
            |_| true,
        )
        .unwrap();
    assert!(!edges.is_empty());
    assert!(
        cost <= 20,
        "Chicago to St. Louis should fit in $20M budget, got {cost}"
    );

    apply_action(&map, &mut state, 0, Action::BuildTrack { edges }).unwrap();
    assert_eq!(state.players[0].cash, 40 - cost);
    assert!(state.turn_tracker.can_undo);

    // Undo restores cash and removes track.
    apply_action(&map, &mut state, 0, Action::Undo).unwrap();
    assert_eq!(state.players[0].cash, 40);
    assert!(state.tracks.is_empty());
    verify_invariants(&map, &state).unwrap();
}

#[test]
fn fast_mode_starts_with_5_cards_and_trims_to_3() {
    let map = MapIndex::new(build_north_america_map());
    let mut state = new_game(&map, GameConfig::fast(), &two_players(), 7).unwrap();
    assert_eq!(state.players[0].cash, 60);
    assert_eq!(state.players[0].hand.len(), 5);

    // Pass 3 initial build rounds (2 players * 3 rounds = 6 EndTurns).
    for _ in 0..6 {
        let p = state.current_player;
        apply_action(&map, &mut state, p, Action::EndTurn).unwrap();
    }
    assert_eq!(state.phase, TurnPhase::TrimHand);

    apply_action(
        &map,
        &mut state,
        0,
        Action::DiscardInitialCards {
            indices: vec![0, 4],
        },
    )
    .unwrap();
    assert_eq!(state.players[0].hand.len(), 3);
    assert_eq!(state.phase, TurnPhase::TrimHand);

    apply_action(
        &map,
        &mut state,
        1,
        Action::DiscardInitialCards {
            indices: vec![1, 2],
        },
    )
    .unwrap();
    assert_eq!(state.players[1].hand.len(), 3);
    assert_eq!(state.phase, TurnPhase::Operate);
    verify_invariants(&map, &state).unwrap();
}

#[test]
fn train_upgrade_path_and_city_entry_limits() {
    let map = MapIndex::new(build_north_america_map());
    let specs: Vec<PlayerSpec> = (0..3)
        .map(|i| PlayerSpec {
            name: format!("P{i}"),
            color: None,
            is_bot: false,
        })
        .collect();
    let mut state = new_game(&map, GameConfig::standard(), &specs, 99).unwrap();

    // Small city entry cap is 2 players.
    let small_city = map
        .data
        .cities
        .iter()
        .find(|c| c.size == CitySize::Small)
        .unwrap();
    let adj_mp = map.adj[small_city.center_mp as usize][0].0;
    state
        .tracks
        .push(rails_server::engine::state::TrackSegment {
            a: adj_mp,
            b: small_city.center_mp,
            owner: 0,
        });
    state
        .tracks
        .push(rails_server::engine::state::TrackSegment {
            a: adj_mp,
            b: small_city.center_mp,
            owner: 1,
        });
    assert!(can_enter_city(&map, &state, 0, &small_city.id));
    assert!(can_enter_city(&map, &state, 1, &small_city.id));
    assert!(!can_enter_city(&map, &state, 2, &small_city.id));

    // Upgrade rules: Freight -> FastFreight OK, Freight -> Superfreight rejected.
    state.phase = TurnPhase::Build;
    assert!(apply_action(
        &map,
        &mut state,
        0,
        Action::UpgradeTrain {
            target_tier: TrainTier::Superfreight
        }
    )
    .is_err());
    apply_action(
        &map,
        &mut state,
        0,
        Action::UpgradeTrain {
            target_tier: TrainTier::FastFreight,
        },
    )
    .unwrap();
    assert_eq!(state.players[0].train_tier, TrainTier::FastFreight);
    assert_eq!(state.players[0].cash, 20);
}

#[test]
fn ai_completes_full_games_standard_and_fast_with_events() {
    let map = MapIndex::new(build_north_america_map());
    for (mode, events, seed) in [
        (GameMode::Standard, false, 1001),
        (GameMode::Fast, false, 2002),
        (GameMode::Standard, true, 3003),
    ] {
        let mut cfg = match mode {
            GameMode::Standard => GameConfig::standard(),
            GameMode::Fast => GameConfig::fast(),
        };
        cfg.events_enabled = events;
        let specs: Vec<PlayerSpec> = (0..4)
            .map(|i| PlayerSpec {
                name: format!("AI {i}"),
                color: None,
                is_bot: true,
            })
            .collect();
        let mut state = new_game(&map, cfg, &specs, seed).unwrap();
        let mut steps = 0;
        while state.phase != TurnPhase::Finished && state.turn_number < 120 {
            play_ai_turn(&map, &mut state).unwrap();
            verify_invariants(&map, &state).unwrap();
            steps += 1;
            assert!(steps < 800, "game stalled");
        }
        assert_eq!(
            state.phase,
            TurnPhase::Finished,
            "AI game ({mode:?}, events={events}) did not finish in 120 turns"
        );
        let winner = state.winner.unwrap();
        assert!(state.players[winner as usize].cash >= 250);
        assert!(connected_major_cities_count(&map, &state, winner) >= 5);
    }
}
