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
    assert!(map.data.mileposts.len() > 500, "expected full NA lattice");
    assert_eq!(map.major_city_ids.len(), 6, "classic NA has 6 major cities");
    assert!(map.data.cities.len() >= 44);
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

    assert!(
        map.data.edges.iter().any(|e| e.kind == EdgeKind::River),
        "must have river crossings"
    );

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

    let json = map.data.to_json().expect("serialize MapData");
    assert!(json.len() > 20_000);
}

#[test]
fn initial_build_undo_right_of_way_and_switchback() {
    let map = MapIndex::new(build_north_america_map());
    let specs: Vec<PlayerSpec> = (0..3)
        .map(|i| PlayerSpec {
            name: format!("P{i}"),
            color: None,
            is_bot: false,
        })
        .collect();
    let mut state = new_game(&map, GameConfig::standard(), &specs, 42).unwrap();
    assert_eq!(state.phase, TurnPhase::InitialBuild);

    // Record exact Switchback order across 2 initial rounds of 3 players:
    // Round 1: f, f+1, f+2; Round 2: f+2, f+1, f
    let f = state.first_player;
    let p0 = state.current_player;
    assert_eq!(p0, f);

    // Build a short path out of Chicago toward St. Louis and test Undo.
    let st_louis = map.city("st_louis").unwrap().center_mp;
    let anchors = player_build_anchors(&map, &state, p0);
    let owned = player_owned_edges(&state, p0);
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
    assert!(cost <= 20);

    apply_action(
        &map,
        &mut state,
        p0,
        Action::BuildTrack {
            edges: edges.clone(),
        },
    )
    .unwrap();
    assert_eq!(state.players[p0 as usize].cash, 40 - cost);
    assert!(state.turn_tracker.can_undo);

    apply_action(&map, &mut state, p0, Action::Undo).unwrap();
    assert_eq!(state.players[p0 as usize].cash, 40);
    assert!(state.tracks.is_empty());

    // Re-build the first edge and advance to next player; verify Right of Way blocks next player!
    let first_edge = edges[0];
    apply_action(
        &map,
        &mut state,
        p0,
        Action::BuildTrack {
            edges: vec![first_edge],
        },
    )
    .unwrap();
    apply_action(&map, &mut state, p0, Action::EndTurn).unwrap();

    let p1 = state.current_player;
    assert_eq!(p1, (f + 1) % 3);
    // Right of Way: p1 cannot build on p0's edge!
    assert!(apply_action(
        &map,
        &mut state,
        p1,
        Action::BuildTrack {
            edges: vec![first_edge],
        }
    )
    .is_err());

    // Verify full Switchback order for remaining initial build steps.
    apply_action(&map, &mut state, p1, Action::EndTurn).unwrap();
    let p2 = state.current_player;
    assert_eq!(p2, (f + 2) % 3);
    apply_action(&map, &mut state, p2, Action::EndTurn).unwrap();
    // Round 2 starts with p2 again (Switchback)!
    assert_eq!(state.initial_round, 2);
    assert_eq!(state.current_player, (f + 2) % 3);
    apply_action(&map, &mut state, p2, Action::EndTurn).unwrap();
    assert_eq!(state.current_player, (f + 1) % 3);
    apply_action(&map, &mut state, p1, Action::EndTurn).unwrap();
    assert_eq!(state.current_player, f);
    apply_action(&map, &mut state, f, Action::EndTurn).unwrap();

    assert_eq!(state.phase, TurnPhase::Operate);
    assert_eq!(state.current_player, f);
    verify_invariants(&map, &state).unwrap();
}

#[test]
fn fast_mode_starts_with_5_cards_and_trims_to_3() {
    let map = MapIndex::new(build_north_america_map());
    let mut state = new_game(&map, GameConfig::fast(), &two_players(), 7).unwrap();
    assert_eq!(state.players[0].cash, 60);
    assert_eq!(state.players[0].hand.len(), 5);

    for _ in 0..6 {
        let p = state.current_player;
        apply_action(&map, &mut state, p, Action::EndTurn).unwrap();
    }
    assert_eq!(state.phase, TurnPhase::TrimHand);

    let first = state.current_player;
    apply_action(
        &map,
        &mut state,
        first,
        Action::DiscardInitialCards {
            indices: vec![0, 4],
        },
    )
    .unwrap();
    assert_eq!(state.players[first as usize].hand.len(), 3);
    assert_eq!(state.phase, TurnPhase::TrimHand);

    let second = state.current_player;
    apply_action(
        &map,
        &mut state,
        second,
        Action::DiscardInitialCards {
            indices: vec![1, 2],
        },
    )
    .unwrap();
    assert_eq!(state.players[second as usize].hand.len(), 3);
    assert_eq!(state.phase, TurnPhase::Operate);
    verify_invariants(&map, &state).unwrap();
}

#[test]
fn train_upgrade_crossgrade_and_city_entry_limits() {
    let map = MapIndex::new(build_north_america_map());
    let specs: Vec<PlayerSpec> = (0..3)
        .map(|i| PlayerSpec {
            name: format!("P{i}"),
            color: None,
            is_bot: false,
        })
        .collect();
    let mut state = new_game(&map, GameConfig::standard(), &specs, 99).unwrap();
    let cur = state.current_player;

    // Small city entry cap is 2 players (using distinct adjacent edges per Right of Way).
    let small_city = map
        .data
        .cities
        .iter()
        .find(|c| c.size == CitySize::Small && map.adj[c.center_mp as usize].len() >= 2)
        .unwrap();
    let adj0 = map.adj[small_city.center_mp as usize][0].0;
    let adj1 = map.adj[small_city.center_mp as usize][1].0;
    state
        .tracks
        .push(rails_server::engine::state::TrackSegment {
            a: adj0,
            b: small_city.center_mp,
            owner: 0,
        });
    state
        .tracks
        .push(rails_server::engine::state::TrackSegment {
            a: adj1,
            b: small_city.center_mp,
            owner: 1,
        });
    assert!(can_enter_city(&map, &state, 0, &small_city.id));
    assert!(can_enter_city(&map, &state, 1, &small_city.id));
    assert!(!can_enter_city(&map, &state, 2, &small_city.id));

    // Upgrade allowed during InitialBuild too (official Page 5 rule); direct Freight -> Superfreight rejected.
    assert!(apply_action(
        &map,
        &mut state,
        cur,
        Action::UpgradeTrain {
            target_tier: TrainTier::Superfreight
        }
    )
    .is_err());
    apply_action(
        &map,
        &mut state,
        cur,
        Action::UpgradeTrain {
            target_tier: TrainTier::FastFreight,
        },
    )
    .unwrap();
    assert_eq!(
        state.players[cur as usize].train_tier,
        TrainTier::FastFreight
    );
    assert_eq!(state.players[cur as usize].cash, 20);

    // Crossgrade FastFreight -> HeavyFreight costs $5M (leaving $15M budget!).
    state.turn_tracker = Default::default();
    apply_action(
        &map,
        &mut state,
        cur,
        Action::UpgradeTrain {
            target_tier: TrainTier::HeavyFreight,
        },
    )
    .unwrap();
    assert_eq!(
        state.players[cur as usize].train_tier,
        TrainTier::HeavyFreight
    );
    assert_eq!(state.players[cur as usize].cash, 15);
    assert_eq!(state.turn_tracker.build_spent, 5);
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
        while state.phase != TurnPhase::Finished && state.turn_number < 130 {
            play_ai_turn(&map, &mut state).unwrap();
            verify_invariants(&map, &state).unwrap();
            steps += 1;
            assert!(steps < 900, "game stalled");
        }
        assert_eq!(
            state.phase,
            TurnPhase::Finished,
            "AI game ({mode:?}, events={events}) did not finish in 130 turns"
        );
        let winner = state.winner.unwrap();
        assert!(state.players[winner as usize].cash >= 250);
        assert!(connected_major_cities_count(&map, &state, winner) >= 5);
    }
}
