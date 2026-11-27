use rails_server::engine::ai::play_ai_turn;
use rails_server::engine::ebm::{build_default_ebm_map, parse_ebm, DEFAULT_EBM};
use rails_server::engine::map::{Card, CitySize, EdgeKind, MapIndex};
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
fn default_ebm_usa_map_parses_with_exact_classic_board_contents() {
    let map = MapIndex::new(build_default_ebm_map());
    assert_eq!(map.data.name, "United States");
    assert!(
        map.data.mileposts.len() > 1500,
        "expected full 63x36 classic EB dot grid, got {}",
        map.data.mileposts.len()
    );
    assert_eq!(
        map.data.cities.len(),
        51,
        "classic USAMAP.EBM has 51 cities"
    );
    assert_eq!(
        map.major_city_ids.len(),
        6,
        "classic EB USA has 6 Major Cities"
    );
    let mut majors = map.major_city_ids.clone();
    majors.sort();
    assert_eq!(
        majors,
        vec![
            "atlanta",
            "chicago",
            "kansas_city",
            "los_angeles",
            "new_york",
            "seattle"
        ]
    );
    assert_eq!(map.data.commodities.len(), 26);

    let demand_cards = map.data.deck.iter().filter(|c| !c.is_event()).count();
    let event_cards = map.data.deck.iter().filter(|c| c.is_event()).count();
    assert_eq!(demand_cards, 120, "classic USAMAP.EBM has 120 demand cards");
    assert!(event_cards >= 18, "classic USAMAP.EBM has event cards");

    // Verify all 51 cities are mutually reachable in a single connected component!
    let start_mp = map.city("chicago").unwrap().center_mp;
    let mut visited = HashSet::new();
    let mut q = VecDeque::new();
    visited.insert(start_mp);
    q.push_back(start_mp);
    while let Some(cur) = q.pop_front() {
        for &(nb, _) in &map.adj[cur as usize] {
            if visited.insert(nb) {
                q.push_back(nb);
            }
        }
    }
    for city in &map.data.cities {
        assert!(
            visited.contains(&city.center_mp),
            "City {} must be reachable from Chicago",
            city.name
        );
    }

    assert!(
        map.data.edges.iter().any(|e| e.kind == EdgeKind::River),
        "must have river crossings"
    );
    assert!(
        map.data.edges.iter().any(|e| e.kind == EdgeKind::Inlet),
        "must have ocean inlet crossings"
    );

    // Every demand entry references a valid city and commodity.
    for card in &map.data.deck {
        if let Card::Demand { demands, .. } = card {
            for d in demands {
                assert!(map.city(&d.city_id).is_some(), "valid demand city");
                assert!(map.commodity_by_id.contains_key(&d.commodity));
                assert!(d.payout >= 1 && d.payout <= 100);
            }
        }
    }

    // Re-parsing raw EBM text yields identical counts.
    let reparsed = parse_ebm(DEFAULT_EBM).expect("reparse DEFAULT_EBM");
    assert_eq!(reparsed.mileposts.len(), map.data.mileposts.len());
    assert_eq!(reparsed.cities.len(), map.data.cities.len());

    let json = map.data.to_json().expect("serialize MapData");
    assert!(json.len() > 50_000);
}

#[test]
fn initial_build_undo_right_of_way_and_switchback() {
    let map = MapIndex::new(build_default_ebm_map());
    let specs: Vec<PlayerSpec> = (0..3)
        .map(|i| PlayerSpec {
            name: format!("P{i}"),
            color: None,
            is_bot: false,
        })
        .collect();
    let mut state = new_game(&map, GameConfig::standard(), &specs, 42).unwrap();
    assert_eq!(state.phase, TurnPhase::InitialBuild);

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

    // Re-build first edge and verify Right of Way blocks next player.
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
    assert!(apply_action(
        &map,
        &mut state,
        p1,
        Action::BuildTrack {
            edges: vec![first_edge],
        }
    )
    .is_err());

    // Verify Switchback order.
    apply_action(&map, &mut state, p1, Action::EndTurn).unwrap();
    let p2 = state.current_player;
    assert_eq!(p2, (f + 2) % 3);
    apply_action(&map, &mut state, p2, Action::EndTurn).unwrap();
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
    let map = MapIndex::new(build_default_ebm_map());
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
    let map = MapIndex::new(build_default_ebm_map());
    let specs: Vec<PlayerSpec> = (0..3)
        .map(|i| PlayerSpec {
            name: format!("P{i}"),
            color: None,
            is_bot: false,
        })
        .collect();
    let mut state = new_game(&map, GameConfig::standard(), &specs, 99).unwrap();
    let cur = state.current_player;

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
fn ai_completes_full_games_on_classic_ebm_board() {
    let map = MapIndex::new(build_default_ebm_map());
    for (mode, events, seed) in [(GameMode::Fast, false, 2002), (GameMode::Fast, true, 3003)] {
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
        while state.phase != TurnPhase::Finished && state.turn_number < 140 {
            play_ai_turn(&map, &mut state).unwrap();
            verify_invariants(&map, &state).unwrap();
            steps += 1;
            assert!(steps < 900, "game stalled");
        }
        assert_eq!(
            state.phase,
            TurnPhase::Finished,
            "AI game ({mode:?}, events={events}) did not finish in 140 turns"
        );
        let winner = state.winner.unwrap();
        assert!(state.players[winner as usize].cash >= 250);
        assert!(connected_major_cities_count(&map, &state, winner) >= 5);
    }
}
