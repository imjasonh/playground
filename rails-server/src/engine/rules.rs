use crate::engine::map::{
    edge_key, Card, CitySize, EdgeKind, EventEffect, MapIndex, MilepostId, PlayerId,
};
use crate::engine::state::{
    Action, ActiveEvent, GameConfig, GameMode, GameState, PlayerState, RuleError, TrackSegment,
    TrainTier, TurnPhase, TurnTracker, UndoCheckpoint, PLAYER_COLORS,
};
use rand::seq::SliceRandom;
use rand::SeedableRng;
use rand_chacha::ChaCha8Rng;
use std::collections::{HashMap, HashSet, VecDeque};

#[derive(Debug, Clone)]
pub struct PlayerSpec {
    pub name: String,
    pub color: Option<String>,
    pub is_bot: bool,
}

#[derive(Debug, Default)]
pub struct ActiveHazards {
    pub blocked_edges: HashSet<(MilepostId, MilepostId)>,
    pub blocked_nodes: HashSet<MilepostId>,
    pub half_speed_nodes: HashSet<MilepostId>,
    pub strike_cities: HashSet<String>,
}

/// Create a new game with deterministic RNG seed.
pub fn new_game(
    map: &MapIndex,
    config: GameConfig,
    specs: &[PlayerSpec],
    seed: u64,
) -> Result<GameState, RuleError> {
    if specs.len() < 2 || specs.len() > 6 {
        return Err(RuleError::new("Game requires between 2 and 6 players"));
    }

    let mut rng = ChaCha8Rng::seed_from_u64(seed);
    let mut draw_pile: Vec<Card> = map
        .data
        .deck
        .iter()
        .filter(|c| match c {
            Card::Demand { .. } => true,
            Card::Event { effect, .. } => {
                if !config.events_enabled {
                    return false;
                }
                if config.mode == GameMode::Fast && matches!(effect, EventEffect::RailTax) {
                    return false;
                }
                true
            }
        })
        .cloned()
        .collect();
    draw_pile.shuffle(&mut rng);

    let mut chip_supply: HashMap<String, u8> = HashMap::new();
    for c in &map.data.commodities {
        chip_supply.insert(c.id.clone(), c.chips);
    }

    // Deal initial demand cards (set aside any events drawn during setup, then reshuffle them back).
    let hand_size = config.initial_hand_size();
    let mut set_aside_events = Vec::new();
    let mut players = Vec::with_capacity(specs.len());

    for (idx, spec) in specs.iter().enumerate() {
        let mut hand = Vec::with_capacity(hand_size);
        while hand.len() < hand_size {
            let card = draw_pile
                .pop()
                .ok_or_else(|| RuleError::new("Not enough demand cards in deck"))?;
            if card.is_event() {
                set_aside_events.push(card);
            } else {
                hand.push(card);
            }
        }
        players.push(PlayerState {
            id: idx as PlayerId,
            name: spec.name.clone(),
            color: spec
                .color
                .clone()
                .unwrap_or_else(|| PLAYER_COLORS[idx % PLAYER_COLORS.len()].to_string()),
            is_bot: spec.is_bot,
            cash: config.starting_cash(),
            debt: 0,
            train_tier: TrainTier::Freight,
            train_pos: None,
            cargo: Vec::new(),
            hand,
            skip_next_turn: false,
            deliveries_completed: 0,
            total_earned: 0,
            total_spent_building: 0,
        });
    }

    draw_pile.extend(set_aside_events);
    draw_pile.shuffle(&mut rng);

    // Official rule (Page 3): player with the highest single demand payout goes first
    // (tie-broken by sorted descending demand payouts).
    let first_player = players
        .iter()
        .max_by(|a, b| {
            let mut pa: Vec<u32> = a
                .hand
                .iter()
                .flat_map(|c| match c {
                    Card::Demand { demands, .. } => demands.iter().map(|d| d.payout).collect(),
                    Card::Event { .. } => Vec::new(),
                })
                .collect();
            let mut pb: Vec<u32> = b
                .hand
                .iter()
                .flat_map(|c| match c {
                    Card::Demand { demands, .. } => demands.iter().map(|d| d.payout).collect(),
                    Card::Event { .. } => Vec::new(),
                })
                .collect();
            pa.sort_unstable_by(|x, y| y.cmp(x));
            pb.sort_unstable_by(|x, y| y.cmp(x));
            pa.cmp(&pb).then_with(|| b.id.cmp(&a.id))
        })
        .map(|p| p.id)
        .unwrap_or(0);

    let mut state = GameState {
        config,
        rng_seed: seed,
        rng_step: 1,
        first_player,
        initial_step: 0,
        turn_number: 1,
        initial_round: 1,
        current_player: first_player,
        phase: TurnPhase::InitialBuild,
        turn_tracker: TurnTracker::default(),
        final_round: false,
        players,
        tracks: Vec::new(),
        chip_supply,
        draw_pile,
        discard_pile: Vec::new(),
        active_events: Vec::new(),
        winner: None,
        log: Vec::new(),
        next_log_seq: 1,
        undo_checkpoint: None,
    };

    state.push_log(
        None,
        format!(
            "Game started ({:?} mode, events {})",
            state.config.mode,
            if state.config.events_enabled {
                "ON"
            } else {
                "OFF"
            }
        ),
    );
    save_checkpoint(&mut state);
    Ok(state)
}

fn save_checkpoint(state: &mut GameState) {
    state.undo_checkpoint = Some(UndoCheckpoint {
        players: state.players.clone(),
        tracks: state.tracks.clone(),
        chip_supply: state.chip_supply.clone(),
        phase: state.phase,
        turn_tracker: state.turn_tracker.clone(),
    });
    state.turn_tracker.can_undo = false;
}

fn clear_checkpoint(state: &mut GameState) {
    state.undo_checkpoint = None;
    state.turn_tracker.can_undo = false;
}

fn next_rng(state: &mut GameState) -> ChaCha8Rng {
    state.rng_step = state.rng_step.wrapping_add(1);
    ChaCha8Rng::seed_from_u64(
        state
            .rng_seed
            .wrapping_add(state.rng_step.wrapping_mul(0x9E37_79B9_7F4A_7C15)),
    )
}

pub fn active_hazards(map: &MapIndex, state: &GameState) -> ActiveHazards {
    let mut h = ActiveHazards::default();
    for ev in &state.active_events {
        match &ev.effect {
            EventEffect::Flood {
                river_name,
                city_id,
                radius,
            } => {
                let area = map.mileposts_within_radius(city_id, *radius);
                for edge in &map.data.edges {
                    if edge.kind == EdgeKind::River
                        && edge.river_name.as_deref() == Some(river_name.as_str())
                        && (area.contains(&edge.a) || area.contains(&edge.b))
                    {
                        h.blocked_edges.insert(edge_key(edge.a, edge.b));
                    }
                }
            }
            EventEffect::Storm {
                city_id,
                radius,
                block_terrain,
            } => {
                let area = map.mileposts_within_radius(city_id, *radius);
                for mp in area {
                    h.half_speed_nodes.insert(mp);
                    if let Some(bt) = block_terrain {
                        if map.milepost(mp).is_some_and(|m| m.terrain == *bt) {
                            h.blocked_nodes.insert(mp);
                        }
                    }
                }
            }
            EventEffect::Strike { cities, radius } => {
                for cid in cities {
                    h.strike_cities.insert(cid.clone());
                    for mp in map.mileposts_within_radius(cid, *radius) {
                        h.blocked_nodes.insert(mp);
                    }
                }
            }
            EventEffect::Derailment { .. }
            | EventEffect::RailTax
            | EventEffect::HeatingFuelShortage { .. } => {}
        }
    }
    h
}

pub fn player_owned_edges(state: &GameState, pid: PlayerId) -> HashSet<(MilepostId, MilepostId)> {
    state
        .tracks
        .iter()
        .filter(|t| t.owner == pid)
        .map(|t| edge_key(t.a, t.b))
        .collect()
}

/// Official Right-of-Way rule (Page 4): edges already built by any other player cannot be built on.
pub fn opponent_occupied_edges(
    state: &GameState,
    pid: PlayerId,
) -> HashSet<(MilepostId, MilepostId)> {
    state
        .tracks
        .iter()
        .filter(|t| t.owner != pid)
        .map(|t| edge_key(t.a, t.b))
        .collect()
}

pub fn edge_owners_map(state: &GameState) -> HashMap<(MilepostId, MilepostId), Vec<PlayerId>> {
    let mut m: HashMap<(MilepostId, MilepostId), Vec<PlayerId>> = HashMap::new();
    for t in &state.tracks {
        m.entry(edge_key(t.a, t.b)).or_default().push(t.owner);
    }
    m
}

/// All mileposts from which `pid` is legally allowed to start building new track.
pub fn player_build_anchors(map: &MapIndex, state: &GameState, pid: PlayerId) -> Vec<MilepostId> {
    let mut anchors: HashSet<MilepostId> = HashSet::new();

    // Players may always start building from any Major City milepost.
    for cid in &map.major_city_ids {
        if let Some(c) = map.city(cid) {
            for &mp in &c.mileposts {
                anchors.insert(mp);
            }
        }
    }

    // Plus any milepost already connected to the player's track (and all mileposts of any Major City they touch).
    for t in &state.tracks {
        if t.owner == pid {
            anchors.insert(t.a);
            anchors.insert(t.b);
            for mp in [t.a, t.b] {
                if let Some(c) = map.city_at(mp) {
                    if c.size == CitySize::Major {
                        for &other in &c.mileposts {
                            anchors.insert(other);
                        }
                    }
                }
            }
        }
    }

    anchors.into_iter().collect()
}

/// Returns which distinct players currently have track entering `city_id`.
pub fn players_in_city(map: &MapIndex, state: &GameState, city_id: &str) -> HashSet<PlayerId> {
    let mut set = HashSet::new();
    let Some(city) = map.city(city_id) else {
        return set;
    };
    let city_mps: HashSet<MilepostId> = city.mileposts.iter().copied().collect();
    for t in &state.tracks {
        if city_mps.contains(&t.a) || city_mps.contains(&t.b) {
            set.insert(t.owner);
        }
    }
    set
}

pub fn can_enter_city(map: &MapIndex, state: &GameState, pid: PlayerId, city_id: &str) -> bool {
    let Some(city) = map.city(city_id) else {
        return true;
    };
    let Some(limit) = city.size.max_players() else {
        return true;
    };
    let occupants = players_in_city(map, state, city_id);
    occupants.contains(&pid) || occupants.len() < limit
}

/// Largest number of Major Cities connected in a single continuous track component for `pid`.
pub fn connected_major_cities_count(map: &MapIndex, state: &GameState, pid: PlayerId) -> usize {
    connected_major_cities_list(map, state, pid).len()
}

pub fn connected_major_cities_list(
    map: &MapIndex,
    state: &GameState,
    pid: PlayerId,
) -> Vec<String> {
    let mut adj: HashMap<MilepostId, Vec<MilepostId>> = HashMap::new();
    let mut nodes: HashSet<MilepostId> = HashSet::new();

    for t in &state.tracks {
        if t.owner == pid {
            adj.entry(t.a).or_default().push(t.b);
            adj.entry(t.b).or_default().push(t.a);
            nodes.insert(t.a);
            nodes.insert(t.b);
        }
    }

    // Add free internal connections for any Major City touched by the player.
    let touched: Vec<MilepostId> = nodes.iter().copied().collect();
    for mp in touched {
        if let Some(c) = map.city_at(mp) {
            if c.size == CitySize::Major {
                for i in 0..c.mileposts.len() {
                    let a = c.mileposts[i];
                    nodes.insert(a);
                    for &b in &c.mileposts[(i + 1)..] {
                        adj.entry(a).or_default().push(b);
                        adj.entry(b).or_default().push(a);
                    }
                }
            }
        }
    }

    let mut visited: HashSet<MilepostId> = HashSet::new();
    let mut best: Vec<String> = Vec::new();

    for &start in &nodes {
        if !visited.insert(start) {
            continue;
        }
        let mut queue = VecDeque::new();
        queue.push_back(start);
        let mut majors: HashSet<String> = HashSet::new();

        while let Some(cur) = queue.pop_front() {
            if let Some(c) = map.city_at(cur) {
                if c.size == CitySize::Major {
                    majors.insert(c.id.clone());
                }
            }
            if let Some(nbs) = adj.get(&cur) {
                for &nb in nbs {
                    if visited.insert(nb) {
                        queue.push_back(nb);
                    }
                }
            }
        }

        if majors.len() > best.len() {
            let mut list: Vec<String> = majors.into_iter().collect();
            list.sort();
            best = list;
        }
    }

    best
}

pub fn effective_move_limit(map: &MapIndex, state: &GameState, pid: PlayerId) -> u32 {
    let player = &state.players[pid as usize];
    let base = player.train_tier.speed(state.config.mode);
    let hazards = active_hazards(map, state);
    if let Some(pos) = player.train_pos {
        if hazards.half_speed_nodes.contains(&pos) {
            return base.div_ceil(2);
        }
    }
    base
}

/// All mileposts reachable in the remainder of the current Operate phase.
pub fn reachable_mileposts(map: &MapIndex, state: &GameState, pid: PlayerId) -> Vec<MilepostId> {
    let player = &state.players[pid as usize];
    let Some(start) = player.train_pos else {
        return Vec::new();
    };
    let limit = effective_move_limit(map, state, pid);
    let remaining = limit.saturating_sub(state.turn_tracker.moves_used);
    if remaining == 0 {
        return vec![start];
    }

    let hazards = active_hazards(map, state);
    let owners = edge_owners_map(state);
    let mut paid_mask = 0u8;
    for &opp in &state.turn_tracker.paid_opponents {
        paid_mask |= 1u8 << opp;
    }

    let mut reached = HashSet::new();
    let mut best: HashMap<(MilepostId, u8), u32> = HashMap::new();
    let mut q = VecDeque::new();
    q.push_back((start, paid_mask, 0u32, 0u32));
    best.insert((start, paid_mask), 0);
    reached.insert(start);

    while let Some((cur, mask, hops, fee)) = q.pop_front() {
        if hops >= remaining {
            continue;
        }
        for &(next, _) in &map.adj[cur as usize] {
            let ek = edge_key(cur, next);
            let same_major = map.is_same_major_city(cur, next);
            if !same_major
                && (hazards.blocked_edges.contains(&ek)
                    || hazards.blocked_nodes.contains(&cur)
                    || hazards.blocked_nodes.contains(&next))
            {
                continue;
            }
            if same_major {
                let nh = hops + 1;
                if best.get(&(next, mask)).is_none_or(|&old| nh < old) {
                    best.insert((next, mask), nh);
                    reached.insert(next);
                    q.push_back((next, mask, nh, fee));
                }
                continue;
            }
            let Some(edge_owners) = owners.get(&ek) else {
                continue;
            };
            if edge_owners.contains(&pid) {
                let nh = hops + 1;
                if best.get(&(next, mask)).is_none_or(|&old| nh < old) {
                    best.insert((next, mask), nh);
                    reached.insert(next);
                    q.push_back((next, mask, nh, fee));
                }
            } else {
                for &opp in edge_owners {
                    let bit = 1u8 << opp;
                    let (nmask, nfee) = if (mask & bit) != 0 {
                        (mask, fee)
                    } else {
                        (mask | bit, fee + state.config.trackage_fee())
                    };
                    if nfee > player.cash {
                        continue;
                    }
                    let nh = hops + 1;
                    if best.get(&(next, nmask)).is_none_or(|&old| nh < old) {
                        best.insert((next, nmask), nh);
                        reached.insert(next);
                        q.push_back((next, nmask, nh, nfee));
                    }
                }
            }
        }
    }

    let mut out: Vec<MilepostId> = reached.into_iter().collect();
    out.sort_unstable();
    out
}

/// Apply an action for `pid`. Authoritative rules engine entry point.
pub fn apply_action(
    map: &MapIndex,
    state: &mut GameState,
    pid: PlayerId,
    action: Action,
) -> Result<(), RuleError> {
    if state.phase == TurnPhase::Finished {
        return Err(RuleError::new("Game is already finished"));
    }
    if state.current_player != pid {
        return Err(RuleError::new("It is not your turn"));
    }

    match action {
        Action::Undo => handle_undo(state),
        Action::DiscardInitialCards { indices } => handle_discard_initial(state, pid, &indices),
        Action::PlaceTrain { milepost } => handle_place_train(map, state, pid, milepost),
        Action::MoveTrain { path } => handle_move_train(map, state, pid, &path),
        Action::PickupLoad { commodity } => handle_pickup(map, state, pid, &commodity),
        Action::DropLoad { slot } => handle_drop(map, state, pid, slot),
        Action::DeliverLoad {
            slot,
            card_index,
            demand_index,
        } => handle_deliver(map, state, pid, slot, card_index, demand_index),
        Action::DeliverEventBonus {
            slot,
            event_card_id,
        } => handle_deliver_event_bonus(map, state, pid, slot, event_card_id),
        Action::PitchHand => handle_pitch_hand(map, state, pid),
        Action::EndOperatePhase => handle_end_operate(state),
        Action::BuildTrack { edges } => handle_build_track(map, state, pid, &edges),
        Action::UpgradeTrain { target_tier } => handle_upgrade_train(state, pid, target_tier),
        Action::Borrow { amount } => handle_borrow(state, pid, amount),
        Action::EndTurn => handle_end_turn(map, state, pid),
    }
}

fn handle_undo(state: &mut GameState) -> Result<(), RuleError> {
    let Some(cp) = state.undo_checkpoint.clone() else {
        return Err(RuleError::new(
            "Cannot undo past a card draw or start of turn",
        ));
    };
    if !state.turn_tracker.can_undo {
        return Err(RuleError::new("Nothing to undo"));
    }
    state.players = cp.players;
    state.tracks = cp.tracks;
    state.chip_supply = cp.chip_supply;
    state.phase = cp.phase;
    state.turn_tracker = cp.turn_tracker;
    state.turn_tracker.can_undo = false;
    Ok(())
}

fn handle_discard_initial(
    state: &mut GameState,
    pid: PlayerId,
    indices: &[usize],
) -> Result<(), RuleError> {
    if state.phase != TurnPhase::TrimHand {
        return Err(RuleError::new("Not in TrimHand phase"));
    }
    let hand_len = state.players[pid as usize].hand.len();
    let expected = hand_len.saturating_sub(3);
    if indices.len() != expected {
        return Err(RuleError::new(format!(
            "Must discard exactly {expected} card(s) to keep 3"
        )));
    }
    let mut sorted = indices.to_vec();
    sorted.sort_unstable();
    sorted.dedup();
    if sorted.len() != expected || sorted.iter().any(|&i| i >= hand_len) {
        return Err(RuleError::new("Invalid card indices"));
    }

    for &i in sorted.iter().rev() {
        let card = state.players[pid as usize].hand.remove(i);
        state.discard_pile.push(card);
    }

    let pname = state.players[pid as usize].name.clone();
    state.push_log(Some(pid), format!("{pname} kept 3 starting demand cards"));

    // Advance to next player who still has >3 cards, or start regular Operate play.
    let n = state.players.len() as PlayerId;
    let next = (pid + 1) % n;
    state.current_player = next;
    if state.players[next as usize].hand.len() > 3 {
        state.phase = TurnPhase::TrimHand;
    } else {
        state.phase = TurnPhase::Operate;
        state.turn_number += 1;
    }
    state.turn_tracker = TurnTracker::default();
    save_checkpoint(state);
    Ok(())
}

fn handle_place_train(
    map: &MapIndex,
    state: &mut GameState,
    pid: PlayerId,
    milepost: MilepostId,
) -> Result<(), RuleError> {
    if state.phase != TurnPhase::Operate {
        return Err(RuleError::new("Can only place train during Operate phase"));
    }
    if state.players[pid as usize].train_pos.is_some() {
        return Err(RuleError::new("Train is already placed"));
    }
    let Some(city) = map.city_at(milepost) else {
        return Err(RuleError::new("Must place train on a city milepost"));
    };
    let city_name = city.name.clone();
    state.players[pid as usize].train_pos = Some(milepost);
    state.turn_tracker.has_acted_this_turn = true;
    state.turn_tracker.can_undo = state.undo_checkpoint.is_some();

    let pname = state.players[pid as usize].name.clone();
    state.push_log(Some(pid), format!("{pname} placed train at {city_name}"));
    Ok(())
}

fn handle_move_train(
    map: &MapIndex,
    state: &mut GameState,
    pid: PlayerId,
    path: &[MilepostId],
) -> Result<(), RuleError> {
    if state.phase != TurnPhase::Operate {
        return Err(RuleError::new("Can only move train during Operate phase"));
    }
    if path.len() < 2 {
        return Err(RuleError::new("Move path must have at least 2 mileposts"));
    }
    let Some(start) = state.players[pid as usize].train_pos else {
        return Err(RuleError::new("Place your train at a city first"));
    };
    if path[0] != start {
        return Err(RuleError::new(
            "Move path must start at current train position",
        ));
    }

    let hazards = active_hazards(map, state);
    let owners = edge_owners_map(state);
    let base_speed = state.players[pid as usize]
        .train_tier
        .speed(state.config.mode);

    let mut entered_storm = hazards.half_speed_nodes.contains(&start);
    let mut paid_mask = 0u8;
    for &opp in &state.turn_tracker.paid_opponents {
        paid_mask |= 1u8 << opp;
    }
    let mut foreign_edge_masks: Vec<u8> = Vec::new();

    for win in path.windows(2) {
        let (a, b) = (win[0], win[1]);
        let ek = edge_key(a, b);
        if !map.edge_map.contains_key(&ek) {
            return Err(RuleError::new(format!(
                "Mileposts {a} and {b} are not adjacent"
            )));
        }
        let same_major = map.is_same_major_city(a, b);
        if !same_major
            && (hazards.blocked_edges.contains(&ek)
                || hazards.blocked_nodes.contains(&a)
                || hazards.blocked_nodes.contains(&b))
        {
            return Err(RuleError::new("Route is blocked by an active event"));
        }
        if hazards.half_speed_nodes.contains(&b) {
            entered_storm = true;
        }
        if same_major {
            continue;
        }
        let Some(edge_owners) = owners.get(&ek) else {
            return Err(RuleError::new("No track built along that segment"));
        };
        if !edge_owners.contains(&pid) {
            let mut m = 0u8;
            for &o in edge_owners {
                m |= 1u8 << o;
            }
            if (m & paid_mask) == 0 && !foreign_edge_masks.contains(&m) {
                foreign_edge_masks.push(m);
            }
        }
    }

    // Find minimum-cardinality set of new opponents covering every foreign edge on the path.
    let mut best_new_mask: Option<u8> = None;
    let n_players = state.players.len() as u8;
    let all_masks = 1u8 << n_players;
    for cand in 0..all_masks {
        if (cand & paid_mask) != 0 || (cand & (1u8 << pid)) != 0 {
            continue;
        }
        if best_new_mask.is_some_and(|b| cand.count_ones() >= b.count_ones()) {
            continue;
        }
        if foreign_edge_masks.iter().all(|&em| (em & cand) != 0) {
            best_new_mask = Some(cand);
        }
    }
    let new_mask = best_new_mask.unwrap_or(0);
    let mut new_opponents: Vec<PlayerId> = Vec::new();
    for opp in 0..n_players {
        if (new_mask & (1u8 << opp)) != 0 {
            new_opponents.push(opp);
        }
    }

    let speed_limit = if entered_storm {
        base_speed.div_ceil(2)
    } else {
        base_speed
    };
    let steps = (path.len() - 1) as u32;
    if state.turn_tracker.moves_used + steps > speed_limit {
        return Err(RuleError::new(format!(
            "Move exceeds speed limit ({} + {} > {})",
            state.turn_tracker.moves_used, steps, speed_limit
        )));
    }

    let total_fee = new_opponents.len() as u32 * state.config.trackage_fee();
    if state.players[pid as usize].cash < total_fee {
        return Err(RuleError::new(format!(
            "Need ${total_fee}M cash to pay opponent trackage fees"
        )));
    }

    // Commit movement & fees.
    state.players[pid as usize].cash -= total_fee;
    let fee_each = state.config.trackage_fee();
    for opp in &new_opponents {
        state.players[*opp as usize].cash += fee_each;
        state.turn_tracker.paid_opponents.push(*opp);
        let pname = state.players[pid as usize].name.clone();
        let oname = state.players[*opp as usize].name.clone();
        state.push_log(
            Some(pid),
            format!("{pname} paid {oname} ${fee_each}M for trackage rights"),
        );
    }

    let dest = *path.last().unwrap();
    state.players[pid as usize].train_pos = Some(dest);
    state.turn_tracker.moves_used += steps;
    state.turn_tracker.has_acted_this_turn = true;
    state.turn_tracker.can_undo = state.undo_checkpoint.is_some();
    Ok(())
}

fn handle_pickup(
    map: &MapIndex,
    state: &mut GameState,
    pid: PlayerId,
    commodity: &str,
) -> Result<(), RuleError> {
    if state.phase != TurnPhase::Operate {
        return Err(RuleError::new(
            "Can only pick up loads during Operate phase",
        ));
    }
    let Some(pos) = state.players[pid as usize].train_pos else {
        return Err(RuleError::new("Train is not placed yet"));
    };
    let Some(city) = map.city_at(pos) else {
        return Err(RuleError::new("Train must be at a city to pick up a load"));
    };
    let hazards = active_hazards(map, state);
    if hazards.strike_cities.contains(&city.id) {
        return Err(RuleError::new("City is on strike — no pickups allowed"));
    }
    if !city.commodities.iter().any(|c| c == commodity) {
        return Err(RuleError::new(format!(
            "{} does not produce {commodity}",
            city.name
        )));
    }
    let cap = state.players[pid as usize].train_tier.capacity();
    if state.players[pid as usize].cargo.len() >= cap {
        return Err(RuleError::new("Train cargo holds are full"));
    }
    let supply = state
        .chip_supply
        .get_mut(commodity)
        .ok_or_else(|| RuleError::new(format!("Unknown commodity: {commodity}")))?;
    if *supply == 0 {
        return Err(RuleError::new(format!(
            "No {commodity} load chips left in supply"
        )));
    }
    *supply -= 1;
    state.players[pid as usize]
        .cargo
        .push(commodity.to_string());
    state.turn_tracker.has_acted_this_turn = true;
    state.turn_tracker.can_undo = state.undo_checkpoint.is_some();
    Ok(())
}

fn handle_drop(
    map: &MapIndex,
    state: &mut GameState,
    pid: PlayerId,
    slot: usize,
) -> Result<(), RuleError> {
    if state.phase != TurnPhase::Operate {
        return Err(RuleError::new("Can only drop loads during Operate phase"));
    }
    let Some(pos) = state.players[pid as usize].train_pos else {
        return Err(RuleError::new("Train is not placed yet"));
    };
    if map.city_at(pos).is_none() {
        return Err(RuleError::new("Train must be at a city to drop a load"));
    }
    if slot >= state.players[pid as usize].cargo.len() {
        return Err(RuleError::new("Invalid cargo slot"));
    }
    let comm = state.players[pid as usize].cargo.remove(slot);
    if let Some(s) = state.chip_supply.get_mut(&comm) {
        *s += 1;
    }
    state.turn_tracker.has_acted_this_turn = true;
    state.turn_tracker.can_undo = state.undo_checkpoint.is_some();
    Ok(())
}

fn handle_deliver(
    map: &MapIndex,
    state: &mut GameState,
    pid: PlayerId,
    slot: usize,
    card_index: usize,
    demand_index: usize,
) -> Result<(), RuleError> {
    if state.phase != TurnPhase::Operate {
        return Err(RuleError::new(
            "Can only deliver loads during Operate phase",
        ));
    }
    let Some(pos) = state.players[pid as usize].train_pos else {
        return Err(RuleError::new("Train is not placed yet"));
    };
    let Some(city) = map.city_at(pos) else {
        return Err(RuleError::new("Train must be at a city to deliver"));
    };
    let city_id = city.id.clone();
    let city_name = city.name.clone();

    let hazards = active_hazards(map, state);
    if hazards.strike_cities.contains(&city_id) {
        return Err(RuleError::new("City is on strike — no deliveries allowed"));
    }

    let cargo_comm = state.players[pid as usize]
        .cargo
        .get(slot)
        .cloned()
        .ok_or_else(|| RuleError::new("Invalid cargo slot"))?;

    let card = state.players[pid as usize]
        .hand
        .get(card_index)
        .cloned()
        .ok_or_else(|| RuleError::new("Invalid card index"))?;

    let demand = match &card {
        Card::Demand { demands, .. } => demands
            .get(demand_index)
            .ok_or_else(|| RuleError::new("Invalid demand index"))?
            .clone(),
        Card::Event { .. } => return Err(RuleError::new("Selected card is not a demand card")),
    };

    if demand.city_id != city_id || demand.commodity != cargo_comm {
        return Err(RuleError::new(
            "Cargo and current city do not match selected demand",
        ));
    }

    // Execute delivery.
    state.players[pid as usize].cargo.remove(slot);
    if let Some(s) = state.chip_supply.get_mut(&cargo_comm) {
        *s += 1;
    }

    // Pay out (automatically servicing any emergency debt first).
    let payout = demand.payout;
    let repaid = payout.min(state.players[pid as usize].debt);
    state.players[pid as usize].debt -= repaid;
    state.players[pid as usize].cash += payout - repaid;
    state.players[pid as usize].deliveries_completed += 1;
    state.players[pid as usize].total_earned += payout;

    // Discard used card and draw replacement (cannot undo past card draw).
    let discarded = state.players[pid as usize].hand.remove(card_index);
    state.discard_pile.push(discarded);
    state.turn_tracker.has_acted_this_turn = true;
    clear_checkpoint(state);

    let pname = state.players[pid as usize].name.clone();
    let comm_name = map
        .commodity_by_id
        .get(&cargo_comm)
        .map(|&i| map.data.commodities[i].name.as_str())
        .unwrap_or(&cargo_comm);
    state.push_log(
        Some(pid),
        format!("{pname} delivered {comm_name} to {city_name} for ${payout}M"),
    );

    draw_until_hand_full(map, state, pid, 3);
    save_checkpoint(state);
    Ok(())
}

fn handle_deliver_event_bonus(
    map: &MapIndex,
    state: &mut GameState,
    pid: PlayerId,
    slot: usize,
    event_card_id: u16,
) -> Result<(), RuleError> {
    if state.phase != TurnPhase::Operate {
        return Err(RuleError::new("Can only deliver during Operate phase"));
    }
    let Some(pos) = state.players[pid as usize].train_pos else {
        return Err(RuleError::new("Train is not placed yet"));
    };
    let Some(city) = map.city_at(pos) else {
        return Err(RuleError::new("Train must be at a city"));
    };
    let city_id = city.id.clone();
    let city_name = city.name.clone();

    let ev_idx = state
        .active_events
        .iter()
        .position(|e| e.card_id == event_card_id)
        .ok_or_else(|| RuleError::new("Active bonus event not found"))?;

    let (req_comm, targets, bonus, title) = match &state.active_events[ev_idx].effect {
        EventEffect::HeatingFuelShortage {
            commodity,
            target_cities,
            bonus,
        } => (
            commodity.clone(),
            target_cities.clone(),
            *bonus,
            state.active_events[ev_idx].title.clone(),
        ),
        _ => return Err(RuleError::new("Event does not accept deliveries")),
    };

    let cargo_comm = state.players[pid as usize]
        .cargo
        .get(slot)
        .cloned()
        .ok_or_else(|| RuleError::new("Invalid cargo slot"))?;

    if (cargo_comm != req_comm && cargo_comm != "coal") || !targets.iter().any(|c| c == &city_id) {
        return Err(RuleError::new(
            "Cargo/city does not satisfy Heating Fuel Shortage",
        ));
    }

    state.players[pid as usize].cargo.remove(slot);
    if let Some(s) = state.chip_supply.get_mut(&cargo_comm) {
        *s += 1;
    }
    let repaid = bonus.min(state.players[pid as usize].debt);
    state.players[pid as usize].debt -= repaid;
    state.players[pid as usize].cash += bonus - repaid;
    state.players[pid as usize].deliveries_completed += 1;
    state.players[pid as usize].total_earned += bonus;
    state.active_events.remove(ev_idx);
    state.turn_tracker.has_acted_this_turn = true;
    clear_checkpoint(state);
    save_checkpoint(state);

    let pname = state.players[pid as usize].name.clone();
    state.push_log(
        Some(pid),
        format!("{pname} fulfilled {title} at {city_name} for ${bonus}M"),
    );
    Ok(())
}

fn handle_pitch_hand(
    map: &MapIndex,
    state: &mut GameState,
    pid: PlayerId,
) -> Result<(), RuleError> {
    if state.phase != TurnPhase::Operate {
        return Err(RuleError::new(
            "Can only pitch hand at the start of your Operate phase",
        ));
    }
    if state.turn_tracker.has_acted_this_turn {
        return Err(RuleError::new(
            "Cannot pitch hand after already moving, loading, or delivering this turn",
        ));
    }

    let old: Vec<Card> = std::mem::take(&mut state.players[pid as usize].hand);
    state.discard_pile.extend(old);
    clear_checkpoint(state);

    let pname = state.players[pid as usize].name.clone();
    state.push_log(
        Some(pid),
        format!("{pname} pitched hand for 3 new demand cards (turn ends)"),
    );

    draw_until_hand_full(map, state, pid, 3);
    advance_turn(map, state, pid);
    Ok(())
}

fn handle_end_operate(state: &mut GameState) -> Result<(), RuleError> {
    if state.phase != TurnPhase::Operate {
        return Err(RuleError::new("Not in Operate phase"));
    }
    state.phase = TurnPhase::Build;
    state.turn_tracker.can_undo = state.undo_checkpoint.is_some();
    Ok(())
}

fn handle_build_track(
    map: &MapIndex,
    state: &mut GameState,
    pid: PlayerId,
    edges: &[(MilepostId, MilepostId)],
) -> Result<(), RuleError> {
    if state.phase != TurnPhase::InitialBuild && state.phase != TurnPhase::Build {
        return Err(RuleError::new(
            "Can only build track during InitialBuild or Build phase",
        ));
    }
    if state.turn_tracker.upgraded_this_turn {
        return Err(RuleError::new(
            "Cannot build track in the same turn you upgraded your train",
        ));
    }
    if edges.is_empty() {
        return Err(RuleError::new("No track edges specified"));
    }

    let hazards = active_hazards(map, state);
    let mut owned = player_owned_edges(state, pid);
    let occupied_by_others = opponent_occupied_edges(state, pid);
    let mut anchors: HashSet<MilepostId> =
        player_build_anchors(map, state, pid).into_iter().collect();

    let mut total_cost = 0u32;
    let mut major_exits = state.turn_tracker.major_city_exits;
    let mut to_add: Vec<(MilepostId, MilepostId)> = Vec::with_capacity(edges.len());

    // Track cities newly entered in this batch to enforce entry caps cleanly.
    let mut batch_entered_cities: HashSet<String> = HashSet::new();

    for &(from, to) in edges {
        let ek = edge_key(from, to);
        if map.is_same_major_city(from, to) {
            continue;
        }
        if owned.contains(&ek) {
            return Err(RuleError::new("You already own track on that segment"));
        }
        if occupied_by_others.contains(&ek) {
            return Err(RuleError::new(
                "Right of Way: another player already owns track on that segment",
            ));
        }
        let step_cost = map
            .build_step_cost(from, to)
            .ok_or_else(|| RuleError::new(format!("Invalid build segment {from} -> {to}")))?;

        if hazards.blocked_edges.contains(&ek)
            || hazards.blocked_nodes.contains(&from)
            || hazards.blocked_nodes.contains(&to)
        {
            return Err(RuleError::new(
                "Cannot build there while an active event blocks the area",
            ));
        }

        if !anchors.contains(&from) {
            return Err(RuleError::new(format!(
                "Segment {from} -> {to} is not connected to your network or a Major City"
            )));
        }

        // Official rule (Page 5): at most 2 track segments may be built OUT OF major city mileposts per turn.
        if map.city_at(from).is_some_and(|c| c.size == CitySize::Major) {
            major_exits += 1;
            if major_exits > 2 {
                return Err(RuleError::new(
                    "May not build more than 2 track segments out of Major Cities in one turn",
                ));
            }
        }

        if let Some(dest_city) = map.city_at(to) {
            if !batch_entered_cities.contains(&dest_city.id)
                && !can_enter_city(map, state, pid, &dest_city.id)
            {
                return Err(RuleError::new(format!(
                    "{} has reached its maximum player entry limit",
                    dest_city.name
                )));
            }
            batch_entered_cities.insert(dest_city.id.clone());
            if dest_city.size == CitySize::Major {
                for &m in &dest_city.mileposts {
                    anchors.insert(m);
                }
            }
        }

        total_cost += step_cost;
        owned.insert(ek);
        anchors.insert(to);
        to_add.push(ek);
    }

    if to_add.is_empty() {
        return Err(RuleError::new("No new track segments to build"));
    }

    let budget = state.config.build_budget_per_turn();
    if state.turn_tracker.build_spent + total_cost > budget {
        return Err(RuleError::new(format!(
            "Build cost ${total_cost}M exceeds remaining ${}M turn budget",
            budget.saturating_sub(state.turn_tracker.build_spent)
        )));
    }
    if state.players[pid as usize].cash < total_cost {
        return Err(RuleError::new(format!(
            "Not enough cash (need ${total_cost}M, have ${}M)",
            state.players[pid as usize].cash
        )));
    }

    state.players[pid as usize].cash -= total_cost;
    state.players[pid as usize].total_spent_building += total_cost;
    state.turn_tracker.build_spent += total_cost;
    state.turn_tracker.major_city_exits = major_exits;
    state.turn_tracker.has_acted_this_turn = true;
    state.turn_tracker.can_undo = state.undo_checkpoint.is_some();

    for (a, b) in &to_add {
        state.tracks.push(TrackSegment {
            a: *a,
            b: *b,
            owner: pid,
        });
    }

    let pname = state.players[pid as usize].name.clone();
    state.push_log(
        Some(pid),
        format!(
            "{pname} built {} track segment(s) for ${total_cost}M",
            to_add.len()
        ),
    );
    Ok(())
}

fn handle_upgrade_train(
    state: &mut GameState,
    pid: PlayerId,
    target_tier: TrainTier,
) -> Result<(), RuleError> {
    if state.phase != TurnPhase::Build && state.phase != TurnPhase::InitialBuild {
        return Err(RuleError::new(
            "Can only upgrade train during InitialBuild or Build phase",
        ));
    }
    let cur = state.players[pid as usize].train_tier;
    let is_crossgrade = cur.can_crossgrade_to(target_tier);
    if !cur.can_upgrade_to(target_tier) && !is_crossgrade {
        return Err(RuleError::new(format!(
            "Cannot upgrade directly from {} to {}",
            cur.label(),
            target_tier.label()
        )));
    }

    let cost = if is_crossgrade {
        5
    } else {
        state.config.upgrade_cost()
    };

    if !is_crossgrade
        && (state.turn_tracker.build_spent > 0 || state.turn_tracker.upgraded_this_turn)
    {
        return Err(RuleError::new(
            "Upgrading your train consumes your entire Build phase",
        ));
    }
    if is_crossgrade && state.turn_tracker.build_spent + cost > state.config.build_budget_per_turn()
    {
        return Err(RuleError::new(
            "Crossgrade ($5M) exceeds remaining turn budget",
        ));
    }
    if state.players[pid as usize].cash < cost {
        return Err(RuleError::new(format!("Need ${cost}M to upgrade train")));
    }

    state.players[pid as usize].cash -= cost;
    state.players[pid as usize].train_tier = target_tier;
    state.turn_tracker.build_spent += cost;
    if !is_crossgrade {
        state.turn_tracker.upgraded_this_turn = true;
    }
    state.turn_tracker.has_acted_this_turn = true;
    state.turn_tracker.can_undo = state.undo_checkpoint.is_some();

    let pname = state.players[pid as usize].name.clone();
    let verb = if is_crossgrade {
        "crossgraded"
    } else {
        "upgraded"
    };
    state.push_log(
        Some(pid),
        format!("{pname} {verb} train to {} (${cost}M)", target_tier.label()),
    );
    Ok(())
}

fn handle_borrow(state: &mut GameState, pid: PlayerId, amount: u32) -> Result<(), RuleError> {
    if amount == 0 || amount > 20 {
        return Err(RuleError::new("Loan amount must be between $1M and $20M"));
    }
    if state.players[pid as usize].debt > 0 {
        return Err(RuleError::new("Repay existing debt before borrowing again"));
    }
    state.players[pid as usize].cash += amount;
    state.players[pid as usize].debt += amount * 2;
    state.turn_tracker.can_undo = state.undo_checkpoint.is_some();

    let pname = state.players[pid as usize].name.clone();
    state.push_log(
        Some(pid),
        format!("{pname} borrowed ${amount}M (owes ${}M)", amount * 2),
    );
    Ok(())
}

fn qualifies_for_victory(map: &MapIndex, state: &GameState, pid: PlayerId) -> bool {
    let p = &state.players[pid as usize];
    p.cash >= state.config.victory_cash
        && p.debt == 0
        && connected_major_cities_count(map, state, pid) >= state.config.victory_major_cities
}

fn handle_end_turn(map: &MapIndex, state: &mut GameState, pid: PlayerId) -> Result<(), RuleError> {
    if state.phase == TurnPhase::TrimHand {
        return Err(RuleError::new("Discard down to 3 cards before ending turn"));
    }

    // Official rule (Page 9): declaring victory triggers the Equal Turns final round!
    if !state.final_round && qualifies_for_victory(map, state, pid) {
        state.final_round = true;
        let pname = state.players[pid as usize].name.clone();
        state.push_log(
            Some(pid),
            format!("{pname} declared victory! Finishing current round for equal turns."),
        );
    }

    let n = state.players.len() as PlayerId;
    let next_clockwise = (pid + 1) % n;
    let round_complete = next_clockwise == state.first_player;

    if state.final_round && round_complete {
        let mut qualifiers: Vec<(PlayerId, u32)> = state
            .players
            .iter()
            .filter(|p| qualifies_for_victory(map, state, p.id))
            .map(|p| (p.id, p.cash))
            .collect();
        qualifiers.sort_by_key(|a| std::cmp::Reverse(a.1));

        if let Some(&(best_pid, best_cash)) = qualifiers.first() {
            let tied = qualifiers.len() > 1 && qualifiers[1].1 == best_cash;
            if tied {
                // Official Page 9 tiebreaker: raise cash target by $50M and continue!
                state.config.victory_cash += 50;
                state.final_round = false;
                state.push_log(
                    None,
                    format!(
                        "Victory tie at ${best_cash}M! Target raised to ${}M — play continues!",
                        state.config.victory_cash
                    ),
                );
            } else {
                state.winner = Some(best_pid);
                state.phase = TurnPhase::Finished;
                clear_checkpoint(state);
                let pname = state.players[best_pid as usize].name.clone();
                state.push_log(Some(best_pid), format!("{pname} WINS the game!"));
                return Ok(());
            }
        } else {
            state.final_round = false;
        }
    }

    advance_turn(map, state, pid);
    Ok(())
}

/// Official Switchback Start (Page 5): Round 1 clockwise from `first_player`,
/// Round 2 counterclockwise (last player goes twice in a row), Round 3 (Fast) clockwise.
fn switchback_player(n: usize, first: PlayerId, step: usize) -> (u8, PlayerId) {
    let round = (step / n) as u8 + 1;
    let offset = step % n;
    let idx = if round % 2 == 1 {
        (first as usize + offset) % n
    } else {
        (first as usize + n - 1 - offset) % n
    };
    (round, idx as PlayerId)
}

fn advance_turn(map: &MapIndex, state: &mut GameState, finished_pid: PlayerId) {
    // Expire events that lasted until the end of `finished_pid`'s turn.
    state
        .active_events
        .retain(|e| e.expires_after_turn_of != Some(finished_pid));

    let n = state.players.len();

    if state.phase == TurnPhase::InitialBuild {
        state.initial_step += 1;
        let total_initial_steps = n * state.config.initial_build_rounds() as usize;
        if state.initial_step < total_initial_steps {
            let (round, next_pid) = switchback_player(n, state.first_player, state.initial_step);
            if round > state.initial_round {
                state.initial_round = round;
                state.turn_number += 1;
            }
            state.current_player = next_pid;
        } else {
            state.current_player = state.first_player;
            if state.players[state.first_player as usize].hand.len() > 3 {
                state.phase = TurnPhase::TrimHand;
            } else {
                state.phase = TurnPhase::Operate;
                state.turn_number += 1;
            }
        }
        state.turn_tracker = TurnTracker::default();
        save_checkpoint(state);
        return;
    }

    let n_u8 = n as PlayerId;
    let mut next = (finished_pid + 1) % n_u8;

    // Regular turn advancement; skip players who lost their turn to a derailment.
    for _ in 0..n_u8 {
        if next == state.first_player {
            state.turn_number += 1;
        }
        if state.players[next as usize].skip_next_turn {
            state.players[next as usize].skip_next_turn = false;
            let pname = state.players[next as usize].name.clone();
            state.push_log(
                Some(next),
                format!("{pname} skipped turn due to derailment"),
            );
            state
                .active_events
                .retain(|e| e.expires_after_turn_of != Some(next));
            next = (next + 1) % n_u8;
        } else {
            break;
        }
    }

    let _ = map;
    state.current_player = next;
    state.phase = TurnPhase::Operate;
    state.turn_tracker = TurnTracker::default();
    save_checkpoint(state);
}

fn draw_until_hand_full(map: &MapIndex, state: &mut GameState, pid: PlayerId, target: usize) {
    let mut safety = 0;
    while state.players[pid as usize].hand.len() < target && safety < 64 {
        safety += 1;
        if state.draw_pile.is_empty() {
            if state.discard_pile.is_empty() {
                break;
            }
            let mut rng = next_rng(state);
            state.draw_pile.append(&mut state.discard_pile);
            state.draw_pile.shuffle(&mut rng);
            state.push_log(None, "Reshuffled discard pile into draw deck");
        }
        let Some(card) = state.draw_pile.pop() else {
            break;
        };
        match card {
            Card::Demand { .. } => {
                state.players[pid as usize].hand.push(card);
            }
            Card::Event {
                id,
                title,
                description,
                effect,
            } => {
                resolve_event(map, state, pid, id, title, description, effect);
                state.discard_pile.push(Card::Event {
                    id,
                    title: String::new(),
                    description: String::new(),
                    effect: EventEffect::RailTax,
                });
                // Re-insert the exact original event card into discard_pile cleanly:
                state.discard_pile.pop();
                if let Some(orig) = map.data.deck.iter().find(|c| c.id() == id) {
                    state.discard_pile.push(orig.clone());
                }
            }
        }
    }
}

fn resolve_event(
    map: &MapIndex,
    state: &mut GameState,
    drawer: PlayerId,
    card_id: u16,
    title: String,
    description: String,
    effect: EventEffect,
) {
    state.push_log(Some(drawer), format!("EVENT: {title} — {description}"));

    match &effect {
        EventEffect::Derailment { cities, radius } => {
            let mut affected = HashSet::new();
            for cid in cities {
                affected.extend(map.mileposts_within_radius(cid, *radius));
            }
            for p in &mut state.players {
                if p.train_pos.is_some_and(|pos| affected.contains(&pos)) {
                    p.skip_next_turn = true;
                    if let Some(lost) = p.cargo.pop() {
                        if let Some(s) = state.chip_supply.get_mut(&lost) {
                            *s += 1;
                        }
                    }
                }
            }
        }
        EventEffect::Flood {
            river_name,
            city_id,
            radius,
        } => {
            let area = map.mileposts_within_radius(city_id, *radius);
            let mut washed_edges = HashSet::new();
            for e in &map.data.edges {
                if e.kind == EdgeKind::River
                    && e.river_name.as_deref() == Some(river_name.as_str())
                    && (area.contains(&e.a) || area.contains(&e.b))
                {
                    washed_edges.insert(edge_key(e.a, e.b));
                }
            }
            state
                .tracks
                .retain(|t| !washed_edges.contains(&edge_key(t.a, t.b)));
            state.active_events.push(ActiveEvent {
                card_id,
                title,
                description,
                effect,
                drawn_by: drawer,
                expires_after_turn_of: Some(drawer),
            });
        }
        EventEffect::Storm { .. } | EventEffect::Strike { .. } => {
            state.active_events.push(ActiveEvent {
                card_id,
                title,
                description,
                effect,
                drawn_by: drawer,
                expires_after_turn_of: Some(drawer),
            });
        }
        EventEffect::RailTax => {
            if state.config.mode != GameMode::Fast {
                for p in &mut state.players {
                    let tax = match p.cash {
                        0..=49 => 0,
                        50..=99 => 10,
                        100..=149 => 15,
                        150..=199 => 20,
                        _ => 25,
                    };
                    p.cash = p.cash.saturating_sub(tax);
                }
            }
        }
        EventEffect::HeatingFuelShortage { .. } => {
            if !state
                .active_events
                .iter()
                .any(|e| matches!(e.effect, EventEffect::HeatingFuelShortage { .. }))
            {
                state.active_events.push(ActiveEvent {
                    card_id,
                    title,
                    description,
                    effect,
                    drawn_by: drawer,
                    expires_after_turn_of: None,
                });
            }
        }
    }
}

/// Strict invariant checker used by tests and the 1,000-game simulator to flush out bugs.
pub fn verify_invariants(map: &MapIndex, state: &GameState) -> Result<(), String> {
    // 1. Commodity chip conservation: supply + all cargo == initial map chip counts.
    let mut counted: HashMap<String, u32> = HashMap::new();
    for (k, &v) in &state.chip_supply {
        *counted.entry(k.clone()).or_default() += v as u32;
    }
    for p in &state.players {
        if p.cargo.len() > p.train_tier.capacity() {
            return Err(format!(
                "Player {} cargo {} exceeds capacity {}",
                p.id,
                p.cargo.len(),
                p.train_tier.capacity()
            ));
        }
        for c in &p.cargo {
            *counted.entry(c.clone()).or_default() += 1;
        }
    }
    for comm in &map.data.commodities {
        let got = counted.get(&comm.id).copied().unwrap_or(0);
        if got != comm.chips as u32 {
            return Err(format!(
                "Chip conservation violated for {}: expected {}, got {}",
                comm.id, comm.chips, got
            ));
        }
    }

    // 2. Right of Way: at most ONE player may own track on any edge, and all edges exist in map.
    let mut seen: HashSet<(MilepostId, MilepostId)> = HashSet::new();
    for t in &state.tracks {
        let ek = edge_key(t.a, t.b);
        if !map.edge_map.contains_key(&ek) {
            return Err(format!("Track edge {:?} does not exist in map", ek));
        }
        if !seen.insert(ek) {
            return Err(format!(
                "Right of Way violated: multiple tracks on edge {:?}",
                ek
            ));
        }
    }

    // 3. City entry caps respected.
    for city in &map.data.cities {
        if let Some(limit) = city.size.max_players() {
            let occ = players_in_city(map, state, &city.id);
            if occ.len() > limit {
                return Err(format!(
                    "City {} has {} players, exceeding limit {}",
                    city.name,
                    occ.len(),
                    limit
                ));
            }
        }
    }

    // 4. Valid hand contents (never hold Event cards in hand) and train positions.
    for p in &state.players {
        for c in &p.hand {
            if c.is_event() {
                return Err(format!("Player {} holds an Event card in hand", p.id));
            }
        }
        if let Some(pos) = p.train_pos {
            if (pos as usize) >= map.data.mileposts.len() {
                return Err(format!("Player {} train_pos {} out of bounds", p.id, pos));
            }
        }
    }

    // 5. Turn build budget never exceeded.
    if state.turn_tracker.build_spent > state.config.build_budget_per_turn() {
        return Err(format!(
            "build_spent {} exceeds budget {}",
            state.turn_tracker.build_spent,
            state.config.build_budget_per_turn()
        ));
    }

    Ok(())
}
