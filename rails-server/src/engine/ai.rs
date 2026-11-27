use crate::engine::map::{Card, CitySize, EventEffect, MapIndex, MilepostId, PlayerId};
use crate::engine::rules::{
    active_hazards, apply_action, can_enter_city, connected_major_cities_list, edge_owners_map,
    effective_move_limit, opponent_occupied_edges, player_owned_edges,
};
use crate::engine::state::{Action, GameState, TrainTier, TurnPhase};
use std::collections::{HashSet, VecDeque};

#[derive(Debug, Clone)]
struct DemandPlan {
    card_index: usize,
    commodity: String,
    source_city: String,
    source_mp: MilepostId,
    dest_mp: MilepostId,
    build_cost: u32,
    score: f32,
}

/// Play one complete turn for the current player (used by both the simulator and multiplayer bot seats).
/// Returns the number of actions applied during the turn.
pub fn play_ai_turn(map: &MapIndex, state: &mut GameState) -> Result<usize, String> {
    let pid = state.current_player;
    let mut steps = 0usize;

    match state.phase {
        TurnPhase::Finished => return Ok(0),
        TurnPhase::TrimHand => {
            let discard = choose_trim_discards(map, state, pid);
            apply_action(
                map,
                state,
                pid,
                Action::DiscardInitialCards { indices: discard },
            )
            .map_err(|e| e.message)?;
            return Ok(1);
        }
        TurnPhase::InitialBuild => {
            steps += ai_build_phase(map, state, pid)?;
            apply_action(map, state, pid, Action::EndTurn).map_err(|e| e.message)?;
            return Ok(steps + 1);
        }
        TurnPhase::Operate => {
            steps += ai_operate_phase(map, state, pid)?;
            // PitchHand already ends the turn and switches player.
            if state.current_player != pid || state.phase == TurnPhase::Finished {
                return Ok(steps);
            }
            apply_action(map, state, pid, Action::EndOperatePhase).map_err(|e| e.message)?;
            steps += 1;
            steps += ai_build_phase(map, state, pid)?;
            apply_action(map, state, pid, Action::EndTurn).map_err(|e| e.message)?;
            steps += 1;
        }
        TurnPhase::Build => {
            steps += ai_build_phase(map, state, pid)?;
            apply_action(map, state, pid, Action::EndTurn).map_err(|e| e.message)?;
            steps += 1;
        }
    }

    Ok(steps)
}

/// Anchors for AI building: if the AI has existing track, always expand from its connected network
/// (so it builds one unified railroad empire); only use all 6 Major Cities before its first track!
fn ai_network_anchors(map: &MapIndex, state: &GameState, pid: PlayerId) -> Vec<MilepostId> {
    let mut owned_nodes: HashSet<MilepostId> = HashSet::new();
    for t in &state.tracks {
        if t.owner == pid {
            owned_nodes.insert(t.a);
            owned_nodes.insert(t.b);
        }
    }

    if owned_nodes.is_empty() {
        // First build ever: pick from all Major City mileposts.
        let mut all = Vec::new();
        for cid in &map.major_city_ids {
            if let Some(c) = map.city(cid) {
                all.extend(&c.mileposts);
            }
        }
        return all;
    }

    // Expand any Major Cities touched by player's track.
    let touched: Vec<MilepostId> = owned_nodes.iter().copied().collect();
    for mp in touched {
        if let Some(c) = map.city_at(mp) {
            if c.size == CitySize::Major {
                for &m in &c.mileposts {
                    owned_nodes.insert(m);
                }
            }
        }
    }

    // If train is placed and on our network, restrict to the component containing the train
    // so new track is always immediately drivable by the train!
    if let Some(pos) = state.players[pid as usize].train_pos {
        if owned_nodes.contains(&pos) {
            let owned_edges = player_owned_edges(state, pid);
            let mut comp = HashSet::new();
            let mut q = VecDeque::new();
            comp.insert(pos);
            q.push_back(pos);
            while let Some(cur) = q.pop_front() {
                if let Some(c) = map.city_at(cur) {
                    if c.size == CitySize::Major {
                        for &m in &c.mileposts {
                            if comp.insert(m) {
                                q.push_back(m);
                            }
                        }
                    }
                }
                for &(nb, _) in &map.adj[cur as usize] {
                    if owned_edges.contains(&crate::engine::map::edge_key(cur, nb))
                        && comp.insert(nb)
                    {
                        q.push_back(nb);
                    }
                }
            }
            return comp.into_iter().collect();
        }
    }

    owned_nodes.into_iter().collect()
}

fn choose_trim_discards(map: &MapIndex, state: &GameState, pid: PlayerId) -> Vec<usize> {
    let hand_len = state.players[pid as usize].hand.len();
    let to_discard = hand_len.saturating_sub(3);
    if to_discard == 0 {
        return Vec::new();
    }

    let plans = evaluate_demands(map, state, pid);
    let mut card_scores: Vec<(usize, f32)> = (0..hand_len)
        .map(|ci| {
            let best = plans
                .iter()
                .filter(|p| p.card_index == ci)
                .map(|p| p.score)
                .fold(f32::NEG_INFINITY, f32::max);
            (ci, best)
        })
        .collect();
    card_scores.sort_by(|a, b| a.1.total_cmp(&b.1));
    card_scores
        .into_iter()
        .take(to_discard)
        .map(|(i, _)| i)
        .collect()
}

/// Precompute which cities `pid` is barred from entering due to city entry limits.
fn full_cities_for(map: &MapIndex, state: &GameState, pid: PlayerId) -> HashSet<String> {
    let mut blocked = HashSet::new();
    for c in &map.data.cities {
        if !can_enter_city(map, state, pid, &c.id) {
            blocked.insert(c.id.clone());
        }
    }
    blocked
}

/// Fast single-pass demand evaluator (1 Dijkstra pass per call, O(1) city-cap lookup).
fn evaluate_demands(map: &MapIndex, state: &GameState, pid: PlayerId) -> Vec<DemandPlan> {
    let owned = player_owned_edges(state, pid);
    let anchors = ai_network_anchors(map, state, pid);
    let mut hazards = active_hazards(map, state);
    hazards
        .blocked_edges
        .extend(opponent_occupied_edges(state, pid));
    let blocked_cities = full_cities_for(map, state, pid);
    let costs = map.build_costs_from(
        &anchors,
        &owned,
        &hazards.blocked_edges,
        &hazards.blocked_nodes,
        |cid| !blocked_cities.contains(cid),
    );

    let mut plans = Vec::new();

    for (ci, card) in state.players[pid as usize].hand.iter().enumerate() {
        let Card::Demand { demands, .. } = card else {
            continue;
        };
        for d in demands.iter() {
            let Some(dest_city) = map.city(&d.city_id) else {
                continue;
            };
            let Some(sources) = map.commodity_sources.get(&d.commodity) else {
                continue;
            };
            let dest_mp = dest_city.center_mp;
            let dest_cost = dest_city
                .mileposts
                .iter()
                .map(|&m| costs[m as usize])
                .min()
                .unwrap_or(u32::MAX);
            if dest_cost == u32::MAX {
                continue;
            }

            let mut best_src: Option<(String, MilepostId, u32)> = None;
            for src_id in sources {
                let Some(src_city) = map.city(src_id) else {
                    continue;
                };
                let c_src = src_city
                    .mileposts
                    .iter()
                    .map(|&m| costs[m as usize])
                    .min()
                    .unwrap_or(u32::MAX);
                if c_src < u32::MAX && best_src.as_ref().is_none_or(|b| c_src < b.2) {
                    best_src = Some((src_id.clone(), src_city.center_mp, c_src));
                }
            }
            let Some((source_city, source_mp, src_cost)) = best_src else {
                continue;
            };

            let build_cost = src_cost.saturating_add(dest_cost);
            let src_coord = &map.data.mileposts[source_mp as usize];
            let dst_coord = &map.data.mileposts[dest_mp as usize];
            let euclid =
                ((src_coord.x - dst_coord.x).powi(2) + (src_coord.y - dst_coord.y).powi(2)).sqrt();
            // Strong bonus for demands whose endpoints are already connected (build_cost == 0)!
            let net = d.payout as f32 - build_cost as f32 * 0.85;
            let score =
                net / (euclid.max(3.0) * 0.3 + 1.0) + if build_cost == 0 { 12.0 } else { 0.0 };

            plans.push(DemandPlan {
                card_index: ci,
                commodity: d.commodity.clone(),
                source_city,
                source_mp,
                dest_mp,
                build_cost,
                score,
            });
        }
    }

    plans.sort_by(|a, b| b.score.total_cmp(&a.score));
    plans
}

fn ai_operate_phase(map: &MapIndex, state: &mut GameState, pid: PlayerId) -> Result<usize, String> {
    let mut steps = 0usize;

    // 1. Place train if not yet placed.
    if state.players[pid as usize].train_pos.is_none() {
        let place_mp = choose_initial_train_pos(map, state, pid);
        apply_action(map, state, pid, Action::PlaceTrain { milepost: place_mp })
            .map_err(|e| e.message)?;
        steps += 1;
    }

    let mut cached_plans = evaluate_demands(map, state, pid);

    // 2. Iterative deliver -> drop useless -> pickup -> move loop.
    for _ in 0..8 {
        let mut delivered = false;
        while let Some(action) = find_immediate_delivery(map, state, pid) {
            apply_action(map, state, pid, action).map_err(|e| e.message)?;
            steps += 1;
            delivered = true;
        }
        if delivered {
            cached_plans = evaluate_demands(map, state, pid);
        }

        while let Some(slot) = find_useless_cargo_slot(map, state, pid) {
            apply_action(map, state, pid, Action::DropLoad { slot }).map_err(|e| e.message)?;
            steps += 1;
        }

        while let Some(comm) = find_useful_pickup(map, state, pid, &cached_plans) {
            apply_action(map, state, pid, Action::PickupLoad { commodity: comm })
                .map_err(|e| e.message)?;
            steps += 1;
        }

        let Some(move_path) = choose_next_move(map, state, pid, &cached_plans) else {
            break;
        };
        apply_action(map, state, pid, Action::MoveTrain { path: move_path })
            .map_err(|e| e.message)?;
        steps += 1;
    }

    let mut delivered = false;
    while let Some(action) = find_immediate_delivery(map, state, pid) {
        apply_action(map, state, pid, action).map_err(|e| e.message)?;
        steps += 1;
        delivered = true;
    }
    if delivered {
        cached_plans = evaluate_demands(map, state, pid);
    }
    while let Some(comm) = find_useful_pickup(map, state, pid, &cached_plans) {
        apply_action(map, state, pid, Action::PickupLoad { commodity: comm })
            .map_err(|e| e.message)?;
        steps += 1;
    }

    // 3. Pitch hand if we couldn't act, carry nothing, and best demand is too expensive.
    if !state.turn_tracker.has_acted_this_turn && state.players[pid as usize].cargo.is_empty() {
        let best_cost = cached_plans.first().map(|p| p.build_cost).unwrap_or(999);
        let cash = state.players[pid as usize].cash;
        if best_cost > cash + 20 {
            apply_action(map, state, pid, Action::PitchHand).map_err(|e| e.message)?;
            steps += 1;
        }
    }

    Ok(steps)
}

fn choose_initial_train_pos(map: &MapIndex, state: &GameState, pid: PlayerId) -> MilepostId {
    let plans = evaluate_demands(map, state, pid);
    let owned_nodes: HashSet<MilepostId> =
        ai_network_anchors(map, state, pid).into_iter().collect();

    for plan in &plans {
        if owned_nodes.contains(&plan.source_mp) {
            return plan.source_mp;
        }
    }
    for &mp in &owned_nodes {
        if map.city_at(mp).is_some() {
            return mp;
        }
    }
    map.city(&map.major_city_ids[0])
        .map(|c| c.center_mp)
        .unwrap_or(0)
}

fn find_immediate_delivery(map: &MapIndex, state: &GameState, pid: PlayerId) -> Option<Action> {
    let p = &state.players[pid as usize];
    let pos = p.train_pos?;
    let city = map.city_at(pos)?;
    let hazards = active_hazards(map, state);
    if hazards.strike_cities.contains(&city.id) {
        return None;
    }

    for ev in &state.active_events {
        if let EventEffect::HeatingFuelShortage {
            commodity,
            target_cities,
            ..
        } = &ev.effect
        {
            if target_cities.contains(&city.id) {
                for (slot, c) in p.cargo.iter().enumerate() {
                    if c == commodity || c == "coal" {
                        return Some(Action::DeliverEventBonus {
                            slot,
                            event_card_id: ev.card_id,
                        });
                    }
                }
            }
        }
    }

    let mut best: Option<(u32, usize, usize, usize)> = None;
    for (slot, cargo_comm) in p.cargo.iter().enumerate() {
        for (ci, card) in p.hand.iter().enumerate() {
            if let Card::Demand { demands, .. } = card {
                for (di, d) in demands.iter().enumerate() {
                    if d.city_id == city.id
                        && &d.commodity == cargo_comm
                        && best.is_none_or(|b| d.payout > b.0)
                    {
                        best = Some((d.payout, slot, ci, di));
                    }
                }
            }
        }
    }

    best.map(|(_, slot, card_index, demand_index)| Action::DeliverLoad {
        slot,
        card_index,
        demand_index,
    })
}

fn find_useless_cargo_slot(map: &MapIndex, state: &GameState, pid: PlayerId) -> Option<usize> {
    let p = &state.players[pid as usize];
    let pos = p.train_pos?;
    map.city_at(pos)?;
    for (slot, comm) in p.cargo.iter().enumerate() {
        let needed_by_hand = p.hand.iter().any(|card| match card {
            Card::Demand { demands, .. } => demands.iter().any(|d| &d.commodity == comm),
            Card::Event { .. } => false,
        });
        let needed_by_event = state.active_events.iter().any(|e| match &e.effect {
            EventEffect::HeatingFuelShortage { commodity, .. } => {
                comm == commodity || comm == "coal"
            }
            _ => false,
        });
        if !needed_by_hand && !needed_by_event {
            return Some(slot);
        }
    }
    None
}

fn find_useful_pickup(
    map: &MapIndex,
    state: &GameState,
    pid: PlayerId,
    plans: &[DemandPlan],
) -> Option<String> {
    let p = &state.players[pid as usize];
    if p.cargo.len() >= p.train_tier.capacity() {
        return None;
    }
    let pos = p.train_pos?;
    let city = map.city_at(pos)?;
    let hazards = active_hazards(map, state);
    if hazards.strike_cities.contains(&city.id) {
        return None;
    }

    for plan in plans {
        if plan.source_city == city.id
            && state.chip_supply.get(&plan.commodity).copied().unwrap_or(0) > 0
            && !p.cargo.contains(&plan.commodity)
            && plan.build_cost <= p.cash + 35
        {
            return Some(plan.commodity.clone());
        }
    }
    None
}

fn choose_next_move(
    map: &MapIndex,
    state: &GameState,
    pid: PlayerId,
    plans: &[DemandPlan],
) -> Option<Vec<MilepostId>> {
    let p = &state.players[pid as usize];
    let start = p.train_pos?;
    let limit = effective_move_limit(map, state, pid);
    let remaining = limit.saturating_sub(state.turn_tracker.moves_used);
    if remaining == 0 {
        return None;
    }

    let hazards = active_hazards(map, state);
    let owners = edge_owners_map(state);
    let mut paid_mask = 0u8;
    for &opp in &state.turn_tracker.paid_opponents {
        paid_mask |= 1u8 << opp;
    }

    let mut targets: Vec<MilepostId> = Vec::new();
    for comm in &p.cargo {
        for card in &p.hand {
            if let Card::Demand { demands, .. } = card {
                for d in demands {
                    if &d.commodity == comm {
                        if let Some(c) = map.city(&d.city_id) {
                            targets.push(c.center_mp);
                        }
                    }
                }
            }
        }
    }

    if p.cargo.len() < p.train_tier.capacity() {
        for plan in plans.iter().take(6) {
            if state.chip_supply.get(&plan.commodity).copied().unwrap_or(0) > 0
                && !p.cargo.contains(&plan.commodity)
            {
                targets.push(plan.source_mp);
            }
        }
    }

    for target in targets {
        if target == start {
            continue;
        }
        let max_fee = p.cash.min(state.config.trackage_fee());
        if let Some(res) = map.shortest_move_path(
            start,
            target,
            pid,
            &owners,
            &hazards.blocked_edges,
            &hazards.blocked_nodes,
            60,
            paid_mask,
            max_fee,
            state.config.trackage_fee(),
        ) {
            if res.path.len() >= 2 {
                let take = (remaining as usize + 1).min(res.path.len());
                let slice = res.path[..take].to_vec();
                let enters_storm = slice.iter().any(|mp| hazards.half_speed_nodes.contains(mp));
                let eff_limit = if enters_storm {
                    p.train_tier.speed(state.config.mode).div_ceil(2)
                } else {
                    limit
                };
                let eff_rem = eff_limit.saturating_sub(state.turn_tracker.moves_used) as usize;
                if eff_rem == 0 {
                    continue;
                }
                let safe_take = (eff_rem + 1).min(slice.len());
                if safe_take >= 2 {
                    return Some(slice[..safe_take].to_vec());
                }
            }
        }
    }

    None
}

fn ai_build_phase(map: &MapIndex, state: &mut GameState, pid: PlayerId) -> Result<usize, String> {
    let mut steps = 0usize;

    // 1. Consider upgrading locomotive during regular Build phase.
    if state.phase == TurnPhase::Build {
        let p = &state.players[pid as usize];
        let desired = match p.train_tier {
            TrainTier::Freight if p.cash >= 42 => Some(TrainTier::FastFreight),
            TrainTier::FastFreight if p.cash >= 80 => Some(TrainTier::Superfreight),
            _ => None,
        };
        if let Some(target_tier) = desired {
            if apply_action(map, state, pid, Action::UpgradeTrain { target_tier }).is_ok() {
                return Ok(1);
            }
        }
    }

    // 2. Emergency loan if cash-starved and not carrying anything.
    if state.phase == TurnPhase::Build
        && state.players[pid as usize].cash < 6
        && state.players[pid as usize].debt == 0
        && state.players[pid as usize].cargo.is_empty()
    {
        let _ = apply_action(map, state, pid, Action::Borrow { amount: 15 });
        steps += 1;
    }

    // 3. Choose build targets using connected network anchors!
    let connected_majors: HashSet<String> = connected_major_cities_list(map, state, pid)
        .into_iter()
        .collect();
    let cash = state.players[pid as usize].cash;
    let need_majors = connected_majors.len() < state.config.victory_major_cities;

    let mut build_targets: Vec<MilepostId> = Vec::new();

    let blocked_cities = full_cities_for(map, state, pid);
    if need_majors && cash >= 140 && state.phase == TurnPhase::Build {
        let owned = player_owned_edges(state, pid);
        let anchors = ai_network_anchors(map, state, pid);
        let mut hazards = active_hazards(map, state);
        hazards
            .blocked_edges
            .extend(opponent_occupied_edges(state, pid));
        let costs = map.build_costs_from(
            &anchors,
            &owned,
            &hazards.blocked_edges,
            &hazards.blocked_nodes,
            |cid| !blocked_cities.contains(cid),
        );
        let mut major_cands: Vec<(u32, MilepostId)> = Vec::new();
        for mid in &map.major_city_ids {
            if connected_majors.contains(mid) {
                continue;
            }
            if let Some(c) = map.city(mid) {
                let cost = c
                    .mileposts
                    .iter()
                    .map(|&m| costs[m as usize])
                    .min()
                    .unwrap_or(u32::MAX);
                if cost > 0 && cost < u32::MAX {
                    major_cands.push((cost, c.center_mp));
                }
            }
        }
        major_cands.sort_by_key(|x| x.0);
        for (_, mp) in major_cands {
            build_targets.push(mp);
        }
    }

    // Carried cargo destinations come next.
    for comm in &state.players[pid as usize].cargo {
        for card in &state.players[pid as usize].hand {
            if let Card::Demand { demands, .. } = card {
                for d in demands {
                    if &d.commodity == comm {
                        if let Some(c) = map.city(&d.city_id) {
                            build_targets.push(c.center_mp);
                        }
                    }
                }
            }
        }
    }

    // Top demand plans (source first, then destination).
    for plan in evaluate_demands(map, state, pid).into_iter().take(4) {
        build_targets.push(plan.source_mp);
        build_targets.push(plan.dest_mp);
    }

    // Build greedily up to remaining $20M turn budget and available cash.
    for target in build_targets {
        let rem_budget = state
            .config
            .build_budget_per_turn()
            .saturating_sub(state.turn_tracker.build_spent);
        let avail_cash = state.players[pid as usize].cash;
        let max_spend = rem_budget.min(avail_cash);
        if max_spend == 0 {
            break;
        }

        let owned = player_owned_edges(state, pid);
        let anchors = ai_network_anchors(map, state, pid);
        let mut hazards = active_hazards(map, state);
        hazards
            .blocked_edges
            .extend(opponent_occupied_edges(state, pid));
        let bc = full_cities_for(map, state, pid);
        let Some((edges, _total_cost)) = map.shortest_build_path(
            &anchors,
            target,
            &owned,
            &hazards.blocked_edges,
            &hazards.blocked_nodes,
            |cid| !bc.contains(cid),
        ) else {
            continue;
        };
        if edges.is_empty() {
            continue;
        }

        let mut affordable = Vec::new();
        let mut spent = 0u32;
        for (a, b) in edges {
            let Some(c) = map.build_step_cost(a, b) else {
                break;
            };
            if spent + c > max_spend {
                break;
            }
            spent += c;
            affordable.push((a, b));
        }

        if !affordable.is_empty()
            && apply_action(map, state, pid, Action::BuildTrack { edges: affordable }).is_ok()
        {
            steps += 1;
        }
    }

    Ok(steps)
}
