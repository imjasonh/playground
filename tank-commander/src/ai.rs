//! Heuristic AI for multi-unit Tank Commander balance runs.
//!
//! Picks the best operational unit on the active side, then either shoots
//! (beam / tactical) or pathfinds toward the nearest enemy. Infantry prefer
//! missiles and cover; APCs hunt infantry with AI weapons.

use crate::action::{Action, TurnBuffs};
use crate::board::Terrain;
use crate::game::{Game, Outcome};
use crate::hex::{Facing, Hex};
use crate::unit::{RoundKind, Side, UnitKind};
use rand::seq::SliceRandom;
use rand::Rng;
use std::collections::{HashMap, VecDeque};

const BEAM: usize = 24;
const MAX_PLAN_STEPS: usize = 10;

#[derive(Clone)]
struct Node {
    actions: Vec<Action>,
    ap_left: i32,
    buffs: TurnBuffs,
    pos: Hex,
    hull: crate::hex::Facing,
    turret_offset: i8,
    moves: i32,
    loaded: Option<RoundKind>,
    on_fire: bool,
    score: f64,
    focus_target: u8,
}

/// Choose which unit to activate and an action plan for it.
pub fn choose_plan<R: Rng>(game: &Game, rng: &mut R) -> Option<(u8, Vec<Action>)> {
    let ids = game.operational_ids(game.active_side);
    if ids.is_empty() {
        return None;
    }

    let mut best_id = ids[0];
    let mut best_score = i64::MIN;
    for id in &ids {
        let s = score_unit(game, *id);
        if s > best_score {
            best_score = s;
            best_id = *id;
        }
    }

    let plan = plan_for_unit(game, best_id, rng);
    Some((best_id, plan))
}

fn score_unit(game: &Game, unit_id: u8) -> i64 {
    let unit = game.tank(unit_id);
    let enemies = game.enemy_units(unit.side);
    if enemies.is_empty() {
        return 0;
    }
    let can_see_any = enemies.iter().any(|e| sees_enemy(game, unit, e));
    let nearest = enemies
        .iter()
        .map(|e| unit.pos.distance(e.pos))
        .min()
        .unwrap_or(99);
    let mut score = 0i64;
    if can_see_any {
        score += 10_000;
    }
    score -= i64::from(nearest) * 10;
    if unit.on_fire {
        score -= 1_000;
    }
    score
}

fn sees_enemy(game: &Game, unit: &crate::unit::Tank, enemy: &crate::unit::Tank) -> bool {
    match unit.kind {
        UnitKind::Apc => enemy.kind == UnitKind::Infantry && game.can_see_ai(unit, enemy),
        UnitKind::Infantry => {
            game.can_see(unit, enemy)
                || (enemy.kind == UnitKind::Infantry && game.can_see_ai(unit, enemy))
        }
        UnitKind::Tank => game.can_see(unit, enemy),
    }
}

fn plan_for_unit<R: Rng>(game: &Game, unit_id: u8, rng: &mut R) -> Vec<Action> {
    let unit = game.tank(unit_id);
    if unit.on_fire {
        return vec![Action::ExtinguishFire];
    }

    match unit.kind {
        UnitKind::Infantry => infantry_plan(game, unit_id, rng),
        UnitKind::Apc => apc_plan(game, unit_id, rng),
        UnitKind::Tank => tank_plan(game, unit_id, rng),
    }
}

fn tank_plan<R: Rng>(game: &Game, tank_id: u8, rng: &mut R) -> Vec<Action> {
    let tank = game.tank(tank_id);
    let enemies: Vec<&crate::unit::Tank> = game.enemy_units(tank.side);
    if enemies.is_empty() {
        return Vec::new();
    }

    // Air strike when several enemies cluster near each other.
    if tank.has_air_support && !tank.air_strike_used && enemies.len() >= 2 {
        let clustered = enemies.iter().any(|a| {
            enemies
                .iter()
                .filter(|b| a.id != b.id)
                .any(|b| a.pos.distance(b.pos) <= 2)
        });
        if clustered && rng.gen_bool(0.45) {
            if let Some(nearest) = enemies.iter().min_by_key(|e| tank.pos.distance(e.pos)) {
                return vec![Action::CallAirStrike { hex: nearest.pos }];
            }
        }
    }

    let visible: Vec<&crate::unit::Tank> = enemies
        .iter()
        .copied()
        .filter(|e| game.can_see(tank, e))
        .collect();
    if let Some(target) = visible
        .iter()
        .min_by_key(|e| (e.hull_points, tank.pos.distance(e.pos)))
        .copied()
    {
        let tactical = beam_plan(game, tank_id, target, rng);
        if !tactical.is_empty() {
            return tactical;
        }
    }

    let Some(enemy) = enemies
        .iter()
        .min_by_key(|e| tank.pos.distance(e.pos))
        .copied()
    else {
        return Vec::new();
    };
    maneuver_plan(game, tank_id, enemy, rng)
}

fn infantry_plan<R: Rng>(game: &Game, unit_id: u8, rng: &mut R) -> Vec<Action> {
    let unit = game.tank(unit_id);
    let enemies = game.enemy_units(unit.side);
    if enemies.is_empty() {
        return Vec::new();
    }

    // Prefer missile shots on anything in LOS.
    let mut actions = Vec::new();
    let mut ap = unit.effective_actions();
    for enemy in &enemies {
        if ap <= 0 {
            break;
        }
        if game.can_see(unit, enemy) {
            let round = if enemy.kind == UnitKind::Infantry || rng.gen_bool(0.4) {
                RoundKind::He
            } else {
                RoundKind::At
            };
            actions.push(Action::FireMissile {
                target: enemy.id,
                round,
            });
            ap -= 1;
            break;
        }
        if enemy.kind == UnitKind::Infantry && game.can_see_ai(unit, enemy) {
            actions.push(Action::FireAi { target: enemy.id });
            ap -= 1;
            break;
        }
    }
    if !actions.is_empty() {
        return actions;
    }

    let Some(enemy) = enemies.iter().min_by_key(|e| unit.pos.distance(e.pos)) else {
        return Vec::new();
    };

    // Under threat (enemy within 3) → take cover if possible.
    if unit.pos.distance(enemy.pos) <= 3 && !unit.in_cover && ap > 0 && rng.gen_bool(0.55) {
        return vec![Action::TakeCover];
    }

    // Step toward nearest enemy.
    let mut steps = Vec::new();
    let mut pos = unit.pos;
    let mut moves = 0i32;
    let max_move = unit.effective_max_move();
    while moves < max_move && ap > 0 {
        let Some(need) = pos.facing_toward(enemy.pos) else {
            break;
        };
        let next = pos.neighbor(need);
        if !game.board.contains(next)
            || game.board.terrain_at(next).impassable()
            || game.occupied_hexes().contains(&next)
        {
            let mut best: Option<(Facing, Hex, i32)> = None;
            for i in 0..6u8 {
                let f = Facing::from_index(i);
                let n = pos.neighbor(f);
                if !game.board.contains(n)
                    || game.board.terrain_at(n).impassable()
                    || game.occupied_hexes().contains(&n)
                {
                    continue;
                }
                let d = n.distance(enemy.pos);
                if best.is_none_or(|(_, _, bd)| d < bd) {
                    best = Some((f, n, d));
                }
            }
            if let Some((f, n, _)) = best {
                steps.push(Action::Step(f));
                pos = n;
                moves += 1;
                ap -= 1;
                continue;
            }
            break;
        }
        steps.push(Action::Step(need));
        pos = next;
        moves += 1;
        ap -= 1;
    }
    if steps.is_empty() && !unit.in_cover {
        return vec![Action::TakeCover];
    }
    steps
}

fn apc_plan<R: Rng>(game: &Game, unit_id: u8, rng: &mut R) -> Vec<Action> {
    let unit = game.tank(unit_id);
    let enemies = game.enemy_units(unit.side);
    let infantry: Vec<&crate::unit::Tank> = enemies
        .iter()
        .copied()
        .filter(|e| e.kind == UnitKind::Infantry)
        .collect();

    for enemy in &infantry {
        if game.can_see_ai(unit, enemy) {
            return vec![Action::FireAi { target: enemy.id }];
        }
    }

    let target = infantry
        .iter()
        .copied()
        .min_by_key(|e| unit.pos.distance(e.pos))
        .or_else(|| {
            enemies
                .iter()
                .copied()
                .min_by_key(|e| unit.pos.distance(e.pos))
        });
    let Some(enemy) = target else {
        return Vec::new();
    };
    maneuver_plan(game, unit_id, enemy, rng)
}

fn beam_plan<R: Rng>(
    game: &Game,
    tank_id: u8,
    enemy: &crate::unit::Tank,
    rng: &mut R,
) -> Vec<Action> {
    let tank = game.tank(tank_id);
    let enemy_hp = enemy.hull_points;
    let enemy_max = enemy.max_hull_points;
    let enemy_id = enemy.id;

    let start = Node {
        actions: Vec::new(),
        ap_left: tank.effective_actions(),
        buffs: TurnBuffs::default(),
        pos: tank.pos,
        hull: tank.hull_facing,
        turret_offset: tank.turret_offset,
        moves: 0,
        loaded: tank.loaded,
        on_fire: tank.on_fire,
        score: 0.0,
        focus_target: enemy_id,
    };

    let mut beam = vec![start];
    let mut best = beam[0].clone();

    for _ in 0..MAX_PLAN_STEPS {
        let mut next = Vec::new();
        for node in &beam {
            if node.score > best.score
                || (node.score == best.score && node.actions.len() < best.actions.len())
            {
                best = node.clone();
            }
            if node.ap_left <= 0 {
                continue;
            }
            let mut opts = shadow_legal(game, tank_id, node);
            if opts.is_empty() {
                continue;
            }
            opts.shuffle(rng);
            opts.truncate(8);
            for action in opts {
                let mut child = node.clone();
                apply_shadow(game, tank_id, &mut child, action);
                child.score =
                    evaluate_tactical(game, tank.side, &child, enemy.pos, enemy_hp, enemy_max);
                next.push(child);
            }
        }
        if next.is_empty() {
            break;
        }
        next.sort_by(|a, b| {
            b.score
                .partial_cmp(&a.score)
                .unwrap_or(std::cmp::Ordering::Equal)
        });
        next.truncate(BEAM);
        beam = next;
        if let Some(top) = beam.first() {
            if top.score > best.score {
                best = top.clone();
            }
        }
    }

    let fires = best
        .actions
        .iter()
        .filter(|a| matches!(a, Action::Fire { .. }))
        .count();
    if fires > 0 || best.score >= 80.0 {
        return best.actions;
    }
    Vec::new()
}

fn maneuver_plan<R: Rng>(
    game: &Game,
    tank_id: u8,
    enemy: &crate::unit::Tank,
    rng: &mut R,
) -> Vec<Action> {
    let tank = game.tank(tank_id);

    if tank.kind == UnitKind::Infantry {
        return infantry_plan(game, tank_id, rng);
    }

    if has_geometric_los(game, tank.pos, enemy.pos) && tank.kind == UnitKind::Tank {
        return aim_and_shoot_plan(game, tank_id, enemy, rng);
    }

    let range = if tank.gun_range > 0 {
        tank.gun_range
    } else {
        tank.ai_range.max(3)
    };
    let goals = firing_positions(game, tank.side, enemy, range);
    if goals.is_empty() {
        return chase_enemy_fallback(tank, enemy.pos);
    }

    let mut goals = goals;
    goals.shuffle(rng);
    goals.sort_by_key(|(h, forest)| {
        let chase = h.distance(enemy.pos);
        let travel = tank.pos.distance(*h);
        (chase, if *forest { 0 } else { 1 }, travel)
    });

    let Some((goal, _)) = goals.first().copied() else {
        return chase_enemy_fallback(tank, enemy.pos);
    };
    let Some(path) = bfs_path(game, tank.pos, goal, tank.side) else {
        return chase_enemy_fallback(tank, enemy.pos);
    };

    if path.len() <= 1 {
        if tank.kind == UnitKind::Tank {
            return aim_and_shoot_plan(game, tank_id, enemy, rng);
        }
        return chase_enemy_fallback(tank, enemy.pos);
    }
    path_to_actions(tank, &path)
}

fn has_geometric_los(game: &Game, from: Hex, to: Hex) -> bool {
    let occ: Vec<Hex> = game
        .tanks
        .iter()
        .filter(|t| !t.destroyed && t.pos != from && t.pos != to)
        .map(|t| t.pos)
        .collect();
    game.board.has_los(from, to, &occ)
}

fn aim_and_shoot_plan<R: Rng>(
    game: &Game,
    tank_id: u8,
    enemy: &crate::unit::Tank,
    rng: &mut R,
) -> Vec<Action> {
    let tank = game.tank(tank_id);
    let mut actions = Vec::new();
    let mut ap = tank.effective_actions();
    let hull = tank.hull_facing;
    let mut turret_off = tank.turret_offset;
    let mut loaded = tank.loaded;
    let mut buffs = TurnBuffs::default();
    let target_id = enemy.id;

    let Some(need) = tank.pos.facing_toward(enemy.pos) else {
        return vec![Action::TurretLeft];
    };

    while hull.with_turret_offset(turret_off) != need && ap > 0 {
        let cur = hull.with_turret_offset(turret_off);
        let left_steps = turn_steps_left(cur, need);
        let right_steps = (6 - left_steps) % 6;
        let go_left = left_steps > 0 && left_steps < right_steps;
        if go_left {
            actions.push(Action::TurretLeft);
            turret_off = crate::action::step_turret(turret_off, true);
        } else {
            actions.push(Action::TurretRight);
            turret_off = crate::action::step_turret(turret_off, false);
        }
        ap -= 1;
    }

    if loaded.is_none() && ap >= tank.load_action_cost() {
        let kind = if enemy.hull_points < enemy.max_hull_points && rng.gen_bool(0.6) {
            RoundKind::He
        } else {
            RoundKind::At
        };
        actions.push(Action::Load(kind));
        loaded = Some(kind);
        ap -= tank.load_action_cost();
    }

    if loaded.is_some() && hull.with_turret_offset(turret_off) == need && ap > 0 {
        if !buffs.hit_on_2
            && tank
                .crew
                .iter()
                .any(|c| c.role == crate::unit::CrewRole::Gunner && !c.ability_used)
            && rng.gen_bool(0.5)
        {
            actions.push(Action::AbilityBringItDown);
            buffs.hit_on_2 = true;
        }
        actions.push(Action::Fire { target: target_id });
        ap -= 1;
        loaded = None;
        if ap >= tank.load_action_cost() {
            actions.push(Action::Load(RoundKind::At));
        }
    }

    let _ = (loaded, hull);
    if actions.is_empty() {
        actions.push(Action::TurretLeft);
    }
    actions
}

fn chase_enemy_fallback(tank: &crate::unit::Tank, enemy: Hex) -> Vec<Action> {
    if tank.kind == UnitKind::Infantry {
        if let Some(need) = tank.pos.facing_toward(enemy) {
            return vec![Action::Step(need), Action::Step(need)];
        }
    }
    let go_north = enemy.r < tank.pos.r || (enemy.r == tank.pos.r && tank.pos.r > 4);
    if go_north {
        vec![Action::TurnLeft, Action::Move, Action::Move]
    } else {
        vec![Action::TurnRight, Action::Move, Action::Move]
    }
}

fn firing_positions(
    game: &Game,
    side: Side,
    enemy: &crate::unit::Tank,
    gun_range: i32,
) -> Vec<(Hex, bool)> {
    let mut out = Vec::new();
    for q in game.board.min_q..=game.board.max_q {
        for r in game.board.min_r..=game.board.max_r {
            let h = Hex::new(q, r);
            if game.board.terrain_at(h).impassable() {
                continue;
            }
            if h == enemy.pos {
                continue;
            }
            if h.distance(enemy.pos) > gun_range || h.distance(enemy.pos) < 1 {
                continue;
            }
            if game
                .tanks
                .iter()
                .any(|t| t.side == side && !t.destroyed && t.pos == h)
            {
                continue;
            }
            let occ: Vec<Hex> = game
                .tanks
                .iter()
                .filter(|t| !t.destroyed && t.pos != h && t.pos != enemy.pos)
                .map(|t| t.pos)
                .collect();
            if !game.board.has_los(h, enemy.pos, &occ) {
                continue;
            }
            let forest = game.board.terrain_at(h) == Terrain::Forest;
            out.push((h, forest));
        }
    }
    out
}

fn bfs_path(game: &Game, start: Hex, goal: Hex, side: Side) -> Option<Vec<Hex>> {
    if start == goal {
        return Some(vec![start]);
    }
    let blocked: std::collections::HashSet<(i32, i32)> = game
        .tanks
        .iter()
        .filter(|t| !t.destroyed && t.side != side)
        .map(|t| (t.pos.q, t.pos.r))
        .collect();

    let mut prev: HashMap<(i32, i32), Option<(i32, i32)>> = HashMap::new();
    let mut q = VecDeque::new();
    q.push_back(start);
    prev.insert((start.q, start.r), None);

    while let Some(cur) = q.pop_front() {
        if cur == goal {
            let mut path = vec![cur];
            let mut walk = (cur.q, cur.r);
            while let Some(Some(p)) = prev.get(&walk).copied() {
                path.push(Hex::new(p.0, p.1));
                walk = p;
            }
            path.reverse();
            return Some(path);
        }
        for n in cur.neighbors() {
            if !game.board.contains(n) || game.board.terrain_at(n).impassable() {
                continue;
            }
            if blocked.contains(&(n.q, n.r)) {
                continue;
            }
            let key = (n.q, n.r);
            if prev.contains_key(&key) {
                continue;
            }
            prev.insert(key, Some((cur.q, cur.r)));
            q.push_back(n);
        }
    }
    None
}

#[allow(clippy::explicit_counter_loop)]
fn path_to_actions(tank: &crate::unit::Tank, path: &[Hex]) -> Vec<Action> {
    if path.len() < 2 {
        return vec![Action::TurretLeft];
    }
    let mut actions = Vec::new();
    let mut facing = tank.hull_facing;
    let mut pos = tank.pos;
    let mut moves = 0i32;
    let mut ap = tank.effective_actions();
    let max_move = tank.effective_max_move();

    for window in path.windows(2) {
        let next = window[1];
        let Some(need) = pos.facing_toward(next) else {
            break;
        };
        while facing != need && ap > 0 {
            let left_steps = turn_steps_left(facing, need);
            let right_steps = (6 - left_steps) % 6;
            let go_left = left_steps > 0 && left_steps < right_steps;
            if go_left {
                actions.push(Action::TurnLeft);
                facing = facing.turn_left();
            } else {
                actions.push(Action::TurnRight);
                facing = facing.turn_right();
            }
            ap -= 1;
        }
        if facing != need || ap <= 0 || moves >= max_move {
            break;
        }
        actions.push(Action::Move);
        pos = next;
        moves += 1;
        ap -= 1;
        if ap <= 0 {
            break;
        }
    }

    if actions.is_empty() {
        return chase_enemy_fallback(tank, path[path.len() - 1]);
    }
    actions
}

fn turn_steps_left(from: Facing, to: Facing) -> u8 {
    (to.index() + 6 - from.index()) % 6
}

fn shadow_legal(game: &Game, tank_id: u8, node: &Node) -> Vec<Action> {
    let mut g = game.clone();
    {
        let t = g.tank_mut(tank_id);
        t.pos = node.pos;
        t.hull_facing = node.hull;
        t.turret_offset = node.turret_offset;
        t.moves_this_turn = node.moves;
        t.on_fire = node.on_fire;
        t.loaded = node.loaded;
    }
    g.legal_actions(tank_id, node.ap_left, &node.buffs)
}

fn apply_shadow(game: &Game, tank_id: u8, node: &mut Node, action: Action) {
    let tank = game.tank(tank_id);
    node.actions.push(action);
    match action {
        Action::AbilityBoomingVoice => {
            node.buffs.extra_actions += 2;
            node.buffs.booming_used = true;
            node.ap_left += 2;
        }
        Action::AbilityMoveMoveMove => node.buffs.move_move_move = true,
        Action::AbilityBringItDown => node.buffs.hit_on_2 = true,
        Action::AbilityQuickLoad => node.buffs.free_load = true,
        Action::Move => {
            let cost = game.board.terrain_at(node.pos).move_cost_to_leave();
            node.pos = node.pos.neighbor(node.hull);
            node.moves += 1;
            node.ap_left -= cost;
        }
        Action::Step(facing) => {
            let cost = game.board.terrain_at(node.pos).move_cost_to_leave();
            node.pos = node.pos.neighbor(facing);
            node.hull = facing;
            node.moves += 1;
            node.ap_left -= cost;
        }
        Action::TurnLeft => {
            let abs = node.hull.with_turret_offset(node.turret_offset);
            node.hull = node.hull.turn_left();
            node.turret_offset = rel(node.hull, abs);
            node.ap_left -= 1;
        }
        Action::TurnRight => {
            let abs = node.hull.with_turret_offset(node.turret_offset);
            node.hull = node.hull.turn_right();
            node.turret_offset = rel(node.hull, abs);
            node.ap_left -= 1;
        }
        Action::TurretLeft => {
            node.turret_offset = crate::action::step_turret(node.turret_offset, true);
            node.ap_left -= 1;
        }
        Action::TurretRight => {
            node.turret_offset = crate::action::step_turret(node.turret_offset, false);
            node.ap_left -= 1;
        }
        Action::Fire { target } => {
            node.focus_target = target;
            node.loaded = None;
            node.ap_left -= 1;
        }
        Action::FireMissile { .. } | Action::FireAi { .. } => {
            node.ap_left -= 1;
        }
        Action::TakeCover | Action::CallAirStrike { .. } => {
            node.ap_left -= 1;
        }
        Action::Load(kind) => {
            let cost = if node.buffs.free_load {
                0
            } else {
                tank.load_action_cost()
            };
            node.loaded = Some(kind);
            node.ap_left -= cost;
        }
        Action::ExtinguishFire => {
            node.on_fire = false;
            node.ap_left -= 1;
        }
    }
}

fn rel(hull: Facing, abs: Facing) -> i8 {
    let mut o = abs.index() as i8 - hull.index() as i8;
    while o > 3 {
        o -= 6;
    }
    while o < -2 {
        o += 6;
    }
    o
}

fn evaluate_tactical(
    game: &Game,
    side: Side,
    node: &Node,
    enemy_pos: Hex,
    enemy_hp: i32,
    enemy_max: i32,
) -> f64 {
    let mut score = 0.0;
    let dist = node.pos.distance(enemy_pos) as f64;
    let range = 5.0;

    let occ: Vec<Hex> = game
        .tanks
        .iter()
        .filter(|t| !t.destroyed && t.side != side)
        .map(|t| t.pos)
        .filter(|h| *h != node.pos)
        .collect();
    let los = game.board.has_los(node.pos, enemy_pos, &occ);
    let facing_ok = node
        .pos
        .facing_toward(enemy_pos)
        .is_some_and(|d| d == node.hull.with_turret_offset(node.turret_offset));

    if los && facing_ok && node.loaded.is_some() && dist <= range {
        score += 120.0;
    } else if los && facing_ok {
        score += 55.0;
    } else if los {
        score += 20.0;
    }

    if game.board.terrain_at(node.pos) == Terrain::Forest {
        score += 18.0;
    }

    match node.loaded {
        Some(RoundKind::At) => {
            score += 12.0;
            if enemy_hp <= 1 {
                score += 10.0;
            }
        }
        Some(RoundKind::He) => {
            score += 8.0;
            if (2..=enemy_max).contains(&enemy_hp) && enemy_hp < enemy_max {
                score += 14.0;
            } else if enemy_hp == enemy_max {
                score += 5.0;
            }
        }
        None => {}
    }

    if enemy_pos.facing_toward(node.pos).is_some() {
        let mut shadow_tank = game
            .tanks
            .iter()
            .find(|t| t.side == side && t.is_operational())
            .cloned()
            .unwrap_or_else(|| {
                game.tanks
                    .iter()
                    .find(|t| t.side == side)
                    .cloned()
                    .expect("self")
            });
        shadow_tank.pos = node.pos;
        shadow_tank.hull_facing = node.hull;
        match shadow_tank.impact_facing(enemy_pos) {
            crate::unit::ImpactFacing::Front => score += 8.0,
            crate::unit::ImpactFacing::Side => score -= 12.0,
            crate::unit::ImpactFacing::Rear => score -= 30.0,
        }
    }

    let fires = node
        .actions
        .iter()
        .filter(|a| matches!(a, Action::Fire { .. }))
        .count();
    score += fires as f64 * 50.0;

    if node.buffs.hit_on_2 {
        score += 10.0;
    }
    if node.buffs.booming_used {
        score += 6.0;
    }

    score
}

/// Run the active side's turn with the heuristic.
pub fn take_turn<R: Rng>(game: &mut Game, rng: &mut R) {
    if game.outcome() != Outcome::InProgress {
        return;
    }
    let Some((unit_id, plan)) = choose_plan(game, rng) else {
        game.activations += 1;
        game.active_side = game.active_side.other();
        return;
    };
    crate::game::play_activation(game, unit_id, &plan, rng);
}
