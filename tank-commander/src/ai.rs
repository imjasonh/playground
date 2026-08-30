//! Heuristic AI for Skirmish balance runs.
//!
//! When the enemy is in sight, a short beam search picks shoot / load / peek
//! plans. When line of sight is blocked (the usual opening on the walled
//! map), the AI pathfinds to a firing hex — preferably forest cover — and
//! spends the activation following that path. Both sides share the policy.

use crate::action::{Action, TurnBuffs};
use crate::board::Terrain;
use crate::game::{Game, Outcome};
use crate::hex::{Facing, Hex};
use crate::unit::{RoundKind, Side};
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
}

/// Choose an action plan for the active tank.
pub fn choose_plan<R: Rng>(game: &Game, rng: &mut R) -> Vec<Action> {
    let Some(tank_id) = game.active_tank_id() else {
        return Vec::new();
    };
    let tank = game.tank(tank_id);
    let Some(enemy) = game.enemy_tank(tank.side) else {
        return Vec::new();
    };

    // Extinguish first if burning.
    if tank.on_fire {
        return vec![Action::ExtinguishFire];
    }

    let can_see = game.can_see(tank, enemy);
    if can_see {
        let tactical = beam_plan(game, tank_id, enemy, rng);
        if !tactical.is_empty() {
            return tactical;
        }
    }

    // No clean shot — drive toward a firing position via an alley.
    maneuver_plan(game, tank_id, enemy, rng)
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

    // Only accept tactical plans that actually shoot or aim meaningfully.
    let fires = best.actions.iter().filter(|a| **a == Action::Fire).count();
    if fires > 0 || best.score >= 80.0 {
        return best.actions;
    }
    Vec::new()
}

/// Pathfind to a hex that can see the enemy, then walk/turn along that path.
fn maneuver_plan<R: Rng>(
    game: &Game,
    tank_id: u8,
    enemy: &crate::unit::Tank,
    rng: &mut R,
) -> Vec<Action> {
    let tank = game.tank(tank_id);

    // If we already have geometric LOS, spend the turn aiming and shooting.
    if has_geometric_los(game, tank.pos, enemy.pos) {
        return aim_and_shoot_plan(game, tank_id, enemy, rng);
    }

    let goals = firing_positions(game, tank.side, enemy, tank.gun_range);
    if goals.is_empty() {
        return chase_enemy_fallback(tank, enemy.pos);
    }

    // Chase the enemy's current alley: prefer goals near them, forest second.
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
        return aim_and_shoot_plan(game, tank_id, enemy, rng);
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

    let Some(need) = tank.pos.facing_toward(enemy.pos) else {
        return vec![Action::TurretLeft];
    };

    // Prefer rotating the turret (keeps armor facing).
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
        actions.push(Action::Fire);
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
    // Turn toward the enemy's row (north/south), then crawl.
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
            // Don't stand on a friendly (only one tank per side in Skirmish).
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
        // Already on a firing hex — turn turret/hull toward a fight next turn.
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
        // Turn hull toward the next step (turret stays absolute).
        while facing != need && ap > 0 {
            let left_steps = turn_steps_left(facing, need);
            let right_steps = (6 - left_steps) % 6;
            // Strict shorter direction; on a dead opposite (3/3) always go right
            // so we cannot oscillate Left/Right.
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
        // Leave-cost is paid from current terrain; approximate as 1 for planning
        // (mud is rare on alley paths).
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
    // Left turns = +1 on the facing index.
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
        Action::Fire => {
            node.loaded = None;
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
            .find(|t| t.side == side)
            .cloned()
            .expect("self");
        shadow_tank.pos = node.pos;
        shadow_tank.hull_facing = node.hull;
        // Armor we present if they shoot us from their hex.
        match shadow_tank.impact_facing(enemy_pos) {
            crate::unit::ImpactFacing::Front => score += 8.0,
            crate::unit::ImpactFacing::Side => score -= 12.0,
            crate::unit::ImpactFacing::Rear => score -= 30.0,
        }
    }

    let fires = node.actions.iter().filter(|a| **a == Action::Fire).count();
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
    let plan = choose_plan(game, rng);
    crate::game::play_activation(game, &plan, rng);
}
