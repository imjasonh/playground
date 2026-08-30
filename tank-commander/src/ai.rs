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
    let ids = game.activatable_ids(game.active_side);
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
    let nearest = enemies
        .iter()
        .map(|e| unit.pos.distance(e.pos))
        .min()
        .unwrap_or(99);
    let mut score = 0i64;
    score -= i64::from(nearest) * 10;
    if unit.on_fire {
        score -= 1_000;
    }

    match unit.kind {
        UnitKind::Tank => {
            if enemies.iter().any(|e| game.can_see(unit, e)) {
                score += 12_000;
            }
        }
        UnitKind::Infantry => {
            if unit.is_embarked() {
                score += 8_500;
            } else if enemies.iter().any(|e| game.can_see(unit, e)) {
                score += 10_000;
            } else if enemies
                .iter()
                .any(|e| e.kind == UnitKind::Infantry && game.can_see_ai(unit, e))
            {
                score += 8_000;
            }
        }
        UnitKind::Apc => {
            if unit.passenger.is_some() {
                score += 9_500;
            } else if enemies
                .iter()
                .any(|e| e.kind == UnitKind::Infantry && game.can_see_ai(unit, e))
            {
                score += 9_000;
            } else if enemies
                .iter()
                .any(|e| e.kind != UnitKind::Infantry && !e.suppressed && game.can_see_ai(unit, e))
            {
                score += 3_500;
            }
        }
    }
    score
}

fn plan_for_unit<R: Rng>(game: &Game, unit_id: u8, rng: &mut R) -> Vec<Action> {
    let unit = game.tank(unit_id);
    if unit.on_fire {
        return vec![Action::ExtinguishFire];
    }

    // Lieutenant cover is free and urgent — restore a killed role before anything else.
    if let Some(cover) = lieutenant_cover_plan(game, unit_id) {
        return cover;
    }

    match unit.kind {
        UnitKind::Infantry => infantry_plan(game, unit_id, rng),
        UnitKind::Apc => apc_plan(game, unit_id, rng),
        UnitKind::Tank => tank_plan(game, unit_id, rng),
    }
}

fn lieutenant_cover_plan(game: &Game, unit_id: u8) -> Option<Vec<Action>> {
    let tank = game.tank(unit_id);
    let lt = tank.crew.iter().find(|c| {
        c.role == crate::unit::CrewRole::Lieutenant && c.status != crate::unit::CrewStatus::Killed
    })?;
    if lt.covering.is_some() {
        return None;
    }
    // Prefer gunner (keep shooting), then commander, driver, loader.
    for role in [
        crate::unit::CrewRole::Gunner,
        crate::unit::CrewRole::Commander,
        crate::unit::CrewRole::Driver,
        crate::unit::CrewRole::Loader,
    ] {
        if tank
            .crew
            .iter()
            .any(|c| c.role == role && c.status == crate::unit::CrewStatus::Killed)
        {
            return Some(vec![Action::LieutenantCover { role }]);
        }
    }
    None
}

/// Place smoke on an intervening hex when an enemy has LOS into this unit.
fn smoke_break_los_plan<R: Rng>(game: &Game, unit_id: u8, rng: &mut R) -> Option<Vec<Action>> {
    let unit = game.tank(unit_id);
    if !unit.has_smoke_launcher || unit.smoke_used {
        return None;
    }
    let enemies = game.enemy_units(unit.side);
    let threats: Vec<&crate::unit::Tank> = enemies
        .iter()
        .copied()
        .filter(|e| {
            if e.destroyed {
                return false;
            }
            // Enemy can shoot us (main gun or AI).
            (e.gun_range > 0 && game.can_see(e, unit))
                || (e.ai_range > 0 && game.can_see_ai(e, unit))
        })
        .collect();
    if threats.is_empty() {
        return None;
    }
    // Prefer smoking when threatened and not already about to delete the threat.
    if !rng.gen_bool(0.7) {
        return None;
    }
    let threat = threats
        .iter()
        .min_by_key(|e| unit.pos.distance(e.pos))
        .copied()?;
    let mut candidates: Vec<Hex> = unit
        .pos
        .line_through(threat.pos)
        .into_iter()
        .filter(|h| unit.pos.distance(*h) <= 2 && *h != unit.pos && *h != threat.pos)
        .filter(|h| game.board.contains(*h))
        .collect();
    if candidates.is_empty() {
        // Fallback: any hex within 2 toward the threat.
        for i in 0..6u8 {
            let n = unit.pos.neighbor(Facing::from_index(i));
            if game.board.contains(n) && n.distance(threat.pos) < unit.pos.distance(threat.pos) {
                candidates.push(n);
            }
        }
    }
    let hex = *candidates.choose(rng)?;
    Some(vec![Action::DeploySmoke { hex }])
}

/// Lay a mine toward the nearest enemy when we still have charges.
fn mine_plan<R: Rng>(game: &Game, unit_id: u8, rng: &mut R) -> Option<Vec<Action>> {
    let unit = game.tank(unit_id);
    if unit.mines_left == 0 {
        return None;
    }
    let enemy = game
        .enemy_units(unit.side)
        .into_iter()
        .filter(|e| !e.destroyed)
        .min_by_key(|e| unit.pos.distance(e.pos))?;
    // Prefer adjacent hex closer to the enemy; else own hex.
    let mut opts: Vec<Hex> = (0..6u8)
        .map(|i| unit.pos.neighbor(Facing::from_index(i)))
        .filter(|h| {
            game.board.contains(*h)
                && !game.board.has_mine(*h)
                && !game.board.terrain_at(*h).impassable()
                && h.distance(enemy.pos) < unit.pos.distance(enemy.pos)
        })
        .collect();
    if opts.is_empty() && !game.board.has_mine(unit.pos) {
        opts.push(unit.pos);
    }
    if opts.is_empty() || !rng.gen_bool(0.55) {
        return None;
    }
    let hex = *opts.choose(rng)?;
    Some(vec![Action::DeployMine { hex }])
}

fn tank_plan<R: Rng>(game: &Game, tank_id: u8, rng: &mut R) -> Vec<Action> {
    let tank = game.tank(tank_id);
    let enemies: Vec<&crate::unit::Tank> = game.enemy_units(tank.side);
    if enemies.is_empty() {
        return Vec::new();
    }

    let visible: Vec<&crate::unit::Tank> = enemies
        .iter()
        .copied()
        .filter(|e| game.can_see(tank, e))
        .collect();

    // Smoke to break incoming LOS when we cannot shoot back this activation.
    if visible.is_empty() {
        if let Some(smoke) = smoke_break_los_plan(game, tank_id, rng) {
            return smoke;
        }
    }

    // Drop a mine on the approach when closing on an enemy.
    if let Some(mine) = mine_plan(game, tank_id, rng) {
        return mine;
    }

    // Tank AI spray vs nearby infantry (anti-infantry upgrade).
    if tank.ai_range > 0 {
        let mut infantry: Vec<&crate::unit::Tank> = enemies
            .iter()
            .copied()
            .filter(|e| e.kind == UnitKind::Infantry)
            .collect();
        infantry.sort_by_key(|e| (if e.in_cover { 1 } else { 0 }, tank.pos.distance(e.pos)));
        for enemy in &infantry {
            if game.can_see_ai(tank, enemy) {
                return vec![Action::FireAi { target: enemy.id }];
            }
        }
    }

    // Air strike when enemies are nearby — don't wait for a perfect cluster.
    if tank.has_air_support && !tank.air_strike_used {
        if let Some(nearest) = enemies.iter().min_by_key(|e| tank.pos.distance(e.pos)) {
            let close = tank.pos.distance(nearest.pos) <= 6;
            let clustered = enemies.iter().any(|a| {
                enemies
                    .iter()
                    .filter(|b| a.id != b.id)
                    .any(|b| a.pos.distance(b.pos) <= 2)
            });
            if (close || clustered) && rng.gen_bool(0.55) {
                return vec![Action::CallAirStrike { hex: nearest.pos }];
            }
        }
    }

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

    // Embarked: get out near a fight or into forest.
    if unit.is_embarked() {
        let legal = game.legal_actions(unit_id, unit.effective_actions(), &TurnBuffs::default());
        let drops: Vec<Action> = legal
            .into_iter()
            .filter(|a| matches!(a, Action::Dismount { .. }))
            .collect();
        if drops.is_empty() {
            return Vec::new();
        }
        let nearest = enemies
            .iter()
            .map(|e| e.pos)
            .min_by_key(|p| unit.pos.distance(*p))
            .unwrap_or(unit.pos);
        let best = drops.into_iter().min_by_key(|a| match a {
            Action::Dismount { hex } => {
                let mut d = hex.distance(nearest) * 10;
                if game.board.terrain_at(*hex) == Terrain::Forest {
                    d -= 4;
                }
                d
            }
            _ => 999,
        });
        return best.into_iter().collect();
    }

    // Missiles on vehicles first; suppressed infantry cannot fire missiles.
    let mut ranked: Vec<&crate::unit::Tank> = enemies.to_vec();
    ranked.sort_by_key(|e| {
        let priority = match e.kind {
            UnitKind::Tank => 0,
            UnitKind::Apc => 1,
            UnitKind::Infantry => 2,
        };
        (priority, unit.pos.distance(e.pos))
    });

    if !unit.suppressed {
        for enemy in &ranked {
            if game.can_see(unit, enemy) {
                let round = if enemy.kind == UnitKind::Infantry {
                    RoundKind::He
                } else {
                    RoundKind::At
                };
                return vec![Action::FireMissile {
                    target: enemy.id,
                    round,
                }];
            }
        }
    }
    for enemy in &ranked {
        if enemy.kind == UnitKind::Infantry && game.can_see_ai(unit, enemy) {
            return vec![Action::FireAi { target: enemy.id }];
        }
    }

    let Some(enemy) = enemies.iter().min_by_key(|e| unit.pos.distance(e.pos)) else {
        return Vec::new();
    };

    // Mount when out of missile range and an empty APC is adjacent.
    let far = unit.pos.distance(enemy.pos) > unit.gun_range;
    if far {
        let legal = game.legal_actions(unit_id, unit.effective_actions(), &TurnBuffs::default());
        if let Some(Action::Mount { vehicle }) =
            legal.iter().find(|a| matches!(a, Action::Mount { .. }))
        {
            return vec![Action::Mount { vehicle: *vehicle }];
        }
    }

    // Charge when a tank can shell us (gun 5) but we cannot missile back (4).
    let tank_shelling = enemies.iter().any(|e| {
        e.kind == UnitKind::Tank
            && unit.pos.distance(e.pos) <= e.gun_range
            && unit.pos.distance(e.pos) > unit.gun_range
    });
    if !unit.in_cover
        && !tank_shelling
        && unit.pos.distance(enemy.pos) <= 4
        && matches!(enemy.kind, UnitKind::Tank | UnitKind::Apc)
        && rng.gen_bool(0.4)
    {
        return vec![Action::TakeCover];
    }

    // Step toward nearest enemy (prefer forest approaches unless charging).
    // Also step toward a friendly empty APC when far from the fight.
    let ride: Option<Hex> = if far {
        game.tanks
            .iter()
            .filter(|t| {
                t.side == unit.side
                    && t.kind == UnitKind::Apc
                    && !t.destroyed
                    && !t.disabled
                    && t.passenger.is_none()
            })
            .map(|t| t.pos)
            .min_by_key(|p| unit.pos.distance(*p))
    } else {
        None
    };
    let goal = ride.unwrap_or(enemy.pos);

    let mut steps = Vec::new();
    let mut pos = unit.pos;
    let mut moves = 0i32;
    let mut ap = unit.effective_actions();
    let max_move = unit.effective_max_move();
    while moves < max_move && ap > 0 {
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
            let mut d = n.distance(goal) * 10;
            if !tank_shelling && game.board.terrain_at(n) == Terrain::Forest {
                d -= 3;
            }
            if best.is_none_or(|(_, _, bd)| d < bd) {
                best = Some((f, n, d));
            }
        }
        let Some((f, n, _)) = best else {
            break;
        };
        steps.push(Action::Step(f));
        pos = n;
        moves += 1;
        ap -= 1;
        // After stepping adjacent to an APC, mount if still far.
        if far && ap > 0 {
            for t in &game.tanks {
                if t.side == unit.side
                    && t.kind == UnitKind::Apc
                    && !t.destroyed
                    && t.passenger.is_none()
                    && t.pos.distance(pos) == 1
                {
                    steps.push(Action::Mount { vehicle: t.id });
                    return steps;
                }
            }
        }
    }
    if steps.is_empty() && !unit.in_cover && !tank_shelling {
        return vec![Action::TakeCover];
    }
    steps
}

fn apc_plan<R: Rng>(game: &Game, unit_id: u8, rng: &mut R) -> Vec<Action> {
    let unit = game.tank(unit_id);
    let enemies = game.enemy_units(unit.side);

    if let Some(smoke) = smoke_break_los_plan(game, unit_id, rng) {
        return smoke;
    }

    // Carrying: drive toward the fight, then free drop-off into forest / closer hex.
    if unit.passenger.is_some() {
        let Some(enemy) = enemies.iter().min_by_key(|e| unit.pos.distance(e.pos)) else {
            return Vec::new();
        };
        let goal = enemy.pos;
        let close_enough = unit.pos.distance(goal) <= 5;
        let mut plan = Vec::new();
        let mut shadow = game.clone();
        let mut ap = unit.effective_actions();
        let mut buffs = TurnBuffs::default();
        // Match play_activation: moves reset at activation start.
        shadow.tank_mut(unit_id).moves_this_turn = 0;
        shadow.tank_mut(unit_id).dropped_passenger_this_activation = false;

        let raw = maneuver_plan(game, unit_id, enemy, rng);
        for a in &raw {
            if !matches!(a, Action::Move | Action::TurnLeft | Action::TurnRight) {
                break;
            }
            let legal = shadow.legal_actions(unit_id, ap, &buffs);
            if !legal.contains(a) {
                break;
            }
            shadow.apply_action(unit_id, *a, &mut buffs, &mut ap, rng);
            plan.push(*a);
            let move_count = plan.iter().filter(|x| matches!(x, Action::Move)).count();
            if matches!(a, Action::Move) && (close_enough || move_count >= 2) {
                break;
            }
        }

        let drops: Vec<Action> = shadow
            .legal_actions(unit_id, ap, &buffs)
            .into_iter()
            .filter(|a| matches!(a, Action::DropOff { .. }))
            .collect();
        if let Some(best) = drops.into_iter().min_by_key(|a| match a {
            Action::DropOff { hex } => {
                let mut d = hex.distance(goal) * 10;
                if shadow.board.terrain_at(*hex) == Terrain::Forest {
                    d -= 5;
                }
                d
            }
            _ => 999,
        }) {
            plan.push(best);
        }
        if !plan.is_empty() {
            return plan;
        }
    }

    let infantry: Vec<&crate::unit::Tank> = enemies
        .iter()
        .copied()
        .filter(|e| e.kind == UnitKind::Infantry)
        .collect();

    // Kill / pin infantry first when in AI range (including dug-in).
    let mut ranked_inf = infantry.clone();
    ranked_inf.sort_by_key(|e| (if e.in_cover { 1 } else { 0 }, unit.pos.distance(e.pos)));
    for enemy in &ranked_inf {
        if game.can_see_ai(unit, enemy) {
            return vec![Action::FireAi { target: enemy.id }];
        }
    }

    // Otherwise suppress one unsuppressed vehicle in AI range.
    let mut vehicles: Vec<&crate::unit::Tank> = enemies
        .iter()
        .copied()
        .filter(|e| e.kind != UnitKind::Infantry && !e.suppressed)
        .collect();
    vehicles.sort_by_key(|e| unit.pos.distance(e.pos));
    for enemy in &vehicles {
        if game.can_see_ai(unit, enemy) {
            return vec![Action::FireAi { target: enemy.id }];
        }
    }

    // Pick up a friendly squad that is out of the fight.
    if unit.passenger.is_none() {
        let legal = game.legal_actions(unit_id, unit.effective_actions(), &TurnBuffs::default());
        let embarks: Vec<u8> = legal
            .iter()
            .filter_map(|a| match a {
                Action::Embark { infantry } => Some(*infantry),
                _ => None,
            })
            .collect();
        for iid in embarks {
            let squad = game.tank(iid);
            let nearest = enemies
                .iter()
                .map(|e| squad.pos.distance(e.pos))
                .min()
                .unwrap_or(0);
            let can_shoot = enemies.iter().any(|e| game.can_see(squad, e));
            if !can_shoot && nearest > squad.gun_range {
                // Embark then drive toward the nearest enemy.
                let mut plan = vec![Action::Embark { infantry: iid }];
                if let Some(enemy) = enemies.iter().min_by_key(|e| unit.pos.distance(e.pos)) {
                    let rest = maneuver_plan(game, unit_id, enemy, rng);
                    // Only append moves/turns (embark already spent 1 AP).
                    for a in rest {
                        if matches!(a, Action::Move | Action::TurnLeft | Action::TurnRight) {
                            plan.push(a);
                        }
                        if plan.iter().filter(|x| matches!(x, Action::Move)).count() >= 2 {
                            break;
                        }
                    }
                }
                return plan;
            }
        }
    }

    // After spraying, push toward infantry (or any enemy) instead of camping.
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

    if tank.kind == UnitKind::Tank
        && tank.pos.distance(enemy.pos) <= tank.gun_range
        && has_geometric_los(game, tank.pos, enemy.pos)
    {
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
    for h in game.board.hexes() {
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
        Action::TakeCover
        | Action::CallAirStrike { .. }
        | Action::DeploySmoke { .. }
        | Action::DeployMine { .. } => {
            node.ap_left -= 1;
        }
        Action::LieutenantCover { .. } => {
            // Free action.
        }
        Action::Mount { .. } | Action::Dismount { .. } | Action::Embark { .. } => {
            node.ap_left -= 1;
        }
        Action::DropOff { .. } => {
            // Free after Move.
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
    if node
        .actions
        .iter()
        .any(|a| matches!(a, Action::DeploySmoke { .. }))
    {
        // Prefer plans that break enemy LOS after smoking.
        let smoked = node.actions.iter().find_map(|a| match a {
            Action::DeploySmoke { hex } => Some(*hex),
            _ => None,
        });
        if let Some(h) = smoked {
            let mut blocked = false;
            for mid in node.pos.line_through(enemy_pos) {
                if mid == h {
                    blocked = true;
                    break;
                }
            }
            if blocked {
                score += 25.0;
            } else {
                score += 8.0;
            }
        }
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
