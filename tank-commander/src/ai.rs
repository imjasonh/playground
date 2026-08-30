//! Heuristic AI for Skirmish balance runs.
//!
//! Builds short action plans with a beam search scored by a simple combat
//! heuristic. Both sides use the same policy so win-rate drift means the
//! rules (or first-player bias), not asymmetric bots.

use crate::action::{Action, TurnBuffs};
use crate::game::{Game, Outcome};
use crate::hex::Hex;
use crate::unit::{RoundKind, Side};
use rand::seq::SliceRandom;
use rand::Rng;

const BEAM: usize = 24;
const MAX_PLAN_STEPS: usize = 10;

#[derive(Clone)]
struct Node {
    actions: Vec<Action>,
    ap_left: i32,
    buffs: TurnBuffs,
    /// Shadow state for scoring without mutating the real game deeply.
    pos: Hex,
    hull: crate::hex::Facing,
    turret_offset: i8,
    moves: i32,
    loaded: bool,
    on_fire: bool,
    score: f64,
}

/// Choose an action plan for the active tank.
pub fn choose_plan<R: Rng>(game: &Game, rng: &mut R) -> Vec<Action> {
    let Some(tank_id) = game.active_tank_id() else {
        return Vec::new();
    };
    let tank = game.tank(tank_id);
    let enemy = match game.enemy_tank(tank.side) {
        Some(e) => e,
        None => return Vec::new(),
    };

    let start = Node {
        actions: Vec::new(),
        ap_left: tank.effective_actions(),
        buffs: TurnBuffs::default(),
        pos: tank.pos,
        hull: tank.hull_facing,
        turret_offset: tank.turret_offset,
        moves: 0,
        loaded: tank.loaded.is_some(),
        on_fire: tank.on_fire,
        score: 0.0,
    };

    let mut beam = vec![start];
    let mut best = beam[0].clone();

    for _ in 0..MAX_PLAN_STEPS {
        let mut next = Vec::new();
        for node in &beam {
            // Always consider stopping here.
            if node.score > best.score
                || (node.score == best.score && node.actions.len() < best.actions.len())
            {
                best = node.clone();
            }
            if node.ap_left <= 0 && !has_pending_ability(node) {
                continue;
            }
            let legal = shadow_legal(game, tank_id, node);
            if legal.is_empty() {
                continue;
            }
            // Cap branching: shuffle and take a subset.
            let mut opts = legal;
            opts.shuffle(rng);
            opts.truncate(8);
            for action in opts {
                let mut child = node.clone();
                apply_shadow(game, tank_id, &mut child, action);
                child.score = evaluate(game, tank.side, &child, enemy.pos, enemy.hull_facing);
                // Prefer plans that actually fire when a shot is available.
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

    // If best is empty, take a random legal opener.
    if best.actions.is_empty() {
        let buffs = TurnBuffs::default();
        let mut legal = game.legal_actions(tank_id, tank.effective_actions(), &buffs);
        legal.shuffle(rng);
        return legal.into_iter().take(3).collect();
    }
    best.actions
}

fn has_pending_ability(node: &Node) -> bool {
    // Abilities are applied as actions; nothing pending beyond ap.
    let _ = node;
    false
}

fn shadow_legal(game: &Game, tank_id: u8, node: &Node) -> Vec<Action> {
    // Use real legal_actions but filter by shadow AP / loaded / fire / moves.
    // Build a temporary view by cloning the game tank state lightly.
    let mut g = game.clone();
    {
        let t = g.tank_mut(tank_id);
        t.pos = node.pos;
        t.hull_facing = node.hull;
        t.turret_offset = node.turret_offset;
        t.moves_this_turn = node.moves;
        t.on_fire = node.on_fire;
        if node.loaded {
            if t.loaded.is_none() {
                t.loaded = Some(RoundKind::At);
            }
        } else {
            t.loaded = None;
        }
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
            node.loaded = false;
            node.ap_left -= 1;
        }
        Action::Load(_) => {
            let cost = if node.buffs.free_load {
                0
            } else {
                tank.load_action_cost()
            };
            node.loaded = true;
            node.ap_left -= cost;
        }
        Action::ExtinguishFire => {
            node.on_fire = false;
            node.ap_left -= 1;
        }
    }
}

fn rel(hull: crate::hex::Facing, abs: crate::hex::Facing) -> i8 {
    let mut o = abs.index() as i8 - hull.index() as i8;
    while o > 3 {
        o -= 6;
    }
    while o < -2 {
        o += 6;
    }
    o
}

fn evaluate(
    game: &Game,
    side: Side,
    node: &Node,
    enemy_pos: Hex,
    enemy_hull: crate::hex::Facing,
) -> f64 {
    let mut score = 0.0;
    let dist = node.pos.distance(enemy_pos) as f64;

    // Prefer medium range: close enough to shoot, not point-blank.
    let range = 5.0;
    if dist <= range {
        score += 30.0 - dist * 2.0;
    } else {
        score += 10.0 - (dist - range) * 4.0;
    }

    // Turret aimed at enemy?
    if let Some(dir) = node.pos.facing_toward(enemy_pos) {
        let turret = node.hull.with_turret_offset(node.turret_offset);
        if dir == turret {
            score += 40.0;
            if node.loaded && dist <= range {
                score += 80.0; // can fire
            }
        } else {
            // Partial credit for being one step away.
            if dir == turret.turn_left() || dir == turret.turn_right() {
                score += 15.0;
            }
        }
    }

    // Present side / rear armor to the enemy when possible (flanking).
    // If enemy hull faces us poorly from their perspective...
    let _ = enemy_hull;
    if let Some(from_enemy) = enemy_pos.facing_toward(node.pos) {
        // Our impact facing if they shoot us.
        let mut shadow_tank = game
            .tanks
            .iter()
            .find(|t| t.side == side)
            .cloned()
            .expect("self");
        shadow_tank.pos = node.pos;
        shadow_tank.hull_facing = node.hull;
        let impact = shadow_tank.impact_facing(enemy_pos);
        match impact {
            crate::unit::ImpactFacing::Front => score += 10.0,
            crate::unit::ImpactFacing::Side => score -= 15.0,
            crate::unit::ImpactFacing::Rear => score -= 35.0,
        }
        let _ = from_enemy;
    }

    // Reward firing in the plan.
    let fires = node.actions.iter().filter(|a| **a == Action::Fire).count();
    score += fires as f64 * 50.0;

    // Extinguish if on fire.
    if node.on_fire {
        score -= 60.0;
    }
    if node.actions.contains(&Action::ExtinguishFire) {
        score += 55.0;
    }

    // Mild preference for using a dramatic ability once engaged.
    if dist <= range + 1.0 {
        if node.buffs.hit_on_2 {
            score += 12.0;
        }
        if node.buffs.booming_used {
            score += 8.0;
        }
    }

    // Stay on the board center-ish (avoid edge camping that never meets).
    let cx = (game.board.min_q + game.board.max_q) as f64 / 2.0;
    let cr = (game.board.min_r + game.board.max_r) as f64 / 2.0;
    let center_dist = ((node.pos.q as f64 - cx).powi(2) + (node.pos.r as f64 - cr).powi(2)).sqrt();
    score -= center_dist * 0.5;

    // Tiny noise already from beam shuffle; keep deterministic score here.
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
