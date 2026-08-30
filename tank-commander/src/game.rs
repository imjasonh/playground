//! Turn-based game state and legal-action resolution.

use crate::action::{is_ability, step_turret, turn_hull, Action, TurnBuffs};
use crate::board::{Board, Terrain};
use crate::combat::{end_of_turn_hazards, resolve_shot, CombatEvent};
use crate::hex::{Facing, Hex};
use crate::unit::{CrewRole, CrewStatus, RoundKind, Side, Tank};
use rand::Rng;
use serde::{Deserialize, Serialize};

#[derive(Clone, Copy, Debug, Eq, PartialEq, Serialize, Deserialize)]
pub enum Outcome {
    Winner(Side),
    Draw,
    InProgress,
}

#[derive(Clone, Debug, Serialize, Deserialize)]
pub struct GameEvent {
    pub turn: u32,
    pub side: Option<Side>,
    pub text: String,
    pub combat: Option<CombatEvent>,
}

#[derive(Clone, Debug)]
pub struct Game {
    pub board: Board,
    pub tanks: Vec<Tank>,
    pub active_side: Side,
    /// Completed player activations. A "battle turn" in the rules is one
    /// activation; the 10-turn limit is modeled as 20 activations (10 each).
    pub activations: u32,
    pub max_activations: u32,
    pub events: Vec<GameEvent>,
    pub first_player: Side,
    /// Consecutive activations with no successful hit (drama/stalemate).
    pub activations_since_hit: u32,
    pub activations_since_damage: u32,
    pub total_hits: u32,
    pub total_pens: u32,
    pub total_glances: u32,
    pub total_fires: u32,
    pub total_cook_offs: u32,
    pub total_crew_wounds: u32,
    pub total_crew_kills: u32,
    pub abilities_used: u32,
    pub shots_fired: u32,
    pub shots_missed: u32,
}

impl Game {
    pub fn tank(&self, id: u8) -> &Tank {
        self.tanks.iter().find(|t| t.id == id).expect("tank id")
    }

    pub fn tank_mut(&mut self, id: u8) -> &mut Tank {
        self.tanks.iter_mut().find(|t| t.id == id).expect("tank id")
    }

    pub fn active_tank_id(&self) -> Option<u8> {
        self.tanks
            .iter()
            .find(|t| t.side == self.active_side && t.is_operational())
            .map(|t| t.id)
    }

    pub fn enemy_tank(&self, side: Side) -> Option<&Tank> {
        self.tanks
            .iter()
            .find(|t| t.side == side.other() && !t.destroyed)
    }

    pub fn outcome(&self) -> Outcome {
        let red_fight = self
            .tanks
            .iter()
            .any(|t| t.side == Side::Red && t.is_operational());
        let blue_fight = self
            .tanks
            .iter()
            .any(|t| t.side == Side::Blue && t.is_operational());
        if red_fight && !blue_fight {
            return Outcome::Winner(Side::Red);
        }
        if blue_fight && !red_fight {
            return Outcome::Winner(Side::Blue);
        }
        if !red_fight && !blue_fight {
            return Outcome::Draw;
        }
        if self.activations >= self.max_activations {
            // Timeout: more hull remaining wins; else draw.
            let red_hp: i32 = self
                .tanks
                .iter()
                .filter(|t| t.side == Side::Red && !t.destroyed)
                .map(|t| t.hull_points)
                .sum();
            let blue_hp: i32 = self
                .tanks
                .iter()
                .filter(|t| t.side == Side::Blue && !t.destroyed)
                .map(|t| t.hull_points)
                .sum();
            return match red_hp.cmp(&blue_hp) {
                std::cmp::Ordering::Greater => Outcome::Winner(Side::Red),
                std::cmp::Ordering::Less => Outcome::Winner(Side::Blue),
                std::cmp::Ordering::Equal => Outcome::Draw,
            };
        }
        Outcome::InProgress
    }

    pub fn occupied_hexes(&self) -> Vec<Hex> {
        self.tanks
            .iter()
            .filter(|t| !t.destroyed)
            .map(|t| t.pos)
            .collect()
    }

    pub fn can_see(&self, shooter: &Tank, target: &Tank) -> bool {
        if shooter.pos.distance(target.pos) > shooter.gun_range {
            return false;
        }
        let Some(dir) = shooter.pos.facing_toward(target.pos) else {
            return false;
        };
        if dir != shooter.turret_facing() {
            return false;
        }
        let occ: Vec<Hex> = self
            .occupied_hexes()
            .into_iter()
            .filter(|h| *h != shooter.pos && *h != target.pos)
            .collect();
        self.board.has_los(shooter.pos, target.pos, &occ)
    }

    /// Legal single actions given remaining AP and buffs (does not spend AP).
    pub fn legal_actions(&self, tank_id: u8, ap_left: i32, buffs: &TurnBuffs) -> Vec<Action> {
        let tank = self.tank(tank_id);
        if !tank.is_operational() || ap_left < 0 {
            return Vec::new();
        }
        let mut out = Vec::new();

        // Abilities cost 0 AP but one per turn and once per battle.
        if !buffs.booming_used && !buffs.move_move_move && !buffs.hit_on_2 && !buffs.free_load {
            for role in [
                CrewRole::Commander,
                CrewRole::Driver,
                CrewRole::Gunner,
                CrewRole::Loader,
            ] {
                if let Some(c) = tank.crew.iter().find(|c| c.role == role) {
                    if c.status != CrewStatus::Killed && !c.ability_used {
                        out.push(match role {
                            CrewRole::Commander => Action::AbilityBoomingVoice,
                            CrewRole::Driver => Action::AbilityMoveMoveMove,
                            CrewRole::Gunner => Action::AbilityBringItDown,
                            CrewRole::Loader => Action::AbilityQuickLoad,
                            CrewRole::Lieutenant => continue,
                        });
                    }
                }
            }
        }

        if tank.on_fire && ap_left >= 1 {
            out.push(Action::ExtinguishFire);
        }

        if tank.can_move_or_turn() {
            if tank.moves_this_turn < tank.effective_max_move() {
                let forward = tank.pos.neighbor(tank.hull_facing);
                let cost = self.board.terrain_at(tank.pos).move_cost_to_leave();
                // Move Move Move: one action can pay for an extra step budget —
                // modeled as Move still costing 1 but max_move effectively +1 when buff active.
                let move_ok = if buffs.move_move_move {
                    tank.moves_this_turn < tank.effective_max_move() + 1
                } else {
                    tank.moves_this_turn < tank.effective_max_move()
                };
                if move_ok
                    && ap_left >= cost
                    && self.board.contains(forward)
                    && !self.board.terrain_at(forward).impassable()
                    && !self.occupied_hexes().contains(&forward)
                {
                    out.push(Action::Move);
                }
            }
            if ap_left >= 1 {
                out.push(Action::TurnLeft);
                out.push(Action::TurnRight);
            }
        }

        if ap_left >= 1 {
            out.push(Action::TurretLeft);
            out.push(Action::TurretRight);
        }

        if tank.can_fire() {
            if let Some(enemy) = self.enemy_tank(tank.side) {
                if enemy.is_operational() || enemy.disabled {
                    // Can shoot disabled tanks still on the table.
                    if !enemy.destroyed && self.can_see(tank, enemy) && ap_left >= 1 {
                        out.push(Action::Fire);
                    }
                }
            }
        }

        if tank.can_load() {
            let cost = if buffs.free_load {
                0
            } else {
                tank.load_action_cost()
            };
            if ap_left >= cost {
                out.push(Action::Load(RoundKind::At));
                if tank.has_he {
                    out.push(Action::Load(RoundKind::He));
                }
            }
        }

        out
    }

    pub fn apply_action<R: Rng>(
        &mut self,
        tank_id: u8,
        action: Action,
        buffs: &mut TurnBuffs,
        ap_left: &mut i32,
        rng: &mut R,
    ) {
        let turn = self.activations;
        let side = self.tank(tank_id).side;

        if is_ability(action) {
            buffs.apply_ability(action);
            if let Some(c) = self.tank_mut(tank_id).crew.iter_mut().find(|c| {
                matches!(
                    (action, c.role),
                    (Action::AbilityBoomingVoice, CrewRole::Commander)
                        | (Action::AbilityMoveMoveMove, CrewRole::Driver)
                        | (Action::AbilityBringItDown, CrewRole::Gunner)
                        | (Action::AbilityQuickLoad, CrewRole::Loader)
                )
            }) {
                c.ability_used = true;
            }
            *ap_left += match action {
                Action::AbilityBoomingVoice => 2,
                _ => 0,
            };
            self.abilities_used += 1;
            self.push_event(turn, Some(side), action.name().to_string(), None);
            return;
        }

        match action {
            Action::Move => {
                let cost = self
                    .board
                    .terrain_at(self.tank(tank_id).pos)
                    .move_cost_to_leave();
                let facing = self.tank(tank_id).hull_facing;
                let next = self.tank(tank_id).pos.neighbor(facing);
                self.tank_mut(tank_id).pos = next;
                self.tank_mut(tank_id).moves_this_turn += 1;
                *ap_left -= cost;
                self.push_event(turn, Some(side), format!("Move → {next}"), None);
            }
            Action::TurnLeft | Action::TurnRight => {
                let left = matches!(action, Action::TurnLeft);
                let hull = self.tank(tank_id).hull_facing;
                // Turret may turn with hull or stay — v1: turret stays absolute,
                // so relative offset shifts opposite to hull turn.
                let new_hull = turn_hull(hull, left);
                let old_abs = hull.with_turret_offset(self.tank(tank_id).turret_offset);
                let new_offset = relative_offset(new_hull, old_abs);
                self.tank_mut(tank_id).hull_facing = new_hull;
                self.tank_mut(tank_id).turret_offset = new_offset;
                *ap_left -= 1;
                self.push_event(turn, Some(side), action.name().to_string(), None);
            }
            Action::TurretLeft | Action::TurretRight => {
                let left = matches!(action, Action::TurretLeft);
                let o = self.tank(tank_id).turret_offset;
                self.tank_mut(tank_id).turret_offset = step_turret(o, left);
                *ap_left -= 1;
                self.push_event(turn, Some(side), action.name().to_string(), None);
            }
            Action::Fire => {
                self.resolve_fire(tank_id, buffs, rng);
                *ap_left -= 1;
            }
            Action::Load(kind) => {
                let cost = if buffs.free_load {
                    0
                } else {
                    self.tank(tank_id).load_action_cost()
                };
                self.tank_mut(tank_id).loaded = Some(kind);
                *ap_left -= cost;
                self.push_event(turn, Some(side), action.name().to_string(), None);
            }
            Action::ExtinguishFire => {
                self.tank_mut(tank_id).on_fire = false;
                *ap_left -= 1;
                self.push_event(turn, Some(side), "Extinguished fire".into(), None);
            }
            _ => {}
        }
    }

    fn resolve_fire<R: Rng>(&mut self, tank_id: u8, buffs: &TurnBuffs, rng: &mut R) {
        let turn = self.activations;
        let side = self.tank(tank_id).side;
        let Some(enemy_id) = self.enemy_tank(side).map(|t| t.id) else {
            return;
        };
        let round = match self.tank_mut(tank_id).loaded.take() {
            Some(r) => r,
            None => return,
        };
        self.shots_fired += 1;

        let shooter_pos = self.tank(tank_id).pos;
        let penalty = self.board.accuracy_penalty_vs(self.tank(enemy_id).pos);
        let impact = self.tank(enemy_id).impact_facing(shooter_pos);
        let acc = if buffs.hit_on_2 {
            2
        } else {
            self.tank(tank_id).effective_accuracy()
        };
        let enemy = self.tank_mut(enemy_id);
        let ev = resolve_shot(
            rng,
            crate::combat::ShotParams {
                attacker_accuracy: acc,
                accuracy_penalty: penalty,
                round,
                impact,
                forced_hit: None,
                forced_pen_roll: None,
            },
            enemy,
        );

        if !ev.hit {
            self.shots_missed += 1;
            self.activations_since_hit += 0; // updated at end of activation
        } else {
            self.total_hits += 1;
            if ev.penetrating {
                self.total_pens += 1;
            }
            if ev.glancing {
                self.total_glances += 1;
            }
            if ev.fire_started {
                self.total_fires += 1;
            }
            if ev.crew_wounded {
                self.total_crew_wounds += 1;
            }
            if ev.crew_killed {
                self.total_crew_kills += 1;
            }
            if ev.hull_damage > 0 {
                self.activations_since_damage = 0;
            }
            self.activations_since_hit = 0;
        }

        if ev.cook_off {
            self.total_cook_offs += 1;
            let pos = self.tank(enemy_id).pos;
            self.board.set_terrain(pos, Terrain::Rubble);
        }

        let text = ev.description.clone();
        self.push_event(turn, Some(side), text, Some(ev));
    }

    pub fn begin_activation(&mut self, tank_id: u8) {
        self.tank_mut(tank_id).moves_this_turn = 0;
    }

    pub fn end_activation<R: Rng>(&mut self, rng: &mut R) {
        // Fire / cook-off for all tanks at end of each activation.
        let ids: Vec<u8> = self.tanks.iter().map(|t| t.id).collect();
        for id in ids {
            let events = {
                let tank = self.tank_mut(id);
                end_of_turn_hazards(rng, tank)
            };
            for ev in events {
                if ev.cook_off {
                    self.total_cook_offs += 1;
                    let pos = self.tank(id).pos;
                    self.board.set_terrain(pos, Terrain::Rubble);
                }
                if ev.hull_damage > 0 {
                    self.activations_since_damage = 0;
                }
                let side = self.tank(id).side;
                let text = ev.description.clone();
                self.push_event(self.activations, Some(side), text, Some(ev));
            }
        }

        self.activations += 1;
        self.activations_since_hit = self.activations_since_hit.saturating_add(1);
        self.activations_since_damage = self.activations_since_damage.saturating_add(1);
        // Note: hit counters reset to 0 inside resolve_fire; the saturating_add
        // above would wrongly increment after a hit on the same activation.
        // Fix: track whether a hit happened this activation.
        self.active_side = self.active_side.other();
    }

    fn push_event(
        &mut self,
        turn: u32,
        side: Option<Side>,
        text: String,
        combat: Option<CombatEvent>,
    ) {
        self.events.push(GameEvent {
            turn,
            side,
            text,
            combat,
        });
    }
}

fn relative_offset(hull: Facing, absolute_turret: Facing) -> i8 {
    let mut o = absolute_turret.index() as i8 - hull.index() as i8;
    while o > 3 {
        o -= 6;
    }
    while o < -2 {
        o += 6;
    }
    o
}

/// Play one full activation using the provided plan of actions.
pub fn play_activation<R: Rng>(game: &mut Game, plan: &[Action], rng: &mut R) {
    let Some(tank_id) = game.active_tank_id() else {
        game.end_activation(rng);
        return;
    };
    game.begin_activation(tank_id);
    let mut buffs = TurnBuffs::default();
    let mut ap = game.tank(tank_id).effective_actions();

    // Re-check hit tracking for this activation.
    let hits_before = game.total_hits;

    for action in plan {
        if game.outcome() != Outcome::InProgress {
            break;
        }
        let legal = game.legal_actions(tank_id, ap, &buffs);
        if !legal.contains(action) {
            continue;
        }
        game.apply_action(tank_id, *action, &mut buffs, &mut ap, rng);
        if ap < 0 {
            break;
        }
    }

    game.end_activation(rng);

    // Correct since-hit: if we got a hit this activation, counter is 0.
    if game.total_hits > hits_before {
        game.activations_since_hit = 0;
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::scenario::skirmish;
    use rand::SeedableRng;
    use rand_chacha::ChaCha8Rng;

    #[test]
    fn skirmish_starts_in_progress() {
        let mut rng = ChaCha8Rng::seed_from_u64(0);
        let g = skirmish(&mut rng);
        assert_eq!(g.outcome(), Outcome::InProgress);
        assert!(g.active_tank_id().is_some());
    }
}
