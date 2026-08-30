//! Turn-based game state and legal-action resolution.

use crate::action::{is_ability, step_turret, turn_hull, Action, TurnBuffs};
use crate::board::{Board, Terrain};
use crate::combat::{end_of_turn_hazards, resolve_shot, CombatEvent, ShotParams};
use crate::dice::succeeds;
use crate::hex::{Facing, Hex};
use crate::unit::{CrewRole, CrewStatus, RoundKind, Side, Tank, UnitKind};
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
pub struct PendingAirStrike {
    pub side: Side,
    pub hex: Hex,
    /// Turns waited; need roll is `(6 - wait).max(2)`. Natural 1 always fails.
    pub wait: u8,
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
    /// `"skirmish"` | `"platoon"` | `"combined"`.
    pub scenario: String,
    pub pending_air_strikes: Vec<PendingAirStrike>,
    pub air_strikes_resolved: u32,
    pub infantry_kills: u32,
    /// End the battle (score like a timeout) after this many activations with
    /// no hull damage. `0` disables. Used so platoon games stop on idle
    /// loops instead of a short hard cap.
    pub stalemate_after: u32,
    /// Consecutive activations with no successful hit (drama/stalemate).
    pub activations_since_hit: u32,
    pub activations_since_damage: u32,
    pub total_hits: u32,
    pub total_pens: u32,
    pub total_glances: u32,
    pub total_suppressions: u32,
    pub total_fires: u32,
    pub total_cook_offs: u32,
    pub total_crew_wounds: u32,
    pub total_crew_kills: u32,
    pub abilities_used: u32,
    pub shots_fired: u32,
    pub shots_missed: u32,
    pub at_shots: u32,
    pub he_shots: u32,
    pub moves_made: u32,
    pub turns_made: u32,
    pub turret_rotations: u32,
}

impl Game {
    pub fn new(
        board: Board,
        tanks: Vec<Tank>,
        first: Side,
        max_activations: u32,
        scenario: impl Into<String>,
    ) -> Self {
        Self {
            board,
            tanks,
            active_side: first,
            activations: 0,
            max_activations,
            events: Vec::new(),
            first_player: first,
            scenario: scenario.into(),
            pending_air_strikes: Vec::new(),
            air_strikes_resolved: 0,
            infantry_kills: 0,
            stalemate_after: 0,
            activations_since_hit: 0,
            activations_since_damage: 0,
            total_hits: 0,
            total_pens: 0,
            total_glances: 0,
            total_suppressions: 0,
            total_fires: 0,
            total_cook_offs: 0,
            total_crew_wounds: 0,
            total_crew_kills: 0,
            abilities_used: 0,
            shots_fired: 0,
            shots_missed: 0,
            at_shots: 0,
            he_shots: 0,
            moves_made: 0,
            turns_made: 0,
            turret_rotations: 0,
        }
    }

    pub fn with_stalemate(mut self, activations_without_damage: u32) -> Self {
        self.stalemate_after = activations_without_damage;
        self
    }

    pub fn tank(&self, id: u8) -> &Tank {
        self.tanks.iter().find(|t| t.id == id).expect("tank id")
    }

    pub fn tank_mut(&mut self, id: u8) -> &mut Tank {
        self.tanks.iter_mut().find(|t| t.id == id).expect("tank id")
    }

    /// First operational unit of the active side (fallback for single-unit callers).
    pub fn active_tank_id(&self) -> Option<u8> {
        self.operational_ids(self.active_side).into_iter().next()
    }

    pub fn operational_ids(&self, side: Side) -> Vec<u8> {
        self.tanks
            .iter()
            .filter(|t| t.side == side && t.is_operational())
            .map(|t| t.id)
            .collect()
    }

    /// Non-destroyed enemy units.
    pub fn enemy_units(&self, side: Side) -> Vec<&Tank> {
        self.tanks
            .iter()
            .filter(|t| t.side == side.other() && !t.destroyed)
            .collect()
    }

    pub fn enemy_tank(&self, side: Side) -> Option<&Tank> {
        self.enemy_units(side).into_iter().next()
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
        if self.stalemate_idle() || self.activations >= self.max_activations {
            return self.score_attrition();
        }
        Outcome::InProgress
    }

    /// Both sides still fighting, but no successful hit for `stalemate_after`
    /// activations after contact — circling / dry lanes. Glances and misses
    /// still count as "alive" combat; only a long no-hit drought ends early.
    pub fn stalemate_idle(&self) -> bool {
        self.stalemate_after > 0
            && self.total_hits > 0
            && self.activations_since_hit >= self.stalemate_after
    }

    fn score_attrition(&self) -> Outcome {
        let red_ops = self
            .tanks
            .iter()
            .filter(|t| t.side == Side::Red && t.is_operational())
            .count();
        let blue_ops = self
            .tanks
            .iter()
            .filter(|t| t.side == Side::Blue && t.is_operational())
            .count();
        match red_ops.cmp(&blue_ops) {
            std::cmp::Ordering::Greater => return Outcome::Winner(Side::Red),
            std::cmp::Ordering::Less => return Outcome::Winner(Side::Blue),
            std::cmp::Ordering::Equal => {}
        }
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
        match red_hp.cmp(&blue_hp) {
            std::cmp::Ordering::Greater => Outcome::Winner(Side::Red),
            std::cmp::Ordering::Less => Outcome::Winner(Side::Blue),
            std::cmp::Ordering::Equal => Outcome::Draw,
        }
    }

    pub fn occupied_hexes(&self) -> Vec<Hex> {
        self.tanks
            .iter()
            .filter(|t| !t.destroyed)
            .map(|t| t.pos)
            .collect()
    }

    fn has_los_between(&self, from: Hex, to: Hex) -> bool {
        let occ: Vec<Hex> = self
            .occupied_hexes()
            .into_iter()
            .filter(|h| *h != from && *h != to)
            .collect();
        self.board.has_los(from, to, &occ)
    }

    /// Main-gun / missile visibility. Infantry ignore turret arc; tanks/APCs require it.
    pub fn can_see(&self, shooter: &Tank, target: &Tank) -> bool {
        if shooter.pos.distance(target.pos) > shooter.gun_range {
            return false;
        }
        if shooter.pos == target.pos {
            return false;
        }
        match shooter.kind {
            UnitKind::Infantry => self.has_los_between(shooter.pos, target.pos),
            UnitKind::Tank | UnitKind::Apc => {
                let Some(dir) = shooter.pos.facing_toward(target.pos) else {
                    return false;
                };
                if dir != shooter.turret_facing() {
                    return false;
                }
                self.has_los_between(shooter.pos, target.pos)
            }
        }
    }

    /// Anti-infantry weapon: range + LOS, no turret arc.
    pub fn can_see_ai(&self, shooter: &Tank, target: &Tank) -> bool {
        if shooter.ai_range <= 0 {
            return false;
        }
        if shooter.pos.distance(target.pos) > shooter.ai_range {
            return false;
        }
        if shooter.pos == target.pos {
            return false;
        }
        self.has_los_between(shooter.pos, target.pos)
    }

    /// Legal single actions given remaining AP and buffs (does not spend AP).
    pub fn legal_actions(&self, tank_id: u8, ap_left: i32, buffs: &TurnBuffs) -> Vec<Action> {
        let tank = self.tank(tank_id);
        if !tank.is_operational() || ap_left < 0 {
            return Vec::new();
        }
        let mut out = Vec::new();

        match tank.kind {
            UnitKind::Tank => self.legal_tank(tank, ap_left, buffs, &mut out),
            UnitKind::Apc => self.legal_apc(tank, ap_left, &mut out),
            UnitKind::Infantry => self.legal_infantry(tank, ap_left, &mut out),
        }

        out
    }

    fn legal_crew_abilities(&self, tank: &Tank, buffs: &TurnBuffs, out: &mut Vec<Action>) {
        if tank.crew.is_empty() {
            return;
        }
        if buffs.booming_used || buffs.move_move_move || buffs.hit_on_2 || buffs.free_load {
            return;
        }
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

    fn legal_tank(&self, tank: &Tank, ap_left: i32, buffs: &TurnBuffs, out: &mut Vec<Action>) {
        self.legal_crew_abilities(tank, buffs, out);

        if tank.on_fire && ap_left >= 1 {
            out.push(Action::ExtinguishFire);
        }

        if tank.can_move_or_turn() {
            self.push_vehicle_move_turn(tank, ap_left, buffs, out);
        }

        if ap_left >= 1 {
            out.push(Action::TurretLeft);
            out.push(Action::TurretRight);
        }

        if tank.can_fire() && ap_left >= 1 {
            for enemy in self.enemy_units(tank.side) {
                if (enemy.is_operational() || enemy.disabled)
                    && !enemy.destroyed
                    && self.can_see(tank, enemy)
                {
                    out.push(Action::Fire { target: enemy.id });
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

        if tank.has_air_support && !tank.air_strike_used && ap_left >= 1 {
            if let Some(nearest) = self
                .enemy_units(tank.side)
                .into_iter()
                .min_by_key(|e| tank.pos.distance(e.pos))
            {
                out.push(Action::CallAirStrike { hex: nearest.pos });
            }
        }
    }

    fn legal_apc(&self, tank: &Tank, ap_left: i32, out: &mut Vec<Action>) {
        if tank.on_fire && ap_left >= 1 {
            out.push(Action::ExtinguishFire);
        }

        if tank.can_move_or_turn() {
            self.push_vehicle_move_turn(tank, ap_left, &TurnBuffs::default(), out);
        }

        if tank.can_fire() && ap_left >= 1 {
            for enemy in self.enemy_units(tank.side) {
                if enemy.kind == UnitKind::Infantry
                    && !enemy.destroyed
                    && self.can_see_ai(tank, enemy)
                {
                    out.push(Action::FireAi { target: enemy.id });
                }
            }
        }
    }

    fn legal_infantry(&self, tank: &Tank, ap_left: i32, out: &mut Vec<Action>) {
        if tank.can_move_or_turn() {
            let max_move = tank.effective_max_move();
            let move_ok = tank.moves_this_turn < max_move;
            if move_ok {
                for i in 0..6u8 {
                    let facing = Facing::from_index(i);
                    let next = tank.pos.neighbor(facing);
                    let cost = self.board.terrain_at(tank.pos).move_cost_to_leave();
                    if ap_left >= cost
                        && self.board.contains(next)
                        && !self.board.terrain_at(next).impassable()
                        && !self.occupied_hexes().contains(&next)
                    {
                        out.push(Action::Step(facing));
                    }
                }
            }
        }

        if tank.can_fire() && ap_left >= 1 {
            for enemy in self.enemy_units(tank.side) {
                if enemy.destroyed {
                    continue;
                }
                if self.can_see(tank, enemy) {
                    out.push(Action::FireMissile {
                        target: enemy.id,
                        round: RoundKind::At,
                    });
                    if tank.has_he {
                        out.push(Action::FireMissile {
                            target: enemy.id,
                            round: RoundKind::He,
                        });
                    }
                }
                if enemy.kind == UnitKind::Infantry && self.can_see_ai(tank, enemy) {
                    out.push(Action::FireAi { target: enemy.id });
                }
            }
        }

        if !tank.in_cover && ap_left >= 1 {
            out.push(Action::TakeCover);
        }
    }

    fn push_vehicle_move_turn(
        &self,
        tank: &Tank,
        ap_left: i32,
        buffs: &TurnBuffs,
        out: &mut Vec<Action>,
    ) {
        if tank.moves_this_turn < tank.effective_max_move() {
            let forward = tank.pos.neighbor(tank.hull_facing);
            let cost = self.board.terrain_at(tank.pos).move_cost_to_leave();
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
                self.moves_made += 1;
                self.push_event(turn, Some(side), format!("Move → {next}"), None);
            }
            Action::Step(facing) => {
                let cost = self
                    .board
                    .terrain_at(self.tank(tank_id).pos)
                    .move_cost_to_leave();
                let next = self.tank(tank_id).pos.neighbor(facing);
                self.tank_mut(tank_id).pos = next;
                self.tank_mut(tank_id).hull_facing = facing;
                self.tank_mut(tank_id).moves_this_turn += 1;
                *ap_left -= cost;
                self.moves_made += 1;
                self.push_event(turn, Some(side), format!("Step {facing:?} → {next}"), None);
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
                self.turns_made += 1;
                self.push_event(turn, Some(side), action.name().to_string(), None);
            }
            Action::TurretLeft | Action::TurretRight => {
                let left = matches!(action, Action::TurretLeft);
                let o = self.tank(tank_id).turret_offset;
                self.tank_mut(tank_id).turret_offset = step_turret(o, left);
                *ap_left -= 1;
                self.turret_rotations += 1;
                self.push_event(turn, Some(side), action.name().to_string(), None);
            }
            Action::Fire { target } => {
                self.resolve_fire(tank_id, target, None, buffs, rng);
                *ap_left -= 1;
            }
            Action::FireMissile { target, round } => {
                self.resolve_fire(tank_id, target, Some(round), buffs, rng);
                *ap_left -= 1;
            }
            Action::FireAi { target } => {
                self.resolve_ai_fire(tank_id, target, buffs, rng);
                *ap_left -= 1;
            }
            Action::TakeCover => {
                self.tank_mut(tank_id).in_cover = true;
                *ap_left -= 1;
                self.push_event(turn, Some(side), "Take cover".into(), None);
            }
            Action::CallAirStrike { hex } => {
                self.tank_mut(tank_id).air_strike_used = true;
                self.pending_air_strikes
                    .push(PendingAirStrike { side, hex, wait: 0 });
                *ap_left -= 1;
                self.push_event(
                    turn,
                    Some(side),
                    format!("Called air strike on {hex}"),
                    None,
                );
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
            Action::AbilityBoomingVoice
            | Action::AbilityMoveMoveMove
            | Action::AbilityBringItDown
            | Action::AbilityQuickLoad => {}
        }
    }

    /// `forced_round` is set for missiles (no magazine); main gun takes from `loaded`.
    pub(crate) fn resolve_fire<R: Rng>(
        &mut self,
        tank_id: u8,
        target_id: u8,
        forced_round: Option<RoundKind>,
        buffs: &TurnBuffs,
        rng: &mut R,
    ) {
        let turn = self.activations;
        let side = self.tank(tank_id).side;
        if self.tanks.iter().all(|t| t.id != target_id) {
            return;
        }

        let round = if let Some(r) = forced_round {
            r
        } else {
            match self.tank_mut(tank_id).loaded.take() {
                Some(r) => r,
                None => return,
            }
        };
        self.shots_fired += 1;
        match round {
            RoundKind::At => self.at_shots += 1,
            RoundKind::He => self.he_shots += 1,
        }

        let shooter_pos = self.tank(tank_id).pos;
        let mut penalty = self.board.accuracy_penalty_vs(self.tank(target_id).pos);
        if self.tank(target_id).in_cover {
            penalty += 1;
        }
        let impact = self.tank(target_id).impact_facing(shooter_pos);
        let acc = if buffs.hit_on_2 {
            2
        } else {
            self.tank(tank_id).effective_accuracy()
        };
        let target_kind = self.tank(target_id).kind;
        let enemy = self.tank_mut(target_id);
        let ev = resolve_shot(
            rng,
            ShotParams {
                attacker_accuracy: acc,
                accuracy_penalty: penalty,
                round,
                impact,
                forced_hit: None,
                forced_pen_roll: None,
            },
            enemy,
        );

        self.record_shot_stats(&ev);

        if ev.hit && target_kind == UnitKind::Infantry {
            self.destroy_infantry(target_id);
        }

        if ev.cook_off {
            self.total_cook_offs += 1;
            let pos = self.tank(target_id).pos;
            self.board.set_terrain(pos, Terrain::Rubble);
        }

        let text = ev.description.clone();
        self.push_event(turn, Some(side), text, Some(ev));
    }

    fn resolve_ai_fire<R: Rng>(
        &mut self,
        tank_id: u8,
        target_id: u8,
        buffs: &TurnBuffs,
        rng: &mut R,
    ) {
        let turn = self.activations;
        let side = self.tank(tank_id).side;
        if self.tanks.iter().all(|t| t.id != target_id) {
            return;
        }
        if self.tank(target_id).kind != UnitKind::Infantry {
            return;
        }

        self.shots_fired += 1;
        let mut penalty = self.board.accuracy_penalty_vs(self.tank(target_id).pos);
        if self.tank(target_id).in_cover {
            penalty += 1;
        }
        let impact = self.tank(target_id).impact_facing(self.tank(tank_id).pos);
        let acc = if buffs.hit_on_2 {
            2
        } else {
            self.tank(tank_id).effective_accuracy()
        };
        // AI weapons: treat as HE strength 4 for pen math; any hit still kills infantry.
        let enemy = self.tank_mut(target_id);
        let ev = resolve_shot(
            rng,
            ShotParams {
                attacker_accuracy: acc,
                accuracy_penalty: penalty,
                round: RoundKind::He,
                impact,
                forced_hit: None,
                forced_pen_roll: None,
            },
            enemy,
        );
        self.record_shot_stats(&ev);
        if ev.hit {
            self.destroy_infantry(target_id);
        }
        let text = format!("AI {}", ev.description);
        self.push_event(turn, Some(side), text, Some(ev));
    }

    fn destroy_infantry(&mut self, target_id: u8) {
        let t = self.tank_mut(target_id);
        if t.kind != UnitKind::Infantry || t.destroyed {
            return;
        }
        t.destroyed = true;
        t.disabled = true;
        t.hull_points = 0;
        self.infantry_kills += 1;
    }

    fn record_shot_stats(&mut self, ev: &CombatEvent) {
        if !ev.hit {
            self.shots_missed += 1;
        } else {
            self.total_hits += 1;
            if ev.penetrating {
                self.total_pens += 1;
            }
            if ev.glancing {
                self.total_glances += 1;
            }
            if ev.suppressed {
                self.total_suppressions += 1;
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
    }

    pub fn begin_activation(&mut self, tank_id: u8) {
        self.tank_mut(tank_id).moves_this_turn = 0;
        if self.tank(tank_id).kind == UnitKind::Infantry {
            self.tank_mut(tank_id).in_cover = false;
        }
    }

    pub fn end_activation<R: Rng>(&mut self, unit_id: u8, rng: &mut R) {
        let acted_side = self.tank(unit_id).side;

        // Clear suppression on the unit that just acted.
        {
            let tank = self.tank_mut(unit_id);
            if tank.suppressed {
                tank.suppressed = false;
                let side = tank.side;
                let name = tank.name.clone();
                self.push_event(
                    self.activations,
                    Some(side),
                    format!("{name} shakes off suppression"),
                    None,
                );
            }
        }

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

        self.tick_air_strikes(acted_side, rng);

        self.activations += 1;
        self.activations_since_hit = self.activations_since_hit.saturating_add(1);
        self.activations_since_damage = self.activations_since_damage.saturating_add(1);
        self.active_side = self.active_side.other();
    }

    fn tick_air_strikes<R: Rng>(&mut self, side: Side, rng: &mut R) {
        let mut still_pending = Vec::new();
        let pending = std::mem::take(&mut self.pending_air_strikes);
        for mut strike in pending {
            if strike.side != side {
                still_pending.push(strike);
                continue;
            }
            strike.wait = strike.wait.saturating_add(1);
            let need = (6 - i32::from(strike.wait)).clamp(2, 6);
            let roll = rng.gen_range(1..=6);
            if succeeds(roll, need) {
                self.resolve_air_strike(strike.hex, side, rng);
                self.air_strikes_resolved += 1;
                self.push_event(
                    self.activations,
                    Some(side),
                    format!(
                        "Air strike arrives on {} (rolled {roll}, needed {need}+)",
                        strike.hex
                    ),
                    None,
                );
            } else {
                self.push_event(
                    self.activations,
                    Some(side),
                    format!(
                        "Air strike delayed on {} (rolled {roll}, needed {need}+)",
                        strike.hex
                    ),
                    None,
                );
                still_pending.push(strike);
            }
        }
        self.pending_air_strikes = still_pending;
    }

    fn resolve_air_strike<R: Rng>(&mut self, hex: Hex, side: Side, rng: &mut R) {
        self.apply_air_blast(hex, side, rng);
        let dir = Facing::from_index(rng.gen_range(0..6));
        let dist = rng.gen_range(1..=6);
        let mut blast = hex;
        for _ in 0..dist {
            blast = blast.neighbor(dir);
        }
        if self.board.contains(blast) {
            self.apply_air_blast(blast, side, rng);
        }
    }

    fn apply_air_blast<R: Rng>(&mut self, hex: Hex, side: Side, rng: &mut R) {
        let victims: Vec<u8> = self
            .tanks
            .iter()
            .filter(|t| !t.destroyed && t.pos == hex)
            .map(|t| t.id)
            .collect();
        for id in victims {
            let kind = self.tank(id).kind;
            let enemy = self.tank_mut(id);
            let ev = resolve_shot(
                rng,
                ShotParams {
                    attacker_accuracy: 2,
                    accuracy_penalty: 0,
                    round: RoundKind::At,
                    impact: crate::unit::ImpactFacing::Front,
                    forced_hit: Some(true),
                    forced_pen_roll: None,
                },
                enemy,
            );
            self.record_shot_stats(&ev);
            if ev.hit && kind == UnitKind::Infantry {
                self.destroy_infantry(id);
            }
            if ev.cook_off {
                self.total_cook_offs += 1;
                let pos = self.tank(id).pos;
                self.board.set_terrain(pos, Terrain::Rubble);
            }
            let text = format!("Air strike: {}", ev.description);
            self.push_event(self.activations, Some(side), text, Some(ev));
        }
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

/// Play one full activation for `unit_id` using the provided plan of actions.
pub fn play_activation<R: Rng>(game: &mut Game, unit_id: u8, plan: &[Action], rng: &mut R) {
    let side = game.active_side;
    let valid = game
        .tanks
        .iter()
        .any(|t| t.id == unit_id && t.side == side && t.is_operational());
    if !valid {
        game.activations += 1;
        game.activations_since_hit = game.activations_since_hit.saturating_add(1);
        game.activations_since_damage = game.activations_since_damage.saturating_add(1);
        game.active_side = side.other();
        return;
    }
    game.begin_activation(unit_id);
    let mut buffs = TurnBuffs::default();
    let mut ap = game.tank(unit_id).effective_actions();

    let hits_before = game.total_hits;

    for action in plan {
        if game.outcome() != Outcome::InProgress {
            break;
        }
        let legal = game.legal_actions(unit_id, ap, &buffs);
        if !legal.contains(action) {
            continue;
        }
        game.apply_action(unit_id, *action, &mut buffs, &mut ap, rng);
        if ap < 0 {
            break;
        }
    }

    game.end_activation(unit_id, rng);

    if game.total_hits > hits_before {
        game.activations_since_hit = 0;
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::board::Board;
    use crate::hex::Facing;
    use crate::unit::Tank;

    fn tiny_skirmish() -> Game {
        let board = Board::rect(11, 9);
        let red = Tank::stock(0, Side::Red, Hex::new(1, 3), Facing::E, "Red One");
        let blue = Tank::stock(1, Side::Blue, Hex::new(9, 5), Facing::W, "Blue One");
        Game::new(board, vec![red, blue], Side::Red, 20, "skirmish")
    }

    #[test]
    fn skirmish_starts_in_progress() {
        let g = tiny_skirmish();
        assert_eq!(g.outcome(), Outcome::InProgress);
        assert!(g.active_tank_id().is_some());
        assert_eq!(g.operational_ids(Side::Red).len(), 1);
        assert_eq!(g.enemy_units(Side::Red).len(), 1);
    }

    #[test]
    fn infantry_hit_is_destroyed() {
        use rand::SeedableRng;
        use rand_chacha::ChaCha8Rng;
        let mut g = tiny_skirmish();
        let inf = Tank::stock_infantry(2, Side::Blue, Hex::new(3, 3), Facing::W, "Blue Squad");
        g.tanks.push(inf);
        // Place red so it can see infantry with turret east.
        g.tank_mut(0).pos = Hex::new(1, 3);
        g.tank_mut(0).hull_facing = Facing::E;
        g.tank_mut(0).turret_offset = 0;
        g.tank_mut(0).loaded = Some(RoundKind::At);
        let mut rng = ChaCha8Rng::seed_from_u64(1);
        let buffs = TurnBuffs::default();
        // Force many fire attempts until a hit, or use resolve path with forced — exercise destroy.
        for _ in 0..20 {
            if g.tank(2).destroyed {
                break;
            }
            g.tank_mut(0).loaded = Some(RoundKind::At);
            if g.can_see(g.tank(0), g.tank(2)) {
                g.resolve_fire(0, 2, None, &buffs, &mut rng);
            }
        }
        // Even on miss, structure is fine; if we hit, infantry is gone.
        if g.total_hits > 0 {
            assert!(g.tank(2).destroyed);
            assert!(g.infantry_kills >= 1);
        }
    }
}
