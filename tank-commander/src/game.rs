//! Turn-based game state and legal-action resolution.

use crate::action::{is_ability, step_turret, turn_hull, Action, TurnBuffs};
use crate::board::{Board, Terrain};
use crate::combat::{
    resolve_shot, tick_disabled_cook_off, tick_fire_damage, CombatEvent, ShotParams,
};
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
    /// 0 = arrives after the caller's next activation ends.
    pub wait: u8,
}

#[derive(Clone, Debug)]
pub struct Game {
    pub board: Board,
    pub tanks: Vec<Tank>,
    pub active_side: Side,
    /// Completed unit activations (both sides).
    pub activations: u32,
    pub max_activations: u32,
    pub events: Vec<GameEvent>,
    pub first_player: Side,
    /// `"skirmish"` | `"platoon"` | `"combined"`.
    pub scenario: String,
    pub pending_air_strikes: Vec<PendingAirStrike>,
    pub air_strikes_resolved: u32,
    pub infantry_kills: u32,
    /// End like a timeout after this many activations with no hit (`0` = off).
    pub stalemate_after: u32,
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
    pub smoke_deployed: u32,
    pub medkit_saves: u32,
    pub lt_covers: u32,
    pub mines_deployed: u32,
    pub mines_triggered: u32,
    pub shots_fired: u32,
    pub shots_missed: u32,
    pub at_shots: u32,
    pub he_shots: u32,
    pub moves_made: u32,
    pub turns_made: u32,
    pub turret_rotations: u32,
    /// Snapshot of upgrades at game start.
    pub loadout_census: crate::upgrades::LoadoutCensus,
    /// True when the lower-spend list won first activation (spoil skipped).
    pub list_initiative: bool,
    pub red_list_points: u32,
    pub blue_list_points: u32,
}

impl Game {
    pub fn new(
        board: Board,
        tanks: Vec<Tank>,
        first: Side,
        max_activations: u32,
        scenario: impl Into<String>,
    ) -> Self {
        let loadout_census = crate::upgrades::LoadoutCensus::from_tanks(&tanks);
        let red_list_points = crate::upgrades::side_list_points(&tanks, Side::Red);
        let blue_list_points = crate::upgrades::side_list_points(&tanks, Side::Blue);
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
            smoke_deployed: 0,
            medkit_saves: 0,
            lt_covers: 0,
            mines_deployed: 0,
            mines_triggered: 0,
            shots_fired: 0,
            shots_missed: 0,
            at_shots: 0,
            he_shots: 0,
            moves_made: 0,
            turns_made: 0,
            turret_rotations: 0,
            loadout_census,
            list_initiative: false,
            red_list_points,
            blue_list_points,
        }
    }

    pub fn with_stalemate(mut self, activations_without_damage: u32) -> Self {
        self.stalemate_after = activations_without_damage;
        self
    }

    pub fn with_list_initiative(mut self, won_by_underspend: bool) -> Self {
        self.list_initiative = won_by_underspend;
        self
    }

    pub fn push_setup_event(&mut self, text: String) {
        self.push_event(0, None, text, None);
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

    /// Units that may activate under pass activation.
    pub fn activatable_ids(&self, side: Side) -> Vec<u8> {
        let ops = self.operational_ids(side);
        let pending: Vec<u8> = ops
            .iter()
            .copied()
            .filter(|id| !self.tank(*id).activated_this_pass)
            .collect();
        if pending.is_empty() {
            ops
        } else {
            pending
        }
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

    /// Infantry adjacent to a friendly (non-destroyed) tank cannot be targeted.
    pub fn infantry_screened(&self, target: &Tank) -> bool {
        if target.kind != UnitKind::Infantry || target.destroyed {
            return false;
        }
        self.tanks.iter().any(|t| {
            t.side == target.side
                && t.kind == UnitKind::Tank
                && !t.destroyed
                && t.pos.distance(target.pos) == 1
        })
    }

    /// Main-gun / missile visibility. Infantry ignore turret arc; tanks/APCs require it.
    pub fn can_see(&self, shooter: &Tank, target: &Tank) -> bool {
        if self.infantry_screened(target) {
            return false;
        }
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
        if self.infantry_screened(target) {
            return false;
        }
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

        // Tank AI weapons (anti-infantry upgrade).
        if tank.ai_range > 0 && ap_left >= 1 {
            for enemy in self.enemy_units(tank.side) {
                if enemy.destroyed {
                    continue;
                }
                if self.can_see_ai(tank, enemy) {
                    out.push(Action::FireAi { target: enemy.id });
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

        self.push_smoke_actions(tank, ap_left, out);
        self.push_mine_actions(tank, ap_left, out);
        self.push_lt_cover_actions(tank, out);
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
                if enemy.destroyed {
                    continue;
                }
                // Soft kill vs infantry; suppression spray vs vehicles.
                if self.can_see_ai(tank, enemy) {
                    out.push(Action::FireAi { target: enemy.id });
                }
            }
        }

        self.push_smoke_actions(tank, ap_left, out);
    }

    fn push_smoke_actions(&self, tank: &Tank, ap_left: i32, out: &mut Vec<Action>) {
        if !tank.has_smoke_launcher || tank.smoke_used || ap_left < 1 {
            return;
        }
        // Offer nearby empty hexes within range 2 (cap list size for the beam).
        let mut n = 0;
        for h in self.board.hexes() {
            if tank.pos.distance(h) > 2 || h == tank.pos {
                continue;
            }
            if !self.board.contains(h) {
                continue;
            }
            out.push(Action::DeploySmoke { hex: h });
            n += 1;
            if n >= 12 {
                break;
            }
        }
    }

    fn push_mine_actions(&self, tank: &Tank, ap_left: i32, out: &mut Vec<Action>) {
        if tank.mines_left == 0 || ap_left < 1 {
            return;
        }
        // Own hex or adjacent empty hexes (not already mined / building).
        let mut candidates = vec![tank.pos];
        for i in 0..6u8 {
            candidates.push(tank.pos.neighbor(Facing::from_index(i)));
        }
        for h in candidates {
            if !self.board.contains(h) || self.board.has_mine(h) {
                continue;
            }
            if self.board.terrain_at(h).impassable() {
                continue;
            }
            out.push(Action::DeployMine { hex: h });
        }
    }

    fn push_lt_cover_actions(&self, tank: &Tank, out: &mut Vec<Action>) {
        let Some(lt) = tank
            .crew
            .iter()
            .find(|c| c.role == CrewRole::Lieutenant && c.status != CrewStatus::Killed)
        else {
            return;
        };
        if lt.covering.is_some() {
            return;
        }
        for role in CrewRole::all_core() {
            if tank
                .crew
                .iter()
                .any(|c| c.role == role && c.status == CrewStatus::Killed)
            {
                out.push(Action::LieutenantCover { role });
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
                // Suppressed infantry cannot fire missiles.
                if !tank.suppressed && self.can_see(tank, enemy) {
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
                self.resolve_mine_at(tank_id, next, rng);
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
                // Dig-in when ending in forest; leaving forest clears it.
                let cover_note = if self.tank(tank_id).kind == UnitKind::Infantry {
                    let in_forest = self.board.terrain_at(next) == Terrain::Forest;
                    self.tank_mut(tank_id).in_cover = in_forest;
                    if in_forest {
                        " (into cover)"
                    } else {
                        ""
                    }
                } else {
                    ""
                };
                self.push_event(
                    turn,
                    Some(side),
                    format!("Step {facing:?} → {next}{cover_note}"),
                    None,
                );
                self.resolve_mine_at(tank_id, next, rng);
            }
            Action::TurnLeft | Action::TurnRight => {
                let left = matches!(action, Action::TurnLeft);
                let hull = self.tank(tank_id).hull_facing;
                // Keep turret absolute facing when the hull turns.
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
                // Revealing fire: missiles leave cover.
                if self.tank(tank_id).in_cover {
                    self.tank_mut(tank_id).in_cover = false;
                    self.push_event(
                        turn,
                        Some(side),
                        "Revealing fire — leave cover".into(),
                        None,
                    );
                }
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
                    format!("Called air strike on {hex} (arrives next activation)"),
                    None,
                );
            }
            Action::DeploySmoke { hex } => {
                self.tank_mut(tank_id).smoke_used = true;
                self.board.add_smoke(hex);
                *ap_left -= 1;
                self.smoke_deployed += 1;
                self.push_event(turn, Some(side), format!("Deployed smoke on {hex}"), None);
            }
            Action::DeployMine { hex } => {
                if self.tank(tank_id).mines_left > 0 && !self.board.has_mine(hex) {
                    self.tank_mut(tank_id).mines_left -= 1;
                    self.board.add_mine(hex);
                    *ap_left -= 1;
                    self.mines_deployed += 1;
                    self.push_event(turn, Some(side), format!("Deployed mine on {hex}"), None);
                }
            }
            Action::LieutenantCover { role } => {
                if let Some(lt) = self.tank_mut(tank_id).crew.iter_mut().find(|c| {
                    c.role == CrewRole::Lieutenant
                        && c.status != CrewStatus::Killed
                        && c.covering.is_none()
                }) {
                    lt.covering = Some(role);
                    self.lt_covers += 1;
                    self.push_event(
                        turn,
                        Some(side),
                        format!("Lieutenant covers {role:?}"),
                        None,
                    );
                }
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

    /// Entering a mined hex: AT strength-6 pen check, then remove the mine.
    fn resolve_mine_at<R: Rng>(&mut self, tank_id: u8, hex: Hex, rng: &mut R) {
        if !self.board.take_mine(hex) {
            return;
        }
        self.mines_triggered += 1;
        let turn = self.activations;
        let side = self.tank(tank_id).side;
        let mut target = self.tank(tank_id).clone();
        let target_kind = target.kind;
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
            &mut target,
        );
        let idx = self.tanks.iter().position(|t| t.id == tank_id).unwrap();
        self.tanks[idx] = target;
        self.record_shot_stats(&ev);
        let mut text = format!("Mine at {hex}: {}", ev.description);
        if target_kind == UnitKind::Infantry && ev.hit {
            self.destroy_infantry(tank_id);
            text.push_str("; infantry destroyed");
        }
        if ev.cook_off {
            self.total_cook_offs += 1;
            let pos = self.tank(tank_id).pos;
            let victim_side = self.tank(tank_id).side;
            self.board.set_terrain(pos, Terrain::Rubble);
            self.apply_cook_off_splash(pos, victim_side, rng);
        }
        self.push_event(turn, Some(side), text, Some(ev));
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
        // Forest −1 only; dig-in does not stack.
        let penalty = self.board.accuracy_penalty_vs(self.tank(target_id).pos);
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
            let side = self.tank(target_id).side;
            self.board.set_terrain(pos, Terrain::Rubble);
            self.apply_cook_off_splash(pos, side, rng);
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
        let target_kind = self.tank(target_id).kind;

        self.shots_fired += 1;
        let penalty = self.board.accuracy_penalty_vs(self.tank(target_id).pos);
        let impact = self.tank(target_id).impact_facing(self.tank(tank_id).pos);
        let acc = if buffs.hit_on_2 {
            2
        } else {
            self.tank(tank_id).effective_accuracy()
        };

        // Soft targets: kill (or pin if dug in). Vehicles: hit → suppress.
        if target_kind == UnitKind::Infantry {
            if self.tank(target_id).in_cover {
                let roll = rng.gen_range(1..=6);
                let need = (acc + penalty).clamp(2, 6);
                let hit = succeeds(roll, need);
                if hit {
                    self.total_hits += 1;
                    self.activations_since_hit = 0;
                    let (name, newly) = {
                        let t = self.tank_mut(target_id);
                        t.in_cover = false;
                        let newly = !t.suppressed;
                        if newly {
                            t.suppressed = true;
                        }
                        (t.name.clone(), newly)
                    };
                    if newly {
                        self.total_suppressions += 1;
                    }
                    self.push_event(
                        turn,
                        Some(side),
                        format!("AI {name} pinned — cover spent, SUPPRESSED (rolled {roll})"),
                        None,
                    );
                } else {
                    self.shots_missed += 1;
                    let name = self.tank(target_id).name.clone();
                    self.push_event(
                        turn,
                        Some(side),
                        format!("AI miss vs {name} in cover (rolled {roll}, needed {need}+)"),
                        None,
                    );
                }
                return;
            }
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
            return;
        }

        // Vehicle suppression spray (no pen / no HP).
        let roll = rng.gen_range(1..=6);
        let need = (acc + penalty).clamp(2, 6);
        let hit = succeeds(roll, need);
        if hit {
            self.total_hits += 1;
            self.activations_since_hit = 0;
            let (name, already) = {
                let t = self.tank_mut(target_id);
                let already = t.suppressed;
                if !already {
                    t.suppressed = true;
                }
                (t.name.clone(), already)
            };
            if !already {
                self.total_suppressions += 1;
            }
            let text = if already {
                format!(
                    "AI spray hits {name} (already suppressed until end of its next activation)"
                )
            } else {
                format!(
                    "AI spray suppresses {name} until end of its next activation \
                     (rolled {roll}, needed {need}+)"
                )
            };
            self.push_event(turn, Some(side), text, None);
        } else {
            self.shots_missed += 1;
            let name = self.tank(target_id).name.clone();
            self.push_event(
                turn,
                Some(side),
                format!("AI spray misses {name} (rolled {roll}, needed {need}+)"),
                None,
            );
        }
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
            if ev.medkit_save {
                self.medkit_saves += 1;
            }
            if ev.lt_cover {
                self.lt_covers += 1;
            }
            if ev.hull_damage > 0 {
                self.activations_since_damage = 0;
            }
            self.activations_since_hit = 0;
        }
    }

    pub fn begin_activation(&mut self, tank_id: u8) {
        let side = self.tank(tank_id).side;
        // New pass: if every operational unit already activated, clear marks.
        let ops = self.operational_ids(side);
        if !ops.is_empty() && ops.iter().all(|id| self.tank(*id).activated_this_pass) {
            for id in ops {
                self.tank_mut(id).activated_this_pass = false;
            }
        }
        self.tank_mut(tank_id).moves_this_turn = 0;
        self.tank_mut(tank_id).activated_this_pass = true;
    }

    pub fn end_activation<R: Rng>(&mut self, unit_id: u8, rng: &mut R) {
        let acted_side = self.tank(unit_id).side;

        // Suppression clears at the end of the suppressed unit's activation.
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

        // Fire ticks only on the unit that just activated.
        let mut cook_off_blasts: Vec<(Hex, Side)> = Vec::new();
        if let Some(ev) = {
            let tank = self.tank_mut(unit_id);
            tick_fire_damage(tank)
        } {
            if ev.cook_off {
                self.total_cook_offs += 1;
                let pos = self.tank(unit_id).pos;
                let side = self.tank(unit_id).side;
                self.board.set_terrain(pos, Terrain::Rubble);
                cook_off_blasts.push((pos, side));
            }
            if ev.hull_damage > 0 {
                self.activations_since_damage = 0;
            }
            let side = self.tank(unit_id).side;
            let text = ev.description.clone();
            self.push_event(self.activations, Some(side), text, Some(ev));
        }

        // Disabled wrecks roll cook-off after every activation while they remain.
        let ids: Vec<u8> = self.tanks.iter().map(|t| t.id).collect();
        for id in ids {
            let ev = {
                let tank = self.tank_mut(id);
                tick_disabled_cook_off(rng, tank)
            };
            if let Some(ev) = ev {
                if ev.cook_off {
                    self.total_cook_offs += 1;
                    let pos = self.tank(id).pos;
                    let side = self.tank(id).side;
                    self.board.set_terrain(pos, Terrain::Rubble);
                    cook_off_blasts.push((pos, side));
                }
                let side = self.tank(id).side;
                let text = ev.description.clone();
                self.push_event(self.activations, Some(side), text, Some(ev));
            }
        }

        for (pos, side) in cook_off_blasts {
            self.apply_cook_off_splash(pos, side, rng);
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
            if strike.wait == 0 {
                // Called this activation — hold until this side activates again.
                strike.wait = 1;
                still_pending.push(strike);
            } else {
                let (impact, note) = scatter_air_impact(strike.hex, &self.board, rng);
                self.air_strikes_resolved += 1;
                match impact {
                    Some(hex) => {
                        self.resolve_air_strike(hex, side, rng);
                        self.push_event(
                            self.activations,
                            Some(side),
                            format!("Air strike arrives on {hex} (aimed {}, {note})", strike.hex),
                            None,
                        );
                    }
                    None => {
                        self.push_event(
                            self.activations,
                            Some(side),
                            format!(
                                "Air strike dissipates off-map (aimed {}, {note})",
                                strike.hex
                            ),
                            None,
                        );
                    }
                }
            }
        }
        self.pending_air_strikes = still_pending;
    }

    fn resolve_air_strike<R: Rng>(&mut self, hex: Hex, side: Side, rng: &mut R) {
        // Blast: impact hex + neighbors.
        self.apply_air_blast(hex, side, rng);
        for n in hex.neighbors() {
            if self.board.contains(n) {
                self.apply_air_blast(n, side, rng);
            }
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
                let victim_side = self.tank(id).side;
                self.board.set_terrain(pos, Terrain::Rubble);
                self.apply_cook_off_splash(pos, victim_side, rng);
            }
            let text = format!("Air strike: {}", ev.description);
            self.push_event(self.activations, Some(side), text, Some(ev));
        }
    }

    /// HE strength-4 hits on every non-destroyed unit within 2 hexes of a cook-off.
    fn apply_cook_off_splash<R: Rng>(&mut self, origin: Hex, side: Side, rng: &mut R) {
        let victims: Vec<u8> = self
            .tanks
            .iter()
            .filter(|t| !t.destroyed && t.pos.distance(origin) >= 1 && t.pos.distance(origin) <= 2)
            .map(|t| t.id)
            .collect();
        let mut nested_blasts: Vec<(Hex, Side)> = Vec::new();
        for id in victims {
            let kind = self.tank(id).kind;
            let impact = self.tank(id).impact_facing(origin);
            let enemy = self.tank_mut(id);
            let ev = resolve_shot(
                rng,
                ShotParams {
                    attacker_accuracy: 2,
                    accuracy_penalty: 0,
                    round: RoundKind::He,
                    impact,
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
                let victim_side = self.tank(id).side;
                self.board.set_terrain(pos, Terrain::Rubble);
                nested_blasts.push((pos, victim_side));
            }
            let name = self.tank(id).name.clone();
            let text = format!("Cook-off splash vs {name}: {}", ev.description);
            self.push_event(self.activations, Some(side), text, Some(ev));
        }
        for (pos, s) in nested_blasts {
            self.apply_cook_off_splash(pos, s, rng);
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

/// Scatter the air-strike impact from the aimed hex.
///
/// Roll d6 on arrival:
/// - **1** — wild: 2 hexes in a random direction (off-map dissipates)
/// - **2–3** — drift: 1 hex in a random direction (off-map dissipates)
/// - **4–6** — on target
///
/// The blast template is still impact + neighbors, so a 1-hex drift almost
/// always still clips the original aim hex. Standing still is unsafe; moving
/// away is the point.
fn scatter_air_impact<R: Rng>(aim: Hex, board: &Board, rng: &mut R) -> (Option<Hex>, &'static str) {
    let roll = rng.gen_range(1..=6);
    let (steps, note) = match roll {
        1 => (2, "wild scatter 2"),
        2 | 3 => (1, "drift 1"),
        _ => (0, "on target"),
    };
    if steps == 0 {
        return (Some(aim), note);
    }
    let dir = Facing::from_index(rng.gen_range(0..6));
    let mut hex = aim;
    for _ in 0..steps {
        hex = hex.neighbor(dir);
    }
    if board.contains(hex) {
        (Some(hex), note)
    } else {
        (None, note)
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
    let valid = game.activatable_ids(side).contains(&unit_id);
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
        let red = Tank::stock(0, Side::Red, Hex::offset(1, 3), Facing::E, "Red One");
        let blue = Tank::stock(1, Side::Blue, Hex::offset(9, 5), Facing::W, "Blue One");
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
        let inf = Tank::stock_infantry(2, Side::Blue, Hex::offset(3, 3), Facing::W, "Blue Squad");
        g.tanks.push(inf);
        // Place red so it can see infantry with turret east.
        g.tank_mut(0).pos = Hex::offset(1, 3);
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

    #[test]
    fn pass_activation_blocks_repeat_until_all_acted() {
        let board = Board::rect(11, 9);
        let tanks = vec![
            Tank::stock(0, Side::Red, Hex::offset(1, 3), Facing::E, "A"),
            Tank::stock(1, Side::Red, Hex::offset(1, 5), Facing::E, "B"),
            Tank::stock(2, Side::Blue, Hex::offset(9, 5), Facing::W, "Enemy"),
        ];
        let mut g = Game::new(board, tanks, Side::Red, 40, "test");
        assert_eq!(g.activatable_ids(Side::Red), vec![0, 1]);
        g.begin_activation(0);
        assert!(g.tank(0).activated_this_pass);
        assert_eq!(g.activatable_ids(Side::Red), vec![1]);
        g.begin_activation(1);
        // Both marked → new pass, both legal again.
        assert_eq!(g.activatable_ids(Side::Red), vec![0, 1]);
        g.begin_activation(0);
        assert!(g.tank(0).activated_this_pass);
        assert!(!g.tank(1).activated_this_pass);
        assert_eq!(g.activatable_ids(Side::Red), vec![1]);
    }

    #[test]
    fn suppressed_infantry_cannot_fire_missiles() {
        let board = Board::rect(11, 9);
        let tanks = vec![
            Tank::stock_infantry(0, Side::Red, Hex::offset(3, 4), Facing::E, "Squad"),
            Tank::stock(1, Side::Blue, Hex::offset(5, 4), Facing::W, "Tank"),
        ];
        let mut g = Game::new(board, tanks, Side::Red, 20, "test");
        g.tank_mut(0).suppressed = true;
        let legal = g.legal_actions(0, 2, &TurnBuffs::default());
        assert!(
            legal
                .iter()
                .all(|a| !matches!(a, Action::FireMissile { .. })),
            "suppressed infantry must not list missile actions: {legal:?}"
        );
    }

    #[test]
    fn main_gun_kills_infantry_through_cover() {
        use rand::SeedableRng;
        use rand_chacha::ChaCha8Rng;
        let board = Board::rect(11, 9);
        let tanks = vec![
            Tank::stock(0, Side::Red, Hex::offset(1, 4), Facing::E, "Tank"),
            Tank::stock_infantry(1, Side::Blue, Hex::offset(4, 4), Facing::W, "Squad"),
        ];
        let mut g = Game::new(board, tanks, Side::Red, 20, "test");
        g.tank_mut(1).in_cover = true;
        g.tank_mut(0).loaded = Some(RoundKind::He);
        let mut rng = ChaCha8Rng::seed_from_u64(3);
        let buffs = TurnBuffs::default();
        for _ in 0..30 {
            if g.tank(1).destroyed {
                break;
            }
            g.tank_mut(0).loaded = Some(RoundKind::He);
            g.resolve_fire(0, 1, None, &buffs, &mut rng);
        }
        assert!(
            g.tank(1).destroyed && g.infantry_kills >= 1,
            "main gun must kill through cover (no pin save)"
        );
    }

    #[test]
    fn missile_revealing_fire_clears_cover() {
        use rand::SeedableRng;
        use rand_chacha::ChaCha8Rng;
        let board = Board::rect(11, 9);
        let tanks = vec![
            Tank::stock_infantry(0, Side::Red, Hex::offset(3, 4), Facing::E, "Squad"),
            Tank::stock(1, Side::Blue, Hex::offset(5, 4), Facing::W, "Tank"),
        ];
        let mut g = Game::new(board, tanks, Side::Red, 20, "test");
        g.tank_mut(0).in_cover = true;
        let mut rng = ChaCha8Rng::seed_from_u64(1);
        let mut ap = 3;
        let mut buffs = TurnBuffs::default();
        g.apply_action(
            0,
            Action::FireMissile {
                target: 1,
                round: RoundKind::At,
            },
            &mut buffs,
            &mut ap,
            &mut rng,
        );
        assert!(
            !g.tank(0).in_cover,
            "missile must clear cover (revealing fire)"
        );
    }

    #[test]
    fn ai_spray_still_pins_covered_infantry() {
        use rand::SeedableRng;
        use rand_chacha::ChaCha8Rng;
        let board = Board::rect(11, 9);
        let tanks = vec![
            Tank::stock_apc(0, Side::Red, Hex::offset(2, 4), Facing::E, "APC"),
            Tank::stock_infantry(1, Side::Blue, Hex::offset(4, 4), Facing::W, "Squad"),
        ];
        let mut g = Game::new(board, tanks, Side::Red, 20, "test");
        g.tank_mut(1).in_cover = true;
        let mut rng = ChaCha8Rng::seed_from_u64(2);
        let buffs = TurnBuffs::default();
        let mut pinned = false;
        for _ in 0..40 {
            if g.tank(1).destroyed {
                break;
            }
            if !g.tank(1).in_cover && g.tank(1).suppressed {
                pinned = true;
                break;
            }
            g.resolve_ai_fire(0, 1, &buffs, &mut rng);
            // Re-dig so we can observe another pin attempt if the first missed.
            if g.tank(1).in_cover || g.tank(1).destroyed {
                continue;
            }
            if !g.tank(1).suppressed {
                g.tank_mut(1).in_cover = true;
            }
        }
        assert!(
            pinned || g.tank(1).destroyed,
            "AI spray should pin covered infantry at least once, or kill after cover spent"
        );
    }

    #[test]
    fn suppression_clears_at_end_of_activation() {
        use rand::SeedableRng;
        use rand_chacha::ChaCha8Rng;
        let board = Board::rect(11, 9);
        let tanks = vec![
            Tank::stock(0, Side::Red, Hex::offset(2, 4), Facing::E, "Red"),
            Tank::stock(1, Side::Blue, Hex::offset(8, 4), Facing::W, "Blue"),
        ];
        let mut g = Game::new(board, tanks, Side::Red, 20, "test");
        g.tank_mut(0).suppressed = true;
        let mut rng = ChaCha8Rng::seed_from_u64(1);
        play_activation(&mut g, 0, &[], &mut rng);
        assert!(
            !g.tank(0).suppressed,
            "suppression must clear after the unit activates"
        );
    }

    #[test]
    fn air_scatter_on_target_or_nearby() {
        use rand::SeedableRng;
        use rand_chacha::ChaCha8Rng;
        let board = Board::rect(11, 9);
        let aim = Hex::offset(5, 4);
        let mut on_target = 0;
        let mut drifted = 0;
        let mut wild = 0;
        let mut rng = ChaCha8Rng::seed_from_u64(7);
        for _ in 0..60 {
            let (impact, note) = scatter_air_impact(aim, &board, &mut rng);
            let Some(hex) = impact else {
                panic!("center aim dissipated: {note}");
            };
            if hex == aim {
                on_target += 1;
                assert_eq!(note, "on target");
            } else if aim.distance(hex) == 1 {
                drifted += 1;
                assert_eq!(note, "drift 1");
            } else if aim.distance(hex) == 2 {
                wild += 1;
                assert_eq!(note, "wild scatter 2");
            } else {
                panic!("scatter too far: {hex} ({note})");
            }
        }
        assert!(
            on_target > 0 && drifted > 0 && wild > 0,
            "{on_target}/{drifted}/{wild}"
        );
    }

    #[test]
    fn fire_does_not_tick_on_other_units_activation() {
        use rand::SeedableRng;
        use rand_chacha::ChaCha8Rng;
        let board = Board::rect(11, 9);
        let tanks = vec![
            Tank::stock(0, Side::Red, Hex::offset(2, 4), Facing::E, "Red"),
            Tank::stock(1, Side::Blue, Hex::offset(8, 4), Facing::W, "Blue"),
        ];
        let mut g = Game::new(board, tanks, Side::Red, 20, "test");
        g.tank_mut(1).on_fire = true;
        let hp_before = g.tank(1).hull_points;
        let mut rng = ChaCha8Rng::seed_from_u64(1);
        // Red activates — Blue is burning but should not take fire damage.
        play_activation(&mut g, 0, &[], &mut rng);
        assert_eq!(g.tank(1).hull_points, hp_before);
        assert!(g.tank(1).on_fire);
        // Blue activates — fire ticks.
        play_activation(&mut g, 1, &[], &mut rng);
        assert_eq!(g.tank(1).hull_points, hp_before - 1);
    }

    #[test]
    fn cook_off_splashes_he_within_two_hexes() {
        use rand::SeedableRng;
        use rand_chacha::ChaCha8Rng;
        let board = Board::rect(11, 9);
        let tanks = vec![
            Tank::stock(0, Side::Red, Hex::offset(4, 4), Facing::E, "Wreck"),
            Tank::stock(1, Side::Blue, Hex::offset(5, 4), Facing::W, "Near"),
            Tank::stock(2, Side::Blue, Hex::offset(9, 4), Facing::W, "Far"),
        ];
        let mut g = Game::new(board, tanks, Side::Red, 20, "test");
        g.tank_mut(0).disabled = true;
        g.tank_mut(0).hull_points = 0;
        let near_hp = g.tank(1).hull_points;
        let far_hp = g.tank(2).hull_points;
        let mut rng = ChaCha8Rng::seed_from_u64(1);
        // Force cook-off via repeated end_activation until it happens.
        let mut cooked = false;
        for _ in 0..40 {
            g.end_activation(0, &mut rng);
            if g.tank(0).destroyed {
                cooked = true;
                break;
            }
        }
        assert!(cooked, "expected cook-off within 40 rolls");
        assert!(
            g.events
                .iter()
                .any(|e| e.text.contains("Cook-off splash vs Near")),
            "near unit must take splash: {:?}",
            g.events.iter().map(|e| &e.text).collect::<Vec<_>>()
        );
        assert!(
            !g.events
                .iter()
                .any(|e| e.text.contains("Cook-off splash vs Far")),
            "far unit (dist 5) must not take splash"
        );
        // Near took an automatic HE hit — hull or at least a combat event.
        assert!(
            g.tank(1).hull_points < near_hp
                || g.tank(1).suppressed
                || g.tank(1).on_fire
                || g.tank(1).destroyed,
            "near unit should feel the HE splash"
        );
        assert_eq!(g.tank(2).hull_points, far_hp);
    }

    #[test]
    fn infantry_adjacent_to_friendly_tank_cannot_be_targeted() {
        let board = Board::rect(11, 9);
        let tanks = vec![
            Tank::stock(0, Side::Red, Hex::offset(1, 4), Facing::E, "Hunter"),
            Tank::stock(1, Side::Blue, Hex::offset(4, 4), Facing::W, "Shield"),
            Tank::stock_infantry(2, Side::Blue, Hex::offset(5, 4), Facing::W, "Squad"),
        ];
        let g = Game::new(board, tanks, Side::Red, 20, "test");
        assert!(g.infantry_screened(g.tank(2)));
        assert!(!g.can_see(g.tank(0), g.tank(2)));
        let legal = g.legal_actions(0, 3, &TurnBuffs::default());
        assert!(
            legal
                .iter()
                .all(|a| !matches!(a, Action::Fire { target: 2 })),
            "screened infantry must not appear as a fire target: {legal:?}"
        );
    }

    #[test]
    fn medkit_absorbs_first_crew_injury() {
        use crate::combat::{resolve_shot, ShotParams};
        use crate::unit::ImpactFacing;
        use rand::SeedableRng;
        use rand_chacha::ChaCha8Rng;
        let mut t = Tank::stock(0, Side::Red, Hex::offset(0, 0), Facing::E, "T").with_field_kit();
        let mut rng = ChaCha8Rng::seed_from_u64(9);
        let ev = resolve_shot(
            &mut rng,
            ShotParams {
                attacker_accuracy: 2,
                accuracy_penalty: 0,
                round: RoundKind::At,
                impact: ImpactFacing::Front,
                forced_hit: Some(true),
                forced_pen_roll: Some(6),
            },
            &mut t,
        );
        assert!(
            ev.medkit_save,
            "first injury should be a medkit save: {ev:?}"
        );
        assert!(!ev.crew_wounded && !ev.crew_killed);
        assert!(t.medkit_used);
        assert!(t.crew.iter().all(|c| c.status == CrewStatus::Healthy));
    }

    #[test]
    fn smoke_blocks_los_and_deploys_once() {
        use rand::SeedableRng;
        use rand_chacha::ChaCha8Rng;
        let board = Board::rect(11, 9);
        let tanks = vec![
            Tank::stock(0, Side::Red, Hex::offset(2, 4), Facing::E, "Red").with_field_kit(),
            Tank::stock(1, Side::Blue, Hex::offset(6, 4), Facing::W, "Blue"),
        ];
        let mut g = Game::new(board, tanks, Side::Red, 20, "test");
        let mid = Hex::offset(4, 4);
        let mut rng = ChaCha8Rng::seed_from_u64(1);
        let mut buffs = TurnBuffs::default();
        let mut ap = 5;
        g.apply_action(
            0,
            Action::DeploySmoke { hex: mid },
            &mut buffs,
            &mut ap,
            &mut rng,
        );
        assert!(g.board.has_smoke(mid));
        assert!(g.tank(0).smoke_used);
        assert_eq!(g.smoke_deployed, 1);
        assert!(!g.board.has_los(Hex::offset(2, 4), Hex::offset(6, 4), &[]));
        // Second deploy not legal.
        let legal = g.legal_actions(0, 5, &TurnBuffs::default());
        assert!(legal
            .iter()
            .all(|a| !matches!(a, Action::DeploySmoke { .. })));
    }

    #[test]
    fn lieutenant_auto_covers_on_crew_kill() {
        use crate::combat::{resolve_shot, ShotParams};
        use crate::unit::ImpactFacing;
        use rand::SeedableRng;
        use rand_chacha::ChaCha8Rng;
        let mut t = Tank::stock(0, Side::Red, Hex::offset(0, 0), Facing::E, "T").with_field_kit();
        // Spend medkit first so the next injury sticks.
        t.medkit_used = true;
        // Wound everyone once so the next pen kills someone.
        for c in &mut t.crew {
            if c.role != CrewRole::Lieutenant {
                c.status = CrewStatus::Wounded;
            }
        }
        let mut covered = false;
        for seed in 0..40u64 {
            let mut t2 = t.clone();
            let mut rng2 = ChaCha8Rng::seed_from_u64(seed);
            let ev = resolve_shot(
                &mut rng2,
                ShotParams {
                    attacker_accuracy: 2,
                    accuracy_penalty: 0,
                    round: RoundKind::At,
                    impact: ImpactFacing::Front,
                    forced_hit: Some(true),
                    forced_pen_roll: Some(6),
                },
                &mut t2,
            );
            if ev.lt_cover {
                covered = true;
                let lt = t2
                    .crew
                    .iter()
                    .find(|c| c.role == CrewRole::Lieutenant)
                    .unwrap();
                assert!(lt.covering.is_some());
                break;
            }
        }
        assert!(covered, "expected LT cover within random kills");
    }
}
