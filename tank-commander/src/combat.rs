//! Combat resolution: hit, glance, penetrate, fire, cook-off.
//!
//! Infantry are destroyed by any hit — callers (see `game.rs`) force-destroy
//! after [`resolve_shot`] when the target kind is Infantry and `ev.hit`.

use crate::dice::{penetrates, succeeds};
use crate::unit::{CrewStatus, ImpactFacing, RoundKind, Tank, UnitKind};
use rand::Rng;
use serde::{Deserialize, Serialize};

#[derive(Clone, Debug, Default, Serialize, Deserialize)]
pub struct CombatEvent {
    pub description: String,
    pub hit: bool,
    pub penetrating: bool,
    pub glancing: bool,
    pub crew_wounded: bool,
    pub crew_killed: bool,
    pub fire_started: bool,
    pub suppressed: bool,
    pub hull_damage: i32,
    pub disabled: bool,
    pub destroyed: bool,
    pub cook_off: bool,
    pub impact: Option<ImpactFacing>,
}

/// Inputs for [`resolve_shot`].
pub struct ShotParams {
    pub attacker_accuracy: i32,
    pub accuracy_penalty: i32,
    pub round: RoundKind,
    pub impact: ImpactFacing,
    pub forced_hit: Option<bool>,
    pub forced_pen_roll: Option<i32>,
}

/// Roll to hit, then strength vs armor. Mutates `target`.
pub fn resolve_shot<R: Rng>(rng: &mut R, params: ShotParams, target: &mut Tank) -> CombatEvent {
    let ShotParams {
        attacker_accuracy,
        accuracy_penalty,
        round,
        impact,
        forced_hit,
        forced_pen_roll,
    } = params;
    let mut ev = CombatEvent {
        impact: Some(impact),
        ..CombatEvent::default()
    };

    let need = attacker_accuracy + accuracy_penalty;
    let hit_roll = rng.gen_range(1..=6);
    let hits = forced_hit.unwrap_or_else(|| succeeds(hit_roll, need));
    if !hits {
        ev.description = format!(
            "miss (rolled {hit_roll}, needed {need}+) vs {} {}",
            target.name,
            impact_name(impact)
        );
        return ev;
    }
    ev.hit = true;

    let pen_roll = forced_pen_roll.unwrap_or_else(|| rng.gen_range(1..=6));
    let total = pen_roll + round.strength();
    let armor = target.armor.for_impact(impact);
    let penetrating = penetrates(pen_roll, round.strength(), armor);

    if penetrating {
        ev.penetrating = true;
        ev.hull_damage = 1;
        target.hull_points -= 1;
        ev.description = format!(
            "PEN {} {} ({}+{}={} vs armor {})",
            target.name,
            impact_name(impact),
            pen_roll,
            round.strength(),
            total,
            armor
        );
        wound_random_crew(rng, target, &mut ev);
        if target.hull_points <= 0 {
            target.hull_points = 0;
            target.disabled = true;
            ev.disabled = true;
        }
    } else {
        ev.glancing = true;
        ev.description = format!(
            "glance {} {} ({}+{}={} vs armor {})",
            target.name,
            impact_name(impact),
            pen_roll,
            round.strength(),
            total,
            armor
        );
        // Glancing wounds on 4+ (1 always fails, 6 always succeeds).
        let wound_roll = rng.gen_range(1..=6);
        if succeeds(wound_roll, 4) {
            wound_random_crew(rng, target, &mut ev);
        }
        ev.description
            .push_str(&format!(", wound roll {wound_roll}"));
        // House rule: every glance suppresses (no stacking).
        if !target.suppressed {
            target.suppressed = true;
            ev.suppressed = true;
            ev.description.push_str("; SUPPRESSED");
        }
    }

    if round == RoundKind::He {
        let fire_roll = rng.gen_range(1..=6);
        if succeeds(fire_roll, 5) {
            target.on_fire = true;
            ev.fire_started = true;
            ev.description.push_str("; FIRE started");
        }
    }

    ev
}

fn impact_name(i: ImpactFacing) -> &'static str {
    match i {
        ImpactFacing::Front => "front",
        ImpactFacing::Side => "side",
        ImpactFacing::Rear => "rear",
    }
}

fn wound_random_crew<R: Rng>(rng: &mut R, target: &mut Tank, ev: &mut CombatEvent) {
    let living = target.living_crew_indices();
    if living.is_empty() {
        return;
    }
    let idx = living[rng.gen_range(0..living.len())];
    match target.crew[idx].status {
        CrewStatus::Healthy => {
            target.crew[idx].status = CrewStatus::Wounded;
            ev.crew_wounded = true;
            ev.description
                .push_str(&format!("; {} wounded", role_name(target.crew[idx].role)));
        }
        CrewStatus::Wounded => {
            target.crew[idx].status = CrewStatus::Killed;
            ev.crew_killed = true;
            ev.description
                .push_str(&format!("; {} killed", role_name(target.crew[idx].role)));
        }
        CrewStatus::Killed => {}
    }
}

fn role_name(role: crate::unit::CrewRole) -> &'static str {
    match role {
        crate::unit::CrewRole::Commander => "Commander",
        crate::unit::CrewRole::Driver => "Driver",
        crate::unit::CrewRole::Gunner => "Gunner",
        crate::unit::CrewRole::Loader => "Loader",
        crate::unit::CrewRole::Lieutenant => "Lieutenant",
    }
}

/// End-of-turn fire damage and cook-off checks for disabled tanks.
pub fn end_of_turn_hazards<R: Rng>(rng: &mut R, tank: &mut Tank) -> Vec<CombatEvent> {
    let mut out = Vec::new();
    if tank.destroyed {
        return out;
    }

    if tank.on_fire && tank.is_operational() {
        tank.hull_points -= 1;
        let mut ev = CombatEvent {
            description: format!("{} burns (-1 HP → {})", tank.name, tank.hull_points),
            hull_damage: 1,
            fire_started: false,
            ..CombatEvent::default()
        };
        if tank.hull_points <= 0 {
            tank.hull_points = 0;
            tank.disabled = true;
            ev.disabled = true;
            // Last HP lost to fire → immediate cook-off.
            cook_off(tank, &mut ev);
        }
        out.push(ev);
    }

    if tank.disabled && !tank.destroyed && tank.kind != UnitKind::Infantry {
        let roll = rng.gen_range(1..=6);
        // Cook-off on 4+ (1 always fails, 6 always succeeds).
        if succeeds(roll, 4) {
            let mut ev = CombatEvent {
                description: format!("{} ammo cooks off (rolled {roll})", tank.name),
                ..CombatEvent::default()
            };
            cook_off(tank, &mut ev);
            out.push(ev);
        }
    }

    out
}

fn cook_off(tank: &mut Tank, ev: &mut CombatEvent) {
    tank.destroyed = true;
    tank.disabled = true;
    tank.hull_points = 0;
    tank.on_fire = false;
    ev.cook_off = true;
    ev.destroyed = true;
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::hex::{Facing, Hex};
    use crate::unit::Side;
    use rand::SeedableRng;
    use rand_chacha::ChaCha8Rng;

    #[test]
    fn forced_pen_disables_at_zero_hp() {
        let mut rng = ChaCha8Rng::seed_from_u64(1);
        let mut t = Tank::stock(0, Side::Blue, Hex::new(1, 0), Facing::E, "B");
        t.hull_points = 1;
        let ev = resolve_shot(
            &mut rng,
            ShotParams {
                attacker_accuracy: 2,
                accuracy_penalty: 0,
                round: RoundKind::At,
                impact: ImpactFacing::Rear,
                forced_hit: Some(true),
                forced_pen_roll: Some(6),
            },
            &mut t,
        );
        assert!(ev.penetrating);
        assert!(ev.disabled);
        assert!(t.disabled);
    }

    #[test]
    fn natural_one_on_pen_is_glance_vs_stock_armor() {
        let mut rng = ChaCha8Rng::seed_from_u64(1);
        let mut t = Tank::stock(0, Side::Blue, Hex::new(1, 0), Facing::E, "B");
        let ev = resolve_shot(
            &mut rng,
            ShotParams {
                attacker_accuracy: 2,
                accuracy_penalty: 0,
                round: RoundKind::At,
                impact: ImpactFacing::Front,
                forced_hit: Some(true),
                forced_pen_roll: Some(1),
            },
            &mut t,
        );
        assert!(ev.glancing);
        assert!(!ev.penetrating);
        assert!(ev.suppressed);
        assert!(t.suppressed);
        assert_eq!(t.hull_points, 4);

        // Second glance does not stack.
        let ev2 = resolve_shot(
            &mut rng,
            ShotParams {
                attacker_accuracy: 2,
                accuracy_penalty: 0,
                round: RoundKind::At,
                impact: ImpactFacing::Front,
                forced_hit: Some(true),
                forced_pen_roll: Some(1),
            },
            &mut t,
        );
        assert!(ev2.glancing);
        assert!(!ev2.suppressed);
        assert!(t.suppressed);
    }
}
