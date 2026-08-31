//! Combat resolution: hit, glance, penetrate, fire, cook-off.
//!
//! Infantry are destroyed by any hit — callers (see `game.rs`) force-destroy
//! after [`resolve_shot`] when the target kind is Infantry and `ev.hit`.

use crate::dice::{penetrates, succeeds};
use crate::unit::{CrewRole, CrewStatus, ImpactFacing, RoundKind, Tank, UnitKind};
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
    /// Medkit absorbed this injury (no status change).
    pub medkit_save: bool,
    /// Lieutenant began covering a killed role after this injury.
    pub lt_cover: bool,
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
            // APCs have no main-gun ammo cook-off — wrecked immediately.
            if target.kind == UnitKind::Apc {
                target.destroyed = true;
                target.on_fire = false;
                ev.destroyed = true;
            }
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
    let role = target.crew[idx].role;

    // Medkit: first injury ignores its penalty once.
    if target.has_medkit && !target.medkit_used {
        target.medkit_used = true;
        ev.medkit_save = true;
        ev.description
            .push_str(&format!("; Medkit ignores {} injury", role_name(role)));
        return;
    }

    match target.crew[idx].status {
        CrewStatus::Healthy => {
            target.crew[idx].status = CrewStatus::Wounded;
            ev.crew_wounded = true;
            ev.description
                .push_str(&format!("; {} wounded", role_name(role)));
        }
        CrewStatus::Wounded => {
            target.crew[idx].status = CrewStatus::Killed;
            ev.crew_killed = true;
            ev.description
                .push_str(&format!("; {} killed", role_name(role)));
            if role == crate::unit::CrewRole::Lieutenant {
                target.crew[idx].covering = None;
            } else if assign_lieutenant_cover(target, role) {
                ev.lt_cover = true;
                ev.description
                    .push_str(&format!("; Lieutenant covers {}", role_name(role)));
            }
        }
        CrewStatus::Killed => {}
    }
}

/// Living uncovered lieutenant steps into a killed core role (acts as wounded).
fn assign_lieutenant_cover(target: &mut Tank, killed: crate::unit::CrewRole) -> bool {
    if matches!(killed, crate::unit::CrewRole::Lieutenant) {
        return false;
    }
    if let Some(lt) = target.crew.iter_mut().find(|c| {
        c.role == crate::unit::CrewRole::Lieutenant
            && c.status != CrewStatus::Killed
            && c.covering.is_none()
    }) {
        lt.covering = Some(killed);
        return true;
    }
    false
}

fn role_name(role: CrewRole) -> &'static str {
    match role {
        crate::unit::CrewRole::Commander => "Commander",
        crate::unit::CrewRole::Driver => "Driver",
        crate::unit::CrewRole::Gunner => "Gunner",
        crate::unit::CrewRole::Loader => "Loader",
        crate::unit::CrewRole::Lieutenant => "Lieutenant",
    }
}

/// −1 hull from fire at the end of **this** unit's activation.
///
/// Last hull point lost to fire on a **tank** → immediate cook-off (caller
/// applies splash). APCs are destroyed without cook-off.
pub fn tick_fire_damage(tank: &mut Tank) -> Option<CombatEvent> {
    if tank.destroyed || !tank.on_fire || !tank.is_operational() {
        return None;
    }
    tank.hull_points -= 1;
    let mut ev = CombatEvent {
        description: format!("{} burns (-1 HP → {})", tank.name, tank.hull_points),
        hull_damage: 1,
        ..CombatEvent::default()
    };
    if tank.hull_points <= 0 {
        tank.hull_points = 0;
        tank.disabled = true;
        ev.disabled = true;
        if tank.kind == UnitKind::Tank {
            apply_cook_off(tank, &mut ev);
        } else if tank.kind == UnitKind::Apc {
            // Soft-skinned: wrecked, no ammo cook-off.
            tank.destroyed = true;
            tank.on_fire = false;
            ev.destroyed = true;
        }
    }
    Some(ev)
}

/// Cook-off roll for a disabled **tank** still on the table.
///
/// APCs never cook off. Checked after every activation while the wreck remains
/// (disabled units cannot activate themselves). Caller applies HE strength-4
/// splash.
pub fn tick_disabled_cook_off<R: Rng>(rng: &mut R, tank: &mut Tank) -> Option<CombatEvent> {
    if tank.destroyed || !tank.disabled || tank.kind != UnitKind::Tank {
        return None;
    }
    let roll = rng.gen_range(1..=6);
    if !succeeds(roll, 4) {
        return None;
    }
    let mut ev = CombatEvent {
        description: format!("{} ammo cooks off (rolled {roll})", tank.name),
        ..CombatEvent::default()
    };
    apply_cook_off(tank, &mut ev);
    Some(ev)
}

fn apply_cook_off(tank: &mut Tank, ev: &mut CombatEvent) {
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

    #[test]
    fn fire_damage_only_on_burning_unit() {
        let mut t = Tank::stock(0, Side::Blue, Hex::new(1, 0), Facing::E, "B");
        t.on_fire = true;
        t.hull_points = 3;
        let ev = tick_fire_damage(&mut t).expect("fire tick");
        assert_eq!(t.hull_points, 2);
        assert_eq!(ev.hull_damage, 1);
        assert!(!ev.cook_off);
        assert!(t.on_fire);
    }

    #[test]
    fn fire_last_hp_cooks_off_immediately() {
        let mut t = Tank::stock(0, Side::Blue, Hex::new(1, 0), Facing::E, "B");
        t.on_fire = true;
        t.hull_points = 1;
        let ev = tick_fire_damage(&mut t).expect("fire tick");
        assert!(ev.cook_off);
        assert!(t.destroyed);
        assert!(!t.on_fire);
    }

    #[test]
    fn apc_never_cooks_off() {
        let mut rng = ChaCha8Rng::seed_from_u64(3);
        let mut a = Tank::stock_apc(0, Side::Blue, Hex::new(1, 0), Facing::E, "APC");
        a.disabled = true;
        a.hull_points = 0;
        for _ in 0..30 {
            assert!(tick_disabled_cook_off(&mut rng, &mut a).is_none());
            assert!(!a.destroyed);
        }

        let mut burning = Tank::stock_apc(1, Side::Blue, Hex::new(2, 0), Facing::E, "APC2");
        burning.on_fire = true;
        burning.hull_points = 1;
        let ev = tick_fire_damage(&mut burning).expect("fire");
        assert!(burning.destroyed);
        assert!(!ev.cook_off, "APC fire death must not cook off");
    }

    #[test]
    fn apc_last_pen_destroys_without_cook_off() {
        let mut rng = ChaCha8Rng::seed_from_u64(4);
        let mut a = Tank::stock_apc(0, Side::Blue, Hex::new(1, 0), Facing::E, "APC");
        a.hull_points = 1;
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
            &mut a,
        );
        assert!(ev.penetrating);
        assert!(ev.disabled);
        assert!(ev.destroyed);
        assert!(!ev.cook_off);
        assert!(a.destroyed);
    }

    #[test]
    fn disabled_cook_off_sometimes_succeeds() {
        let mut cooked = false;
        for seed in 0..40u64 {
            let mut rng = ChaCha8Rng::seed_from_u64(seed);
            let mut t = Tank::stock(0, Side::Blue, Hex::new(1, 0), Facing::E, "B");
            t.disabled = true;
            t.hull_points = 0;
            if let Some(ev) = tick_disabled_cook_off(&mut rng, &mut t) {
                assert!(ev.cook_off);
                assert!(t.destroyed);
                cooked = true;
                break;
            }
        }
        assert!(cooked, "expected some seed to cook off");
    }
}
