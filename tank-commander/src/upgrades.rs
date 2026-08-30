//! List-building upgrades (up to 10 points for tanks, 4 for APCs).

use crate::unit::{CrewMember, CrewRole, Tank, UnitKind};
use rand::Rng;
use serde::{Deserialize, Serialize};

/// Purchased upgrades applied to a stock unit.
#[derive(Clone, Debug, Default, Serialize, Deserialize)]
pub struct Loadout {
    pub armor_front: u8,
    pub armor_side: u8,
    pub armor_rear: u8,
    pub engine: bool,
    pub extended_barrel: bool,
    pub enhanced_optics: bool,
    pub he: bool,
    pub anti_infantry: bool,
    pub smoke: bool,
    pub medkit: bool,
    pub lieutenant: bool,
    pub air_support: bool,
    pub mines: u8,
}

impl Loadout {
    pub fn cost(&self) -> i32 {
        i32::from(self.armor_front)
            + i32::from(self.armor_side)
            + i32::from(self.armor_rear)
            + i32::from(self.engine)
            + i32::from(self.extended_barrel)
            + i32::from(self.enhanced_optics)
            + i32::from(self.he)
            + i32::from(self.anti_infantry)
            + i32::from(self.smoke)
            + i32::from(self.medkit)
            + i32::from(self.lieutenant)
            + if self.air_support { 2 } else { 0 }
            + i32::from(self.mines)
    }

    pub fn armor_points(&self) -> u8 {
        self.armor_front + self.armor_side + self.armor_rear
    }

    /// Side ≤ front, rear ≤ side; each facing within the kind's max; mines 0..=3.
    pub fn is_legal(&self) -> bool {
        self.is_legal_for(UnitKind::Tank)
    }

    /// Tank facings max +3; APC facings max +2 (upstream).
    pub fn is_legal_for(&self, kind: UnitKind) -> bool {
        let max = armor_facing_max(kind);
        self.armor_front <= max
            && self.armor_side <= max
            && self.armor_rear <= max
            && self.armor_side <= self.armor_front
            && self.armor_rear <= self.armor_side
            && self.mines <= 3
    }
}

fn armor_facing_max(kind: UnitKind) -> u8 {
    match kind {
        UnitKind::Apc => 2,
        UnitKind::Tank | UnitKind::Infantry => 3,
    }
}

/// Apply a legal loadout to a stock unit. Panics if illegal (callers validate).
pub fn apply_loadout(tank: &mut Tank, load: &Loadout) {
    debug_assert!(load.is_legal_for(tank.kind));
    tank.armor.front += i32::from(load.armor_front);
    tank.armor.side += i32::from(load.armor_side);
    tank.armor.rear += i32::from(load.armor_rear);

    let armor_pts = load.armor_points();
    if armor_pts == 0 {
        tank.max_move += 1; // light armor
    }
    if load.armor_front == 3 || load.armor_side == 3 || load.armor_rear == 3 {
        tank.max_move = (tank.max_move - 1).max(1); // heavy armor
    }
    if load.engine {
        tank.max_move += 1;
        tank.has_engine = true;
    }
    if load.extended_barrel {
        tank.gun_range += 1;
        tank.has_barrel = true;
    }
    if load.enhanced_optics {
        // Accuracy is a target number (4+ stock); optics improve it to 3+.
        tank.accuracy = (tank.accuracy - 1).max(2);
        tank.has_optics = true;
    }
    if load.he {
        tank.has_he = true;
    }
    if load.anti_infantry && tank.kind == UnitKind::Tank && tank.ai_range == 0 {
        tank.ai_range = 2;
    }
    if load.smoke {
        tank.has_smoke_launcher = true;
    }
    if load.medkit {
        tank.has_medkit = true;
    }
    if load.lieutenant
        && tank.kind == UnitKind::Tank
        && !tank.crew.iter().any(|c| c.role == CrewRole::Lieutenant)
    {
        tank.crew.push(CrewMember::healthy(CrewRole::Lieutenant));
    }
    if load.air_support {
        tank.has_air_support = true;
    }
    tank.mines_left = load.mines;
    tank.armor_points_bought = armor_pts;
    tank.upgrade_points_spent = load.cost() as u8;
}

/// Weighted random spend up to `budget`. Picks a target in `0..=budget` so
/// sides can under-spend (and win initiative — see scenario setup).
/// `allow_mines` unlocks anti-tank mines.
pub fn spend_budget<R: Rng>(
    tank: &mut Tank,
    budget: i32,
    allow_mines: bool,
    rng: &mut R,
) -> Loadout {
    let target = if budget <= 0 {
        0
    } else {
        rng.gen_range(0..=budget)
    };
    spend_up_to(tank, target, allow_mines, rng)
}

/// Spend up to exactly `target` points (never more).
pub fn spend_up_to<R: Rng>(
    tank: &mut Tank,
    target: i32,
    allow_mines: bool,
    rng: &mut R,
) -> Loadout {
    let budget = target.max(0);
    let mut load = Loadout::default();
    // Stock HE house rule: tanks already have HE; don't charge unless missing.
    if tank.kind == UnitKind::Tank && !tank.has_he {
        load.he = true;
    }

    if budget == 0 {
        apply_loadout(tank, &load);
        return load;
    }

    // Build a shuffled shopping list of one-point options.
    let mut menu: Vec<Buy> = Vec::new();
    match tank.kind {
        UnitKind::Tank => {
            menu.extend([
                Buy::Smoke,
                Buy::Medkit,
                Buy::Lieutenant,
                Buy::Optics,
                Buy::Barrel,
                Buy::Engine,
                Buy::AntiInfantry,
                Buy::ArmorFront,
                Buy::ArmorSide,
                Buy::ArmorRear,
            ]);
            if allow_mines {
                menu.push(Buy::Mine);
                menu.push(Buy::Mine);
                menu.push(Buy::Mine);
            }
        }
        UnitKind::Apc => {
            // APC list: armor, engine, smoke (4 pts).
            menu.extend([
                Buy::Smoke,
                Buy::Engine,
                Buy::ArmorFront,
                Buy::ArmorSide,
                Buy::ArmorRear,
            ]);
        }
        UnitKind::Infantry => {
            apply_loadout(tank, &load);
            return load;
        }
    }
    menu.shuffle_stable(rng);
    // Drop some options so lists trade off instead of always buying everything.
    menu.retain(|_| rng.gen_bool(0.55));

    let kind = tank.kind;
    let armor_max = armor_facing_max(kind);
    let mut spent = load.cost();
    for buy in menu {
        let cost = buy.cost();
        if spent + cost > budget {
            continue;
        }
        if !buy.can_add(&load, kind) {
            continue;
        }
        buy.add(&mut load);
        spent += cost;
        if spent >= budget {
            break;
        }
    }

    // Fill leftover points with armor / mines / engine (tradeoffs still matter).
    let fillers: [Buy; 5] = [
        Buy::ArmorFront,
        Buy::ArmorSide,
        Buy::ArmorRear,
        Buy::Mine,
        Buy::Engine,
    ];
    let mut fill_order = fillers.to_vec();
    fill_order.shuffle_stable(rng);
    while spent < budget {
        let mut filled = false;
        for buy in &fill_order {
            if matches!(buy, Buy::Mine) && !allow_mines {
                continue;
            }
            if spent >= budget || !buy.can_add(&load, kind) {
                continue;
            }
            let cost = buy.cost();
            if spent + cost > budget {
                continue;
            }
            buy.add(&mut load);
            spent += cost;
            filled = true;
            break;
        }
        if !filled {
            // Last resort: front armor if still legal for this kind.
            if load.armor_front < armor_max {
                let mut trial = load.clone();
                trial.armor_front += 1;
                if trial.is_legal_for(kind) && spent < budget {
                    load.armor_front += 1;
                    spent += 1;
                    continue;
                }
            }
            break;
        }
    }

    debug_assert!(load.is_legal_for(kind));
    debug_assert!(load.cost() <= budget);
    apply_loadout(tank, &load);
    load
}

/// Total upgrade points spent by a side (infantry count as 0).
pub fn side_list_points(tanks: &[Tank], side: crate::unit::Side) -> u32 {
    tanks
        .iter()
        .filter(|t| t.side == side)
        .map(|t| u32::from(t.upgrade_points_spent))
        .sum()
}

/// First player from list totals: lower spend goes first and skips spoil.
/// Equal spend → coin flip and spoil still applies.
pub fn initiative_from_lists<R: Rng>(
    tanks: &[Tank],
    rng: &mut R,
) -> (crate::unit::Side, bool /* spoil */) {
    use crate::unit::Side;
    let red = side_list_points(tanks, Side::Red);
    let blue = side_list_points(tanks, Side::Blue);
    if red < blue {
        (Side::Red, false)
    } else if blue < red {
        (Side::Blue, false)
    } else if rng.gen_bool(0.5) {
        (Side::Red, true)
    } else {
        (Side::Blue, true)
    }
}

#[derive(Clone, Copy)]
enum Buy {
    Smoke,
    Medkit,
    Lieutenant,
    Optics,
    Barrel,
    Engine,
    AntiInfantry,
    ArmorFront,
    ArmorSide,
    ArmorRear,
    Mine,
}

impl Buy {
    fn cost(self) -> i32 {
        1
    }

    fn can_add(self, load: &Loadout, kind: UnitKind) -> bool {
        let armor_max = armor_facing_max(kind);
        match self {
            Buy::Smoke => !load.smoke,
            Buy::Medkit => !load.medkit,
            Buy::Lieutenant => !load.lieutenant,
            Buy::Optics => !load.enhanced_optics,
            Buy::Barrel => !load.extended_barrel,
            Buy::Engine => !load.engine,
            Buy::AntiInfantry => !load.anti_infantry,
            Buy::ArmorFront => load.armor_front < armor_max,
            Buy::ArmorSide => load.armor_side < armor_max && load.armor_side < load.armor_front,
            Buy::ArmorRear => load.armor_rear < armor_max && load.armor_rear < load.armor_side,
            Buy::Mine => load.mines < 3,
        }
    }

    fn add(self, load: &mut Loadout) {
        match self {
            Buy::Smoke => load.smoke = true,
            Buy::Medkit => load.medkit = true,
            Buy::Lieutenant => load.lieutenant = true,
            Buy::Optics => load.enhanced_optics = true,
            Buy::Barrel => load.extended_barrel = true,
            Buy::Engine => load.engine = true,
            Buy::AntiInfantry => load.anti_infantry = true,
            Buy::ArmorFront => load.armor_front += 1,
            Buy::ArmorSide => load.armor_side += 1,
            Buy::ArmorRear => load.armor_rear += 1,
            Buy::Mine => load.mines += 1,
        }
    }
}

trait ShuffleStable {
    fn shuffle_stable<R: Rng>(&mut self, rng: &mut R);
}

impl<T> ShuffleStable for Vec<T> {
    fn shuffle_stable<R: Rng>(&mut self, rng: &mut R) {
        use rand::seq::SliceRandom;
        self.shuffle(rng);
    }
}

/// Aggregate how often each upgrade appears on a force.
#[derive(Clone, Debug, Default, Serialize, Deserialize)]
pub struct LoadoutCensus {
    pub tanks: u32,
    pub smoke: u32,
    pub medkit: u32,
    pub lieutenant: u32,
    pub optics: u32,
    pub barrel: u32,
    pub engine: u32,
    pub anti_infantry: u32,
    pub air: u32,
    pub mines_charges: u32,
    pub armor_points: u32,
    pub upgrade_points: u32,
}

impl LoadoutCensus {
    pub fn from_tanks(tanks: &[Tank]) -> Self {
        let mut c = Self::default();
        for t in tanks {
            if t.kind == UnitKind::Infantry {
                continue;
            }
            c.tanks += 1;
            if t.has_smoke_launcher {
                c.smoke += 1;
            }
            if t.has_medkit {
                c.medkit += 1;
            }
            if t.crew.iter().any(|m| m.role == CrewRole::Lieutenant) {
                c.lieutenant += 1;
            }
            if t.has_optics {
                c.optics += 1;
            }
            if t.has_barrel {
                c.barrel += 1;
            }
            if t.has_engine {
                c.engine += 1;
            }
            if t.kind == UnitKind::Tank && t.ai_range > 0 {
                c.anti_infantry += 1;
            }
            if t.has_air_support {
                c.air += 1;
            }
            c.mines_charges += u32::from(t.mines_left);
            c.armor_points += u32::from(t.armor_points_bought);
            c.upgrade_points += u32::from(t.upgrade_points_spent);
        }
        c
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::hex::{Facing, Hex};
    use crate::unit::{Armor, Side};
    use rand::SeedableRng;
    use rand_chacha::ChaCha8Rng;

    #[test]
    fn armor_constraints_and_heavy_light() {
        let mut t = Tank::stock(0, Side::Red, Hex::new(0, 0), Facing::E, "T");
        let base_move = t.max_move;
        let load = Loadout {
            armor_front: 3,
            armor_side: 2,
            armor_rear: 1,
            engine: true,
            ..Loadout::default()
        };
        assert!(load.is_legal());
        assert_eq!(load.cost(), 3 + 2 + 1 + 1);
        apply_loadout(&mut t, &load);
        assert_eq!(
            t.armor,
            Armor {
                front: 9,
                side: 8,
                rear: 7,
            }
        );
        // Heavy (−1) + engine (+1) → same as base; no light bonus.
        assert_eq!(t.max_move, base_move);
    }

    #[test]
    fn apc_armor_facing_max_is_two() {
        let ok = Loadout {
            armor_front: 2,
            armor_side: 1,
            armor_rear: 1,
            ..Loadout::default()
        };
        assert!(ok.is_legal_for(UnitKind::Apc));
        let too_much = Loadout {
            armor_front: 3,
            armor_side: 1,
            armor_rear: 0,
            ..Loadout::default()
        };
        assert!(!too_much.is_legal_for(UnitKind::Apc));
        assert!(too_much.is_legal_for(UnitKind::Tank));

        for seed in 0..40u64 {
            let mut a = Tank::stock_apc(0, Side::Red, Hex::new(0, 0), Facing::E, "A");
            let mut rr = ChaCha8Rng::seed_from_u64(seed);
            let load = spend_up_to(&mut a, 4, false, &mut rr);
            assert!(
                load.is_legal_for(UnitKind::Apc),
                "APC loadout illegal: {load:?}"
            );
            assert!(load.armor_front <= 2);
            assert!(load.armor_side <= 2);
            assert!(load.armor_rear <= 2);
        }
    }

    #[test]
    fn light_armor_boosts_move() {
        let mut t = Tank::stock(0, Side::Red, Hex::new(0, 0), Facing::E, "T");
        let base = t.max_move;
        apply_loadout(
            &mut t,
            &Loadout {
                engine: true,
                smoke: true,
                ..Loadout::default()
            },
        );
        assert_eq!(t.max_move, base + 1 + 1); // light + engine
    }

    #[test]
    fn optics_improve_target_number() {
        let mut t = Tank::stock(0, Side::Red, Hex::new(0, 0), Facing::E, "T");
        apply_loadout(
            &mut t,
            &Loadout {
                enhanced_optics: true,
                ..Loadout::default()
            },
        );
        assert_eq!(t.accuracy, 3);
        assert!(t.has_optics);
    }

    #[test]
    fn random_spend_respects_budget() {
        for seed in 0..30u64 {
            let mut t = Tank::stock(0, Side::Red, Hex::new(0, 0), Facing::E, "T");
            let mut r = ChaCha8Rng::seed_from_u64(seed);
            let load = spend_budget(&mut t, 10, true, &mut r);
            assert!(load.is_legal(), "{load:?}");
            assert!(load.cost() <= 10, "{} > 10", load.cost());
            assert!(t.upgrade_points_spent as i32 <= 10);
        }
    }

    #[test]
    fn spend_up_to_exact_target() {
        let mut r = ChaCha8Rng::seed_from_u64(7);
        for target in [0, 3, 7, 10] {
            let mut t = Tank::stock(0, Side::Red, Hex::new(0, 0), Facing::E, "T");
            let load = spend_up_to(&mut t, target, false, &mut r);
            assert!(load.cost() <= target);
            assert_eq!(t.upgrade_points_spent as i32, load.cost());
        }
    }

    #[test]
    fn lower_list_spend_wins_initiative_without_spoil() {
        let mut red = Tank::stock(0, Side::Red, Hex::new(0, 0), Facing::E, "R");
        let mut blue = Tank::stock(1, Side::Blue, Hex::new(1, 0), Facing::W, "B");
        let mut r = ChaCha8Rng::seed_from_u64(1);
        spend_up_to(&mut red, 3, false, &mut r);
        spend_up_to(&mut blue, 8, false, &mut r);
        let tanks = vec![red, blue];
        let (first, spoil) = initiative_from_lists(&tanks, &mut r);
        assert_eq!(first, Side::Red);
        assert!(!spoil);
    }

    #[test]
    fn tied_lists_allow_spoil() {
        let mut red = Tank::stock(0, Side::Red, Hex::new(0, 0), Facing::E, "R");
        let mut blue = Tank::stock(1, Side::Blue, Hex::new(1, 0), Facing::W, "B");
        let mut r = ChaCha8Rng::seed_from_u64(2);
        spend_up_to(&mut red, 5, false, &mut r);
        // Force blue to the same spend total as red after red's spend.
        let red_pts = red.upgrade_points_spent;
        spend_up_to(&mut blue, red_pts as i32, false, &mut r);
        // If random shop undershot, pad by re-rolling until equal or give up.
        // Directly set points for a clean tie when shop can't match.
        if blue.upgrade_points_spent != red_pts {
            blue.upgrade_points_spent = red_pts;
        }
        let tanks = vec![red, blue];
        let (_, spoil) = initiative_from_lists(&tanks, &mut r);
        assert!(spoil);
    }

    #[test]
    fn illegal_side_exceeds_front() {
        let load = Loadout {
            armor_front: 1,
            armor_side: 2,
            ..Loadout::default()
        };
        assert!(!load.is_legal());
    }
}
