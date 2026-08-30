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

    /// Side ≤ front, rear ≤ side; each facing 0..=3; mines 0..=3.
    pub fn is_legal(&self) -> bool {
        self.armor_front <= 3
            && self.armor_side <= 3
            && self.armor_rear <= 3
            && self.armor_side <= self.armor_front
            && self.armor_rear <= self.armor_side
            && self.mines <= 3
    }
}

/// Apply a legal loadout to a stock unit. Panics if illegal (callers validate).
pub fn apply_loadout(tank: &mut Tank, load: &Loadout) {
    debug_assert!(load.is_legal());
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

/// Weighted random spend within `budget`. `allow_mines` unlocks anti-tank mines.
pub fn spend_budget<R: Rng>(
    tank: &mut Tank,
    budget: i32,
    allow_mines: bool,
    rng: &mut R,
) -> Loadout {
    let mut load = Loadout::default();
    // Stock HE house rule: tanks already have HE; don't charge unless missing.
    if tank.kind == UnitKind::Tank && !tank.has_he {
        load.he = true;
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
        UnitKind::Infantry => return load,
    }
    menu.shuffle_stable(rng);
    // Drop some options so lists trade off instead of always buying everything.
    menu.retain(|_| rng.gen_bool(0.55));

    let mut spent = load.cost();
    for buy in menu {
        let cost = buy.cost();
        if spent + cost > budget {
            continue;
        }
        if !buy.can_add(&load) {
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
            if spent >= budget || !buy.can_add(&load) {
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
            // Last resort: front armor if still legal.
            if load.armor_front < 3 && load.is_legal() {
                let mut trial = load.clone();
                trial.armor_front += 1;
                if trial.is_legal() && spent < budget {
                    load.armor_front += 1;
                    spent += 1;
                    continue;
                }
            }
            break;
        }
    }

    debug_assert!(load.is_legal());
    debug_assert!(load.cost() <= budget);
    apply_loadout(tank, &load);
    load
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

    fn can_add(self, load: &Loadout) -> bool {
        match self {
            Buy::Smoke => !load.smoke,
            Buy::Medkit => !load.medkit,
            Buy::Lieutenant => !load.lieutenant,
            Buy::Optics => !load.enhanced_optics,
            Buy::Barrel => !load.extended_barrel,
            Buy::Engine => !load.engine,
            Buy::AntiInfantry => !load.anti_infantry,
            Buy::ArmorFront => load.armor_front < 3,
            Buy::ArmorSide => load.armor_side < 3 && load.armor_side < load.armor_front,
            Buy::ArmorRear => load.armor_rear < 3 && load.armor_rear < load.armor_side,
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
    fn illegal_side_exceeds_front() {
        let load = Loadout {
            armor_front: 1,
            armor_side: 2,
            ..Loadout::default()
        };
        assert!(!load.is_legal());
    }
}
