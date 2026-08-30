//! Units, crew, and loadouts for Tank Commander.

use crate::hex::{Facing, Hex};
use serde::{Deserialize, Serialize};

/// Which side owns a unit.
#[derive(Clone, Copy, Debug, Eq, Hash, PartialEq, Serialize, Deserialize)]
pub enum Side {
    Red,
    Blue,
}

impl Side {
    pub fn other(self) -> Self {
        match self {
            Side::Red => Side::Blue,
            Side::Blue => Side::Red,
        }
    }
}

/// Crew role on a tank.
#[derive(Clone, Copy, Debug, Eq, Hash, PartialEq, Serialize, Deserialize)]
pub enum CrewRole {
    Commander,
    Driver,
    Gunner,
    Loader,
    Lieutenant,
}

impl CrewRole {
    pub fn all_core() -> [CrewRole; 4] {
        [
            CrewRole::Commander,
            CrewRole::Driver,
            CrewRole::Gunner,
            CrewRole::Loader,
        ]
    }
}

#[derive(Clone, Copy, Debug, Eq, PartialEq, Serialize, Deserialize)]
pub enum CrewStatus {
    Healthy,
    Wounded,
    Killed,
}

#[derive(Clone, Debug, Serialize, Deserialize)]
pub struct CrewMember {
    pub role: CrewRole,
    pub status: CrewStatus,
    /// True after the once-per-battle special ability is spent.
    pub ability_used: bool,
    /// True when this member is a Lieutenant covering a killed role.
    pub covering: Option<CrewRole>,
}

impl CrewMember {
    pub fn healthy(role: CrewRole) -> Self {
        Self {
            role,
            status: CrewStatus::Healthy,
            ability_used: false,
            covering: None,
        }
    }
}

/// Round type for the main gun.
#[derive(Clone, Copy, Debug, Eq, PartialEq, Serialize, Deserialize)]
pub enum RoundKind {
    At,
    He,
}

impl RoundKind {
    pub fn strength(self) -> i32 {
        match self {
            RoundKind::At => 6,
            RoundKind::He => 4,
        }
    }
}

/// Armor values for front / side / rear facings.
#[derive(Clone, Copy, Debug, Eq, PartialEq, Serialize, Deserialize)]
pub struct Armor {
    pub front: i32,
    pub side: i32,
    pub rear: i32,
}

impl Armor {
    pub const STOCK_TANK: Armor = Armor {
        front: 6,
        side: 6,
        rear: 6,
    };

    pub fn for_impact(self, impact: ImpactFacing) -> i32 {
        match impact {
            ImpactFacing::Front => self.front,
            ImpactFacing::Side => self.side,
            ImpactFacing::Rear => self.rear,
        }
    }
}

#[derive(Clone, Copy, Debug, Eq, PartialEq, Serialize, Deserialize)]
pub enum ImpactFacing {
    Front,
    Side,
    Rear,
}

/// Stock battle tank for Skirmish (no upgrades yet).
#[derive(Clone, Debug, Serialize, Deserialize)]
pub struct Tank {
    pub id: u8,
    pub side: Side,
    pub name: String,
    pub pos: Hex,
    pub hull_facing: Facing,
    /// Turret offset relative to hull, in 60° steps (-2..=3 typically).
    pub turret_offset: i8,
    pub armor: Armor,
    pub accuracy: i32,
    pub hull_points: i32,
    pub max_hull_points: i32,
    pub actions_per_turn: i32,
    pub max_move: i32,
    pub gun_range: i32,
    pub loaded: Option<RoundKind>,
    pub has_he: bool,
    pub crew: Vec<CrewMember>,
    pub on_fire: bool,
    pub disabled: bool,
    pub destroyed: bool,
    /// Medkit not yet implemented in v1; reserved for later loadouts.
    pub moves_this_turn: i32,
}

impl Tank {
    pub fn stock(
        id: u8,
        side: Side,
        pos: Hex,
        hull_facing: Facing,
        name: impl Into<String>,
    ) -> Self {
        Self {
            id,
            side,
            name: name.into(),
            pos,
            hull_facing,
            turret_offset: 0,
            armor: Armor::STOCK_TANK,
            accuracy: 4,
            hull_points: 4,
            max_hull_points: 4,
            actions_per_turn: 5,
            max_move: 3,
            gun_range: 5,
            loaded: Some(RoundKind::At),
            has_he: true, // stock Skirmish: HE is always available to load
            crew: CrewRole::all_core()
                .into_iter()
                .map(CrewMember::healthy)
                .collect(),
            on_fire: false,
            disabled: false,
            destroyed: false,
            moves_this_turn: 0,
        }
    }

    pub fn turret_facing(&self) -> Facing {
        self.hull_facing.with_turret_offset(self.turret_offset)
    }

    pub fn is_operational(&self) -> bool {
        !self.disabled && !self.destroyed && self.hull_points > 0
    }

    pub fn crew_status(&self, role: CrewRole) -> CrewStatus {
        if let Some(c) = self.crew.iter().find(|c| c.role == role) {
            return c.status;
        }
        // Lieutenant covering a role acts as wounded for that role.
        if let Some(lt) = self
            .crew
            .iter()
            .find(|c| c.role == CrewRole::Lieutenant && c.covering == Some(role))
        {
            return match lt.status {
                CrewStatus::Killed => CrewStatus::Killed,
                _ => CrewStatus::Wounded,
            };
        }
        CrewStatus::Killed
    }

    pub fn effective_actions(&self) -> i32 {
        let mut actions = self.actions_per_turn;
        match self.crew_status(CrewRole::Commander) {
            CrewStatus::Wounded => actions -= 1,
            CrewStatus::Killed => actions -= 2,
            CrewStatus::Healthy => {}
        }
        actions.max(0)
    }

    pub fn effective_accuracy(&self) -> i32 {
        let mut acc = self.accuracy;
        if self.crew_status(CrewRole::Gunner) == CrewStatus::Wounded {
            acc += 1; // harder to hit: need higher roll
        }
        acc
    }

    pub fn can_fire(&self) -> bool {
        self.crew_status(CrewRole::Gunner) != CrewStatus::Killed && self.loaded.is_some()
    }

    pub fn can_load(&self) -> bool {
        self.crew_status(CrewRole::Loader) != CrewStatus::Killed && self.loaded.is_none()
    }

    pub fn load_action_cost(&self) -> i32 {
        match self.crew_status(CrewRole::Loader) {
            CrewStatus::Wounded => 2,
            _ => 1,
        }
    }

    pub fn effective_max_move(&self) -> i32 {
        let mut m = self.max_move;
        if self.crew_status(CrewRole::Driver) == CrewStatus::Wounded {
            m -= 1;
        }
        m.max(0)
    }

    pub fn can_move_or_turn(&self) -> bool {
        self.crew_status(CrewRole::Driver) != CrewStatus::Killed
    }

    pub fn living_crew_indices(&self) -> Vec<usize> {
        self.crew
            .iter()
            .enumerate()
            .filter(|(_, c)| c.status != CrewStatus::Killed)
            .map(|(i, _)| i)
            .collect()
    }

    /// Which armor facing is struck when shot from `from` into this tank.
    pub fn impact_facing(&self, from: Hex) -> ImpactFacing {
        let Some(dir_to_shooter) = self.pos.facing_toward(from) else {
            return ImpactFacing::Front;
        };
        let hull = self.hull_facing.index() as i32;
        let to_shooter = dir_to_shooter.index() as i32;
        // Relative bearing of the attacker from the hull's nose.
        let rel = (to_shooter - hull + 6) % 6;
        match rel {
            0 => ImpactFacing::Front,
            3 => ImpactFacing::Rear,
            _ => ImpactFacing::Side,
        }
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn wounded_commander_reduces_actions() {
        let mut t = Tank::stock(0, Side::Red, Hex::new(0, 0), Facing::E, "T");
        t.crew[0].status = CrewStatus::Wounded;
        assert_eq!(t.effective_actions(), 4);
        t.crew[0].status = CrewStatus::Killed;
        assert_eq!(t.effective_actions(), 3);
    }

    #[test]
    fn front_impact_when_shot_from_ahead() {
        // Tank faces east; shooter west of it → rear armor.
        let t = Tank::stock(0, Side::Red, Hex::new(3, 0), Facing::E, "T");
        assert_eq!(t.impact_facing(Hex::new(0, 0)), ImpactFacing::Rear);
        // Shooter east of tank (ahead of its nose) → front armor.
        let t2 = Tank::stock(0, Side::Red, Hex::new(0, 0), Facing::E, "T");
        assert_eq!(t2.impact_facing(Hex::new(3, 0)), ImpactFacing::Front);
    }

    #[test]
    fn stock_tank_can_load_he() {
        let t = Tank::stock(0, Side::Red, Hex::new(0, 0), Facing::E, "T");
        assert!(t.has_he);
    }
}
