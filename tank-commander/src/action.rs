//! Player actions for a tank activation.

use crate::hex::Facing;
use crate::unit::RoundKind;
use serde::{Deserialize, Serialize};

#[derive(Clone, Copy, Debug, Eq, PartialEq, Serialize, Deserialize)]
pub enum Action {
    /// Move one hex forward (hull facing).
    Move,
    TurnLeft,
    TurnRight,
    /// Rotate turret one step left relative to hull.
    TurretLeft,
    /// Rotate turret one step right relative to hull.
    TurretRight,
    /// Fire the loaded main-gun round at the enemy (only legal when in arc/range/LOS).
    Fire,
    Load(RoundKind),
    ExtinguishFire,
    /// Commander ability: +2 actions this turn (applied when planning).
    AbilityBoomingVoice,
    /// Driver ability: next Move this turn counts as two forward spaces, or
    /// three straight if already planned as such — v1: free extra Move budget.
    AbilityMoveMoveMove,
    /// Gunner ability: hit on 2+ this turn.
    AbilityBringItDown,
    /// Loader ability: Load costs 0 this turn.
    AbilityQuickLoad,
}

impl Action {
    pub fn name(self) -> &'static str {
        match self {
            Action::Move => "Move",
            Action::TurnLeft => "TurnLeft",
            Action::TurnRight => "TurnRight",
            Action::TurretLeft => "TurretLeft",
            Action::TurretRight => "TurretRight",
            Action::Fire => "Fire",
            Action::Load(RoundKind::At) => "LoadAT",
            Action::Load(RoundKind::He) => "LoadHE",
            Action::ExtinguishFire => "Extinguish",
            Action::AbilityBoomingVoice => "Ability:BoomingVoice",
            Action::AbilityMoveMoveMove => "Ability:MoveMoveMove",
            Action::AbilityBringItDown => "Ability:BringItDown",
            Action::AbilityQuickLoad => "Ability:QuickLoad",
        }
    }
}

/// Per-turn modifiers from crew abilities.
#[derive(Clone, Debug, Default)]
pub struct TurnBuffs {
    pub extra_actions: i32,
    pub move_move_move: bool,
    pub hit_on_2: bool,
    pub free_load: bool,
    pub booming_used: bool,
}

impl TurnBuffs {
    pub fn apply_ability(&mut self, action: Action) {
        match action {
            Action::AbilityBoomingVoice => {
                self.extra_actions += 2;
                self.booming_used = true;
            }
            Action::AbilityMoveMoveMove => self.move_move_move = true,
            Action::AbilityBringItDown => self.hit_on_2 = true,
            Action::AbilityQuickLoad => self.free_load = true,
            _ => {}
        }
    }
}

pub fn is_ability(action: Action) -> bool {
    matches!(
        action,
        Action::AbilityBoomingVoice
            | Action::AbilityMoveMoveMove
            | Action::AbilityBringItDown
            | Action::AbilityQuickLoad
    )
}

/// Relative turret offset after a left/right step, wrapped to -2..=3.
pub fn step_turret(offset: i8, left: bool) -> i8 {
    let mut o = if left { offset - 1 } else { offset + 1 };
    while o > 3 {
        o -= 6;
    }
    while o < -2 {
        o += 6;
    }
    o
}

pub fn turn_hull(facing: Facing, left: bool) -> Facing {
    if left {
        facing.turn_left()
    } else {
        facing.turn_right()
    }
}
