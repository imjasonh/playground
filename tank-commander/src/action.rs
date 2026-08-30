//! Player actions for a unit activation.

use crate::hex::{Facing, Hex};
use crate::unit::RoundKind;
use serde::{Deserialize, Serialize};

#[derive(Clone, Copy, Debug, Eq, PartialEq, Serialize, Deserialize)]
pub enum Action {
    /// Move one hex forward (hull facing). Vehicles only.
    Move,
    /// Infantry: step one hex in any facing.
    Step(Facing),
    TurnLeft,
    TurnRight,
    /// Rotate turret one step left relative to hull.
    TurretLeft,
    /// Rotate turret one step right relative to hull.
    TurretRight,
    /// Fire the loaded main-gun round at a target.
    Fire {
        target: u8,
    },
    /// Infantry missile (no load required).
    FireMissile {
        target: u8,
        round: RoundKind,
    },
    /// Anti-infantry weapon (APC / infantry).
    FireAi {
        target: u8,
    },
    Load(RoundKind),
    ExtinguishFire,
    /// Infantry: −1 enemy accuracy until this unit's next activation ends.
    TakeCover,
    /// Mark a hex for an air strike (resolves on later turns).
    CallAirStrike {
        hex: Hex,
    },
    /// Place smoke in a hex within range 2 (smoke launcher upgrade).
    DeploySmoke {
        hex: Hex,
    },
    /// Place an anti-tank mine in an adjacent empty hex (or own hex).
    DeployMine {
        hex: Hex,
    },
    /// Lieutenant covers a killed core role (acts as wounded for that role).
    LieutenantCover {
        role: crate::unit::CrewRole,
    },
    /// Infantry: claim an enemy objective hex this unit occupies.
    Capture,
    /// Infantry: remove an adjacent mine hex from the board.
    DisarmMine {
        hex: Hex,
    },
    /// Infantry: board an adjacent friendly APC (capacity 1).
    Mount {
        vehicle: u8,
    },
    /// Infantry: leave the APC into an adjacent empty hex.
    Dismount {
        hex: Hex,
    },
    /// APC: load an adjacent friendly infantry squad.
    Embark {
        infantry: u8,
    },
    /// APC: unload passenger into an adjacent empty hex (free after a Move).
    DropOff {
        hex: Hex,
    },
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
            Action::Step(_) => "Step",
            Action::TurnLeft => "TurnLeft",
            Action::TurnRight => "TurnRight",
            Action::TurretLeft => "TurretLeft",
            Action::TurretRight => "TurretRight",
            Action::Fire { .. } => "Fire",
            Action::FireMissile {
                round: RoundKind::At,
                ..
            } => "MissileAT",
            Action::FireMissile {
                round: RoundKind::He,
                ..
            } => "MissileHE",
            Action::FireAi { .. } => "FireAI",
            Action::Load(RoundKind::At) => "LoadAT",
            Action::Load(RoundKind::He) => "LoadHE",
            Action::ExtinguishFire => "Extinguish",
            Action::TakeCover => "TakeCover",
            Action::CallAirStrike { .. } => "CallAirStrike",
            Action::DeploySmoke { .. } => "DeploySmoke",
            Action::DeployMine { .. } => "DeployMine",
            Action::LieutenantCover { .. } => "LieutenantCover",
            Action::Capture => "Capture",
            Action::DisarmMine { .. } => "DisarmMine",
            Action::Mount { .. } => "Mount",
            Action::Dismount { .. } => "Dismount",
            Action::Embark { .. } => "Embark",
            Action::DropOff { .. } => "DropOff",
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

pub fn step_turret(offset: i8, left: bool) -> i8 {
    // Left matches Facing::turn_left (+1 on the facing index).
    let mut o = if left { offset + 1 } else { offset - 1 };
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
