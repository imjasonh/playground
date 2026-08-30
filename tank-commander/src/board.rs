//! Board terrain and occupancy.

use crate::hex::Hex;
use serde::{Deserialize, Serialize};
use std::collections::{HashMap, HashSet};

#[derive(Clone, Copy, Debug, Eq, PartialEq, Serialize, Deserialize)]
pub enum Terrain {
    Open,
    Mud,
    Rubble,
    Forest,
    Building,
}

impl Terrain {
    pub fn blocks_los(self) -> bool {
        matches!(self, Terrain::Building)
    }

    pub fn move_cost_to_leave(self) -> i32 {
        match self {
            Terrain::Mud | Terrain::Rubble => 2,
            _ => 1,
        }
    }

    pub fn impassable(self) -> bool {
        matches!(self, Terrain::Building)
    }
}

#[derive(Clone, Debug, Serialize, Deserialize)]
pub struct Board {
    pub min_q: i32,
    pub max_q: i32,
    pub min_r: i32,
    pub max_r: i32,
    pub terrain: HashMap<(i32, i32), Terrain>,
    pub smoke: HashSet<(i32, i32)>,
}

impl Board {
    pub fn rect(width: i32, height: i32) -> Self {
        Self {
            min_q: 0,
            max_q: width - 1,
            min_r: 0,
            max_r: height - 1,
            terrain: HashMap::new(),
            smoke: HashSet::new(),
        }
    }

    pub fn contains(&self, hex: Hex) -> bool {
        hex.q >= self.min_q && hex.q <= self.max_q && hex.r >= self.min_r && hex.r <= self.max_r
    }

    pub fn terrain_at(&self, hex: Hex) -> Terrain {
        self.terrain
            .get(&(hex.q, hex.r))
            .copied()
            .unwrap_or(Terrain::Open)
    }

    pub fn set_terrain(&mut self, hex: Hex, terrain: Terrain) {
        self.terrain.insert((hex.q, hex.r), terrain);
    }

    pub fn add_smoke(&mut self, hex: Hex) {
        self.smoke.insert((hex.q, hex.r));
    }

    pub fn has_smoke(&self, hex: Hex) -> bool {
        self.smoke.contains(&(hex.q, hex.r))
    }

    /// Line of sight is blocked by buildings, smoke, or occupied hexes on the
    /// line between endpoints (endpoints themselves are ignored).
    pub fn has_los(&self, from: Hex, to: Hex, occupied: &[Hex]) -> bool {
        for h in from.line_through(to) {
            if self.terrain_at(h).blocks_los() {
                return false;
            }
            if self.has_smoke(h) {
                return false;
            }
            if occupied.contains(&h) {
                return false;
            }
        }
        true
    }

    /// Accuracy modifier from terrain: forest cover for the target.
    pub fn accuracy_penalty_vs(&self, target: Hex) -> i32 {
        if self.terrain_at(target) == Terrain::Forest {
            return 1;
        }
        // Behind forest: any forest neighbor between shooter and target is
        // handled as "in forest" for v1 simplicity — only in-forest counts.
        0
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn building_blocks_los() {
        let mut b = Board::rect(8, 8);
        b.set_terrain(Hex::new(2, 0), Terrain::Building);
        assert!(!b.has_los(Hex::new(0, 0), Hex::new(4, 0), &[]));
        assert!(b.has_los(Hex::new(0, 0), Hex::new(1, 0), &[]));
    }
}
