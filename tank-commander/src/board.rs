//! Board terrain and occupancy.
//!
//! Boards are **odd-q offset rectangles** (flat-top / point-sided): `width`
//! columns by `height` rows. That matches a tabletop hex mat. Internally hexes
//! stay axial for distance / facing math — see [`crate::hex::Hex::offset`].

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
    /// Offset columns (odd-q).
    pub width: i32,
    /// Offset rows.
    pub height: i32,
    /// Terrain keyed by axial `(q, r)`.
    pub terrain: HashMap<(i32, i32), Terrain>,
    pub smoke: HashSet<(i32, i32)>,
    pub mines: HashSet<(i32, i32)>,
}

impl Board {
    pub fn rect(width: i32, height: i32) -> Self {
        Self {
            width,
            height,
            terrain: HashMap::new(),
            smoke: HashSet::new(),
            mines: HashSet::new(),
        }
    }

    pub fn contains(&self, hex: Hex) -> bool {
        let (col, row) = hex.to_offset();
        col >= 0 && col < self.width && row >= 0 && row < self.height
    }

    /// Every hex on the rectangular mat, row-major in offset space.
    pub fn hexes(&self) -> impl Iterator<Item = Hex> + '_ {
        (0..self.height).flat_map(|row| (0..self.width).map(move |col| Hex::offset(col, row)))
    }

    pub fn center(&self) -> Hex {
        Hex::offset(self.width / 2, self.height / 2)
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

    pub fn add_mine(&mut self, hex: Hex) {
        self.mines.insert((hex.q, hex.r));
    }

    pub fn take_mine(&mut self, hex: Hex) -> bool {
        self.mines.remove(&(hex.q, hex.r))
    }

    pub fn has_mine(&self, hex: Hex) -> bool {
        self.mines.contains(&(hex.q, hex.r))
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

    /// Accuracy modifier from terrain: −1 when the target is **in** a forest
    /// hex or **behind** one (any intervening forest on the line of fire).
    /// Matches upstream: "in or behind a forest space."
    pub fn accuracy_penalty_vs(&self, from: Hex, target: Hex) -> i32 {
        if self.terrain_at(target) == Terrain::Forest {
            return 1;
        }
        for h in from.line_through(target) {
            if self.terrain_at(h) == Terrain::Forest {
                return 1;
            }
        }
        0
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn building_blocks_los() {
        let mut b = Board::rect(8, 8);
        b.set_terrain(Hex::offset(2, 0), Terrain::Building);
        assert!(!b.has_los(Hex::offset(0, 0), Hex::offset(4, 0), &[]));
        assert!(b.has_los(Hex::offset(0, 0), Hex::offset(1, 0), &[]));
    }

    #[test]
    fn forest_in_or_behind_gives_accuracy_penalty() {
        let mut b = Board::rect(8, 8);
        let shooter = Hex::offset(0, 0);
        let behind = Hex::offset(4, 0);
        let in_forest = Hex::offset(2, 0);
        // Open shot: no penalty.
        assert_eq!(b.accuracy_penalty_vs(shooter, behind), 0);
        // Target in forest.
        b.set_terrain(in_forest, Terrain::Forest);
        assert_eq!(b.accuracy_penalty_vs(shooter, in_forest), 1);
        // Target behind intervening forest (LOS still open — forest does not block).
        assert!(b.has_los(shooter, behind, &[]));
        assert_eq!(b.accuracy_penalty_vs(shooter, behind), 1);
        // Adjacent: no intervening hexes, so "behind" does not apply.
        assert_eq!(b.accuracy_penalty_vs(shooter, Hex::offset(1, 0)), 0);
    }

    #[test]
    fn rect_contains_offset_cells_not_axial_parallelogram() {
        let b = Board::rect(5, 3);
        assert_eq!(b.hexes().count(), 15);
        // Offset (4,1) is on the east edge of a 5-wide mat.
        assert!(b.contains(Hex::offset(4, 1)));
        // Same axial numbers as a former parallelogram corner may fall off.
        let axial_style = Hex::new(4, 1);
        let (c, r) = axial_style.to_offset();
        // Documented: contains uses offset bounds, not raw axial q/r.
        assert_eq!(
            b.contains(axial_style),
            (0..5).contains(&c) && (0..3).contains(&r)
        );
    }
}
