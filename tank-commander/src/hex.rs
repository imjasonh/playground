//! Hex grid helpers for Tank Commander.
//!
//! Internally each [`Hex`] is axial `(q, r)`. Map layouts are **odd-r**
//! offset rectangles (pointy-top): column × row looks like a normal tabletop
//! mat, not an axial parallelogram. Use [`Hex::offset`] for board positions.
//!
//! The six facings are numbered 0..=5 counterclockwise starting at east (`+q`).

use serde::{Deserialize, Serialize};
use std::fmt;

/// One hex on the board (stored as axial).
#[derive(Clone, Copy, Debug, Eq, Hash, PartialEq, Serialize, Deserialize)]
pub struct Hex {
    pub q: i32,
    pub r: i32,
}

impl Hex {
    /// Axial constructor (neighbor math, tests). Prefer [`Hex::offset`] for maps.
    pub const fn new(q: i32, r: i32) -> Self {
        Self { q, r }
    }

    /// Odd-r (pointy-top) offset column/row → axial. Use for board layouts.
    pub const fn offset(col: i32, row: i32) -> Self {
        Self {
            q: col - (row - (row & 1)) / 2,
            r: row,
        }
    }

    /// Axial → odd-r offset `(col, row)`.
    pub const fn to_offset(self) -> (i32, i32) {
        let col = self.q + (self.r - (self.r & 1)) / 2;
        (col, self.r)
    }

    pub fn neighbors(self) -> [Hex; 6] {
        [
            self.neighbor(Facing::E),
            self.neighbor(Facing::NE),
            self.neighbor(Facing::NW),
            self.neighbor(Facing::W),
            self.neighbor(Facing::SW),
            self.neighbor(Facing::SE),
        ]
    }

    pub fn neighbor(self, facing: Facing) -> Hex {
        let (dq, dr) = facing.delta();
        Hex::new(self.q + dq, self.r + dr)
    }

    pub fn distance(self, other: Hex) -> i32 {
        let dq = self.q - other.q;
        let dr = self.r - other.r;
        let ds = (-self.q - self.r) - (-other.q - other.r);
        (dq.abs() + dr.abs() + ds.abs()) / 2
    }

    /// Hexes on the line from `self` to `other`, excluding both endpoints.
    pub fn line_through(self, other: Hex) -> Vec<Hex> {
        let n = self.distance(other);
        if n <= 1 {
            return Vec::new();
        }
        let mut out = Vec::with_capacity((n - 1) as usize);
        for i in 1..n {
            let t = f64::from(i) / f64::from(n);
            let q = lerp(f64::from(self.q), f64::from(other.q), t);
            let r = lerp(f64::from(self.r), f64::from(other.r), t);
            out.push(cube_round(q, r));
        }
        out
    }

    /// Nearest of the six facings from `self` toward `other`.
    ///
    /// Returns `None` when `self == other`.
    pub fn facing_toward(self, other: Hex) -> Option<Facing> {
        if self == other {
            return None;
        }
        let dq = f64::from(other.q - self.q);
        let dr = f64::from(other.r - self.r);
        // Convert axial delta to a continuous angle in cube space.
        // x = q, z = r, y = -q-r. Angle from +q (east).
        let x = dq;
        let z = dr;
        let y = -dq - dr;
        // Pointy-top axial: east is (1,0), angle via atan2 of cartesian.
        // Using cube-to-pixel for pointy-top: x = √3*q + √3/2*r, y = 3/2*r
        let px = 3f64.sqrt() * x + (3f64.sqrt() / 2.0) * z;
        let py = 1.5 * z;
        let _ = y;
        let angle = py.atan2(px); // -pi..pi, 0 = east
                                  // Facings at 0, 60, 120, 180, -120, -60 degrees.
        let deg = angle.to_degrees();
        let norm = ((deg % 360.0) + 360.0) % 360.0;
        // Pointy-top +y-down pixel space: 0°=E, 60°=SE, 120°=SW, 180°=W,
        // 240°=NW, 300°=NE — not the same order as the Facing enum.
        let idx = ((norm + 30.0) / 60.0).floor() as i32 % 6;
        Some(match idx {
            0 => Facing::E,
            1 => Facing::SE,
            2 => Facing::SW,
            3 => Facing::W,
            4 => Facing::NW,
            _ => Facing::NE,
        })
    }
}

impl fmt::Display for Hex {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        let (col, row) = self.to_offset();
        write!(f, "({col},{row})")
    }
}

fn lerp(a: f64, b: f64, t: f64) -> f64 {
    a + (b - a) * t
}

fn cube_round(q: f64, r: f64) -> Hex {
    let s = -q - r;
    let mut rq = q.round();
    let mut rr = r.round();
    let rs = s.round();
    let q_diff = (rq - q).abs();
    let r_diff = (rr - r).abs();
    let s_diff = (rs - s).abs();
    if q_diff > r_diff && q_diff > s_diff {
        rq = -rr - rs;
    } else if r_diff > s_diff {
        rr = -rq - rs;
    }
    Hex::new(rq as i32, rr as i32)
}

/// One of six hex facings.
#[derive(Clone, Copy, Debug, Eq, Hash, PartialEq, Serialize, Deserialize)]
#[repr(u8)]
pub enum Facing {
    E = 0,
    NE = 1,
    NW = 2,
    W = 3,
    SW = 4,
    SE = 5,
}

impl Facing {
    pub fn from_index(i: u8) -> Self {
        match i % 6 {
            0 => Facing::E,
            1 => Facing::NE,
            2 => Facing::NW,
            3 => Facing::W,
            4 => Facing::SW,
            _ => Facing::SE,
        }
    }

    pub fn index(self) -> u8 {
        self as u8
    }

    pub fn delta(self) -> (i32, i32) {
        match self {
            Facing::E => (1, 0),
            Facing::NE => (1, -1),
            Facing::NW => (0, -1),
            Facing::W => (-1, 0),
            Facing::SW => (-1, 1),
            Facing::SE => (0, 1),
        }
    }

    pub fn turn_left(self) -> Self {
        // Enum order is counterclockwise: E → NE → NW → W → SW → SE.
        Facing::from_index((self.index() + 1) % 6)
    }

    pub fn turn_right(self) -> Self {
        Facing::from_index((self.index() + 5) % 6)
    }

    /// Absolute facing after applying a turret offset relative to hull.
    pub fn with_turret_offset(self, offset: i8) -> Self {
        let o = offset.rem_euclid(6);
        Facing::from_index(self.index() + o as u8)
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn distance_neighbors_is_one() {
        let a = Hex::new(0, 0);
        for n in a.neighbors() {
            assert_eq!(a.distance(n), 1);
        }
    }

    #[test]
    fn facing_toward_neighbors() {
        let a = Hex::new(2, 2);
        assert_eq!(a.facing_toward(Hex::new(3, 2)), Some(Facing::E));
        assert_eq!(a.facing_toward(Hex::new(3, 1)), Some(Facing::NE));
        assert_eq!(a.facing_toward(Hex::new(2, 1)), Some(Facing::NW));
        assert_eq!(a.facing_toward(Hex::new(1, 2)), Some(Facing::W));
        assert_eq!(a.facing_toward(Hex::new(1, 3)), Some(Facing::SW));
        assert_eq!(a.facing_toward(Hex::new(2, 3)), Some(Facing::SE));
    }

    #[test]
    fn turn_left_from_east_is_northeast() {
        assert_eq!(Facing::E.turn_left(), Facing::NE);
        assert_eq!(Facing::E.turn_right(), Facing::SE);
        assert_eq!(Facing::W.turn_left(), Facing::SW);
        assert_eq!(Facing::W.turn_right(), Facing::NW);
    }

    #[test]
    fn offset_round_trip() {
        for row in 0..8 {
            for col in 0..10 {
                let h = Hex::offset(col, row);
                assert_eq!(h.to_offset(), (col, row));
            }
        }
    }

    #[test]
    fn offset_neighbors_stay_near_rectangle() {
        // In a wide enough odd-r rectangle, interior offset (3,3) has six
        // neighbors that also convert to nearby offset cells.
        let h = Hex::offset(3, 3);
        let offs: Vec<_> = h.neighbors().into_iter().map(|n| n.to_offset()).collect();
        assert_eq!(offs.len(), 6);
        for (c, r) in offs {
            assert!((2..=4).contains(&c) || (2..=4).contains(&r));
        }
    }
}
