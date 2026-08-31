//! Hex grid helpers for Tank Commander.
//!
//! Internally each [`Hex`] is axial `(q, r)`. Map layouts are **odd-q**
//! offset rectangles (**flat-top** / point-sided): column × row looks like a
//! normal tabletop mat. Flat faces point east–west, so opposed Red/Blue
//! approaches along columns are distance-symmetric (odd-r pointy-top was
//! chiral on that axis). Use [`Hex::offset`] for board positions.
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

    /// Odd-q (flat-top) offset column/row → axial. Use for board layouts.
    pub const fn offset(col: i32, row: i32) -> Self {
        Self {
            q: col,
            r: row - (col - (col & 1)) / 2,
        }
    }

    /// Axial → odd-q offset `(col, row)`.
    pub const fn to_offset(self) -> (i32, i32) {
        let col = self.q;
        let row = self.r + (self.q - (self.q & 1)) / 2;
        (col, row)
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
        // Flat-top cube-to-pixel: x = 3/2·q, y = √3/2·q + √3·r (+y down).
        // Axial neighbor deltas stay the cube-adjacent set (same as pointy-top);
        // only the pixel projection changes with orientation.
        let px = 1.5 * dq;
        let py = (3f64.sqrt() / 2.0) * dq + 3f64.sqrt() * dr;
        let angle = py.atan2(px); // -pi..pi
        let deg = angle.to_degrees();
        let norm = ((deg % 360.0) + 360.0) % 360.0;
        // With flat-top pixels, cube neighbors land at 30°, 90°, 150°, …
        // (E=(1,0) at 30°, SE=(0,1) at 90°, …). Offset by −30° then bin.
        let idx = (((norm - 30.0) + 360.0) % 360.0 / 60.0).floor() as i32 % 6;
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

/// One of six hex facings (cube-adjacent axial deltas).
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

    /// Cube-adjacent axial deltas (orientation-independent).
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

    /// Facing 180° opposite (three steps left or right).
    pub fn opposite(self) -> Self {
        Facing::from_index(self.index() + 3)
    }

    /// Turret offset relative to hull, in −2..=3 steps.
    pub fn relative_offset(self, absolute: Facing) -> i8 {
        let mut o = absolute.index() as i8 - self.index() as i8;
        while o > 3 {
            o -= 6;
        }
        while o < -2 {
            o += 6;
        }
        o
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
        for f in [
            Facing::E,
            Facing::NE,
            Facing::NW,
            Facing::W,
            Facing::SW,
            Facing::SE,
        ] {
            assert_eq!(a.facing_toward(a.neighbor(f)), Some(f));
        }
    }

    #[test]
    fn turn_left_from_east_is_northeast() {
        assert_eq!(Facing::E.turn_left(), Facing::NE);
        assert_eq!(Facing::E.turn_right(), Facing::SE);
        assert_eq!(Facing::W.turn_left(), Facing::SW);
        assert_eq!(Facing::W.turn_right(), Facing::NW);
        assert_eq!(Facing::E.opposite(), Facing::W);
        assert_eq!(Facing::NE.opposite(), Facing::SW);
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
        // In a wide enough odd-q rectangle, interior offset (3,3) has six
        // neighbors that also convert to nearby offset cells.
        let h = Hex::offset(3, 3);
        let offs: Vec<_> = h.neighbors().into_iter().map(|n| n.to_offset()).collect();
        assert_eq!(offs.len(), 6);
        for (c, r) in offs {
            assert!((2..=4).contains(&c) || (2..=4).contains(&r));
        }
    }

    #[test]
    fn ew_race_distances_are_symmetric() {
        // The reason we switched to flat-top: Red/Blue forward edges match.
        let w = 18i32;
        let depth = 3i32;
        let flag_row = 6i32;
        let rflag = Hex::offset(0, flag_row);
        let bflag = Hex::offset(w - 1, flag_row);
        for row in 0..12 {
            let red = Hex::offset(depth - 1, row).distance(bflag);
            let blue = Hex::offset(w - depth, row).distance(rflag);
            assert_eq!(red, blue, "row {row}: red={red} blue={blue}");
        }
    }
}
