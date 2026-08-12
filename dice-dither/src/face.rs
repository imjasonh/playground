//! Die faces: how many pips a face shows, and where those pips sit.

/// Highest pip count on a six-sided die.
pub const MAX_PIPS: u8 = 6;

/// Which of the two dice colours a face is cut from.
///
/// A physical dice mosaic is built from white dice with black pips and black
/// dice with white pips; together they span the full tonal range.
#[derive(Clone, Copy, Debug, PartialEq, Eq, PartialOrd, Ord, Hash)]
pub enum DieStyle {
    /// White body, black pips. Renders bright; more pips means darker.
    Light,
    /// Black body, white pips. Renders dark; more pips means brighter.
    Dark,
}

impl DieStyle {
    /// Linear-light grey of the die body. Real dice are neither paper white
    /// nor ink black, and keeping them honest keeps the mosaic's tone honest.
    pub fn body_gray(self) -> f32 {
        match self {
            DieStyle::Light => 0.95,
            DieStyle::Dark => 0.02,
        }
    }

    /// Linear-light grey of the pips.
    pub fn pip_gray(self) -> f32 {
        match self {
            DieStyle::Light => 0.03,
            DieStyle::Dark => 0.90,
        }
    }

    /// Single-letter tag used in the build sheet: `W`hite or `B`lack.
    pub fn tag(self) -> char {
        match self {
            DieStyle::Light => 'W',
            DieStyle::Dark => 'B',
        }
    }
}

/// One die placed in the mosaic.
#[derive(Clone, Copy, Debug, PartialEq, Eq, PartialOrd, Ord, Hash)]
pub struct DieFace {
    pub style: DieStyle,
    pub pips: u8,
    /// Quarter turns clockwise, 0-3. Only 2, 3 and 6 look different when
    /// turned, but every face carries one so rotation can be applied blindly.
    pub quarter_turns: u8,
}

impl DieFace {
    pub fn new(style: DieStyle, pips: u8) -> Self {
        DieFace {
            style,
            pips,
            quarter_turns: 0,
        }
    }

    pub fn rotated(self, quarter_turns: u8) -> Self {
        DieFace {
            quarter_turns: quarter_turns % 4,
            ..self
        }
    }

    /// Pip centres in unit-square coordinates (0,0 top-left to 1,1
    /// bottom-right), already rotated.
    ///
    /// `spread` is the distance from the die centre to the outer pip rows.
    pub fn pip_positions(self, spread: f32) -> Vec<(f32, f32)> {
        let lo = 0.5 - spread;
        let mid = 0.5;
        let hi = 0.5 + spread;
        let positions: Vec<(f32, f32)> = match self.pips {
            0 => vec![],
            1 => vec![(mid, mid)],
            2 => vec![(lo, lo), (hi, hi)],
            3 => vec![(lo, lo), (mid, mid), (hi, hi)],
            4 => vec![(lo, lo), (hi, lo), (lo, hi), (hi, hi)],
            5 => vec![(lo, lo), (hi, lo), (mid, mid), (lo, hi), (hi, hi)],
            _ => vec![(lo, lo), (lo, mid), (lo, hi), (hi, lo), (hi, mid), (hi, hi)],
        };
        positions
            .into_iter()
            .map(|p| rotate(p, self.quarter_turns))
            .collect()
    }
}

/// Rotate a point in the unit square clockwise about its centre.
fn rotate((x, y): (f32, f32), quarter_turns: u8) -> (f32, f32) {
    let (mut x, mut y) = (x - 0.5, y - 0.5);
    for _ in 0..(quarter_turns % 4) {
        (x, y) = (-y, x);
    }
    (x + 0.5, y + 0.5)
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn every_face_has_the_pips_it_advertises() {
        for style in [DieStyle::Light, DieStyle::Dark] {
            for pips in 0..=MAX_PIPS {
                let face = DieFace::new(style, pips);
                assert_eq!(face.pip_positions(0.24).len(), pips as usize);
            }
        }
    }

    #[test]
    fn pips_stay_inside_the_die() {
        for pips in 0..=MAX_PIPS {
            for turns in 0..4 {
                let face = DieFace::new(DieStyle::Light, pips).rotated(turns);
                for (x, y) in face.pip_positions(0.26) {
                    assert!((0.1..=0.9).contains(&x), "pip x {x} out of range");
                    assert!((0.1..=0.9).contains(&y), "pip y {y} out of range");
                }
            }
        }
    }

    #[test]
    fn pip_layouts_are_balanced_about_the_centre() {
        for pips in 1..=MAX_PIPS {
            let face = DieFace::new(DieStyle::Dark, pips);
            let ps = face.pip_positions(0.24);
            let cx: f32 = ps.iter().map(|p| p.0).sum::<f32>() / ps.len() as f32;
            let cy: f32 = ps.iter().map(|p| p.1).sum::<f32>() / ps.len() as f32;
            assert!((cx - 0.5).abs() < 1e-5, "{pips} pips: centroid x {cx}");
            assert!((cy - 0.5).abs() < 1e-5, "{pips} pips: centroid y {cy}");
        }
    }

    #[test]
    fn rotation_permutes_pips_without_moving_the_set_for_symmetric_faces() {
        // 1, 4 and 5 are four-fold symmetric: turning them changes nothing.
        for pips in [1, 4, 5] {
            let base = sorted(DieFace::new(DieStyle::Light, pips).pip_positions(0.24));
            for turns in 1..4 {
                let turned = sorted(
                    DieFace::new(DieStyle::Light, pips)
                        .rotated(turns)
                        .pip_positions(0.24),
                );
                for (a, b) in base.iter().zip(turned.iter()) {
                    assert!((a.0 - b.0).abs() < 1e-5 && (a.1 - b.1).abs() < 1e-5);
                }
            }
        }
        // A 2 turned once lies on the other diagonal; turned twice it is
        // back where it started.
        let two = sorted(DieFace::new(DieStyle::Light, 2).pip_positions(0.24));
        let two_90 = sorted(
            DieFace::new(DieStyle::Light, 2)
                .rotated(1)
                .pip_positions(0.24),
        );
        let two_180 = sorted(
            DieFace::new(DieStyle::Light, 2)
                .rotated(2)
                .pip_positions(0.24),
        );
        assert!((two[0].1 - two_90[0].1).abs() > 0.1, "{two:?} {two_90:?}");
        assert!((two[0].1 - two_180[0].1).abs() < 1e-5);
    }

    #[test]
    fn four_turns_is_no_turn() {
        assert_eq!(DieFace::new(DieStyle::Dark, 6).rotated(4).quarter_turns, 0);
    }

    fn sorted(mut ps: Vec<(f32, f32)>) -> Vec<(f32, f32)> {
        ps.sort_by(|a, b| a.partial_cmp(b).unwrap());
        ps
    }
}
