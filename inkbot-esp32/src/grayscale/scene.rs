//! Procedural demo scene for tuning the drive mode on real hardware: a dark
//! disc with a radial gradient that orbits the panel, over a white field
//! with a fixed 8-step gray ramp along the bottom.
//!
//! This is a synthetic test pattern, not a video decoder. The moving disc
//! shows ghosting and how far behind a moving edge the pixels settle; the
//! ramp shows how many distinct grays the drive steps produce.

use super::{LOGICAL_HEIGHT, LOGICAL_WIDTH};

const RAMP_STEPS: usize = 8;

/// The scene at refresh `tick`, as a luma function of logical `(x, y)`
/// (`0` = black, `255` = white).
pub fn demo_scene(tick: u32) -> impl Fn(usize, usize) -> u8 {
    let w = LOGICAL_WIDTH as i32;
    let ramp_top = LOGICAL_HEIGHT * 7 / 8;
    let h = ramp_top as i32;
    let radius = (w.min(h) / 5).max(4);
    let t = tick as f32 * 0.05;
    let cx = radius + ((w - 2 * radius) as f32 * (0.5 + 0.5 * t.sin())) as i32;
    let cy = radius + ((h - 2 * radius) as f32 * (0.5 + 0.5 * (t * 1.7).cos())) as i32;
    let r_sq = radius * radius;

    move |x, y| {
        if y >= ramp_top {
            let step = x * RAMP_STEPS / LOGICAL_WIDTH;
            return (step * 255 / (RAMP_STEPS - 1)) as u8;
        }
        let (dx, dy) = (x as i32 - cx, y as i32 - cy);
        let d_sq = dx * dx + dy * dy;
        if d_sq >= r_sq {
            255
        } else {
            (d_sq * 255 / r_sq) as u8
        }
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    fn frame(tick: u32) -> Vec<u8> {
        let scene = demo_scene(tick);
        (0..LOGICAL_HEIGHT)
            .flat_map(|y| (0..LOGICAL_WIDTH).map(move |x| (x, y)))
            .map(|(x, y)| scene(x, y))
            .collect()
    }

    #[test]
    fn scene_spans_black_to_white() {
        let f = frame(0);
        assert_eq!(f.iter().min(), Some(&0));
        assert_eq!(f.iter().max(), Some(&255));
    }

    #[test]
    fn ramp_has_eight_steps() {
        let scene = demo_scene(0);
        let y = LOGICAL_HEIGHT - 1;
        let mut steps: Vec<u8> = (0..LOGICAL_WIDTH).map(|x| scene(x, y)).collect();
        steps.dedup();
        assert_eq!(steps.len(), RAMP_STEPS);
    }

    #[test]
    fn disc_moves_between_ticks() {
        assert_ne!(frame(0), frame(10));
    }

    #[test]
    fn scene_is_deterministic() {
        assert_eq!(frame(7), frame(7));
    }
}
