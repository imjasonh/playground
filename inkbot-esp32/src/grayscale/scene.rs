//! The demo scene the grayscale drive mode shows: a small flock of boids
//! ([`super::boids`]) rendered as acute triangles pointing along their
//! direction of travel, on a white field.
//!
//! [`BoidsScene`] owns the flock and a logical-sized luma buffer so the
//! drive loop can call [`BoidsScene::step`] once per refresh and hand
//! [`BoidsScene::luma`] straight to the planner without reallocating.

use super::boids::{Flock, FlockConfig};
use super::{LOGICAL_HEIGHT, LOGICAL_WIDTH};

pub struct BoidsScene {
    flock: Flock,
    buffer: Vec<u8>,
}

impl BoidsScene {
    pub fn new(seed: u32) -> Self {
        let flock = Flock::new(FlockConfig::default(), seed);
        let mut scene = Self {
            flock,
            buffer: vec![255; LOGICAL_WIDTH * LOGICAL_HEIGHT],
        };
        scene.render();
        scene
    }

    /// Advance the flock one step and re-render the buffer.
    pub fn step(&mut self) {
        self.flock.step();
        self.render();
    }

    /// Luma at logical `(x, y)`, as of the last [`BoidsScene::step`].
    pub fn luma(&self, x: usize, y: usize) -> u8 {
        self.buffer[y * LOGICAL_WIDTH + x]
    }

    fn render(&mut self) {
        self.flock
            .render_luma(&mut self.buffer, LOGICAL_WIDTH, LOGICAL_HEIGHT);
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn buffer_is_logical_sized() {
        let scene = BoidsScene::new(0);
        for y in 0..LOGICAL_HEIGHT {
            for x in 0..LOGICAL_WIDTH {
                let _ = scene.luma(x, y); // panics (index out of bounds) if undersized
            }
        }
    }

    #[test]
    fn stepping_changes_the_scene() {
        let mut scene = BoidsScene::new(1);
        let before: Vec<u8> = (0..LOGICAL_HEIGHT * LOGICAL_WIDTH)
            .map(|i| scene.luma(i % LOGICAL_WIDTH, i / LOGICAL_WIDTH))
            .collect();
        for _ in 0..10 {
            scene.step();
        }
        let after: Vec<u8> = (0..LOGICAL_HEIGHT * LOGICAL_WIDTH)
            .map(|i| scene.luma(i % LOGICAL_WIDTH, i / LOGICAL_WIDTH))
            .collect();
        assert_ne!(before, after, "the flock should have moved");
    }

    #[test]
    fn same_seed_renders_the_same_scene() {
        let mut a = BoidsScene::new(99);
        let mut b = BoidsScene::new(99);
        for _ in 0..25 {
            a.step();
            b.step();
        }
        for y in 0..LOGICAL_HEIGHT {
            for x in 0..LOGICAL_WIDTH {
                assert_eq!(a.luma(x, y), b.luma(x, y));
            }
        }
    }
}
