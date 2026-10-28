//! Grayscale video on the UC8179 by many short drive steps per second.
//!
//! Instead of one multi-second factory waveform per image, the panel runs a
//! custom waveform ([`lut`]) that drives each pixel for one frame (about
//! 20 ms) per refresh, and [`drive::DrivePlanner`] decides per pixel
//! whether that step goes toward black, toward white, or holds. Gray
//! levels come from how many net steps a pixel has had, the way InkBoy
//! builds grays on its panel. Pixels are planned in 2×2 blocks (400×240
//! logical pixels) to keep the planner's per-pixel state small.
//!
//! The step model only estimates where the ink is. Drift, ghosting, and
//! leftover charge are cleared by a periodic factory full refresh, after
//! the planner drives every pixel back to white.
//!
//! [`scene::BoidsScene`] is the demo scene shown while measuring: a small
//! [`boids`] flock rendered as acute triangles pointing along their
//! direction of travel, chosen to be continuously moving (so every refresh
//! has something to draw) while staying visually calm (no hard edges, no
//! sudden cuts).

pub mod boids;
pub mod drive;
pub mod lut;
pub mod scene;

use crate::panel::{PANEL_HEIGHT, PANEL_WIDTH};

/// Baked into the grayscale demo ELF so `make flash APP=grayscale` can
/// refuse a stale image, the same way `MAZE_FIRMWARE_ID` does for maze.
pub const GRAYSCALE_FIRMWARE_ID: &str = "grayscale-esp32/0.10";

/// Logical pixels are `LOGICAL_BLOCK`×`LOGICAL_BLOCK` physical pixels.
pub const LOGICAL_BLOCK: usize = 2;
pub const LOGICAL_WIDTH: usize = PANEL_WIDTH as usize / LOGICAL_BLOCK;
pub const LOGICAL_HEIGHT: usize = PANEL_HEIGHT as usize / LOGICAL_BLOCK;

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn logical_dims_tile_the_panel_exactly() {
        assert_eq!(LOGICAL_WIDTH * LOGICAL_BLOCK, PANEL_WIDTH as usize);
        assert_eq!(LOGICAL_HEIGHT * LOGICAL_BLOCK, PANEL_HEIGHT as usize);
    }
}
