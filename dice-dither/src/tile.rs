//! Drawing one die into a square tile of linear-light grey samples.
//!
//! Tiles are drawn from signed distance fields so the rounded die body and the
//! round pips are anti-aliased, and so a tile's mean grey (which is what the
//! ditherer matches against) is a faithful measure of how bright that die
//! looks from across the room.

use std::collections::HashMap;

use crate::color::linear_to_srgb;
use crate::face::DieFace;

/// How a die is drawn: proportions shared by every tile in a mosaic.
#[derive(Clone, Copy, Debug)]
pub struct TileStyle {
    /// Tile size in pixels; also the spacing of the mosaic grid.
    pub cell_px: u32,
    /// Seam between neighbouring dice, as a fraction of the cell.
    pub gap: f32,
    /// Corner radius of the die body, as a fraction of the cell.
    pub corner: f32,
    /// Pip radius, as a fraction of the cell.
    pub pip_radius: f32,
    /// Distance from the die centre to the outer pip rows, as a fraction of
    /// the cell.
    pub pip_spread: f32,
    /// Linear-light grey showing through the seam between dice.
    pub seam_gray: f32,
}

impl Default for TileStyle {
    fn default() -> Self {
        TileStyle {
            cell_px: 24,
            gap: 0.07,
            corner: 0.18,
            pip_radius: 0.088,
            pip_spread: 0.24,
            seam_gray: 0.06,
        }
    }
}

/// A rendered tile: `cell_px * cell_px` linear-light grey samples, row major.
#[derive(Clone, Debug)]
pub struct Tile {
    pub cell_px: u32,
    pub pixels: Vec<f32>,
}

impl Tile {
    /// Mean grey of the tile in `space`: the tone this die contributes.
    pub fn mean_gray(&self, space: ToneSpace) -> f32 {
        let sum: f32 = match space {
            ToneSpace::Linear => self.pixels.iter().sum(),
            ToneSpace::Display => self.pixels.iter().copied().map(linear_to_srgb).sum(),
        };
        sum / self.pixels.len() as f32
    }
}

/// Which brightness scale tones are compared on.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum ToneSpace {
    /// Physical light. Squint at a real tray of dice and this is the tone you
    /// see, so it is the right choice for a mosaic you intend to build.
    Linear,
    /// Gamma-encoded brightness, the scale monitors and image scalers average
    /// on. Pictures meant to be looked at on a screen match the source better
    /// here, which is why it is the default.
    Display,
}

/// Draws (and remembers) tiles for a given style.
pub struct TileRenderer {
    style: TileStyle,
    cache: HashMap<DieFace, Tile>,
}

impl TileRenderer {
    pub fn new(style: TileStyle) -> Self {
        TileRenderer {
            style,
            cache: HashMap::new(),
        }
    }

    pub fn style(&self) -> TileStyle {
        self.style
    }

    pub fn tile(&mut self, face: DieFace) -> &Tile {
        self.cache
            .entry(face)
            .or_insert_with(|| draw(face, &self.style))
    }

    /// Mean grey of a face, for tone matching.
    pub fn mean_gray(&mut self, face: DieFace, space: ToneSpace) -> f32 {
        self.tile(face).mean_gray(space)
    }
}

fn draw(face: DieFace, style: &TileStyle) -> Tile {
    let n = style.cell_px.max(3);
    let size = n as f32;
    let body_gray = face.style.body_gray();
    let pip_gray = face.style.pip_gray();
    let pips: Vec<(f32, f32)> = face
        .pip_positions(style.pip_spread)
        .into_iter()
        .map(|(x, y)| (x * size, y * size))
        .collect();

    let inset = style.gap * size * 0.5;
    let half = size * 0.5 - inset;
    let radius = (style.corner * size).min(half);
    let pip_r = style.pip_radius * size;

    let mut pixels = Vec::with_capacity((n * n) as usize);
    for py in 0..n {
        for px in 0..n {
            let p = (px as f32 + 0.5, py as f32 + 0.5);
            let body = coverage(rounded_box_sdf(p, (size * 0.5, size * 0.5), half, radius));
            let pip = pips
                .iter()
                .map(|&c| coverage(circle_sdf(p, c, pip_r)))
                .fold(0.0f32, f32::max);
            let die = body_gray * (1.0 - pip) + pip_gray * pip;
            pixels.push(style.seam_gray * (1.0 - body) + die * body);
        }
    }
    Tile { cell_px: n, pixels }
}

/// Signed distance (pixels, negative inside) to a rounded square.
fn rounded_box_sdf(p: (f32, f32), center: (f32, f32), half: f32, radius: f32) -> f32 {
    let qx = (p.0 - center.0).abs() - (half - radius);
    let qy = (p.1 - center.1).abs() - (half - radius);
    let outside = (qx.max(0.0).powi(2) + qy.max(0.0).powi(2)).sqrt();
    outside + qx.max(qy).min(0.0) - radius
}

/// Signed distance (pixels, negative inside) to a circle.
fn circle_sdf(p: (f32, f32), center: (f32, f32), radius: f32) -> f32 {
    ((p.0 - center.0).powi(2) + (p.1 - center.1).powi(2)).sqrt() - radius
}

/// One-pixel-wide anti-aliasing ramp across an edge.
fn coverage(signed_distance: f32) -> f32 {
    (0.5 - signed_distance).clamp(0.0, 1.0)
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::face::{DieFace, DieStyle, MAX_PIPS};

    fn renderer() -> TileRenderer {
        TileRenderer::new(TileStyle::default())
    }

    #[test]
    fn tiles_are_square_and_in_range() {
        let mut r = renderer();
        let tile = r.tile(DieFace::new(DieStyle::Dark, 5));
        assert_eq!(tile.pixels.len(), (tile.cell_px * tile.cell_px) as usize);
        assert!(tile.pixels.iter().all(|v| (0.0..=1.0).contains(v)));
    }

    #[test]
    fn pips_brighten_dark_dice_and_darken_light_dice() {
        let mut r = renderer();
        for space in [ToneSpace::Linear, ToneSpace::Display] {
            for pips in 1..=MAX_PIPS {
                let less = r.mean_gray(DieFace::new(DieStyle::Dark, pips - 1), space);
                let more = r.mean_gray(DieFace::new(DieStyle::Dark, pips), space);
                assert!(more > less, "{space:?} dark {pips}: {more} !> {less}");

                let less = r.mean_gray(DieFace::new(DieStyle::Light, pips - 1), space);
                let more = r.mean_gray(DieFace::new(DieStyle::Light, pips), space);
                assert!(more < less, "{space:?} light {pips}: {more} !< {less}");
            }
        }
    }

    #[test]
    fn every_dark_die_is_darker_than_every_light_die() {
        let mut r = renderer();
        let darkest_light = (0..=MAX_PIPS)
            .map(|p| r.mean_gray(DieFace::new(DieStyle::Light, p), ToneSpace::Linear))
            .fold(f32::INFINITY, f32::min);
        let brightest_dark = (0..=MAX_PIPS)
            .map(|p| r.mean_gray(DieFace::new(DieStyle::Dark, p), ToneSpace::Linear))
            .fold(f32::NEG_INFINITY, f32::max);
        assert!(brightest_dark < darkest_light);
    }

    #[test]
    fn rotation_does_not_change_tone() {
        let mut r = renderer();
        let base = r.mean_gray(DieFace::new(DieStyle::Dark, 6), ToneSpace::Linear);
        for turns in 1..4 {
            let turned = r.mean_gray(
                DieFace::new(DieStyle::Dark, 6).rotated(turns),
                ToneSpace::Linear,
            );
            assert!(
                (turned - base).abs() < 1e-4,
                "turn {turns}: {turned} vs {base}"
            );
        }
    }

    #[test]
    fn rotating_a_six_actually_moves_its_pips() {
        let mut r = renderer();
        let flat = r.tile(DieFace::new(DieStyle::Dark, 6)).pixels.clone();
        let turned = r
            .tile(DieFace::new(DieStyle::Dark, 6).rotated(1))
            .pixels
            .clone();
        let diff: f32 = flat
            .iter()
            .zip(turned.iter())
            .map(|(a, b)| (a - b).abs())
            .sum();
        assert!(diff > 1.0, "a turned six should look different: {diff}");
    }

    #[test]
    fn the_seam_shows_at_the_tile_corner() {
        let style = TileStyle::default();
        let mut r = TileRenderer::new(style);
        let tile = r.tile(DieFace::new(DieStyle::Light, 1));
        assert!((tile.pixels[0] - style.seam_gray).abs() < 1e-4);
    }

    #[test]
    fn tiny_cells_still_render() {
        let mut r = TileRenderer::new(TileStyle {
            cell_px: 1,
            ..TileStyle::default()
        });
        let tile = r.tile(DieFace::new(DieStyle::Dark, 6));
        assert_eq!(tile.cell_px, 3);
    }
}
