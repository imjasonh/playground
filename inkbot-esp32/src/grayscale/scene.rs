//! Procedural demo scene: a moving 4-band circle that exercises every shade
//! and every transition between them, for reading real refresh latency and
//! ghosting off actual hardware.
//!
//! This is a synthetic test pattern, not a video decoder — there is no SD
//! card, no file format, and no codec here. It is meant to replace both:
//! a known, repeatable "video" to watch while tuning, the same role
//! InkBoy's transition test and PaperBoy's moving targets play for their
//! panels.

use super::{Shade, LOGICAL_HEIGHT, LOGICAL_WIDTH};

/// Render logical frame `tick` (each call one step further along the path).
/// Output length is always `LOGICAL_WIDTH * LOGICAL_HEIGHT`.
pub fn render_demo_frame(tick: u32) -> Vec<Shade> {
    let w = LOGICAL_WIDTH as i32;
    let h = LOGICAL_HEIGHT as i32;
    let margin = 40i32.min(w / 4).min(h / 4).max(1);
    let t = tick as f32 * 0.08;

    let span_x = (w - 2 * margin).max(1) as f32;
    let span_y = (h - 2 * margin).max(1) as f32;
    let cx = margin + (span_x * (0.5 + 0.5 * t.sin())) as i32;
    let cy = margin + (span_y * (0.5 + 0.5 * (t * 1.3).cos())) as i32;
    let radius = (w.min(h) / 8).max(4);

    let mut out = vec![Shade::White; LOGICAL_WIDTH * LOGICAL_HEIGHT];
    for y in 0..h {
        for x in 0..w {
            let dx = x - cx;
            let dy = y - cy;
            let dist_sq = dx * dx + dy * dy;
            let shade = if dist_sq <= (radius / 4).pow(2) {
                Shade::Black
            } else if dist_sq <= (radius / 2).pow(2) {
                Shade::Gray2
            } else if dist_sq <= radius.pow(2) {
                Shade::Gray1
            } else {
                Shade::White
            };
            out[(y * w + x) as usize] = shade;
        }
    }
    out
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn frame_is_logical_sized() {
        let frame = render_demo_frame(0);
        assert_eq!(frame.len(), LOGICAL_WIDTH * LOGICAL_HEIGHT);
    }

    #[test]
    fn frame_uses_every_shade() {
        let frame = render_demo_frame(0);
        for shade in [Shade::White, Shade::Gray1, Shade::Gray2, Shade::Black] {
            assert!(
                frame.contains(&shade),
                "demo frame is missing {shade:?}; widen the test pattern"
            );
        }
    }

    #[test]
    fn frame_changes_with_tick() {
        let a = render_demo_frame(0);
        let b = render_demo_frame(10);
        assert_ne!(a, b, "the circle should have moved after 10 ticks");
    }

    #[test]
    fn frame_is_deterministic() {
        assert_eq!(render_demo_frame(7), render_demo_frame(7));
    }
}
