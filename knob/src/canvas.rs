//! RGB565 canvas for the round 360 panel.
//!
//! Apps draw here. The S3 driver byte-swaps on the way out to the ST77916.
//! Pixels outside the circle are left untouched when `round` is set, which
//! matches the circular glass.

/// Pack 8-bit channels into RGB565.
pub fn rgb(r: u8, g: u8, b: u8) -> u16 {
    (u16::from(r & 0xF8) << 8) | (u16::from(g & 0xFC) << 3) | u16::from(b >> 3)
}

pub const BLACK: u16 = 0x0000;
pub const WHITE: u16 = 0xFFFF;
pub const RED: u16 = 0xF800;
pub const GREEN: u16 = 0x07E0;
pub const BLUE: u16 = 0x001F;
pub const AMBER: u16 = 0xFD20;
pub const GRAY: u16 = 0x8410;

#[derive(Clone, Debug)]
pub struct Canvas {
    w: u16,
    h: u16,
    round: bool,
    px: Vec<u16>,
}

impl Canvas {
    pub fn new(w: u16, h: u16, round: bool) -> Self {
        Self {
            w,
            h,
            round,
            px: vec![0; usize::from(w) * usize::from(h)],
        }
    }

    pub fn panel() -> Self {
        Self::new(crate::board::PANEL_W, crate::board::PANEL_H, true)
    }

    pub fn width(&self) -> u16 {
        self.w
    }

    pub fn height(&self) -> u16 {
        self.h
    }

    pub fn pixels(&self) -> &[u16] {
        &self.px
    }

    pub fn clear(&mut self, color: u16) {
        self.px.fill(color);
        if self.round {
            let cx = i32::from(self.w) / 2;
            let cy = i32::from(self.h) / 2;
            let r = cx.min(cy);
            let r2 = r * r;
            for y in 0..self.h {
                for x in 0..self.w {
                    let dx = i32::from(x) - cx;
                    let dy = i32::from(y) - cy;
                    if dx * dx + dy * dy > r2 {
                        let i = self.idx(x, y);
                        self.px[i] = BLACK;
                    }
                }
            }
        }
    }

    pub fn get(&self, x: i32, y: i32) -> Option<u16> {
        if !self.inside(x, y) {
            return None;
        }
        Some(self.px[self.idx(x as u16, y as u16)])
    }

    pub fn pixel(&mut self, x: i32, y: i32, color: u16) {
        if self.inside(x, y) {
            let i = self.idx(x as u16, y as u16);
            self.px[i] = color;
        }
    }

    pub fn fill_rect(&mut self, x: i32, y: i32, w: i32, h: i32, color: u16) {
        for yy in y..y.saturating_add(h) {
            for xx in x..x.saturating_add(w) {
                self.pixel(xx, yy, color);
            }
        }
    }

    pub fn line(&mut self, x0: i32, y0: i32, x1: i32, y1: i32, color: u16) {
        let dx = (x1 - x0).abs();
        let dy = (y1 - y0).abs();
        let sx = if x0 < x1 { 1 } else { -1 };
        let sy = if y0 < y1 { 1 } else { -1 };
        let mut err = dx - dy;
        let mut x = x0;
        let mut y = y0;
        loop {
            self.pixel(x, y, color);
            if x == x1 && y == y1 {
                break;
            }
            let e2 = 2 * err;
            if e2 > -dy {
                err -= dy;
                x += sx;
            }
            if e2 < dx {
                err += dx;
                y += sy;
            }
        }
    }

    pub fn fill_circle(&mut self, cx: i32, cy: i32, r: i32, color: u16) {
        let r2 = r * r;
        for y in cy - r..=cy + r {
            for x in cx - r..=cx + r {
                let dx = x - cx;
                let dy = y - cy;
                if dx * dx + dy * dy <= r2 {
                    self.pixel(x, y, color);
                }
            }
        }
    }

    /// Draw uppercase text. Unknown characters become a box. `scale` is 1 or more.
    pub fn text(&mut self, x: i32, y: i32, text: &str, color: u16, scale: i32) {
        let scale = scale.max(1);
        let mut cursor = x;
        for ch in text.chars() {
            let glyph = super::font::glyph(ch);
            for (row, bits) in glyph.iter().enumerate() {
                for col in 0..5 {
                    if bits & (1 << (4 - col)) != 0 {
                        self.fill_rect(
                            cursor + col * scale,
                            y + row as i32 * scale,
                            scale,
                            scale,
                            color,
                        );
                    }
                }
            }
            cursor += 6 * scale;
        }
    }

    /// Needle from the center out to `radius` at `turns` of a full circle.
    /// 0 is the top, and the direction is clockwise.
    pub fn needle(&mut self, turns: f32, radius: i32, color: u16) {
        let cx = i32::from(self.w) / 2;
        let cy = i32::from(self.h) / 2;
        let angle = turns * std::f32::consts::TAU - std::f32::consts::FRAC_PI_2;
        let x1 = cx + (angle.cos() * radius as f32) as i32;
        let y1 = cy + (angle.sin() * radius as f32) as i32;
        self.line(cx, cy, x1, y1, color);
    }

    /// Vertical bars along the bottom half, used by the spectrum app.
    pub fn bars(&mut self, values: &[u8], color: u16) {
        if values.is_empty() {
            return;
        }
        let n = values.len() as i32;
        let gap = 2;
        let usable = i32::from(self.w) - gap * (n + 1);
        let bw = (usable / n).max(1);
        let base = i32::from(self.h) - 8;
        let max_h = i32::from(self.h) / 2;
        for (i, v) in values.iter().enumerate() {
            let h = i32::from(*v) * max_h / 255;
            let x = gap + i as i32 * (bw + gap);
            self.fill_rect(x, base - h, bw, h.max(1), color);
        }
    }

    fn inside(&self, x: i32, y: i32) -> bool {
        if x < 0 || y < 0 || x >= i32::from(self.w) || y >= i32::from(self.h) {
            return false;
        }
        if !self.round {
            return true;
        }
        let cx = i32::from(self.w) / 2;
        let cy = i32::from(self.h) / 2;
        let r = cx.min(cy);
        let dx = x - cx;
        let dy = y - cy;
        dx * dx + dy * dy <= r * r
    }

    fn idx(&self, x: u16, y: u16) -> usize {
        usize::from(y) * usize::from(self.w) + usize::from(x)
    }
}

/// Big-endian bytes for the ST77916 RAM write.
pub fn to_be_bytes(pixels: &[u16]) -> Vec<u8> {
    let mut out = Vec::with_capacity(pixels.len() * 2);
    for p in pixels {
        out.extend_from_slice(&p.to_be_bytes());
    }
    out
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn round_canvas_rejects_the_corner() {
        let mut c = Canvas::new(32, 32, true);
        c.pixel(0, 0, WHITE);
        assert_eq!(c.get(0, 0), None);
        c.pixel(16, 16, WHITE);
        assert_eq!(c.get(16, 16), Some(WHITE));
    }

    #[test]
    fn text_and_byte_swap() {
        let mut c = Canvas::new(40, 16, false);
        c.text(0, 0, "A", WHITE, 1);
        assert!(c.pixels().contains(&WHITE));
        assert_eq!(to_be_bytes(&[0x1234]), vec![0x12, 0x34]);
        assert_eq!(rgb(255, 0, 0), RED);
    }
}
