//! Microphone bars. The knob raises or lowers the gain.

use super::{App, Effects, Event, World};
use crate::canvas::{Canvas, BLACK, GREEN};

pub struct Spectrum {
    gain: u8,
    base: bool,
    last_gain: u8,
    last_len: u8,
    last_bands: [u8; 16],
    have_last: bool,
}

impl Spectrum {
    pub fn new() -> Self {
        Self {
            gain: 4,
            base: false,
            last_gain: 0,
            last_len: 0,
            last_bands: [0; 16],
            have_last: false,
        }
    }

    fn unchanged(&self, bands: &[u8]) -> bool {
        self.have_last
            && self.last_gain == self.gain
            && usize::from(self.last_len) == bands.len()
            && self.last_bands[..bands.len()] == *bands
    }
}

impl App for Spectrum {
    fn id(&self) -> &'static str {
        "spectrum"
    }

    fn title(&self) -> &'static str {
        "SPECTRUM"
    }

    fn handle(&mut self, ev: Event, world: &World, _fx: &mut Effects, canvas: &mut Canvas) {
        if let Event::Knob(d) = ev {
            self.gain = (i32::from(self.gain) + d).clamp(1, 16) as u8;
        }
        if self.unchanged(world.bands) {
            return;
        }
        let n = world.bands.len().min(self.last_bands.len());
        self.last_bands[..n].copy_from_slice(&world.bands[..n]);
        self.last_len = n as u8;
        self.last_gain = self.gain;
        self.have_last = true;
        let mut scaled = [0u8; 16];
        for (slot, sample) in scaled.iter_mut().zip(world.bands.iter()).take(n) {
            *slot = sample.saturating_mul(self.gain);
        }
        let scale = if canvas.width() >= 200 { 2 } else { 1 };
        if !self.base {
            canvas.clear(BLACK);
            canvas.text(8, 8, "MIC", GREEN, scale);
            self.base = true;
        } else {
            let h = i32::from(canvas.height());
            canvas.fill_rect(0, h / 2, i32::from(canvas.width()), h - h / 2, BLACK);
        }
        canvas.bars(&scaled[..n], GREEN);
    }
}
