//! Microphone bars. The knob raises or lowers the gain.

use super::{App, Effects, Event, World};
use crate::canvas::{Canvas, BLACK, GREEN};

pub struct Spectrum {
    gain: u8,
}

impl Spectrum {
    pub fn new() -> Self {
        Self { gain: 4 }
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
        canvas.clear(BLACK);
        let scale = if canvas.width() >= 200 { 2 } else { 1 };
        canvas.text(8, 8, "MIC", GREEN, scale);
        let scaled: Vec<u8> = world
            .bands
            .iter()
            .map(|b| b.saturating_mul(self.gain))
            .collect();
        canvas.bars(&scaled, GREEN);
    }
}
