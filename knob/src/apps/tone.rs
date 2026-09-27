//! Sine tone out the 3.5 mm jack. The knob changes the pitch. A tap mutes.

use super::{label, App, Effects, Event, World};
use crate::canvas::Canvas;

pub struct ToneApp {
    hz: u16,
    on: bool,
    drawn: Option<u64>,
}

impl ToneApp {
    pub fn new() -> Self {
        Self {
            hz: 440,
            on: false,
            drawn: None,
        }
    }
}

impl App for ToneApp {
    fn id(&self) -> &'static str {
        "tone"
    }

    fn title(&self) -> &'static str {
        "TONE"
    }

    fn handle(&mut self, ev: Event, _world: &World, fx: &mut Effects, canvas: &mut Canvas) {
        match ev {
            Event::Knob(d) => {
                self.hz = (i32::from(self.hz) + d * 10).clamp(110, 4000) as u16;
            }
            Event::Tap(_) => self.on = !self.on,
            _ => {}
        }
        if self.on {
            fx.tone_hz = Some(self.hz);
        }
        let stamp = u64::from(self.hz) | (u64::from(self.on) << 16);
        if !super::redraw(&mut self.drawn, stamp) {
            return;
        }
        let state = if self.on { "ON" } else { "OFF" };
        label(canvas, "TONE", &format!("{state} {} HZ", self.hz));
    }
}
