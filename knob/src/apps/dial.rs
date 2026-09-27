//! Knob gauge. The needle follows the encoder. A tap returns it to zero.

use super::{label, App, Effects, Event, World};
use crate::canvas::{Canvas, WHITE};

pub struct Dial {
    value: i32,
    drawn: Option<u64>,
}

impl Dial {
    pub fn new() -> Self {
        Self {
            value: 50,
            drawn: None,
        }
    }
}

impl App for Dial {
    fn id(&self) -> &'static str {
        "dial"
    }

    fn title(&self) -> &'static str {
        "DIAL"
    }

    fn handle(&mut self, ev: Event, _world: &World, _fx: &mut Effects, canvas: &mut Canvas) {
        match ev {
            Event::Knob(d) => self.value = (self.value + d).clamp(0, 100),
            Event::Tap(_) => self.value = 0,
            Event::Point(_) | Event::Tick => {}
        }
        if !super::redraw(&mut self.drawn, self.value as u64) {
            return;
        }
        label(canvas, "DIAL", &format!("{:03}", self.value));
        let r = i32::from(canvas.width()) / 3;
        canvas.needle(self.value as f32 / 100.0, r, WHITE);
    }
}
