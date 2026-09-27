//! Pick a DRV2605 effect with the knob. A tap plays it.

use super::{label, App, Effects, Event, World};
use crate::canvas::Canvas;

pub struct Haptics {
    effect: u8,
}

impl Haptics {
    pub fn new() -> Self {
        Self { effect: 1 }
    }
}

impl App for Haptics {
    fn id(&self) -> &'static str {
        "haptics"
    }

    fn title(&self) -> &'static str {
        "HAPTICS"
    }

    fn handle(&mut self, ev: Event, _world: &World, fx: &mut Effects, canvas: &mut Canvas) {
        match ev {
            Event::Knob(d) => {
                self.effect = (i32::from(self.effect) + d).clamp(1, 123) as u8;
            }
            Event::Tap(_) => fx.haptic = Some(self.effect),
            _ => {}
        }
        label(canvas, "HAPTICS", &format!("EFFECT {:03}", self.effect));
    }
}
