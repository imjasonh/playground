//! Finger drawing. The knob cycles the ink color. A swipe up leaves the app.

use super::{App, Effects, Event, World};
use crate::canvas::{Canvas, BLACK};

const COLORS: [u16; 4] = [0xFFFF, 0xF800, 0x07E0, 0x001F];

pub struct Sketch {
    color: usize,
    ready: bool,
    swatch: Option<usize>,
}

impl Sketch {
    pub fn new() -> Self {
        Self {
            color: 0,
            ready: false,
            swatch: None,
        }
    }

    fn swatch(&mut self, canvas: &mut Canvas) {
        if self.swatch == Some(self.color) {
            return;
        }
        self.swatch = Some(self.color);
        canvas.fill_rect(8, 8, 8, 8, COLORS[self.color]);
    }
}

impl App for Sketch {
    fn id(&self) -> &'static str {
        "sketch"
    }

    fn title(&self) -> &'static str {
        "SKETCH"
    }

    fn handle(&mut self, ev: Event, _world: &World, _fx: &mut Effects, canvas: &mut Canvas) {
        if !self.ready {
            canvas.clear(BLACK);
            self.ready = true;
            self.swatch(canvas);
        }
        match ev {
            Event::Knob(d) => {
                let n = COLORS.len() as i32;
                self.color = (self.color as i32 + d).rem_euclid(n) as usize;
                self.swatch(canvas);
            }
            Event::Point(p) | Event::Tap(p) => {
                let ink = COLORS[self.color];
                let x = i32::from(p.x) * i32::from(canvas.width()) / 360;
                let y = i32::from(p.y) * i32::from(canvas.height()) / 360;
                canvas.fill_circle(x, y, 2, ink);
            }
            Event::Tick => {}
        }
    }
}
