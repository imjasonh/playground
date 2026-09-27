//! Theme clock. The knob steps the timezone by 15 minutes.
//! The device fills `World.unix` from SNTP when Wi-Fi is up.

use super::{label, App, Effects, Event, World};
use crate::canvas::Canvas;

pub struct Clock {
    offset_min: i32,
    drawn: Option<u64>,
}

impl Clock {
    pub fn new() -> Self {
        Self {
            offset_min: 0,
            drawn: None,
        }
    }

    fn hm(&self, unix: u64) -> (u32, u32) {
        let shifted = unix as i64 + i64::from(self.offset_min) * 60;
        let shifted = shifted.max(0) as u64;
        let mins = (shifted / 60) % (24 * 60);
        ((mins / 60) as u32, (mins % 60) as u32)
    }
}

impl App for Clock {
    fn id(&self) -> &'static str {
        "clock"
    }

    fn title(&self) -> &'static str {
        "CLOCK"
    }

    fn handle(&mut self, ev: Event, world: &World, _fx: &mut Effects, canvas: &mut Canvas) {
        if let Event::Knob(d) = ev {
            self.offset_min = (self.offset_min + d * 15).clamp(-12 * 60, 14 * 60);
        }
        let (stamp, line) = match world.unix {
            Some(unix) => {
                let (h, m) = self.hm(unix);
                let stamp =
                    (u64::from(h) << 32) | (u64::from(m) << 16) | (self.offset_min as u32 as u64);
                (stamp, format!("{h:02}:{m:02} {:+03}", self.offset_min))
            }
            None => (
                (1 << 63) | (self.offset_min as u32 as u64),
                format!("NO TIME {:+03}", self.offset_min),
            ),
        };
        if !super::redraw(&mut self.drawn, stamp) {
            return;
        }
        label(canvas, "CLOCK", &line);
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn offset_moves_the_hour() {
        let clock = Clock {
            offset_min: 60,
            drawn: None,
        };
        assert_eq!(clock.hm(0), (1, 0));
    }
}
