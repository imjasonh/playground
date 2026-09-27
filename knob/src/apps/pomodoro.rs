//! Pomodoro timer. The knob sets minutes while stopped. A tap starts or pauses.
//! Reaching zero fires the strong-click haptic once.

use super::{label, App, Effects, Event, World};
use crate::canvas::Canvas;
use crate::haptic::STRONG_CLICK;

pub struct Pomodoro {
    minutes: u32,
    left_ms: u64,
    running: bool,
    fired: bool,
}

impl Pomodoro {
    pub fn new() -> Self {
        Self {
            minutes: 25,
            left_ms: 25 * 60 * 1000,
            running: false,
            fired: false,
        }
    }
}

impl App for Pomodoro {
    fn id(&self) -> &'static str {
        "pomodoro"
    }

    fn title(&self) -> &'static str {
        "POMODORO"
    }

    fn handle(&mut self, ev: Event, world: &World, fx: &mut Effects, canvas: &mut Canvas) {
        match ev {
            Event::Knob(d) if !self.running => {
                self.minutes = (self.minutes as i32 + d).clamp(1, 90) as u32;
                self.left_ms = u64::from(self.minutes) * 60_000;
                self.fired = false;
            }
            Event::Tap(_) => {
                self.running = !self.running;
                if self.left_ms == 0 {
                    self.left_ms = u64::from(self.minutes) * 60_000;
                    self.running = true;
                    self.fired = false;
                }
            }
            Event::Tick if self.running => {
                let _ = world.now_ms;
                self.left_ms = self.left_ms.saturating_sub(50);
                if self.left_ms == 0 {
                    self.running = false;
                    if !self.fired {
                        fx.haptic = Some(STRONG_CLICK);
                        self.fired = true;
                    }
                }
            }
            _ => {}
        }
        let secs = self.left_ms / 1000;
        let state = if self.running { "RUN" } else { "STOP" };
        label(
            canvas,
            "POMODORO",
            &format!("{state} {:02}:{:02}", secs / 60, secs % 60),
        );
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::apps::World;
    use crate::canvas::Canvas;

    #[test]
    fn finishing_clicks_once() {
        let mut app = Pomodoro::new();
        app.left_ms = 50;
        app.running = true;
        let mut fx = Effects::default();
        let mut canvas = Canvas::new(40, 40, false);
        let world = World::empty();
        app.handle(Event::Tick, &world, &mut fx, &mut canvas);
        assert_eq!(fx.haptic, Some(STRONG_CLICK));
        assert!(!app.running);
        let mut fx = Effects::default();
        app.handle(Event::Tick, &world, &mut fx, &mut canvas);
        assert_eq!(fx.haptic, None);
    }
}
