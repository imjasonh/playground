//! Launcher. The knob picks an app, a tap opens it, a swipe up closes it.
//! Only apps compiled into this image appear in the list.

use crate::apps::{catalog, App, Effects, Event, World};
use crate::canvas::{Canvas, AMBER, BLACK, WHITE};
use crate::touch::{Gesture, GestureTracker, Point, TouchReport};

pub struct Shell {
    apps: Vec<Box<dyn App>>,
    index: usize,
    inside: bool,
    tracker: GestureTracker,
    canvas: Canvas,
}

impl Shell {
    pub fn new(canvas: Canvas) -> Self {
        let mut shell = Self {
            apps: catalog(),
            index: 0,
            inside: false,
            tracker: GestureTracker::new(),
            canvas,
        };
        shell.draw_launcher();
        shell
    }

    pub fn len(&self) -> usize {
        self.apps.len()
    }

    pub fn is_empty(&self) -> bool {
        self.apps.is_empty()
    }

    pub fn inside(&self) -> bool {
        self.inside
    }

    pub fn current_id(&self) -> Option<&str> {
        if self.inside {
            self.apps.get(self.index).map(|app| app.id())
        } else {
            None
        }
    }

    pub fn selected_id(&self) -> Option<&str> {
        self.apps.get(self.index).map(|app| app.id())
    }

    pub fn ids(&self) -> Vec<&str> {
        self.apps.iter().map(|app| app.id()).collect()
    }

    /// Open one compiled-in app by id. Returns false when this image omitted it.
    pub fn open_id(&mut self, id: &str, world: &World) -> bool {
        let Some(index) = self.apps.iter().position(|app| app.id() == id) else {
            return false;
        };
        self.index = index;
        self.enter(world);
        true
    }

    pub fn canvas(&self) -> &Canvas {
        &self.canvas
    }

    pub fn knob(&mut self, delta: i32, world: &World) -> Effects {
        if delta == 0 {
            return Effects::default();
        }
        if self.inside {
            return self.forward(Event::Knob(delta), world);
        }
        if self.is_empty() {
            return Effects::default();
        }
        let n = self.apps.len() as i32;
        self.index = (self.index as i32 + delta).rem_euclid(n) as usize;
        self.draw_launcher();
        Effects::default()
    }

    pub fn touch(&mut self, report: TouchReport, world: &World) -> Effects {
        let gesture = self.tracker.update(report);
        if matches!(gesture, Some(Gesture::SwipeUp)) && self.inside {
            self.inside = false;
            self.draw_launcher();
            return Effects::default();
        }
        if !self.inside {
            if matches!(gesture, Some(Gesture::Tap)) {
                self.enter(world);
            }
            return Effects::default();
        }
        let mut fx = Effects::default();
        if let Some(p) = report.point {
            self.apply(Event::Point(p), world, &mut fx);
        }
        if matches!(gesture, Some(Gesture::Tap)) {
            let p = report.point.unwrap_or(Point { x: 180, y: 180 });
            self.apply(Event::Tap(p), world, &mut fx);
        }
        fx
    }

    pub fn tick(&mut self, world: &World) -> Effects {
        if self.inside {
            self.forward(Event::Tick, world)
        } else {
            self.draw_launcher();
            Effects::default()
        }
    }

    fn enter(&mut self, world: &World) {
        if self.is_empty() {
            return;
        }
        self.inside = true;
        self.canvas.clear(BLACK);
        let mut fx = Effects::default();
        self.apply(Event::Tick, world, &mut fx);
    }

    fn forward(&mut self, ev: Event, world: &World) -> Effects {
        let mut fx = Effects::default();
        self.apply(ev, world, &mut fx);
        fx
    }

    fn apply(&mut self, ev: Event, world: &World, fx: &mut Effects) {
        if let Some(app) = self.apps.get_mut(self.index) {
            app.handle(ev, world, fx, &mut self.canvas);
        }
    }

    fn draw_launcher(&mut self) {
        self.canvas.clear(BLACK);
        let scale = if self.canvas.width() >= 200 { 3 } else { 1 };
        if self.is_empty() {
            self.canvas.text(8, 8, "NO APPS", WHITE, scale);
            return;
        }
        let title = self.apps[self.index].title();
        let n = self.apps.len();
        self.canvas.text(8, 8, title, AMBER, scale);
        self.canvas.text(
            8,
            8 + 12 * scale,
            &format!("{}/{}", self.index + 1, n),
            WHITE,
            scale,
        );
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::touch::{Gesture, Point, TouchReport};

    fn shell() -> Shell {
        Shell::new(Canvas::new(80, 80, false))
    }

    #[test]
    fn knob_selects_and_tap_opens() {
        let mut shell = shell();
        assert!(shell.len() >= 1);
        assert!(!shell.inside());
        let first = shell.selected_id().unwrap().to_string();
        let world = World::empty();
        if shell.len() > 1 {
            shell.knob(1, &world);
            assert_ne!(shell.selected_id().unwrap(), first);
        }
        shell.touch(
            TouchReport {
                gesture: Some(Gesture::Tap),
                point: Some(Point { x: 10, y: 10 }),
            },
            &world,
        );
        assert!(shell.inside());
        assert_eq!(shell.current_id(), shell.selected_id());
        shell.touch(
            TouchReport {
                gesture: Some(Gesture::SwipeUp),
                point: None,
            },
            &world,
        );
        assert!(!shell.inside());
    }

    #[test]
    fn open_id_enters_that_app() {
        let mut shell = shell();
        let world = World::empty();
        let id = shell.selected_id().unwrap().to_string();
        assert!(shell.open_id(&id, &world));
        assert!(shell.inside());
        assert_eq!(shell.current_id(), Some(id.as_str()));
        assert!(!shell.open_id("missing", &world));
    }
}
