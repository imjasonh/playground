//! Cell voltage from the divider on GPIO 1.

use super::{label, App, Effects, Event, World};
use crate::canvas::Canvas;

pub struct BatteryApp;

impl BatteryApp {
    pub fn new() -> Self {
        Self
    }
}

impl App for BatteryApp {
    fn id(&self) -> &'static str {
        "battery"
    }

    fn title(&self) -> &'static str {
        "BATTERY"
    }

    fn handle(&mut self, _ev: Event, world: &World, _fx: &mut Effects, canvas: &mut Canvas) {
        label(
            canvas,
            "BATTERY",
            &format!("{} MV {} PCT", world.battery_mv, world.battery_pct),
        );
    }
}
