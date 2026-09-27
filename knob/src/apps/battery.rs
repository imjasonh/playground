//! Cell voltage from the divider on GPIO 1.

use super::{label, App, Effects, Event, World};
use crate::canvas::Canvas;

pub struct BatteryApp {
    drawn: Option<u64>,
}

impl BatteryApp {
    pub fn new() -> Self {
        Self { drawn: None }
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
        let stamp = (u64::from(world.battery_mv) << 8) | u64::from(world.battery_pct);
        if !super::redraw(&mut self.drawn, stamp) {
            return;
        }
        label(
            canvas,
            "BATTERY",
            &format!("{} MV {} PCT", world.battery_mv, world.battery_pct),
        );
    }
}
