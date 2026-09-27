//! Example apps. Each one is a Cargo feature (`app-dial`, `app-clock`, ...).
//! The default build includes all ten. `make build APPS=clock,tone` compiles
//! only those two into the S3 image.

use crate::canvas::Canvas;
#[cfg(feature = "any-app")]
use crate::canvas::{AMBER, BLACK, WHITE};
use crate::link::{BtState, Msg, PlayState};
use crate::touch::Point;

pub type AppId = &'static str;

#[derive(Clone, Debug, PartialEq, Eq)]
pub struct SdEntry {
    pub name: String,
    pub bytes: u64,
    pub dir: bool,
}

#[derive(Clone, Debug)]
pub struct World<'a> {
    pub now_ms: u64,
    pub unix: Option<u64>,
    pub bands: &'a [u8],
    pub battery_mv: u32,
    pub battery_pct: u8,
    pub sd: &'a [SdEntry],
    pub bt: BtState,
    pub play: PlayState,
    pub track: &'a str,
}

impl World<'_> {
    pub fn empty() -> World<'static> {
        World {
            now_ms: 0,
            unix: None,
            bands: &[],
            battery_mv: 0,
            battery_pct: 0,
            sd: &[],
            bt: BtState::Disconnected,
            play: PlayState::Unknown,
            track: "",
        }
    }
}

#[derive(Clone, Debug, Default)]
pub struct Effects {
    pub tone_hz: Option<u16>,
    pub haptic: Option<u8>,
    pub consumer: Option<u16>,
    pub link: Vec<Msg>,
}

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum Event {
    Knob(i32),
    Tap(Point),
    Point(Point),
    Tick,
}

pub trait App {
    fn id(&self) -> AppId;
    fn title(&self) -> &'static str;
    fn handle(&mut self, ev: Event, world: &World, fx: &mut Effects, canvas: &mut Canvas);
}

#[cfg(feature = "app-battery")]
mod battery;
#[cfg(feature = "app-card")]
mod card;
#[cfg(feature = "app-clock")]
mod clock;
#[cfg(feature = "app-dial")]
mod dial;
#[cfg(feature = "app-haptics")]
mod haptics;
#[cfg(feature = "app-pomodoro")]
mod pomodoro;
#[cfg(feature = "app-remote")]
mod remote;
#[cfg(feature = "app-sketch")]
mod sketch;
#[cfg(feature = "app-spectrum")]
mod spectrum;
#[cfg(feature = "app-tone")]
mod tone;

#[allow(clippy::vec_init_then_push)]
pub fn catalog() -> Vec<Box<dyn App>> {
    #[cfg_attr(not(feature = "any-app"), allow(unused_mut))]
    let mut apps: Vec<Box<dyn App>> = Vec::new();
    #[cfg(feature = "app-dial")]
    apps.push(Box::new(dial::Dial::new()));
    #[cfg(feature = "app-clock")]
    apps.push(Box::new(clock::Clock::new()));
    #[cfg(feature = "app-pomodoro")]
    apps.push(Box::new(pomodoro::Pomodoro::new()));
    #[cfg(feature = "app-spectrum")]
    apps.push(Box::new(spectrum::Spectrum::new()));
    #[cfg(feature = "app-tone")]
    apps.push(Box::new(tone::ToneApp::new()));
    #[cfg(feature = "app-sketch")]
    apps.push(Box::new(sketch::Sketch::new()));
    #[cfg(feature = "app-haptics")]
    apps.push(Box::new(haptics::Haptics::new()));
    #[cfg(feature = "app-battery")]
    apps.push(Box::new(battery::BatteryApp::new()));
    #[cfg(feature = "app-card")]
    apps.push(Box::new(card::Card::new()));
    #[cfg(feature = "app-remote")]
    apps.push(Box::new(remote::Remote::new()));
    apps
}

pub fn feature_count() -> usize {
    #[cfg_attr(not(feature = "any-app"), allow(unused_mut))]
    let mut n = 0;
    #[cfg(feature = "app-dial")]
    {
        n += 1;
    }
    #[cfg(feature = "app-clock")]
    {
        n += 1;
    }
    #[cfg(feature = "app-pomodoro")]
    {
        n += 1;
    }
    #[cfg(feature = "app-spectrum")]
    {
        n += 1;
    }
    #[cfg(feature = "app-tone")]
    {
        n += 1;
    }
    #[cfg(feature = "app-sketch")]
    {
        n += 1;
    }
    #[cfg(feature = "app-haptics")]
    {
        n += 1;
    }
    #[cfg(feature = "app-battery")]
    {
        n += 1;
    }
    #[cfg(feature = "app-card")]
    {
        n += 1;
    }
    #[cfg(feature = "app-remote")]
    {
        n += 1;
    }
    n
}

#[cfg(feature = "any-app")]
pub(super) fn redraw(slot: &mut Option<u64>, stamp: u64) -> bool {
    if *slot == Some(stamp) {
        false
    } else {
        *slot = Some(stamp);
        true
    }
}

#[cfg(feature = "any-app")]
fn label(canvas: &mut Canvas, title: &str, line: &str) {
    canvas.clear(BLACK);
    let scale = if canvas.width() >= 200 { 3 } else { 1 };
    canvas.text(8, 8, title, AMBER, scale);
    canvas.text(8, 8 + 10 * scale, line, WHITE, scale);
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn catalog_follows_features() {
        let apps = catalog();
        assert_eq!(apps.len(), feature_count());
        let mut ids: Vec<_> = apps.iter().map(|a| a.id()).collect();
        let before = ids.len();
        ids.sort_unstable();
        ids.dedup();
        assert_eq!(ids.len(), before);
        assert_has(&ids, "dial", cfg!(feature = "app-dial"));
        assert_has(&ids, "clock", cfg!(feature = "app-clock"));
        assert_has(&ids, "pomodoro", cfg!(feature = "app-pomodoro"));
        assert_has(&ids, "spectrum", cfg!(feature = "app-spectrum"));
        assert_has(&ids, "tone", cfg!(feature = "app-tone"));
        assert_has(&ids, "sketch", cfg!(feature = "app-sketch"));
        assert_has(&ids, "haptics", cfg!(feature = "app-haptics"));
        assert_has(&ids, "battery", cfg!(feature = "app-battery"));
        assert_has(&ids, "card", cfg!(feature = "app-card"));
        assert_has(&ids, "remote", cfg!(feature = "app-remote"));
    }

    fn assert_has(ids: &[&str], id: &str, on: bool) {
        assert_eq!(ids.contains(&id), on, "{id}");
    }

    #[test]
    fn each_app_draws_on_a_tick() {
        let world = World::empty();
        for app in catalog() {
            let mut app = app;
            let mut canvas = Canvas::new(80, 80, false);
            let mut fx = Effects::default();
            app.handle(Event::Tick, &world, &mut fx, &mut canvas);
            assert!(
                canvas.pixels().iter().any(|p| *p != 0),
                "{} drew nothing",
                app.id()
            );
        }
    }
}
