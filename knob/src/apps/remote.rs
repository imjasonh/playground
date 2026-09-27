//! Media remote. The knob sends HID volume and the same command to the
//! companion over the UART link. A tap sends play/pause.

use super::{label, App, Effects, Event, World};
use crate::canvas::Canvas;
use crate::hid::{PLAY_PAUSE, VOLUME_DOWN, VOLUME_UP};
use crate::link::{BtState, Msg, PlayState};

pub struct Remote {
    drawn: Option<u64>,
}

impl Remote {
    pub fn new() -> Self {
        Self { drawn: None }
    }
}

impl App for Remote {
    fn id(&self) -> &'static str {
        "remote"
    }

    fn title(&self) -> &'static str {
        "REMOTE"
    }

    fn handle(&mut self, ev: Event, world: &World, fx: &mut Effects, canvas: &mut Canvas) {
        match ev {
            Event::Knob(d) if d > 0 => {
                fx.consumer = Some(VOLUME_UP);
                fx.link.push(Msg::VolUp);
            }
            Event::Knob(d) if d < 0 => {
                fx.consumer = Some(VOLUME_DOWN);
                fx.link.push(Msg::VolDown);
            }
            Event::Tap(_) => {
                fx.consumer = Some(PLAY_PAUSE);
                fx.link.push(match world.play {
                    PlayState::Playing => Msg::Pause,
                    _ => Msg::Play,
                });
            }
            _ => {}
        }
        let stamp = (world.bt as u64) | ((world.play as u64) << 8) | (mix(world.track) << 16);
        if !super::redraw(&mut self.drawn, stamp) {
            return;
        }
        let bt = match world.bt {
            BtState::Disconnected => "OFF",
            BtState::Discoverable => "PAIR",
            BtState::Connecting => "WAIT",
            BtState::Connected => "ON",
        };
        let track = if world.track.is_empty() {
            "NO TRACK"
        } else {
            world.track
        };
        label(canvas, "REMOTE", &format!("{bt} {track}"));
    }
}

fn mix(text: &str) -> u64 {
    let mut h = 0xcbf29ce484222325;
    for b in text.bytes() {
        h ^= u64::from(b);
        h = h.wrapping_mul(0x100000001b3);
    }
    h
}
