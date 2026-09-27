//! TF card listing. The knob scrolls. Names come from the SDMMC mount.

use super::{App, Effects, Event, World};
use crate::canvas::{Canvas, BLACK, WHITE};

pub struct Card {
    index: usize,
}

impl Card {
    pub fn new() -> Self {
        Self { index: 0 }
    }
}

impl App for Card {
    fn id(&self) -> &'static str {
        "card"
    }

    fn title(&self) -> &'static str {
        "CARD"
    }

    fn handle(&mut self, ev: Event, world: &World, _fx: &mut Effects, canvas: &mut Canvas) {
        if let Event::Knob(d) = ev {
            if !world.sd.is_empty() {
                let n = world.sd.len() as i32;
                self.index = (self.index as i32 + d).rem_euclid(n) as usize;
            }
        }
        canvas.clear(BLACK);
        let scale = if canvas.width() >= 200 { 2 } else { 1 };
        if world.sd.is_empty() {
            canvas.text(8, 8, "NO CARD", WHITE, scale);
            return;
        }
        let start = self.index.min(world.sd.len() - 1);
        for (row, entry) in world.sd.iter().skip(start).take(4).enumerate() {
            let mark = if row == 0 { ">" } else { " " };
            let kind = if entry.dir { "DIR" } else { "FILE" };
            canvas.text(
                4,
                4 + row as i32 * 10 * scale,
                &format!("{mark}{kind} {}", entry.name),
                WHITE,
                scale,
            );
        }
    }
}
