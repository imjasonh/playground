//! Knob step counter.
//!
//! On this board the two lines are not a quadrature pair. One direction is a
//! low pulse on GPIO7 while GPIO8 stays high. The other is a low pulse on
//! GPIO8 while GPIO7 stays high. A falling edge is one detent. The same
//! decoder also counts one step per cycle of a real quadrature encoder, which
//! is what the companion's second pair looks like on the schematic.

const DEBOUNCE_MS: u64 = 5;

#[derive(Clone, Debug)]
pub struct Encoder {
    prev_a: bool,
    prev_b: bool,
    last_a_ms: u64,
    last_b_ms: u64,
    detents: i32,
}

impl Default for Encoder {
    fn default() -> Self {
        Self::new()
    }
}

impl Encoder {
    pub fn new() -> Self {
        Self {
            prev_a: true,
            prev_b: true,
            last_a_ms: 0,
            last_b_ms: 0,
            detents: 0,
        }
    }

    /// Sample both channels. `a` is GPIO8 on the S3, `b` is GPIO7.
    /// `now_ms` is milliseconds since boot, used to ignore bounce.
    /// A falling edge on `b` while `a` is high returns 1.
    /// A falling edge on `a` while `b` is high returns -1.
    pub fn update(&mut self, a: bool, b: bool, now_ms: u64) -> i32 {
        let mut delta = 0;
        if self.prev_b && !b && a && now_ms.saturating_sub(self.last_b_ms) >= DEBOUNCE_MS {
            delta += 1;
            self.last_b_ms = now_ms;
        }
        if self.prev_a && !a && b && now_ms.saturating_sub(self.last_a_ms) >= DEBOUNCE_MS {
            delta -= 1;
            self.last_a_ms = now_ms;
        }
        self.prev_a = a;
        self.prev_b = b;
        self.detents = self.detents.saturating_add(delta);
        delta
    }

    pub fn detents(&self) -> i32 {
        self.detents
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn direction_pulses_count_once_each() {
        let mut enc = Encoder::new();
        assert_eq!(enc.update(true, true, 0), 0);
        assert_eq!(enc.update(true, false, 10), 1);
        assert_eq!(enc.update(true, true, 20), 0);
        assert_eq!(enc.update(false, true, 40), -1);
        assert_eq!(enc.update(true, true, 50), 0);
        assert_eq!(enc.detents(), 0);
    }

    #[test]
    fn bounce_inside_five_milliseconds_is_ignored() {
        let mut enc = Encoder::new();
        assert_eq!(enc.update(true, false, 10), 1);
        assert_eq!(enc.update(true, true, 12), 0);
        assert_eq!(enc.update(true, false, 14), 0);
        assert_eq!(enc.update(true, true, 16), 0);
        assert_eq!(enc.update(true, false, 20), 1);
    }

    #[test]
    fn one_quadrature_cycle_is_one_step() {
        let mut enc = Encoder::new();
        let mut t = 0u64;
        let mut sum = 0;
        for (a, b) in [
            (true, true),
            (true, false),
            (false, false),
            (false, true),
            (true, true),
        ] {
            t += 10;
            sum += enc.update(a, b, t);
        }
        assert_eq!(sum, 1);
    }
}
