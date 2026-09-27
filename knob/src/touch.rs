//! CST816 report parser and a small gesture tracker.
//!
//! A read of register 0 returns six bytes: gesture, finger count, X high,
//! X low, Y high, Y low. Coordinates are 12-bit. Values already inside the
//! 360 panel are used as pixels. Larger values are scaled from the 12-bit range.
//! The glass is mounted upside down (MADCTL 0xC0), so both axes are mirrored
//! into the same frame as the pixels.

use crate::board::{PANEL_H, PANEL_W};

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum Gesture {
    SwipeUp,
    SwipeDown,
    SwipeLeft,
    SwipeRight,
    Tap,
}

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub struct Point {
    pub x: u16,
    pub y: u16,
}

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub struct TouchReport {
    pub gesture: Option<Gesture>,
    pub point: Option<Point>,
}

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum TouchError {
    Short,
}

pub fn parse_report(bytes: &[u8]) -> Result<TouchReport, TouchError> {
    if bytes.len() < 6 {
        return Err(TouchError::Short);
    }
    let fingers = bytes[1];
    let point = if fingers == 0 {
        None
    } else {
        let x = u16::from(bytes[2] & 0x0F) << 8 | u16::from(bytes[3]);
        let y = u16::from(bytes[4] & 0x0F) << 8 | u16::from(bytes[5]);
        Some(Point {
            x: mount(x, PANEL_W),
            y: mount(y, PANEL_H),
        })
    };
    Ok(TouchReport {
        gesture: gesture_byte(bytes[0]),
        point,
    })
}

fn scale(raw: u16, span: u16) -> u16 {
    if raw < span {
        raw
    } else {
        let v = u32::from(raw).saturating_mul(u32::from(span)) / 4096;
        u16::try_from(v).unwrap_or(span - 1).min(span - 1)
    }
}

fn mount(raw: u16, span: u16) -> u16 {
    span - 1 - scale(raw, span)
}

fn gesture_byte(v: u8) -> Option<Gesture> {
    match v {
        0x01 => Some(Gesture::SwipeUp),
        0x02 => Some(Gesture::SwipeDown),
        0x03 => Some(Gesture::SwipeLeft),
        0x04 => Some(Gesture::SwipeRight),
        0x05 => Some(Gesture::Tap),
        _ => None,
    }
}

/// Tracks a press so a swipe still counts when the controller omits the gesture byte.
#[derive(Clone, Debug, Default)]
pub struct GestureTracker {
    origin: Option<Point>,
    last: Option<Point>,
}

impl GestureTracker {
    pub fn new() -> Self {
        Self::default()
    }

    pub fn update(&mut self, report: TouchReport) -> Option<Gesture> {
        if let Some(g) = report.gesture {
            if report.point.is_none() {
                self.origin = None;
                self.last = None;
            }
            return Some(g);
        }
        match report.point {
            Some(p) => {
                if self.origin.is_none() {
                    self.origin = Some(p);
                }
                self.last = Some(p);
                None
            }
            None => {
                let g = self.finish();
                self.origin = None;
                self.last = None;
                g
            }
        }
    }

    fn finish(&self) -> Option<Gesture> {
        let (a, b) = (self.origin?, self.last?);
        let dx = i32::from(b.x) - i32::from(a.x);
        let dy = i32::from(b.y) - i32::from(a.y);
        if dx.abs() < 30 && dy.abs() < 30 {
            return Some(Gesture::Tap);
        }
        if dx.abs() > dy.abs() {
            if dx > 0 {
                Some(Gesture::SwipeRight)
            } else {
                Some(Gesture::SwipeLeft)
            }
        } else if dy > 0 {
            Some(Gesture::SwipeDown)
        } else {
            Some(Gesture::SwipeUp)
        }
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn parses_a_tap_inside_the_panel() {
        let report = parse_report(&[0x05, 1, 0x00, 40, 0x00, 80]).unwrap();
        assert_eq!(report.gesture, Some(Gesture::Tap));
        assert_eq!(report.point, Some(Point { x: 319, y: 279 }));
    }

    #[test]
    fn scales_12_bit_coordinates() {
        let report = parse_report(&[0x00, 1, 0x0F, 0xFF, 0x08, 0x00]).unwrap();
        let p = report.point.unwrap();
        assert_eq!(p.x, 0);
        assert_eq!(p.y, 179);
    }

    #[test]
    fn lift_after_a_long_drag_is_a_swipe() {
        let mut t = GestureTracker::new();
        assert_eq!(
            t.update(TouchReport {
                gesture: None,
                point: Some(Point { x: 180, y: 300 })
            }),
            None
        );
        t.update(TouchReport {
            gesture: None,
            point: Some(Point { x: 180, y: 40 }),
        });
        assert_eq!(
            t.update(TouchReport {
                gesture: None,
                point: None
            }),
            Some(Gesture::SwipeUp)
        );
    }
}
