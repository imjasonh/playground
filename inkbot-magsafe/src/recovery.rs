//! Physical owner-reset gesture for a sealed device with no button or port.
//!
//! Five deliberate placements on a Qi pad within 45 seconds request bond
//! erasure. The final transition leaves the tile on external power while it
//! erases settings and displays a new pairing passkey.

pub const REQUIRED_ATTACHMENTS: u8 = 5;
pub const MIN_PHASE_MS: u32 = 750;
pub const SEQUENCE_TIMEOUT_MS: u32 = 45_000;

#[derive(Clone, Copy, PartialEq, Eq, Debug)]
pub enum GestureEvent {
    Pending { attachments: u8 },
    TriggerOwnerReset,
}

#[derive(Clone, Copy, PartialEq, Eq, Debug)]
pub struct OwnerResetGesture {
    qi_present: bool,
    last_transition_ms: u32,
    started_ms: u32,
    attachments: u8,
}

impl OwnerResetGesture {
    pub const fn new(now_ms: u32, qi_present: bool) -> Self {
        Self {
            qi_present,
            last_transition_ms: now_ms,
            started_ms: now_ms,
            attachments: 0,
        }
    }

    /// Observe a debounced Qi-presence level and return any completed gesture.
    pub const fn observe(&mut self, now_ms: u32, qi_present: bool) -> GestureEvent {
        if qi_present == self.qi_present {
            return GestureEvent::Pending {
                attachments: self.attachments,
            };
        }

        let dwell_ms = now_ms.wrapping_sub(self.last_transition_ms);
        self.qi_present = qi_present;
        self.last_transition_ms = now_ms;
        if dwell_ms < MIN_PHASE_MS {
            self.attachments = 0;
            self.started_ms = now_ms;
            return GestureEvent::Pending { attachments: 0 };
        }

        if !qi_present {
            return GestureEvent::Pending {
                attachments: self.attachments,
            };
        }

        if self.attachments == 0 || now_ms.wrapping_sub(self.started_ms) > SEQUENCE_TIMEOUT_MS {
            self.started_ms = now_ms;
            self.attachments = 1;
        } else {
            self.attachments = self.attachments.saturating_add(1);
        }

        if self.attachments == REQUIRED_ATTACHMENTS {
            self.attachments = 0;
            self.started_ms = now_ms;
            GestureEvent::TriggerOwnerReset
        } else {
            GestureEvent::Pending {
                attachments: self.attachments,
            }
        }
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    fn transition(
        gesture: &mut OwnerResetGesture,
        now_ms: &mut u32,
        present: bool,
    ) -> GestureEvent {
        *now_ms += MIN_PHASE_MS;
        gesture.observe(*now_ms, present)
    }

    #[test]
    fn five_deliberate_attachments_trigger_on_external_power() {
        let mut now = 0;
        let mut gesture = OwnerResetGesture::new(now, false);
        for expected in 1..REQUIRED_ATTACHMENTS {
            assert_eq!(
                transition(&mut gesture, &mut now, true),
                GestureEvent::Pending {
                    attachments: expected
                }
            );
            assert_eq!(
                transition(&mut gesture, &mut now, false),
                GestureEvent::Pending {
                    attachments: expected
                }
            );
        }
        assert_eq!(
            transition(&mut gesture, &mut now, true),
            GestureEvent::TriggerOwnerReset
        );
    }

    #[test]
    fn contact_bounce_cancels_progress() {
        let mut gesture = OwnerResetGesture::new(0, false);
        assert_eq!(
            gesture.observe(MIN_PHASE_MS, true),
            GestureEvent::Pending { attachments: 1 }
        );
        assert_eq!(
            gesture.observe(MIN_PHASE_MS + 1, false),
            GestureEvent::Pending { attachments: 0 }
        );
        assert_eq!(
            gesture.observe(2 * MIN_PHASE_MS + 1, true),
            GestureEvent::Pending { attachments: 1 }
        );
    }

    #[test]
    fn timeout_starts_a_new_sequence() {
        let mut gesture = OwnerResetGesture::new(0, false);
        assert_eq!(
            gesture.observe(MIN_PHASE_MS, true),
            GestureEvent::Pending { attachments: 1 }
        );
        gesture.observe(2 * MIN_PHASE_MS, false);
        assert_eq!(
            gesture.observe(SEQUENCE_TIMEOUT_MS + 2 * MIN_PHASE_MS + 1, true),
            GestureEvent::Pending { attachments: 1 }
        );
    }

    #[test]
    fn booting_while_on_a_charger_does_not_count() {
        let mut gesture = OwnerResetGesture::new(0, true);
        assert_eq!(
            gesture.observe(10_000, true),
            GestureEvent::Pending { attachments: 0 }
        );
        assert_eq!(
            gesture.observe(11_000, false),
            GestureEvent::Pending { attachments: 0 }
        );
        assert_eq!(
            gesture.observe(12_000, true),
            GestureEvent::Pending { attachments: 1 }
        );
    }
}
