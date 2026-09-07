//! Battery state-of-charge estimate and the gates that keep a refresh or a
//! charge from happening at an unsafe voltage or temperature.
//!
//! The numbers are coarse on purpose. A LiPo discharge curve is not linear, but
//! a status glyph does not need fuel-gauge accuracy, and integer math keeps the
//! bare-metal build free of a soft-float dependency.

/// Resting cell voltage treated as empty, in millivolts.
pub const EMPTY_MV: u16 = 3300;

/// Resting cell voltage treated as full, in millivolts.
pub const FULL_MV: u16 = 4200;

/// Lowest voltage at which a panel refresh is allowed, in millivolts. Below
/// this a refresh risks a half-drawn frame if the cell sags under the spike.
pub const REFRESH_FLOOR_MV: u16 = 3400;

/// BQ25185 state decoded from its two open-drain status pins.
#[derive(Clone, Copy, PartialEq, Eq, Debug)]
pub enum ChargerStatus {
    CompleteOrIdle,
    Charging,
    RecoverableFault,
    LatchedFault,
}

impl ChargerStatus {
    /// Decode the pulled-up logic levels on STAT1 and STAT2.
    pub const fn from_pins(stat1_high: bool, stat2_high: bool) -> Self {
        match (stat1_high, stat2_high) {
            (true, true) => Self::CompleteOrIdle,
            (true, false) => Self::Charging,
            (false, true) => Self::RecoverableFault,
            (false, false) => Self::LatchedFault,
        }
    }

    /// Return whether firmware can leave charging enabled.
    pub const fn permits_charging(self) -> bool {
        matches!(self, Self::CompleteOrIdle | Self::Charging)
    }
}

/// Estimated state of charge as a percentage in `0..=100`, from a resting
/// cell voltage.
pub fn soc_percent(mv: u16) -> u8 {
    // Resting-voltage anchors for a light-load LiPo. Linear interpolation
    // within each segment is still approximate, but it avoids claiming 50%
    // at 3.75 V where a typical cell is closer to one-third charged.
    const CURVE: &[(u16, u8)] = &[
        (EMPTY_MV, 0),
        (3500, 5),
        (3600, 12),
        (3700, 25),
        (3750, 35),
        (3800, 50),
        (3900, 70),
        (4000, 85),
        (4100, 95),
        (FULL_MV, 100),
    ];

    if mv <= CURVE[0].0 {
        return 0;
    }
    for pair in CURVE.windows(2) {
        let (low_mv, low_percent) = pair[0];
        let (high_mv, high_percent) = pair[1];
        if mv <= high_mv {
            let span_mv = u32::from(high_mv - low_mv);
            let offset_mv = u32::from(mv - low_mv);
            let span_percent = u32::from(high_percent - low_percent);
            return low_percent + ((offset_mv * span_percent) / span_mv) as u8;
        }
    }
    100
}

/// Whether a panel refresh should proceed at this voltage and panel
/// temperature. E-ink refresh is unreliable when the cell is nearly empty or
/// the panel is below freezing or too hot.
pub fn refresh_allowed(mv: u16, temp_c: i8) -> bool {
    mv >= REFRESH_FLOOR_MV && (0..=50).contains(&temp_c)
}

/// The BLE connection interval to request, in units of 1.25 ms. Tight while a
/// transfer is in flight for throughput, relaxed while idle to save power.
pub fn conn_interval_1_25ms(transfer_active: bool) -> u16 {
    if transfer_active {
        12 // 15 ms
    } else {
        800 // 1 s
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn soc_clamps_at_the_ends() {
        assert_eq!(soc_percent(3000), 0);
        assert_eq!(soc_percent(EMPTY_MV), 0);
        assert_eq!(soc_percent(FULL_MV), 100);
        assert_eq!(soc_percent(5000), 100);
    }

    #[test]
    fn soc_is_monotonic_in_the_middle() {
        assert_eq!(soc_percent(3800), 50);
        assert!(soc_percent(3600) < soc_percent(3900));
    }

    #[test]
    fn refresh_is_gated_by_voltage_and_temperature() {
        assert!(refresh_allowed(3800, 22));
        assert!(!refresh_allowed(3350, 22)); // too empty
        assert!(!refresh_allowed(3800, -5)); // too cold
        assert!(!refresh_allowed(3800, 60)); // too hot
    }

    #[test]
    fn connection_interval_tightens_during_transfer() {
        assert!(conn_interval_1_25ms(true) < conn_interval_1_25ms(false));
    }

    #[test]
    fn charger_status_table_matches_bq25185() {
        assert_eq!(
            ChargerStatus::from_pins(true, true),
            ChargerStatus::CompleteOrIdle
        );
        assert_eq!(
            ChargerStatus::from_pins(true, false),
            ChargerStatus::Charging
        );
        assert_eq!(
            ChargerStatus::from_pins(false, true),
            ChargerStatus::RecoverableFault
        );
        assert_eq!(
            ChargerStatus::from_pins(false, false),
            ChargerStatus::LatchedFault
        );
        assert!(!ChargerStatus::LatchedFault.permits_charging());
    }
}
