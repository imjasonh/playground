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

/// Estimated state of charge as a percentage in `0..=100`, from a resting
/// cell voltage. Linear between [`EMPTY_MV`] and [`FULL_MV`].
pub fn soc_percent(mv: u16) -> u8 {
    if mv <= EMPTY_MV {
        return 0;
    }
    if mv >= FULL_MV {
        return 100;
    }
    let span = u32::from(FULL_MV - EMPTY_MV);
    let over = u32::from(mv - EMPTY_MV);
    ((over * 100) / span) as u8
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
        assert_eq!(soc_percent(3750), 50);
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
}
