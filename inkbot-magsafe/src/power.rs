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

/// SAADC resolution required by [`vddh_mv_from_saadc`].
pub const SAADC_RESOLUTION_BITS: u8 = 12;
/// SAADC internal reference voltage, in millivolts.
pub const SAADC_REFERENCE_MV: u16 = 600;
/// Reciprocal SAADC gain required by [`vddh_mv_from_saadc`].
pub const SAADC_GAIN_RECIPROCAL: u8 = 6;
/// Hardware divider applied by the nRF52833 VDDHDIV5 input.
pub const VDDH_DIVIDER: u8 = 5;

/// Convert a 12-bit SAADC sample from VDDHDIV5 to millivolts.
///
/// This assumes the 0.6 V internal reference, gain 1/6, and no oversampling.
/// Production firmware must apply measured offset calibration before calling
/// this function.
pub fn vddh_mv_from_saadc(raw: i16) -> Option<u16> {
    let raw = u32::try_from(raw).ok()?;
    let full_scale_mv =
        u32::from(SAADC_REFERENCE_MV) * u32::from(SAADC_GAIN_RECIPROCAL) * u32::from(VDDH_DIVIDER);
    let adc_steps = 1_u32 << SAADC_RESOLUTION_BITS;
    let millivolts = (raw * full_scale_mv + adc_steps / 2) / adc_steps;
    u16::try_from(millivolts).ok()
}

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

    /// Return whether the charger reports a fault.
    pub const fn is_fault(self) -> bool {
        matches!(self, Self::RecoverableFault | Self::LatchedFault)
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

/// Estimate cell state of charge from SYS only while wireless input is absent.
///
/// When Qi input is present, the BQ25185 power path can raise SYS above BAT.
/// That sample is useful for brownout policy but does not represent resting
/// cell voltage.
pub fn resting_soc_percent(sys_mv: u16, qi_present: bool) -> Option<u8> {
    if qi_present {
        None
    } else {
        Some(soc_percent(sys_mv))
    }
}

/// Whether a panel refresh should proceed at this voltage and panel
/// temperature. A charger fault also blocks the panel's high-current load.
pub fn refresh_allowed(mv: u16, temp_c: i8, charger: ChargerStatus) -> bool {
    mv >= REFRESH_FLOOR_MV && (0..=50).contains(&temp_c) && !charger.is_fault()
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
    fn vddh_conversion_matches_saadc_configuration() {
        assert_eq!(SAADC_RESOLUTION_BITS, 12);
        assert_eq!(SAADC_REFERENCE_MV, 600);
        assert_eq!(SAADC_GAIN_RECIPROCAL, 6);
        assert_eq!(VDDH_DIVIDER, 5);
        assert_eq!(vddh_mv_from_saadc(-1), None);
        assert_eq!(vddh_mv_from_saadc(0), Some(0));
        assert_eq!(vddh_mv_from_saadc(956), Some(4201));
    }

    #[test]
    fn soc_is_monotonic_in_the_middle() {
        assert_eq!(soc_percent(3800), 50);
        assert!(soc_percent(3600) < soc_percent(3900));
    }

    #[test]
    fn refresh_is_gated_by_voltage_and_temperature() {
        let idle = ChargerStatus::CompleteOrIdle;
        assert!(refresh_allowed(3800, 22, idle));
        assert!(!refresh_allowed(3350, 22, idle)); // too empty
        assert!(!refresh_allowed(3800, -5, idle)); // too cold
        assert!(!refresh_allowed(3800, 60, idle)); // too hot
        assert!(!refresh_allowed(4200, 22, ChargerStatus::RecoverableFault));
        assert!(!refresh_allowed(4200, 22, ChargerStatus::LatchedFault));
    }

    #[test]
    fn sys_is_not_reported_as_resting_cell_voltage_while_qi_is_present() {
        assert_eq!(resting_soc_percent(3800, false), Some(50));
        assert_eq!(resting_soc_percent(4500, true), None);
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
