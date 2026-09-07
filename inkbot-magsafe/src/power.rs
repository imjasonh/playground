//! Host-testable battery, charger, and refresh policy.
//!
//! Hardware code supplies debounced BQ25186 status, a calibrated SYS sample,
//! and a qualified panel-temperature reading. These predicates do not replace
//! the charger's autonomous JEITA protection.

/// Resting cell voltage treated as empty, in millivolts.
pub const EMPTY_MV: u16 = 3300;
/// Resting cell voltage treated as full, in millivolts.
pub const FULL_MV: u16 = 4200;

/// Configuration that firmware must write before it enables BQ25186 `/CE`.
#[derive(Clone, Copy, PartialEq, Eq, Debug)]
pub struct ChargerConfig {
    pub charge_ma: u16,
    pub input_limit_ma: u16,
    pub regulation_mv: u16,
    pub cold_c: i8,
    pub hot_c: i8,
}

pub const REQUIRED_CHARGER_CONFIG: ChargerConfig = ChargerConfig {
    charge_ma: 40,
    input_limit_ma: 100,
    regulation_mv: 4200,
    cold_c: 0,
    hot_c: 45,
};

/// BQ25186 state after reading and decoding its status and fault registers.
#[derive(Clone, Copy, PartialEq, Eq, Debug)]
pub enum ChargerStatus {
    InputAbsent,
    Charging,
    ChargeComplete,
    ThermalRegulation,
    Fault,
}

impl ChargerStatus {
    pub const fn blocks_refresh(self) -> bool {
        matches!(self, Self::Charging | Self::ThermalRegulation | Self::Fault)
    }
}

/// Provisional limits that EVT measurements must replace or confirm.
#[derive(Clone, Copy, PartialEq, Eq, Debug)]
pub struct SafetyLimits {
    pub refresh_start_mv: u16,
    pub min_panel_temp_c: i8,
    pub max_panel_temp_c: i8,
}

pub const EVT_SAFETY_LIMITS: SafetyLimits = SafetyLimits {
    refresh_start_mv: 3400,
    min_panel_temp_c: 0,
    max_panel_temp_c: 50,
};

/// Inputs required before firmware starts a panel refresh.
#[derive(Clone, Copy, PartialEq, Eq, Debug)]
pub struct PowerSample {
    pub sys_mv: u16,
    pub qi_present: bool,
    pub charger: ChargerStatus,
    pub panel_temp_c: Option<i8>,
}

#[derive(Clone, Copy, PartialEq, Eq, Debug)]
pub enum RefreshInhibit {
    LowVoltage,
    WirelessPower,
    Charging,
    ChargerFault,
    TemperatureUnavailable,
    TemperatureOutOfRange,
}

/// Apply the conservative pre-EVT refresh policy.
pub fn refresh_decision(sample: PowerSample, limits: SafetyLimits) -> Result<(), RefreshInhibit> {
    if sample.sys_mv < limits.refresh_start_mv {
        return Err(RefreshInhibit::LowVoltage);
    }
    if sample.qi_present {
        return Err(RefreshInhibit::WirelessPower);
    }
    match sample.charger {
        ChargerStatus::Fault => return Err(RefreshInhibit::ChargerFault),
        ChargerStatus::Charging | ChargerStatus::ThermalRegulation => {
            return Err(RefreshInhibit::Charging);
        }
        ChargerStatus::InputAbsent | ChargerStatus::ChargeComplete => {}
    }
    let Some(temp_c) = sample.panel_temp_c else {
        return Err(RefreshInhibit::TemperatureUnavailable);
    };
    if !(limits.min_panel_temp_c..=limits.max_panel_temp_c).contains(&temp_c) {
        return Err(RefreshInhibit::TemperatureOutOfRange);
    }
    Ok(())
}

/// SAADC resolution used for the external SYS divider.
pub const SAADC_RESOLUTION_BITS: u8 = 12;
/// SAADC internal reference voltage, in millivolts.
pub const SAADC_REFERENCE_MV: u16 = 600;
/// Reciprocal gain used for the external SYS divider.
pub const SAADC_GAIN_RECIPROCAL: u8 = 4;
/// Upper resistance of the SYS divider, in kilohms.
pub const SYS_DIVIDER_TOP_KOHM: u16 = 1000;
/// Lower resistance of the SYS divider, in kilohms.
pub const SYS_DIVIDER_BOTTOM_KOHM: u16 = 330;

/// Convert a calibrated 12-bit SAADC sample into SYS millivolts.
pub fn sys_mv_from_saadc(raw: i16) -> Option<u16> {
    let raw = u64::try_from(raw).ok()?;
    let adc_steps = 1_u64 << SAADC_RESOLUTION_BITS;
    let adc_full_scale_mv = u64::from(SAADC_REFERENCE_MV) * u64::from(SAADC_GAIN_RECIPROCAL);
    let divider_total = u64::from(SYS_DIVIDER_TOP_KOHM) + u64::from(SYS_DIVIDER_BOTTOM_KOHM);
    let numerator = raw * adc_full_scale_mv * divider_total;
    let denominator = adc_steps * u64::from(SYS_DIVIDER_BOTTOM_KOHM);
    u16::try_from((numerator + denominator / 2) / denominator).ok()
}

/// Maximum code from the 12-bit ratiometric panel-temperature sample.
pub const PANEL_TEMP_ADC_MAX: u16 = (1 << SAADC_RESOLUTION_BITS) - 1;

/// Acquisition time for the 10 kOhm panel-temperature divider.
pub const PANEL_TEMP_ACQUISITION_US: u8 = 40;

/// A panel-temperature divider reading that cannot represent a valid sensor.
#[derive(Clone, Copy, PartialEq, Eq, Debug)]
pub enum ThermistorFault {
    ShortCircuit,
    OpenCircuit,
}

// Expected 12-bit codes for a 10 kOhm high-side resistor and the
// NCP18XH103F03RB thermistor. Configure SAADC for the VDD/4 reference and 1/4
// gain so the measurement is ratiometric to the GPIO excitation voltage.
const PANEL_TEMP_TABLE: [(u16, i8); 19] = [
    (3613, -20),
    (3492, -15),
    (3353, -10),
    (3196, -5),
    (3024, 0),
    (2839, 5),
    (2644, 10),
    (2445, 15),
    (2245, 20),
    (2048, 25),
    (1857, 30),
    (1675, 35),
    (1505, 40),
    (1347, 45),
    (1203, 50),
    (1072, 55),
    (954, 60),
    (849, 65),
    (755, 70),
];

/// Convert a ratiometric panel-thermistor sample to degrees Celsius.
///
/// Drive `PANEL_TEMP_EXCITE` high only for the acquisition, sample AIN4 with
/// the VDD/4 reference and 1/4 gain, then drive the excitation pin low.
pub fn panel_temp_c_from_saadc(raw: u16) -> Result<i8, ThermistorFault> {
    const SHORT_MAX: u16 = 16;
    const OPEN_MIN: u16 = PANEL_TEMP_ADC_MAX - 16;

    if raw <= SHORT_MAX {
        return Err(ThermistorFault::ShortCircuit);
    }
    if raw >= OPEN_MIN {
        return Err(ThermistorFault::OpenCircuit);
    }
    if raw >= PANEL_TEMP_TABLE[0].0 {
        return Ok(PANEL_TEMP_TABLE[0].1);
    }
    if raw <= PANEL_TEMP_TABLE[PANEL_TEMP_TABLE.len() - 1].0 {
        return Ok(PANEL_TEMP_TABLE[PANEL_TEMP_TABLE.len() - 1].1);
    }

    for pair in PANEL_TEMP_TABLE.windows(2) {
        let (cold_raw, cold_c) = pair[0];
        let (warm_raw, warm_c) = pair[1];
        if raw <= cold_raw && raw >= warm_raw {
            let code_span = u32::from(cold_raw - warm_raw);
            let code_offset = u32::from(cold_raw - raw);
            let temp_span = u32::from((warm_c - cold_c) as u8);
            let interpolated = (code_offset * temp_span + code_span / 2) / code_span;
            return Ok(cold_c + interpolated as i8);
        }
    }

    unreachable!("the bounded ADC code falls within one table interval")
}

/// Estimate state of charge from a resting cell voltage.
pub fn soc_percent(mv: u16) -> u8 {
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

/// Return an SOC estimate only for a resting, battery-only sample.
pub fn resting_soc_percent(sys_mv: u16, qi_present: bool, charger: ChargerStatus) -> Option<u8> {
    if qi_present || charger != ChargerStatus::InputAbsent {
        None
    } else {
        Some(soc_percent(sys_mv))
    }
}

/// BLE connection parameters to request. The central can choose other values.
#[derive(Clone, Copy, PartialEq, Eq, Debug)]
pub struct ConnectionParameters {
    pub min_interval_1_25ms: u16,
    pub max_interval_1_25ms: u16,
    pub latency: u16,
    pub supervision_timeout_10ms: u16,
}

pub const fn connection_parameters(transfer_active: bool) -> ConnectionParameters {
    if transfer_active {
        ConnectionParameters {
            min_interval_1_25ms: 12,
            max_interval_1_25ms: 24,
            latency: 0,
            supervision_timeout_10ms: 400,
        }
    } else {
        ConnectionParameters {
            min_interval_1_25ms: 640,
            max_interval_1_25ms: 800,
            latency: 4,
            supervision_timeout_10ms: 600,
        }
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    fn safe_sample() -> PowerSample {
        PowerSample {
            sys_mv: 3800,
            qi_present: false,
            charger: ChargerStatus::InputAbsent,
            panel_temp_c: Some(22),
        }
    }

    #[test]
    fn charger_configuration_matches_pack_limits() {
        assert_eq!(REQUIRED_CHARGER_CONFIG.charge_ma, 40);
        assert_eq!(REQUIRED_CHARGER_CONFIG.input_limit_ma, 100);
        assert_eq!(REQUIRED_CHARGER_CONFIG.regulation_mv, 4200);
        assert_eq!(
            (
                REQUIRED_CHARGER_CONFIG.cold_c,
                REQUIRED_CHARGER_CONFIG.hot_c
            ),
            (0, 45)
        );
    }

    #[test]
    fn sys_conversion_matches_divider_configuration() {
        assert_eq!(sys_mv_from_saadc(-1), None);
        assert_eq!(sys_mv_from_saadc(0), Some(0));
        assert_eq!(sys_mv_from_saadc(1779), Some(4201));
    }

    #[test]
    fn panel_temperature_conversion_is_ratiometric_and_fault_aware() {
        assert_eq!(
            panel_temp_c_from_saadc(0),
            Err(ThermistorFault::ShortCircuit)
        );
        assert_eq!(
            panel_temp_c_from_saadc(PANEL_TEMP_ADC_MAX),
            Err(ThermistorFault::OpenCircuit)
        );
        assert_eq!(panel_temp_c_from_saadc(3024), Ok(0));
        assert_eq!(panel_temp_c_from_saadc(2048), Ok(25));
        assert_eq!(panel_temp_c_from_saadc(1203), Ok(50));
        assert_eq!(panel_temp_c_from_saadc(2932), Ok(2));
        assert_eq!(panel_temp_c_from_saadc(2931), Ok(3));
        assert_eq!(panel_temp_c_from_saadc(3500), Ok(-15));
        assert_eq!(panel_temp_c_from_saadc(700), Ok(70));
    }

    #[test]
    fn soc_clamps_and_interpolates() {
        assert_eq!(soc_percent(3000), 0);
        assert_eq!(soc_percent(3800), 50);
        assert_eq!(soc_percent(5000), 100);
    }

    #[test]
    fn soc_requires_a_resting_battery_only_sample() {
        assert_eq!(
            resting_soc_percent(3800, false, ChargerStatus::InputAbsent),
            Some(50)
        );
        assert_eq!(
            resting_soc_percent(4200, true, ChargerStatus::ChargeComplete),
            None
        );
        assert_eq!(
            resting_soc_percent(3900, false, ChargerStatus::Charging),
            None
        );
    }

    #[test]
    fn refresh_requires_voltage_temperature_and_idle_charger() {
        assert_eq!(refresh_decision(safe_sample(), EVT_SAFETY_LIMITS), Ok(()));

        let mut sample = safe_sample();
        sample.sys_mv = 3300;
        assert_eq!(
            refresh_decision(sample, EVT_SAFETY_LIMITS),
            Err(RefreshInhibit::LowVoltage)
        );

        sample = safe_sample();
        sample.panel_temp_c = None;
        assert_eq!(
            refresh_decision(sample, EVT_SAFETY_LIMITS),
            Err(RefreshInhibit::TemperatureUnavailable)
        );

        sample = safe_sample();
        sample.qi_present = true;
        sample.charger = ChargerStatus::ChargeComplete;
        assert_eq!(
            refresh_decision(sample, EVT_SAFETY_LIMITS),
            Err(RefreshInhibit::WirelessPower)
        );

        sample = safe_sample();
        sample.charger = ChargerStatus::Charging;
        assert_eq!(
            refresh_decision(sample, EVT_SAFETY_LIMITS),
            Err(RefreshInhibit::Charging)
        );

        sample = safe_sample();
        sample.charger = ChargerStatus::Fault;
        assert_eq!(
            refresh_decision(sample, EVT_SAFETY_LIMITS),
            Err(RefreshInhibit::ChargerFault)
        );
    }

    #[test]
    fn connection_parameters_cover_active_and_idle_states() {
        let active = connection_parameters(true);
        let idle = connection_parameters(false);
        assert!(active.min_interval_1_25ms <= active.max_interval_1_25ms);
        assert!(idle.min_interval_1_25ms <= idle.max_interval_1_25ms);
        assert!(active.max_interval_1_25ms < idle.min_interval_1_25ms);
        assert_eq!(active.latency, 0);
    }
}
