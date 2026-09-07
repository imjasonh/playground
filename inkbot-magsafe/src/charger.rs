//! BQ25186 configuration values that must be written and read back while the
//! external `/CE` gate is still holding charging off.

pub const I2C_ADDRESS: u8 = 0x6a;

pub const REG_VBAT_CTRL: u8 = 0x03;
pub const REG_ICHG_CTRL: u8 = 0x04;
pub const REG_TMR_ILIM: u8 = 0x08;
pub const REG_TS_CONTROL: u8 = 0x0b;

pub const VBAT_4200_MV: u8 = 0x46;
pub const ICHG_40_MA_DISABLED: u8 = 0x9f;
pub const ICHG_40_MA_ENABLED: u8 = 0x1f;
pub const ILIM_100_MA_WITH_RESET_DEFAULTS: u8 = 0x49;
pub const TS_COLD_0_HOT_45: u8 = 0xc0;

#[derive(Clone, Copy, PartialEq, Eq, Debug)]
pub struct RegisterWrite {
    pub register: u8,
    pub value: u8,
}

/// Safe write order while Q2 is off and R5 holds `/CE` high.
pub const CONFIGURATION_WRITES: [RegisterWrite; 5] = [
    RegisterWrite {
        register: REG_ICHG_CTRL,
        value: ICHG_40_MA_DISABLED,
    },
    RegisterWrite {
        register: REG_VBAT_CTRL,
        value: VBAT_4200_MV,
    },
    RegisterWrite {
        register: REG_TMR_ILIM,
        value: ILIM_100_MA_WITH_RESET_DEFAULTS,
    },
    RegisterWrite {
        register: REG_TS_CONTROL,
        value: TS_COLD_0_HOT_45,
    },
    RegisterWrite {
        register: REG_ICHG_CTRL,
        value: ICHG_40_MA_ENABLED,
    },
];

/// Verify the safety-critical register values before driving Q2 high.
pub const fn configuration_matches(
    vbat_ctrl: u8,
    ichg_ctrl: u8,
    tmr_ilim: u8,
    ts_control: u8,
) -> bool {
    vbat_ctrl == VBAT_4200_MV
        && ichg_ctrl == ICHG_40_MA_ENABLED
        && tmr_ilim == ILIM_100_MA_WITH_RESET_DEFAULTS
        && ts_control == TS_COLD_0_HOT_45
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn write_sequence_disables_charge_before_other_registers() {
        assert_eq!(
            CONFIGURATION_WRITES[0],
            RegisterWrite {
                register: REG_ICHG_CTRL,
                value: ICHG_40_MA_DISABLED
            }
        );
        assert_eq!(
            CONFIGURATION_WRITES[CONFIGURATION_WRITES.len() - 1],
            RegisterWrite {
                register: REG_ICHG_CTRL,
                value: ICHG_40_MA_ENABLED
            }
        );
    }

    #[test]
    fn readback_requires_every_safety_value() {
        assert!(configuration_matches(0x46, 0x1f, 0x49, 0xc0));
        assert!(!configuration_matches(0x46, 0x1f, 0x4d, 0xc0));
        assert!(!configuration_matches(0x46, 0x1f, 0x49, 0x00));
    }
}
