//! BQ25186 configuration values that must be written and read back while the
//! external `/CE` gate is still holding charging off.

pub const I2C_ADDRESS: u8 = 0x6a;

pub const REG_STAT0: u8 = 0x00;
pub const REG_STAT1: u8 = 0x01;
pub const REG_FLAG0: u8 = 0x02;
pub const REG_VBAT_CTRL: u8 = 0x03;
pub const REG_ICHG_CTRL: u8 = 0x04;
pub const REG_CHARGECTRL1: u8 = 0x06;
pub const REG_IC_CTRL: u8 = 0x07;
pub const REG_TMR_ILIM: u8 = 0x08;
pub const REG_SHIP_RST: u8 = 0x09;
pub const REG_TS_CONTROL: u8 = 0x0b;

pub const VBAT_4200_MV: u8 = 0x46;
pub const ICHG_40_MA_DISABLED: u8 = 0x9f;
pub const ICHG_40_MA_ENABLED: u8 = 0x1f;
/// Keep TS and the six-hour safety timer enabled, but disable the charger
/// watchdog. A charger watchdog reset would restore the 60 C hot threshold
/// while the MCU could still be holding Q2 on. The MCU watchdog instead resets
/// the GPIO and lets R6 turn Q2 off.
pub const IC_CTRL_TS_6H_NO_WATCHDOG: u8 = 0x87;
pub const ILIM_100_MA_WITH_RESET_DEFAULTS: u8 = 0x49;
pub const SHIP_MODE_WITH_RESET_DEFAULTS: u8 = 0x51;
pub const TS_COLD_0_HOT_45: u8 = 0xc0;
pub const BAT_OCP_500_MA_BUVLO_3V_INTERRUPTS: u8 = 0x10;

/// Maximum interval between safety-register readbacks while charging is on.
pub const SAFETY_READBACK_INTERVAL_MS: u32 = 30_000;

#[derive(Clone, Copy, PartialEq, Eq, Debug)]
pub struct RegisterWrite {
    pub register: u8,
    pub value: u8,
}

/// Safe write order while Q2 is off and R5 holds `/CE` high.
pub const CONFIGURATION_WRITES: [RegisterWrite; 7] = [
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
        register: REG_IC_CTRL,
        value: IC_CTRL_TS_6H_NO_WATCHDOG,
    },
    RegisterWrite {
        register: REG_CHARGECTRL1,
        value: BAT_OCP_500_MA_BUVLO_3V_INTERRUPTS,
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
    ic_ctrl: u8,
    tmr_ilim: u8,
    ts_control: u8,
    chargectrl1: u8,
) -> bool {
    vbat_ctrl == VBAT_4200_MV
        && ichg_ctrl == ICHG_40_MA_ENABLED
        && ic_ctrl == IC_CTRL_TS_6H_NO_WATCHDOG
        && tmr_ilim == ILIM_100_MA_WITH_RESET_DEFAULTS
        && ts_control == TS_COLD_0_HOT_45
        && chargectrl1 == BAT_OCP_500_MA_BUVLO_3V_INTERRUPTS
}

/// One readback of every safety-critical charger register.
#[derive(Clone, Copy, PartialEq, Eq, Debug)]
pub struct SafetyRegisters {
    pub vbat_ctrl: u8,
    pub ichg_ctrl: u8,
    pub ic_ctrl: u8,
    pub tmr_ilim: u8,
    pub ts_control: u8,
    pub chargectrl1: u8,
}

impl SafetyRegisters {
    pub const fn matches_required(self) -> bool {
        configuration_matches(
            self.vbat_ctrl,
            self.ichg_ctrl,
            self.ic_ctrl,
            self.tmr_ilim,
            self.ts_control,
            self.chargectrl1,
        )
    }
}

/// Current BQ25186 status registers. Read `STAT1` before read-to-clear flags.
#[derive(Clone, Copy, PartialEq, Eq, Debug)]
pub struct StatusRegisters {
    pub stat0: u8,
    pub stat1: u8,
    pub flag0: u8,
}

#[derive(Clone, Copy, PartialEq, Eq, Debug)]
pub enum SafetyFault {
    ConfigurationMismatch,
    ExternalPowerPresent,
    ThermistorOpenOrBatteryBelowHalt,
    InputOvervoltage,
    BatteryUndervoltage,
    BatteryOvercurrent,
    Temperature,
    SafetyTimer,
}

/// Minimal target-side operations needed for fail-closed charger control.
pub trait ChargerIo {
    type Error;

    /// Drive Q2. `false` must put the pin low and leave BQ25186 `/CE` high.
    fn set_charge_gate(&mut self, enabled: bool);
    fn write_register(&mut self, register: u8, value: u8) -> Result<(), Self::Error>;
    fn read_register(&mut self, register: u8) -> Result<u8, Self::Error>;
}

#[derive(PartialEq, Eq, Debug)]
pub enum ChargerControlError<E> {
    Bus(E),
    Safety(SafetyFault),
}

impl StatusRegisters {
    /// Return the first condition that requires the external charge gate off.
    pub const fn safety_fault(self) -> Option<SafetyFault> {
        if self.stat0 & 0x80 != 0 {
            Some(SafetyFault::ThermistorOpenOrBatteryBelowHalt)
        } else if self.stat1 & 0x80 != 0 {
            Some(SafetyFault::InputOvervoltage)
        } else if self.stat1 & 0x40 != 0 {
            Some(SafetyFault::BatteryUndervoltage)
        } else if self.stat1 & 0x18 != 0 {
            Some(SafetyFault::Temperature)
        } else if self.stat1 & 0x04 != 0 {
            Some(SafetyFault::SafetyTimer)
        } else if self.flag0 & 0x80 != 0 || self.flag0 & 0x08 != 0 {
            Some(SafetyFault::Temperature)
        } else if self.flag0 & 0x04 != 0 {
            Some(SafetyFault::InputOvervoltage)
        } else if self.flag0 & 0x02 != 0 {
            Some(SafetyFault::BatteryUndervoltage)
        } else if self.flag0 & 0x01 != 0 {
            Some(SafetyFault::BatteryOvercurrent)
        } else {
            None
        }
    }

    const fn charge_state(self) -> u8 {
        (self.stat0 >> 5) & 0x03
    }

    const fn input_power_good(self) -> bool {
        self.stat0 & 0x01 != 0
    }
}

/// State retained only while the external Q2 charge gate is on.
#[derive(Clone, Copy, PartialEq, Eq, Debug)]
pub struct EnabledCharger {
    last_verified_ms: u32,
    saw_charging: bool,
}

impl EnabledCharger {
    /// Authorize Q2 only after a complete readback and fault check.
    pub const fn authorize(
        now_ms: u32,
        safety: SafetyRegisters,
        status: StatusRegisters,
    ) -> Result<Self, SafetyFault> {
        if !safety.matches_required() {
            return Err(SafetyFault::ConfigurationMismatch);
        }
        if let Some(fault) = status.safety_fault() {
            return Err(fault);
        }
        Ok(Self {
            last_verified_ms: now_ms,
            saw_charging: false,
        })
    }

    /// Return `true` when the periodic safety readback is due.
    pub const fn readback_due(self, now_ms: u32) -> bool {
        now_ms.wrapping_sub(self.last_verified_ms) >= SAFETY_READBACK_INTERVAL_MS
    }

    /// Accept a periodic readback or return the fault that requires Q2 off.
    ///
    /// Consume `self` so a failed check cannot leave an enabled token behind.
    pub const fn verify(
        self,
        now_ms: u32,
        safety: SafetyRegisters,
        status: StatusRegisters,
    ) -> Result<Self, SafetyFault> {
        if !safety.matches_required() {
            return Err(SafetyFault::ConfigurationMismatch);
        }
        if let Some(fault) = status.safety_fault() {
            return Err(fault);
        }
        let state = status.charge_state();
        Ok(Self {
            last_verified_ms: now_ms,
            saw_charging: self.saw_charging || state == 1 || state == 2,
        })
    }

    /// Return `true` only after this power session has observed active charging.
    pub const fn charge_complete(self, status: StatusRegisters) -> bool {
        self.saw_charging
            && status.safety_fault().is_none()
            && status.input_power_good()
            && status.charge_state() == 3
    }
}

/// Configure, read back, and then enable the external charge gate.
pub fn configure<I: ChargerIo>(
    io: &mut I,
    now_ms: u32,
) -> Result<EnabledCharger, ChargerControlError<I::Error>> {
    io.set_charge_gate(false);
    for write in CONFIGURATION_WRITES {
        if let Err(error) = io.write_register(write.register, write.value) {
            io.set_charge_gate(false);
            return Err(ChargerControlError::Bus(error));
        }
    }
    let (safety, status) = match read_safety(io) {
        Ok(readback) => readback,
        Err(error) => {
            io.set_charge_gate(false);
            return Err(ChargerControlError::Bus(error));
        }
    };
    let enabled = match EnabledCharger::authorize(now_ms, safety, status) {
        Ok(enabled) => enabled,
        Err(fault) => {
            io.set_charge_gate(false);
            return Err(ChargerControlError::Safety(fault));
        }
    };
    io.set_charge_gate(true);
    Ok(enabled)
}

/// Recheck an enabled charger when its periodic deadline expires.
///
/// Any bus or safety error drops the external gate before returning.
pub fn revalidate<I: ChargerIo>(
    io: &mut I,
    enabled: EnabledCharger,
    now_ms: u32,
) -> Result<EnabledCharger, ChargerControlError<I::Error>> {
    if !enabled.readback_due(now_ms) {
        return Ok(enabled);
    }
    let (safety, status) = match read_safety(io) {
        Ok(readback) => readback,
        Err(error) => {
            io.set_charge_gate(false);
            return Err(ChargerControlError::Bus(error));
        }
    };
    match enabled.verify(now_ms, safety, status) {
        Ok(enabled) => Ok(enabled),
        Err(fault) => {
            io.set_charge_gate(false);
            Err(ChargerControlError::Safety(fault))
        }
    }
}

/// Disable charging and enter the BQ25186 ship mode for storage or transport.
///
/// The caller must confirm that Qi input is absent. Valid input power exits
/// ship mode immediately.
pub fn enter_ship_mode<I: ChargerIo>(
    io: &mut I,
    qi_present: bool,
) -> Result<(), ChargerControlError<I::Error>> {
    io.set_charge_gate(false);
    if qi_present {
        return Err(ChargerControlError::Safety(
            SafetyFault::ExternalPowerPresent,
        ));
    }
    for write in [
        RegisterWrite {
            register: REG_ICHG_CTRL,
            value: ICHG_40_MA_DISABLED,
        },
        RegisterWrite {
            register: REG_SHIP_RST,
            value: SHIP_MODE_WITH_RESET_DEFAULTS,
        },
    ] {
        if let Err(error) = io.write_register(write.register, write.value) {
            io.set_charge_gate(false);
            return Err(ChargerControlError::Bus(error));
        }
    }
    Ok(())
}

fn read_safety<I: ChargerIo>(io: &mut I) -> Result<(SafetyRegisters, StatusRegisters), I::Error> {
    let safety = SafetyRegisters {
        vbat_ctrl: io.read_register(REG_VBAT_CTRL)?,
        ichg_ctrl: io.read_register(REG_ICHG_CTRL)?,
        ic_ctrl: io.read_register(REG_IC_CTRL)?,
        tmr_ilim: io.read_register(REG_TMR_ILIM)?,
        ts_control: io.read_register(REG_TS_CONTROL)?,
        chargectrl1: io.read_register(REG_CHARGECTRL1)?,
    };
    let status = StatusRegisters {
        stat0: io.read_register(REG_STAT0)?,
        stat1: io.read_register(REG_STAT1)?,
        flag0: io.read_register(REG_FLAG0)?,
    };
    Ok((safety, status))
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
        let required = required_registers();
        assert!(required.matches_required());
        for wrong in [
            SafetyRegisters {
                vbat_ctrl: 0,
                ..required
            },
            SafetyRegisters {
                ichg_ctrl: 0,
                ..required
            },
            SafetyRegisters {
                ic_ctrl: 0,
                ..required
            },
            SafetyRegisters {
                tmr_ilim: 0,
                ..required
            },
            SafetyRegisters {
                ts_control: 0,
                ..required
            },
            SafetyRegisters {
                chargectrl1: 0,
                ..required
            },
        ] {
            assert!(!wrong.matches_required());
        }
    }

    fn required_registers() -> SafetyRegisters {
        SafetyRegisters {
            vbat_ctrl: VBAT_4200_MV,
            ichg_ctrl: ICHG_40_MA_ENABLED,
            ic_ctrl: IC_CTRL_TS_6H_NO_WATCHDOG,
            tmr_ilim: ILIM_100_MA_WITH_RESET_DEFAULTS,
            ts_control: TS_COLD_0_HOT_45,
            chargectrl1: BAT_OCP_500_MA_BUVLO_3V_INTERRUPTS,
        }
    }

    fn status(charge_state: u8) -> StatusRegisters {
        StatusRegisters {
            stat0: (charge_state << 5) | 1,
            stat1: 0,
            flag0: 0,
        }
    }

    #[test]
    fn charge_gate_requires_configuration_and_fault_free_status() {
        let mut wrong = required_registers();
        wrong.ts_control = 0;
        assert_eq!(
            EnabledCharger::authorize(0, wrong, status(0)),
            Err(SafetyFault::ConfigurationMismatch)
        );
        assert_eq!(
            EnabledCharger::authorize(
                0,
                required_registers(),
                StatusRegisters {
                    stat0: 0,
                    stat1: 0x04,
                    flag0: 0,
                }
            ),
            Err(SafetyFault::SafetyTimer)
        );
        assert!(EnabledCharger::authorize(0, required_registers(), status(0)).is_ok());
    }

    #[test]
    fn periodic_readback_consumes_enabled_state_on_failure() {
        let enabled = EnabledCharger::authorize(10, required_registers(), status(0)).unwrap();
        assert!(!enabled.readback_due(30_009));
        assert!(enabled.readback_due(30_010));

        let mut reset = required_registers();
        reset.ic_ctrl = 0x84;
        assert_eq!(
            enabled.verify(30_010, reset, status(1)),
            Err(SafetyFault::ConfigurationMismatch)
        );
    }

    #[test]
    fn charge_complete_requires_observed_charging() {
        let enabled = EnabledCharger::authorize(0, required_registers(), status(3)).unwrap();
        assert!(!enabled.charge_complete(status(3)));
        let enabled = enabled
            .verify(100, required_registers(), status(1))
            .unwrap();
        assert!(!enabled.charge_complete(status(1)));
        let enabled = enabled
            .verify(200, required_registers(), status(3))
            .unwrap();
        assert!(enabled.charge_complete(status(3)));
    }

    #[test]
    fn every_live_fault_disables_charging() {
        let cases = [
            (
                0x80,
                0x00,
                0x00,
                SafetyFault::ThermistorOpenOrBatteryBelowHalt,
            ),
            (0x00, 0x80, 0x00, SafetyFault::InputOvervoltage),
            (0x00, 0x40, 0x00, SafetyFault::BatteryUndervoltage),
            (0x00, 0x08, 0x00, SafetyFault::Temperature),
            (0x00, 0x04, 0x00, SafetyFault::SafetyTimer),
            (0x00, 0x00, 0x80, SafetyFault::Temperature),
            (0x00, 0x00, 0x08, SafetyFault::Temperature),
            (0x00, 0x00, 0x04, SafetyFault::InputOvervoltage),
            (0x00, 0x00, 0x02, SafetyFault::BatteryUndervoltage),
            (0x00, 0x00, 0x01, SafetyFault::BatteryOvercurrent),
        ];
        for (stat0, stat1, flag0, expected) in cases {
            let enabled = EnabledCharger::authorize(0, required_registers(), status(1)).unwrap();
            assert_eq!(
                enabled.verify(
                    1,
                    required_registers(),
                    StatusRegisters {
                        stat0,
                        stat1,
                        flag0,
                    }
                ),
                Err(expected)
            );
        }
    }

    struct MockIo {
        registers: [u8; 12],
        writes: std::vec::Vec<RegisterWrite>,
        gates: std::vec::Vec<bool>,
        fail_operation: Option<usize>,
        operation: usize,
    }

    impl MockIo {
        fn healthy() -> Self {
            let mut registers = [0; 12];
            registers[REG_VBAT_CTRL as usize] = VBAT_4200_MV;
            registers[REG_ICHG_CTRL as usize] = ICHG_40_MA_ENABLED;
            registers[REG_IC_CTRL as usize] = IC_CTRL_TS_6H_NO_WATCHDOG;
            registers[REG_TMR_ILIM as usize] = ILIM_100_MA_WITH_RESET_DEFAULTS;
            registers[REG_TS_CONTROL as usize] = TS_COLD_0_HOT_45;
            registers[REG_CHARGECTRL1 as usize] =
                BAT_OCP_500_MA_BUVLO_3V_INTERRUPTS;
            Self {
                registers,
                writes: std::vec::Vec::new(),
                gates: std::vec::Vec::new(),
                fail_operation: None,
                operation: 0,
            }
        }

        fn fail_if_requested(&mut self) -> Result<(), u8> {
            let operation = self.operation;
            self.operation += 1;
            if self.fail_operation == Some(operation) {
                Err(operation as u8)
            } else {
                Ok(())
            }
        }
    }

    impl ChargerIo for MockIo {
        type Error = u8;

        fn set_charge_gate(&mut self, enabled: bool) {
            self.gates.push(enabled);
        }

        fn write_register(&mut self, register: u8, value: u8) -> Result<(), Self::Error> {
            self.fail_if_requested()?;
            self.registers[register as usize] = value;
            self.writes.push(RegisterWrite { register, value });
            Ok(())
        }

        fn read_register(&mut self, register: u8) -> Result<u8, Self::Error> {
            self.fail_if_requested()?;
            Ok(self.registers[register as usize])
        }
    }

    #[test]
    fn configure_keeps_gate_off_until_ordered_writes_and_readback_finish() {
        let mut io = MockIo::healthy();
        let enabled = configure(&mut io, 100).unwrap();
        assert_eq!(io.writes, CONFIGURATION_WRITES);
        assert_eq!(io.gates, [false, true]);
        assert!(!enabled.readback_due(30_099));
    }

    #[test]
    fn every_configuration_bus_failure_leaves_gate_off() {
        let operation_count = CONFIGURATION_WRITES.len() + 8;
        for failing_operation in 0..operation_count {
            let mut io = MockIo::healthy();
            io.fail_operation = Some(failing_operation);
            assert!(matches!(
                configure(&mut io, 0),
                Err(ChargerControlError::Bus(_))
            ));
            assert_eq!(io.gates.first(), Some(&false));
            assert_eq!(io.gates.last(), Some(&false));
            assert!(!io.gates.contains(&true));
        }
    }

    #[test]
    fn ship_mode_requires_detachment_and_orders_safe_writes() {
        let mut attached = MockIo::healthy();
        assert_eq!(
            enter_ship_mode(&mut attached, true),
            Err(ChargerControlError::Safety(
                SafetyFault::ExternalPowerPresent
            ))
        );
        assert_eq!(attached.gates, [false]);
        assert!(attached.writes.is_empty());

        let mut detached = MockIo::healthy();
        enter_ship_mode(&mut detached, false).unwrap();
        assert_eq!(detached.gates, [false]);
        assert_eq!(
            detached.writes,
            [
                RegisterWrite {
                    register: REG_ICHG_CTRL,
                    value: ICHG_40_MA_DISABLED,
                },
                RegisterWrite {
                    register: REG_SHIP_RST,
                    value: SHIP_MODE_WITH_RESET_DEFAULTS,
                },
            ]
        );
    }

    #[test]
    fn ship_mode_bus_failures_leave_charge_gate_off() {
        for failing_operation in 0..2 {
            let mut io = MockIo::healthy();
            io.fail_operation = Some(failing_operation);
            assert!(matches!(
                enter_ship_mode(&mut io, false),
                Err(ChargerControlError::Bus(_))
            ));
            assert_eq!(io.gates.first(), Some(&false));
            assert_eq!(io.gates.last(), Some(&false));
            assert!(!io.gates.contains(&true));
        }
    }

    #[test]
    fn periodic_bus_or_register_failure_drops_gate() {
        let mut io = MockIo::healthy();
        let enabled = configure(&mut io, 0).unwrap();
        io.gates.clear();
        io.operation = 0;
        io.fail_operation = Some(3);
        assert!(matches!(
            revalidate(&mut io, enabled, SAFETY_READBACK_INTERVAL_MS),
            Err(ChargerControlError::Bus(_))
        ));
        assert_eq!(io.gates, [false]);

        let mut io = MockIo::healthy();
        let enabled = configure(&mut io, 0).unwrap();
        io.gates.clear();
        io.registers[REG_TS_CONTROL as usize] = 0;
        assert_eq!(
            revalidate(&mut io, enabled, SAFETY_READBACK_INTERVAL_MS),
            Err(ChargerControlError::Safety(
                SafetyFault::ConfigurationMismatch
            ))
        );
        assert_eq!(io.gates, [false]);
    }
}
