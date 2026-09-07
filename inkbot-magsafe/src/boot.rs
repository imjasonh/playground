//! Early-boot policy for the nRF52833 high-voltage regulator.
//!
//! UICR writes can only clear bits until the device is erased. The application
//! can program an erased `REGOUT0` field once, but it must reject a different
//! programmed voltage instead of attempting an unsafe in-place rewrite.

/// Address of `UICR.REGOUT0` on the nRF52833.
pub const REGOUT0_ADDRESS: usize = 0x1000_1304;

/// `REGOUT0.VOUT` occupies bits 0 through 2.
pub const REGOUT0_VOUT_MASK: u32 = 0b111;

/// Encoding for a 3.0 V REG0 output.
pub const REGOUT0_3V0: u32 = 0b100;

/// Action required before any GPIO or panel peripheral is configured.
#[derive(Clone, Copy, PartialEq, Eq, Debug)]
pub enum RegoutPlan {
    /// The persistent setting already selects 3.0 V.
    Ready,
    /// Program this complete register value, restore read mode, and reset.
    ProgramAndReset(u32),
    /// Another voltage is already programmed and requires SWD recovery.
    Reject,
}

/// Determine how early boot must handle the current UICR register value.
pub const fn plan_regout0(current: u32) -> RegoutPlan {
    match current & REGOUT0_VOUT_MASK {
        REGOUT0_3V0 => RegoutPlan::Ready,
        REGOUT0_VOUT_MASK => {
            RegoutPlan::ProgramAndReset((current & !REGOUT0_VOUT_MASK) | REGOUT0_3V0)
        }
        _ => RegoutPlan::Reject,
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn erased_uicr_is_programmed_without_clearing_reserved_bits() {
        assert_eq!(
            plan_regout0(u32::MAX),
            RegoutPlan::ProgramAndReset(0xFFFF_FFFC)
        );
    }

    #[test]
    fn configured_uicr_continues() {
        assert_eq!(plan_regout0(0xFFFF_FFFC), RegoutPlan::Ready);
    }

    #[test]
    fn another_programmed_voltage_requires_an_erase() {
        assert_eq!(plan_regout0(0xFFFF_FFF8), RegoutPlan::Reject);
        assert_eq!(plan_regout0(0xFFFF_FFFD), RegoutPlan::Reject);
    }
}
