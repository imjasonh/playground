//! Board Support Packages (BSPs) and hardware capability traits.
//!
//! Each board owns its silicon metadata ([`BoardSpec`]), pinout, peripheral
//! initialization, power/battery reporting, and default sleep cadence. Apps
//! depend only on [`Board`] plus whichever capability traits ([`HasEpd75`],
//! [`HasLogicProbe`]) they require — never on raw GPIO pin numbers.

use anyhow::Result;
use esp_idf_svc::hal::peripherals::Peripherals;

use crate::epd_display::Panel;
use crate::platform::RunMode;
use crate::protocol::BoardSpec;

#[cfg(target_arch = "riscv32")]
pub mod xiao_esp32c3;

#[cfg(target_arch = "xtensa")]
pub mod waveshare_epd75;

/// Hardware board abstraction implemented once per physical board / pinout.
pub trait Board: Sized {
    /// Static board metadata (ID, chip, GAP name, CPU MHz, battery OTA threshold).
    const SPEC: BoardSpec;

    /// Default execution cadence for idle / base apps on this board.
    fn default_run_mode() -> RunMode;

    /// Take ownership of the SoC peripherals and initialize board hardware.
    fn init(peripherals: Peripherals) -> Result<Self>;

    /// Hardware self-test run once while booting a `PENDING_VERIFY` OTA slot.
    fn self_test(&mut self) -> Result<()> {
        Ok(())
    }

    /// Read or report the current supply / battery rail voltage in millivolts.
    fn read_battery_mv(&mut self) -> u16;

    /// Optional extra low-nibble advertisement flags describing attached hardware
    /// (e.g., `FLAG_EPD_ATTACHED`).
    fn hardware_flags(&self) -> u8 {
        0
    }
}

/// Capability trait for boards wired to a Waveshare 7.5″ 800×480 e-Paper panel.
pub trait HasEpd75 {
    fn panel(&mut self) -> &mut Panel;
}

/// Capability trait for boards with a GPIO logic-marker pin for PPK2 / scope correlation.
pub trait HasLogicProbe {
    fn measure_phase<T>(&mut self, f: impl FnOnce() -> T) -> Result<(T, u32)>;
}
