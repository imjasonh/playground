//! Waveshare e-Paper ESP32 Driver Board (classic ESP32 + 7.5″ 800×480 UC8179) BSP.

use anyhow::Result;
use esp_idf_svc::hal::peripherals::Peripherals;

use crate::boards::{Board, HasEpd75};
use crate::epd_display::Panel;
use crate::platform::RunMode;
use crate::protocol::{BoardSpec, BOARD_WAVESHARE_EPD75, CHIP_ID_ESP32, FLAG_EPD_ATTACHED};

/// Nominal USB rail voltage reported in `battery_mv` (5.0 V USB-powered board).
const USB_RAIL_MV: u16 = 5000;

/// Waveshare e-Paper ESP32 Driver Board wired to a 7.5″ 800×480 UC8179 display.
pub struct WaveshareEpd75 {
    panel: Panel,
}

impl Board for WaveshareEpd75 {
    const SPEC: BoardSpec = BoardSpec {
        board_id: BOARD_WAVESHARE_EPD75,
        board: "waveshare-epd75",
        chip: "esp32",
        gap_name: "EPD-75",
        chip_id: CHIP_ID_ESP32,
        cpu_mhz: 240,
        min_ota_battery_mv: 0, // USB-powered board
    };

    fn default_run_mode() -> RunMode {
        RunMode::Continuous {
            burst_ms: 500,
            min_step_ms: 2_000,
        }
    }

    fn init(peripherals: Peripherals) -> Result<Self> {
        let panel = Panel::new(
            peripherals.spi2,
            peripherals.pins.gpio13,
            peripherals.pins.gpio14,
            peripherals.pins.gpio15,
            peripherals.pins.gpio25,
            peripherals.pins.gpio27,
            peripherals.pins.gpio26,
        )?;
        Ok(Self { panel })
    }

    fn read_battery_mv(&mut self) -> u16 {
        USB_RAIL_MV
    }

    fn hardware_flags(&self) -> u8 {
        FLAG_EPD_ATTACHED
    }
}

impl HasEpd75 for WaveshareEpd75 {
    fn panel(&mut self) -> &mut Panel {
        &mut self.panel
    }
}
