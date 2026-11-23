//! Universal `BaseApp` — minimal OTA-ready + OTel-reporting bootstrap firmware
//! that runs on any [`Board`].
//!
//! Flash once over USB (`make flash-all BOARD=<board> APP=base`), then push
//! feature apps (`maze`, `bench`, etc.) wirelessly over BLE GATT OTA.

use anyhow::Result;

use crate::boards::Board;
use crate::platform::{App, StepContext, StepOutput};
use crate::protocol::BASE_FIRMWARE_ID;

/// Minimal idle/bootstrap application that works on every board.
pub struct BaseApp;

impl<B: Board> App<B> for BaseApp {
    const APP_NAME: &'static str = "base";
    const FIRMWARE_ID: &'static str = BASE_FIRMWARE_ID;

    fn init(_board: &mut B) -> Result<Self> {
        Ok(Self)
    }

    fn step(&mut self, board: &mut B, ctx: &mut StepContext<'_>) -> Result<StepOutput> {
        let (battery_mv, sensor_us) =
            ctx.measure_span("base.read_battery", "sensor", || board.read_battery_mv());
        Ok(StepOutput {
            sensor_us,
            compute_us: 0,
            epd_refresh_us: 0,
            battery_mv,
            flags: 0,
            post_burst_delay_ms: 0,
        })
    }
}
