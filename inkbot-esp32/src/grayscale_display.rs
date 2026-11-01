//! UC8179 driver for the grayscale drive mode on the Waveshare 7.5″ V2.
//!
//! Two modes share one panel:
//!
//! - [`Panel::full_refresh_white`] is the factory waveform, with the same
//!   init and plane polarity `maze_display.rs` uses. It clears ghosting and
//!   resets the drive planner's model.
//! - [`Panel::init_drive`] loads the custom one-step tables from
//!   [`inkbot_esp32::grayscale::lut`] (panel setting `0x3F`, "LUT from
//!   registers", as in GxEPD2's fast partial mode). Each
//!   [`Panel::start_drive`] then runs one short refresh, and the caller
//!   plans the next one while the panel is busy.
//!
//! Drive mode leaves the panel powered between refreshes and polls BUSY
//! without the 100 ms settle and 10 ms poll steps the full-refresh path
//! uses, because at 20+ refreshes a second those delays would be most of
//! the budget.

use std::time::{Duration, Instant};

use anyhow::{anyhow, Context, Result};
use esp_idf_svc::hal::{
    delay::{Ets, FreeRtos},
    gpio::{Input, InputPin, Output, OutputPin, PinDriver, Pull},
    spi::{config, Dma, SpiAnyPins, SpiDeviceDriver, SpiDriver},
    units::FromValueType,
};

use inkbot_esp32::grayscale::lut::{
    DriveLuts, PANEL_SETTING_REGISTER_LUT, VCOM_DATA_INTERVAL, VCOM_DC,
};
use inkbot_esp32::FRAME_BYTES;

type BusyPin = PinDriver<'static, Input>;
type DcPin = PinDriver<'static, Output>;
type RstPin = PinDriver<'static, Output>;
type PanelSpi = SpiDeviceDriver<'static, SpiDriver<'static>>;

const CMD_PANEL_SETTING: u8 = 0x00;
const CMD_POWER_SETTING: u8 = 0x01;
const CMD_POWER_OFF: u8 = 0x02;
const CMD_POWER_ON: u8 = 0x04;
const CMD_BOOSTER: u8 = 0x06;
const CMD_DTM1: u8 = 0x10;
const CMD_REFRESH: u8 = 0x12;
const CMD_DTM2: u8 = 0x13;
const CMD_DUAL_SPI: u8 = 0x15;
const CMD_VCOM: u8 = 0x50;
const CMD_TCON: u8 = 0x60;
const CMD_RESOLUTION: u8 = 0x61;
const CMD_GET_STATUS: u8 = 0x71;
const CMD_VCOM_DC: u8 = 0x82;

/// SPI clock. `maze_display.rs` uses 4 MHz, at which one plane takes
/// 96 ms; 20 MHz brings that to about 19 ms. The UC8179's maximum serial
/// clock is not confirmed here: if the panel shows noise or ignores
/// commands, lower this.
pub const SPI_MHZ: u32 = 20;

/// Largest single DMA transfer. Without DMA, esp-idf-hal splits every
/// write into 64-byte transactions with a gap after each.
const DMA_TRANSFER_BYTES: usize = 4092;

/// Upper bound on one drive refresh before it counts as stuck.
const DRIVE_TIMEOUT: Duration = Duration::from_millis(500);

/// Owns the SPI bus + panel for the grayscale demo firmware.
pub struct Panel {
    spi: PanelSpi,
    busy: BusyPin,
    dc: DcPin,
    rst: RstPin,
}

impl Panel {
    /// Consume the Waveshare board's fixed display pins. Does not touch the
    /// panel; call [`Panel::full_refresh_white`] first.
    #[allow(clippy::too_many_arguments)]
    pub fn new<SPI, SCLK, MOSI, CS, BUSY, DC, RST>(
        spi: SPI,
        sclk: SCLK,
        mosi: MOSI,
        cs: CS,
        busy: BUSY,
        dc: DC,
        rst: RST,
    ) -> Result<Self>
    where
        SPI: SpiAnyPins + 'static,
        SCLK: OutputPin + 'static,
        MOSI: OutputPin + 'static,
        CS: OutputPin + 'static,
        BUSY: InputPin + 'static,
        DC: OutputPin + 'static,
        RST: OutputPin + 'static,
    {
        let spi_config = config::Config::new().baudrate(SPI_MHZ.MHz().into());
        let spi = SpiDeviceDriver::new_single(
            spi,
            sclk,
            mosi,
            Option::<BUSY>::None,
            Some(cs),
            &config::DriverConfig::new().dma(Dma::Auto(DMA_TRANSFER_BYTES)),
            &spi_config,
        )
        .context("configure e-paper SPI")?;

        let busy = PinDriver::input(busy, Pull::Floating).context("configure BUSY pin")?;
        let dc = PinDriver::output(dc).context("configure DC pin")?;
        let rst = PinDriver::output(rst).context("configure RST pin")?;

        Ok(Self { spi, busy, dc, rst })
    }

    /// Factory full refresh to white, using `maze_display.rs`'s init and
    /// plane polarity. Takes a few seconds. Leaves the panel in OTP mode:
    /// call [`Panel::init_drive`] before driving again.
    pub fn full_refresh_white(&mut self) -> Result<()> {
        self.init_full()?;
        let white = [0xFFu8; 1000];
        self.cmd(CMD_DTM1)?;
        for _ in 0..FRAME_BYTES / white.len() {
            self.data(&white)?;
        }
        self.cmd(CMD_DTM2)?;
        for _ in 0..FRAME_BYTES / white.len() {
            self.data(&[0x00; 1000])?;
        }
        self.cmd(CMD_REFRESH)?;
        FreeRtos::delay_ms(100);
        self.wait_idle_slow()
    }

    /// Reset the controller and load the custom drive tables. The old
    /// plane is undefined until the next [`Panel::write_old`].
    pub fn init_drive(&mut self, luts: &DriveLuts) -> Result<()> {
        self.hardware_reset();
        self.cmd_data(CMD_POWER_SETTING, &[0x07, 0x07, 0x3F, 0x3F])?;
        self.cmd_data(CMD_BOOSTER, &[0x17, 0x17, 0x28, 0x17])?;
        self.cmd(CMD_POWER_ON)?;
        FreeRtos::delay_ms(100);
        self.wait_idle_slow()?;
        self.cmd_data(CMD_PANEL_SETTING, &[PANEL_SETTING_REGISTER_LUT])?;
        self.cmd_data(CMD_RESOLUTION, &[0x03, 0x20, 0x01, 0xE0])?;
        self.cmd_data(CMD_DUAL_SPI, &[0x00])?;
        self.cmd_data(CMD_VCOM, &VCOM_DATA_INTERVAL)?;
        self.cmd_data(CMD_TCON, &[0x22])?;
        self.cmd_data(CMD_VCOM_DC, &[VCOM_DC])?;
        for (command, table) in &luts.registers {
            self.cmd_data(*command, table)?;
        }
        Ok(())
    }

    pub fn write_old(&mut self, plane: &[u8]) -> Result<()> {
        self.write_plane(CMD_DTM1, plane)
    }

    pub fn write_new(&mut self, plane: &[u8]) -> Result<()> {
        self.write_plane(CMD_DTM2, plane)
    }

    /// Start one drive refresh and return while the panel is busy.
    pub fn start_drive(&mut self) -> Result<()> {
        self.cmd(CMD_REFRESH)?;
        // Give BUSY time to assert before anyone polls it.
        Ets::delay_us(200);
        Ok(())
    }

    /// Wait for the refresh [`Panel::start_drive`] began.
    pub fn wait_drive(&mut self) -> Result<()> {
        let start = Instant::now();
        while self.busy.is_low() {
            if start.elapsed() > DRIVE_TIMEOUT {
                return Err(anyhow!("drive refresh busy timeout"));
            }
            Ets::delay_us(50);
        }
        Ok(())
    }

    /// Power the panel's drive voltages off.
    pub fn power_off(&mut self) -> Result<()> {
        self.cmd(CMD_POWER_OFF)?;
        self.wait_idle_slow()
    }

    fn write_plane(&mut self, command: u8, plane: &[u8]) -> Result<()> {
        if plane.len() != FRAME_BYTES {
            return Err(anyhow!(
                "plane must be {FRAME_BYTES} bytes, got {}",
                plane.len()
            ));
        }
        self.cmd(command)?;
        self.data(plane)
    }

    fn init_full(&mut self) -> Result<()> {
        self.hardware_reset();
        self.cmd_data(CMD_POWER_SETTING, &[0x07, 0x07, 0x3F, 0x3F])?;
        self.cmd_data(CMD_BOOSTER, &[0x17, 0x17, 0x28, 0x17])?;
        self.cmd(CMD_POWER_ON)?;
        FreeRtos::delay_ms(100);
        self.wait_idle_slow()?;
        self.cmd_data(CMD_PANEL_SETTING, &[0x1F])?;
        self.cmd_data(CMD_RESOLUTION, &[0x03, 0x20, 0x01, 0xE0])?;
        self.cmd_data(CMD_DUAL_SPI, &[0x00])?;
        self.cmd_data(CMD_VCOM, &[0x10, 0x07])?;
        self.cmd_data(CMD_TCON, &[0x22])?;
        Ok(())
    }

    fn hardware_reset(&mut self) {
        let _ = self.rst.set_high();
        Ets::delay_us(10_000);
        let _ = self.rst.set_low();
        Ets::delay_us(2_000);
        let _ = self.rst.set_high();
        FreeRtos::delay_ms(200);
    }

    fn wait_idle_slow(&mut self) -> Result<()> {
        let start = Instant::now();
        loop {
            self.cmd(CMD_GET_STATUS)?;
            FreeRtos::delay_ms(10);
            if !self.busy.is_low() {
                break;
            }
            if start.elapsed() > Duration::from_secs(15) {
                return Err(anyhow!("panel busy timeout"));
            }
        }
        FreeRtos::delay_ms(5);
        Ok(())
    }

    fn cmd(&mut self, command: u8) -> Result<()> {
        self.dc.set_low().map_err(|e| anyhow!("dc low: {e:?}"))?;
        self.spi
            .write(&[command])
            .map_err(|e| anyhow!("spi cmd {command:#04x}: {e:?}"))
    }

    fn data(&mut self, bytes: &[u8]) -> Result<()> {
        self.dc.set_high().map_err(|e| anyhow!("dc high: {e:?}"))?;
        self.spi
            .write(bytes)
            .map_err(|e| anyhow!("spi data {}B: {e:?}", bytes.len()))
    }

    fn cmd_data(&mut self, command: u8, bytes: &[u8]) -> Result<()> {
        self.cmd(command)?;
        self.data(bytes)
    }
}
