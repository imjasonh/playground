//! Waveshare 7.5″ V2 (UC8179) driver with full and partial refresh.
//!
//! Pin map matches `display.rs` (Waveshare ESP32 driver board). Full refresh
//! copies the DTM1/DTM2 polarity that inkbot already uses. Partial refresh
//! follows Waveshare's `Init_Part` + `Display_Partial` sequence; the pinned
//! `epd-waveshare` crate leaves `update_partial_frame` unimplemented.

use anyhow::{anyhow, Context, Result};
use esp_idf_svc::hal::{
    delay::{Ets, FreeRtos},
    gpio::{Input, InputPin, Output, OutputPin, PinDriver, Pull},
    spi::{config, SpiAnyPins, SpiDeviceDriver, SpiDriver},
    units::FromValueType,
};

use inkbot_esp32::maze::ByteRect;
use inkbot_esp32::{FRAME_BYTES, PANEL_HEIGHT, PANEL_WIDTH};

type BusyPin = PinDriver<'static, Input>;
type DcPin = PinDriver<'static, Output>;
type RstPin = PinDriver<'static, Output>;
type PanelSpi = SpiDeviceDriver<'static, SpiDriver<'static>>;

const CMD_PANEL_SETTING: u8 = 0x00;
const CMD_POWER_SETTING: u8 = 0x01;
const CMD_POWER_OFF: u8 = 0x02;
const CMD_POWER_ON: u8 = 0x04;
const CMD_BOOSTER: u8 = 0x06;
const CMD_DEEP_SLEEP: u8 = 0x07;
const CMD_DTM1: u8 = 0x10;
const CMD_REFRESH: u8 = 0x12;
const CMD_DTM2: u8 = 0x13;
const CMD_DUAL_SPI: u8 = 0x15;
const CMD_VCOM: u8 = 0x50;
const CMD_TCON: u8 = 0x60;
const CMD_RESOLUTION: u8 = 0x61;
const CMD_GET_STATUS: u8 = 0x71;
const CMD_PARTIAL_IN: u8 = 0x91;
const CMD_PARTIAL_WINDOW: u8 = 0x90;
const CMD_TEMP_SEL: u8 = 0xE0;
const CMD_TEMP_LUT: u8 = 0xE5;

/// Owns the SPI bus + panel for the maze firmware.
pub struct Panel {
    spi: PanelSpi,
    busy: BusyPin,
    dc: DcPin,
    rst: RstPin,
}

impl Panel {
    /// Consume the Waveshare board's fixed display pins and bring the panel up.
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
        let spi_config = config::Config::new().baudrate(4_u32.MHz().into());
        let spi = SpiDeviceDriver::new_single(
            spi,
            sclk,
            mosi,
            Option::<BUSY>::None,
            Some(cs),
            &config::DriverConfig::new(),
            &spi_config,
        )
        .context("configure e-paper SPI")?;

        let busy = PinDriver::input(busy, Pull::Floating).context("configure BUSY pin")?;
        let dc = PinDriver::output(dc).context("configure DC pin")?;
        let rst = PinDriver::output(rst).context("configure RST pin")?;

        let mut panel = Self { spi, busy, dc, rst };
        panel.init_full()?;
        Ok(panel)
    }

    /// Full-refresh a packed 1-bit framebuffer (MSB first, 1 = white). Leaves
    /// the panel awake so the next call can be a partial update.
    pub fn show_frame_awake(&mut self, frame: &[u8]) -> Result<()> {
        if frame.len() != FRAME_BYTES {
            return Err(anyhow!(
                "framebuffer must be {FRAME_BYTES} bytes, got {}",
                frame.len()
            ));
        }
        self.init_full()?;
        self.cmd(CMD_DTM1)?;
        self.data(frame)?;
        self.cmd(CMD_DTM2)?;
        self.data_inverted(frame)?;
        self.refresh()?;
        Ok(())
    }

    /// Switch to Waveshare's partial-refresh LUT (temperature-select hack).
    pub fn enter_partial_mode(&mut self) -> Result<()> {
        self.init_part()
    }

    /// Partial-refresh `window`, which must be a byte-aligned crop of a full frame.
    ///
    /// DTM2 gets the packed 1-bit crop as-is (1 = white), matching Waveshare's
    /// C `Display_Part` after a 1=white buffer.
    pub fn show_partial(&mut self, window: &[u8], rect: ByteRect) -> Result<()> {
        if window.len() != rect.byte_count() {
            return Err(anyhow!(
                "partial window must be {} bytes, got {}",
                rect.byte_count(),
                window.len()
            ));
        }
        if rect.x % 8 != 0 || rect.width % 8 != 0 || rect.width == 0 || rect.height == 0 {
            return Err(anyhow!(
                "partial rect must be byte-aligned and non-empty, got {rect:?}"
            ));
        }
        if rect.x + rect.width > PANEL_WIDTH || rect.y + rect.height > PANEL_HEIGHT {
            return Err(anyhow!(
                "partial rect {rect:?} exceeds {PANEL_WIDTH}x{PANEL_HEIGHT}"
            ));
        }

        let x_end = rect.x + rect.width - 1;
        let y_end = rect.y + rect.height - 1;
        self.cmd_data(CMD_VCOM, &[0xA9, 0x07])?;
        self.cmd(CMD_PARTIAL_IN)?;
        self.cmd_data(
            CMD_PARTIAL_WINDOW,
            &[
                (rect.x >> 8) as u8,
                rect.x as u8,
                (x_end >> 8) as u8,
                x_end as u8,
                (rect.y >> 8) as u8,
                rect.y as u8,
                (y_end >> 8) as u8,
                y_end as u8,
                0x01,
            ],
        )?;
        self.cmd(CMD_DTM2)?;
        self.data(window)?;
        self.refresh()?;
        Ok(())
    }

    /// Power the panel down until the next `show_frame_awake`.
    pub fn sleep(&mut self) -> Result<()> {
        self.wait_idle()?;
        self.cmd_data(CMD_VCOM, &[0xF7])?;
        self.cmd(CMD_POWER_OFF)?;
        self.wait_idle()?;
        self.cmd_data(CMD_DEEP_SLEEP, &[0xA5])?;
        Ok(())
    }

    fn init_full(&mut self) -> Result<()> {
        self.hardware_reset();
        self.cmd_data(CMD_POWER_SETTING, &[0x07, 0x07, 0x3F, 0x3F])?;
        self.cmd_data(CMD_BOOSTER, &[0x17, 0x17, 0x28, 0x17])?;
        self.cmd(CMD_POWER_ON)?;
        FreeRtos::delay_ms(100);
        self.wait_idle()?;
        self.cmd_data(CMD_PANEL_SETTING, &[0x1F])?;
        self.cmd_data(CMD_RESOLUTION, &[0x03, 0x20, 0x01, 0xE0])?;
        self.cmd_data(CMD_DUAL_SPI, &[0x00])?;
        self.cmd_data(CMD_VCOM, &[0x10, 0x07])?;
        self.cmd_data(CMD_TCON, &[0x22])?;
        Ok(())
    }

    fn init_part(&mut self) -> Result<()> {
        self.hardware_reset();
        self.cmd_data(CMD_PANEL_SETTING, &[0x1F])?;
        self.cmd(CMD_POWER_ON)?;
        FreeRtos::delay_ms(100);
        self.wait_idle()?;
        self.cmd_data(CMD_TEMP_SEL, &[0x02])?;
        self.cmd_data(CMD_TEMP_LUT, &[0x6E])?;
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

    fn refresh(&mut self) -> Result<()> {
        self.cmd(CMD_REFRESH)?;
        FreeRtos::delay_ms(100);
        self.wait_idle()
    }

    fn wait_idle(&mut self) -> Result<()> {
        // BUSY is low while the UC8179 is working.
        loop {
            self.cmd(CMD_GET_STATUS)?;
            FreeRtos::delay_ms(10);
            if !self.busy.is_low() {
                break;
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

    fn data_inverted(&mut self, bytes: &[u8]) -> Result<()> {
        self.dc.set_high().map_err(|e| anyhow!("dc high: {e:?}"))?;
        let mut chunk = [0u8; 256];
        for source in bytes.chunks(chunk.len()) {
            for (i, &b) in source.iter().enumerate() {
                chunk[i] = !b;
            }
            self.spi
                .write(&chunk[..source.len()])
                .map_err(|e| anyhow!("spi inv data: {e:?}"))?;
        }
        Ok(())
    }
}
