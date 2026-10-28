//! UC8179 "4 Gray" and "fast" full-refresh modes for the Waveshare 7.5″ V2.
//!
//! `init_4gray`/`show_4gray` and `init_fast`/`show_fast` transliterate
//! Waveshare's own `EPD_7IN5_V2_Init_4Gray` / `_Display_4Gray` and
//! `_Init_Fast` (<https://github.com/waveshare/e-Paper>,
//! `Arduino_R4/src/e-Paper/EPD_7in5_V2.cpp`). Both select a built-in,
//! factory-programmed waveform through the same "temperature select" trick
//! `maze_display.rs` already uses for partial refresh (`0xE0=0x02`,
//! `0xE5=0x6E`); 4-gray and fast use `0x5F` and `0x5A` instead. No
//! waveform-LUT registers (`0x20`-`0x25`) are written, and no
//! one-time-programming command is sent — only commands Waveshare's own
//! driver sends for this exact panel.
//!
//! **Timing is not yet measured on real hardware.** The datasheet does not
//! state the 4-gray or fast waveform's length, and InkBoy's own technique —
//! a short *custom* waveform, redriving only pixels that changed, many
//! times a second — does not apply to either mode here: both still redrive
//! the whole panel in one `0x12` (`DISPLAY REFRESH`) call, timed by their
//! own factory waveform, not by anything this firmware controls.
//! `grayscale_main.rs` logs each call's wall-clock time so the real number
//! for this board and panel can be read off the serial monitor.

use std::time::{Duration, Instant};

use anyhow::{anyhow, Context, Result};
use esp_idf_svc::hal::{
    delay::{Ets, FreeRtos},
    gpio::{Input, InputPin, Output, OutputPin, PinDriver, Pull},
    spi::{config, SpiAnyPins, SpiDeviceDriver, SpiDriver},
    units::FromValueType,
};

use inkbot_esp32::FRAME_BYTES;

type BusyPin = PinDriver<'static, Input>;
type DcPin = PinDriver<'static, Output>;
type RstPin = PinDriver<'static, Output>;
type PanelSpi = SpiDeviceDriver<'static, SpiDriver<'static>>;

const CMD_PANEL_SETTING: u8 = 0x00;
const CMD_POWER_OFF: u8 = 0x02;
const CMD_POWER_ON: u8 = 0x04;
const CMD_BOOSTER: u8 = 0x06;
const CMD_DEEP_SLEEP: u8 = 0x07;
const CMD_DTM1: u8 = 0x10;
const CMD_REFRESH: u8 = 0x12;
const CMD_DTM2: u8 = 0x13;
const CMD_VCOM: u8 = 0x50;
const CMD_GET_STATUS: u8 = 0x71;
const CMD_TEMP_SEL: u8 = 0xE0;
const CMD_TEMP_LUT: u8 = 0xE5;

/// `0xE5` value `Init_4Gray` loads after `0xE0=0x02`.
const TEMP_LUT_4GRAY: u8 = 0x5F;
/// `0xE5` value `Init_Fast` loads after `0xE0=0x02`.
const TEMP_LUT_FAST: u8 = 0x5A;

/// Owns the SPI bus + panel for the grayscale demo firmware.
pub struct Panel {
    spi: PanelSpi,
    busy: BusyPin,
    dc: DcPin,
    rst: RstPin,
}

impl Panel {
    /// Consume the Waveshare board's fixed display pins. Does not bring the
    /// panel up — `show_4gray` / `show_fast` each run a full `Init_*`
    /// sequence first, mirroring how Waveshare's own demos always call
    /// `Init_*` immediately before a `Display_*` call.
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

        Ok(Self { spi, busy, dc, rst })
    }

    /// Full-refresh a 4-level image, given as the two `DTM1`/`DTM2` planes
    /// [`inkbot_esp32::grayscale::plan_panel_frame`] produces. Leaves the
    /// panel awake; call [`Panel::sleep`] when done for the cycle.
    pub fn show_4gray(&mut self, old_plane: &[u8], new_plane: &[u8]) -> Result<()> {
        if old_plane.len() != FRAME_BYTES || new_plane.len() != FRAME_BYTES {
            return Err(anyhow!(
                "4-gray planes must each be {FRAME_BYTES} bytes, got {} and {}",
                old_plane.len(),
                new_plane.len()
            ));
        }
        self.init_4gray()?;
        self.cmd(CMD_DTM1)?;
        self.data(old_plane)?;
        self.cmd(CMD_DTM2)?;
        self.data(new_plane)?;
        self.refresh()
    }

    /// Full-refresh a packed 1-bit framebuffer (MSB first, 1 = white) using
    /// Waveshare's "fast" full-refresh waveform, which is still a complete
    /// panel redrive (not InkBoy's per-pixel short pulse) but is a
    /// vendor-documented faster alternative to the normal factory waveform.
    pub fn show_fast(&mut self, frame: &[u8]) -> Result<()> {
        if frame.len() != FRAME_BYTES {
            return Err(anyhow!(
                "framebuffer must be {FRAME_BYTES} bytes, got {}",
                frame.len()
            ));
        }
        self.init_fast()?;
        self.cmd(CMD_DTM1)?;
        self.data(frame)?;
        self.cmd(CMD_DTM2)?;
        self.data_inverted(frame)?;
        self.refresh()
    }

    /// Power the panel down until the next `show_*` call.
    pub fn sleep(&mut self) -> Result<()> {
        self.wait_idle()?;
        self.cmd_data(CMD_VCOM, &[0xF7])?;
        self.cmd(CMD_POWER_OFF)?;
        self.wait_idle()?;
        self.cmd_data(CMD_DEEP_SLEEP, &[0xA5])?;
        Ok(())
    }

    /// `EPD_7IN5_V2_Init_4Gray()`.
    fn init_4gray(&mut self) -> Result<()> {
        self.init_with_temp_lut(TEMP_LUT_4GRAY)
    }

    /// `EPD_7IN5_V2_Init_Fast()`. Identical to `Init_4Gray` except the
    /// `0xE5` value, matching the vendor source exactly.
    fn init_fast(&mut self) -> Result<()> {
        self.init_with_temp_lut(TEMP_LUT_FAST)
    }

    fn init_with_temp_lut(&mut self, temp_lut: u8) -> Result<()> {
        self.hardware_reset();
        self.cmd_data(CMD_PANEL_SETTING, &[0x1F])?;
        self.cmd_data(CMD_VCOM, &[0x10, 0x07])?;
        self.cmd(CMD_POWER_ON)?;
        FreeRtos::delay_ms(100);
        self.wait_idle()?;
        self.cmd_data(CMD_BOOSTER, &[0x27, 0x27, 0x18, 0x17])?;
        self.cmd_data(CMD_TEMP_SEL, &[0x02])?;
        self.cmd_data(CMD_TEMP_LUT, &[temp_lut])?;
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
        // BUSY is low while the UC8179 is working (matches maze_display.rs).
        // 4-gray and fast refresh times are unmeasured; this timeout is a
        // generous upper bound, not a measurement of either mode's speed.
        let start = Instant::now();
        loop {
            self.cmd(CMD_GET_STATUS)?;
            FreeRtos::delay_ms(10);
            if !self.busy.is_low() {
                break;
            }
            if start.elapsed() > Duration::from_secs(20) {
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
