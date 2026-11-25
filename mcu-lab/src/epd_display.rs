//! Waveshare 7.5″ V2 (UC8179) driver with full and partial refresh.
//!
//! Pin map matches `display.rs` (Waveshare ESP32 driver board). Full refresh
//! copies the DTM1/DTM2 polarity that inkbot already uses. Partial refresh
//! follows Waveshare's `Init_Part` + `Display_Partial` sequence; the pinned
//! `epd-waveshare` crate leaves `update_partial_frame` unimplemented.

use std::time::{Duration, Instant};

use anyhow::{anyhow, Context, Result};
use esp_idf_svc::hal::delay::{Ets, FreeRtos};
use esp_idf_svc::hal::gpio::{Input, InputPin, Output, OutputPin, PinDriver, Pull};
use esp_idf_svc::hal::spi::{config, Dma, SpiAnyPins, SpiDeviceDriver, SpiDriver};
use esp_idf_svc::hal::units::FromValueType;

use crate::grayscale::lut::{DriveLuts, PANEL_SETTING_REGISTER_LUT, VCOM_DATA_INTERVAL, VCOM_DC};
use crate::maze::ByteRect;
use crate::panel::FRAME_BYTES;

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
const CMD_VCOM_DC: u8 = 0x82;
const CMD_PARTIAL_IN: u8 = 0x91;
const CMD_PARTIAL_WINDOW: u8 = 0x90;
const CMD_TEMP_SEL: u8 = 0xE0;
const CMD_TEMP_LUT: u8 = 0xE5;

/// SPI clock in MHz. At 4 MHz one 48 KB plane takes 96 ms; 20 MHz with DMA
/// brings that to ~19 ms, enabling 20+ refreshes/sec in grayscale drive mode.
pub const SPI_MHZ: u32 = 20;

/// Largest single DMA transfer. Without DMA, esp-idf-hal splits every write
/// into 64-byte transactions with a gap after each.
const DMA_TRANSFER_BYTES: usize = 4092;

/// Upper bound on one custom drive refresh before it counts as stuck.
const DRIVE_TIMEOUT: Duration = Duration::from_millis(500);

/// Owns the SPI bus + panel for Waveshare 7.5″ V2 e-Paper apps.
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

    /// Full-refresh a packed 1-bit framebuffer (MSB first, 1 = white) streamed in
    /// small chunks from flash so no 48 KiB heap buffer is needed. Leaves the panel awake.
    pub fn show_bw_stream<F>(&mut self, mut read_at: F) -> Result<()>
    where
        F: FnMut(usize, &mut [u8]) -> Result<()>,
    {
        self.init_full()?;
        let mut buf = [0u8; 4096];

        self.cmd(CMD_DTM1)?;
        let mut offset = 0usize;
        while offset < FRAME_BYTES {
            let len = (FRAME_BYTES - offset).min(buf.len());
            read_at(offset, &mut buf[..len])?;
            self.data(&buf[..len])?;
            offset += len;
        }

        self.cmd(CMD_DTM2)?;
        offset = 0;
        while offset < FRAME_BYTES {
            let len = (FRAME_BYTES - offset).min(buf.len());
            read_at(offset, &mut buf[..len])?;
            for b in &mut buf[..len] {
                *b = !*b;
            }
            self.data(&buf[..len])?;
            offset += len;
        }

        self.refresh()?;
        Ok(())
    }

    /// Full-refresh a 4-level grayscale (2-bit) image stored as two contiguous
    /// 48,000-byte planes (`DTM1` at `0..48_000`, `DTM2` at `48_000..96_000`) streamed
    /// in 4 KiB chunks from flash. Leaves the panel awake.
    pub fn show_4gray_stream<F>(&mut self, mut read_at: F) -> Result<()>
    where
        F: FnMut(usize, &mut [u8]) -> Result<()>,
    {
        self.init_4gray()?;
        let mut buf = [0u8; 4096];

        self.cmd(CMD_DTM1)?;
        let mut offset = 0usize;
        while offset < FRAME_BYTES {
            let len = (FRAME_BYTES - offset).min(buf.len());
            read_at(offset, &mut buf[..len])?;
            self.data(&buf[..len])?;
            offset += len;
        }

        self.cmd(CMD_DTM2)?;
        offset = 0;
        while offset < FRAME_BYTES {
            let len = (FRAME_BYTES - offset).min(buf.len());
            read_at(FRAME_BYTES + offset, &mut buf[..len])?;
            self.data(&buf[..len])?;
            offset += len;
        }

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
        let Some(rect) = rect.clamped() else {
            return Err(anyhow!(
                "partial rect {rect:?} is empty or not byte-aligned"
            ));
        };
        if window.len() != rect.byte_count() {
            return Err(anyhow!(
                "partial window must be {} bytes, got {}",
                rect.byte_count(),
                window.len()
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

    /// Factory full refresh to white. Takes a few seconds and leaves the panel
    /// in OTP mode: call [`Panel::init_drive`] before custom-LUT driving.
    pub fn full_refresh_white(&mut self) -> Result<()> {
        self.init_full()?;
        let white = [0xFFu8; 1000];
        self.cmd(CMD_DTM1)?;
        for _ in 0..FRAME_BYTES / white.len() {
            self.data(&white)?;
        }
        let zero = [0x00u8; 1000];
        self.cmd(CMD_DTM2)?;
        for _ in 0..FRAME_BYTES / zero.len() {
            self.data(&zero)?;
        }
        self.refresh()
    }

    /// Reset the controller and load custom one-step waveform LUTs. The old
    /// plane is undefined until the next [`Panel::write_old_rows`].
    pub fn init_drive(&mut self, luts: &DriveLuts) -> Result<()> {
        self.hardware_reset();
        self.cmd_data(CMD_POWER_SETTING, &[0x07, 0x07, 0x3F, 0x3F])?;
        self.cmd_data(CMD_BOOSTER, &[0x17, 0x17, 0x28, 0x17])?;
        self.cmd(CMD_POWER_ON)?;
        FreeRtos::delay_ms(100);
        self.wait_idle()?;
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

    /// Stream the `old` plane (`DTM1`) by packing each logical row on the fly
    /// and doubling it vertically into DMA-sized chunks.
    pub fn write_old_rows(
        &mut self,
        logical_rows: usize,
        row_bytes: usize,
        fill_row: impl FnMut(usize, &mut [u8]),
    ) -> Result<()> {
        self.write_doubled_plane(CMD_DTM1, logical_rows, row_bytes, fill_row)
    }

    /// Stream a half-height `new` plane (`DTM2`), doubling each logical row
    /// vertically into DMA-sized chunks.
    pub fn write_new_half_plane(
        &mut self,
        new_half: &[u8],
        logical_rows: usize,
        row_bytes: usize,
    ) -> Result<()> {
        if new_half.len() != logical_rows * row_bytes {
            return Err(anyhow!(
                "new half-plane must be {} bytes, got {}",
                logical_rows * row_bytes,
                new_half.len()
            ));
        }
        self.write_doubled_plane(CMD_DTM2, logical_rows, row_bytes, |y, dst| {
            let start = y * row_bytes;
            dst.copy_from_slice(&new_half[start..start + row_bytes]);
        })
    }

    /// Start one custom drive refresh and return while the panel is busy.
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
        self.wait_idle()
    }

    fn write_doubled_plane(
        &mut self,
        command: u8,
        logical_rows: usize,
        row_bytes: usize,
        mut fill_row: impl FnMut(usize, &mut [u8]),
    ) -> Result<()> {
        let doubled_row = row_bytes * 2;
        if logical_rows * doubled_row != FRAME_BYTES {
            return Err(anyhow!(
                "doubled plane must be {FRAME_BYTES} bytes, got {}",
                logical_rows * doubled_row
            ));
        }
        self.cmd(command)?;
        let mut chunk = [0u8; DMA_TRANSFER_BYTES];
        let rows_per_chunk = (DMA_TRANSFER_BYTES / doubled_row).max(1);
        let mut y = 0;
        while y < logical_rows {
            let y_end = (y + rows_per_chunk).min(logical_rows);
            let mut off = 0;
            for row_idx in y..y_end {
                fill_row(row_idx, &mut chunk[off..off + row_bytes]);
                chunk.copy_within(off..off + row_bytes, off + row_bytes);
                off += doubled_row;
            }
            self.data(&chunk[..off])?;
            y = y_end;
        }
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

    /// Waveshare 7.5″ V2 4-Gray OTP LUT initialization (`epd7in5_V2.py: init_4Gray`).
    fn init_4gray(&mut self) -> Result<()> {
        self.hardware_reset();
        self.cmd_data(CMD_PANEL_SETTING, &[0x1F])?;
        self.cmd_data(CMD_VCOM, &[0x10, 0x07])?;
        self.cmd(CMD_POWER_ON)?;
        FreeRtos::delay_ms(100);
        self.wait_idle()?;
        self.cmd_data(CMD_BOOSTER, &[0x27, 0x27, 0x18, 0x17])?;
        self.cmd_data(CMD_TEMP_SEL, &[0x02])?;
        self.cmd_data(CMD_TEMP_LUT, &[0x5F])?;
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
        // BUSY is low while the UC8179 is working. A 7.5″ full refresh is a few
        // seconds; if the pin sticks, fail instead of hanging the desk loop.
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
