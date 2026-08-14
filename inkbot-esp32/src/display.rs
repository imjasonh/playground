//! Waveshare 7.5″ V2 panel bring-up and full refresh.
//!
//! Fixed driver-board wiring (SKU 15823):
//! SCLK=13, MOSI=14, CS=15, DC=27, RST=26, BUSY=25.

use anyhow::{anyhow, Context, Result};
use epd_waveshare::{epd7in5_v2::Epd7in5, prelude::WaveshareDisplay};
use esp_idf_svc::hal::{
    delay::Ets,
    gpio::{Input, InputPin, Output, OutputPin, PinDriver, Pull},
    spi::{config, SpiAnyPins, SpiDeviceDriver, SpiDriver},
    units::FromValueType,
};

use inkbot_esp32::{overlay_status_line, FRAME_BYTES};

// esp-idf-hal 0.46: PinDriver<'d, MODE> — pin type is erased into MODE.
type BusyPin = PinDriver<'static, Input>;
type DcPin = PinDriver<'static, Output>;
type RstPin = PinDriver<'static, Output>;
type PanelSpi = SpiDeviceDriver<'static, SpiDriver<'static>>;
type Epd = Epd7in5<PanelSpi, BusyPin, DcPin, RstPin, Ets>;

/// Owns the SPI bus + panel for the life of the firmware.
///
/// The 48 KB framebuffer is allocated only around a refresh so HTTPS/TLS can
/// claim a contiguous buffer while the panel is idle.
pub struct Panel {
    spi: PanelSpi,
    epd: Epd,
    delay: Ets,
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
        // Typed None: new_single's sdi is `Option<impl InputPin>`; a bare None
        // can't pick a concrete type. Reuse BUSY's InputPin bound.
        let mut spi = SpiDeviceDriver::new_single(
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
        let mut delay = Ets;

        let epd =
            Epd7in5::new(&mut spi, busy, dc, rst, &mut delay, None).context("initialize panel")?;

        Ok(Self { spi, epd, delay })
    }

    /// Full-refresh a packed 1-bit framebuffer (MSB first, 1 = white), then
    /// deep-sleep the panel until the next call.
    pub fn show_frame(&mut self, frame: &[u8]) -> Result<()> {
        if frame.len() != FRAME_BYTES {
            return Err(anyhow!(
                "framebuffer must be {FRAME_BYTES} bytes, got {}",
                frame.len()
            ));
        }
        // new() leaves the panel awake; after sleep() we must wake first.
        let _ = self.epd.wake_up(&mut self.spi, &mut self.delay);
        self.epd
            .update_and_display_frame(&mut self.spi, frame, &mut self.delay)
            .context("refresh panel")?;
        self.epd
            .sleep(&mut self.spi, &mut self.delay)
            .context("put panel into deep sleep")?;
        Ok(())
    }

    /// Full-refresh `frame`, overlaying a bottom status bar only when `status`
    /// is `Some`. Healthy frames are painted unchanged so the image keeps the
    /// full 800×480.
    pub fn show_with_status(&mut self, frame: &[u8], status: Option<&str>) -> Result<()> {
        match status {
            None => self.show_frame(frame),
            Some(text) => {
                let mut copy = frame.to_vec();
                overlay_status_line(&mut copy, text).map_err(|e| anyhow!("status overlay: {e}"))?;
                self.show_frame(&copy)
            }
        }
    }

    /// White panel with only the bottom status bar (no image available).
    pub fn show_status_only(&mut self, status: &str) -> Result<()> {
        let mut frame = vec![0xffu8; FRAME_BYTES];
        overlay_status_line(&mut frame, status).map_err(|e| anyhow!("status overlay: {e}"))?;
        self.show_frame(&frame)
    }
}
