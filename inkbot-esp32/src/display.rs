//! Waveshare 7.5″ V2 panel bring-up and full refresh.
//!
//! Fixed driver-board wiring (SKU 15823):
//! SCLK=13, MOSI=14, CS=15, DC=27, RST=26, BUSY=25.

use anyhow::{anyhow, Context, Result};
use embedded_graphics::{
    mono_font::{ascii::FONT_9X18, MonoTextStyle},
    prelude::*,
    text::{Baseline, Text},
};
use epd_waveshare::{
    color::Color,
    epd7in5_v2::{Epd7in5, HEIGHT, WIDTH},
    graphics::VarDisplay,
    prelude::WaveshareDisplay,
};
use esp_idf_svc::hal::{
    delay::Ets,
    gpio::{Gpio13, Gpio14, Gpio15, Gpio25, Gpio26, Gpio27, Input, Output, PinDriver, Pull},
    peripheral::Peripheral,
    spi::{config, SpiDeviceDriver, SpiDriver, SPI2},
    units::FromValueType,
};

use inkbot_esp32::FRAME_BYTES;

type BusyPin = PinDriver<'static, Gpio25, Input>;
type DcPin = PinDriver<'static, Gpio27, Output>;
type RstPin = PinDriver<'static, Gpio26, Output>;
type PanelSpi = SpiDeviceDriver<'static, SpiDriver<'static>>;
type Epd = Epd7in5<PanelSpi, BusyPin, DcPin, RstPin, Ets>;

/// Owns the SPI bus + panel for the life of the firmware.
pub struct Panel {
    spi: PanelSpi,
    epd: Epd,
    delay: Ets,
}

impl Panel {
    pub fn new(
        spi2: impl Peripheral<P = SPI2> + 'static,
        sclk: Gpio13,
        mosi: Gpio14,
        cs: Gpio15,
        busy: Gpio25,
        dc: Gpio27,
        rst: Gpio26,
    ) -> Result<Self> {
        let spi_config = config::Config::new().baudrate(4_u32.MHz().into());
        let mut spi = SpiDeviceDriver::new_single(
            spi2,
            sclk,
            mosi,
            Option::<Gpio14>::None,
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

    /// Render a short status string on a white panel.
    pub fn show_message(&mut self, message: &str) -> Result<()> {
        let mut frame = vec![0xffu8; FRAME_BYTES];
        {
            let mut target = VarDisplay::<Color>::new(WIDTH, HEIGHT, &mut frame, false)
                .map_err(|_| anyhow!("48 KB e-paper framebuffer rejected"))?;
            target.clear(Color::White).unwrap();
            let style = MonoTextStyle::new(&FONT_9X18, Color::Black);
            Text::with_baseline(message, Point::new(24, 220), style, Baseline::Top)
                .draw(&mut target)
                .unwrap();
        }
        self.show_frame(&frame)
    }
}
