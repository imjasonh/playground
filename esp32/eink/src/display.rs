use anyhow::{Context, Result, anyhow};
use embedded_graphics::{
    mono_font::{MonoTextStyle, ascii::FONT_9X18},
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
    gpio::{InputPin, OutputPin, PinDriver, Pull},
    spi::{SpiAnyPins, SpiDeviceDriver, config},
    units::FromValueType,
};

use esp32_eink::terminal::{ROWS, TerminalBuffer};

const FRAME_BYTES: usize = WIDTH as usize * HEIGHT as usize / 8;
const LEFT_MARGIN: i32 = 40;
const LINE_HEIGHT: i32 = 19;

/// Consume the Waveshare board's fixed display pins, render one terminal
/// snapshot, perform a full refresh, then put the panel into deep sleep.
///
/// Current Waveshare board wiring:
/// SCLK=13, MOSI=14, CS=15, DC=27, RST=26, BUSY=25.
#[allow(clippy::too_many_arguments)]
pub fn show<SPI, SCLK, MOSI, CS, BUSY, DC, RST>(
    terminal: &TerminalBuffer,
    spi: SPI,
    sclk: SCLK,
    mosi: MOSI,
    cs: CS,
    busy: BUSY,
    dc: DC,
    rst: RST,
) -> Result<()>
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

    // A Vec puts the 48 KB monochrome framebuffer on the heap. Constructing
    // Display7in5::default() directly could transiently place it on the task
    // stack, which is unsafe on a classic ESP32 without PSRAM.
    let mut frame = vec![0xff; FRAME_BYTES];
    {
        let mut target = VarDisplay::<Color>::new(WIDTH, HEIGHT, &mut frame, false)
            .map_err(|_| anyhow!("48 KB e-paper framebuffer rejected"))?;
        target.clear(Color::White).unwrap();
        let style = MonoTextStyle::new(&FONT_9X18, Color::Black);

        for row in 0..ROWS {
            // TerminalBuffer guarantees printable ASCII cells.
            let line = std::str::from_utf8(terminal.line(row)).unwrap();
            Text::with_baseline(
                line,
                Point::new(LEFT_MARGIN, row as i32 * LINE_HEIGHT),
                style,
                Baseline::Top,
            )
            .draw(&mut target)
            .unwrap();
        }
    }

    let mut epd =
        Epd7in5::new(&mut spi, busy, dc, rst, &mut delay, None).context("initialize panel")?;
    epd.update_and_display_frame(&mut spi, &frame, &mut delay)
        .context("refresh panel")?;
    epd.sleep(&mut spi, &mut delay)
        .context("put panel into deep sleep")?;
    Ok(())
}
