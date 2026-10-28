//! grayscale-esp32 — experimental grayscale video demo for the UC8179.
//!
//! Plays a small flock of boids through the custom one-step drive mode
//! (`inkbot_esp32::grayscale`) as many times a second as the panel and SPI
//! bus allow, and logs where each refresh's time goes. Every
//! [`FULL_REFRESH_INTERVAL`] it drives every pixel back to white and runs a
//! factory full refresh to clear ghosting and drift.
//!
//! No Wi-Fi, no OTA pull, and no OTA registration: USB-flash only
//! (`make flash APP=grayscale`).

mod grayscale_display;

use std::time::{Duration, Instant};

use anyhow::Result;
use esp_idf_svc::hal::{delay::FreeRtos, peripherals::Peripherals};
use log::{error, info};

use grayscale_display::{Panel, SPI_MHZ};
use inkbot_esp32::grayscale::{
    drive::{DriveConfig, DrivePlanner},
    lut::DriveLuts,
    scene::BoidsScene,
    GRAYSCALE_FIRMWARE_ID, LOGICAL_HEIGHT, LOGICAL_WIDTH,
};

/// Seeds the flock's starting positions and headings. Any value works; it
/// is fixed so a given firmware build always starts the same way.
const FLOCK_SEED: u32 = 0x5EED_B01D;

/// Frames each drive step lasts. One is the shortest step and the fastest
/// refresh; more frames per step move ink further per refresh.
const FRAMES_PER_STEP: u8 = 1;

/// Set if pixels move the wrong way (the scene appears as a negative, or
/// barely appears at all).
const SWAP_DRIVE_POLARITY: bool = false;

const FULL_REFRESH_INTERVAL: Duration = Duration::from_secs(60);

const STATS_EVERY: u32 = 50;

fn main() -> Result<()> {
    esp_idf_svc::sys::link_patches();
    esp_idf_svc::log::EspLogger::initialize_default();
    info!("{GRAYSCALE_FIRMWARE_ID} boot spi_mhz={SPI_MHZ} frames_per_step={FRAMES_PER_STEP}");

    let peripherals = Peripherals::take()?;
    let mut panel = Panel::new(
        peripherals.spi2,
        peripherals.pins.gpio13,
        peripherals.pins.gpio14,
        peripherals.pins.gpio15,
        peripherals.pins.gpio25,
        peripherals.pins.gpio27,
        peripherals.pins.gpio26,
    )?;

    let luts = DriveLuts::new(FRAMES_PER_STEP, SWAP_DRIVE_POLARITY);
    let mut planner = DrivePlanner::new(LOGICAL_WIDTH, LOGICAL_HEIGHT, DriveConfig::default());
    let mut old = vec![0u8; planner.plane_bytes()];
    let mut new = vec![0u8; planner.plane_bytes()];
    // Persists across full-refresh cycles so the flock keeps moving
    // through the periodic cleanup instead of restarting each time.
    let mut scene = BoidsScene::new(FLOCK_SEED);

    loop {
        if let Err(e) = run_cycle(
            &mut panel,
            &mut planner,
            &luts,
            &mut old,
            &mut new,
            &mut scene,
        ) {
            error!("drive cycle failed: {e:#}");
            if let Err(e) = panel.power_off() {
                error!("power off failed: {e:#}");
            }
            FreeRtos::delay_ms(2000);
        }
    }
}

/// Full refresh to white, drive the scene until the interval ends, then
/// drain every pixel back to white.
fn run_cycle(
    panel: &mut Panel,
    planner: &mut DrivePlanner,
    luts: &DriveLuts,
    old: &mut [u8],
    new: &mut [u8],
    scene: &mut BoidsScene,
) -> Result<()> {
    let start = Instant::now();
    panel.full_refresh_white()?;
    info!("full refresh ms={}", start.elapsed().as_millis());

    planner.reset_white();
    panel.init_drive(luts)?;

    let cycle_start = Instant::now();
    let mut draining = false;
    let mut stats = Stats::default();
    let mut plan = planner.plan_tick(|x, y| scene.luma(x, y), old, new);

    loop {
        let refresh_start = Instant::now();
        if plan.rewrite_old {
            panel.write_old(old)?;
        }
        panel.write_new(new)?;
        let sent = Instant::now();
        panel.start_drive()?;

        if draining && plan.undrained == 0 {
            panel.wait_drive()?;
            info!("drained after ms={}", cycle_start.elapsed().as_millis());
            return Ok(());
        }
        let sent_plan = plan;

        draining |= cycle_start.elapsed() >= FULL_REFRESH_INTERVAL;
        plan = if draining {
            planner.plan_tick(|_, _| 255, old, new)
        } else {
            scene.step();
            planner.plan_tick(|x, y| scene.luma(x, y), old, new)
        };
        let planned = Instant::now();

        panel.wait_drive()?;
        // Let the idle task run so the task watchdog stays fed.
        FreeRtos::delay_ms(1);
        let done = Instant::now();

        stats.refreshes += 1;
        stats.rewrites += u32::from(sent_plan.rewrite_old);
        stats.driven += sent_plan.driven as u64;
        stats.spi += sent - refresh_start;
        stats.plan += planned - sent;
        stats.wait += done - planned;
        stats.total += done - refresh_start;
        if stats.refreshes == STATS_EVERY {
            stats.log(sent_plan.pending_flips);
            stats = Stats::default();
        }
    }
}

#[derive(Default)]
struct Stats {
    refreshes: u32,
    rewrites: u32,
    driven: u64,
    spi: Duration,
    plan: Duration,
    wait: Duration,
    total: Duration,
}

impl Stats {
    fn log(&self, pending_flips: usize) {
        let n = self.refreshes.max(1);
        let avg_ms = |d: Duration| d.as_secs_f32() * 1000.0 / n as f32;
        info!(
            "drive hz={:.1} ms/refresh={:.1} spi={:.1} plan={:.1} wait={:.1} \
             old_rewrites={}/{} avg_driven={} pending_flips={}",
            n as f32 / self.total.as_secs_f32().max(f32::EPSILON),
            avg_ms(self.total),
            avg_ms(self.spi),
            avg_ms(self.plan),
            avg_ms(self.wait),
            self.rewrites,
            n,
            self.driven / u64::from(n),
            pending_flips,
        );
    }
}
