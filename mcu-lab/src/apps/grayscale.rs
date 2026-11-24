//! `GrayscaleApp` — experimental grayscale video drive with a flocking boids
//! scene on any board implementing [`Board`] + [`HasEpd75`].
//!
//! Alternates between two steps:
//! 1. **Full refresh**: factory full refresh to white + power off (~4 s), so
//!    boot-time BLE telemetry and OTA rollback verification complete quickly.
//! 2. **Drive cycle**: loads the custom one-frame waveform LUTs, drives the
//!    boids flock at 20+ refreshes/s for [`FULL_REFRESH_INTERVAL`], drains
//!    every pixel back to white for DC balance, and powers the panel off
//!    before returning for the BLE telemetry / OTA window.
//!
//! Uses row-by-row triangle rendering and compact half-plane planning so total
//! heap usage stays around ~128 KiB alongside NimBLE on a no-PSRAM ESP32.

use std::time::{Duration, Instant};

use anyhow::Result;
use esp_idf_svc::hal::delay::FreeRtos;
use log::{error, info};

use crate::boards::{Board, HasEpd75};
use crate::epd_display::SPI_MHZ;
use crate::grayscale::boids::{Flock, FlockConfig, RenderTriangle};
use crate::grayscale::drive::{DriveConfig, DrivePlanner};
use crate::grayscale::lut::DriveLuts;
use crate::grayscale::{GRAYSCALE_FIRMWARE_ID, LOGICAL_HEIGHT, LOGICAL_WIDTH};
use crate::platform::{App, RunMode, StepContext, StepOutput};
use crate::profiler::now_us;
use crate::protocol::FLAG_EPD_PARTIAL;

/// Seeds the flock's starting positions and headings. Fixed so a given
/// firmware build always starts the same way.
const FLOCK_SEED: u32 = 0x5EED_B01D;

/// Frames each drive step lasts. One is the shortest step and the fastest
/// refresh; more frames per step move ink further per refresh.
const FRAMES_PER_STEP: u8 = 1;

/// Set if pixels move the wrong way (the scene appears as a negative, or
/// barely appears at all).
const SWAP_DRIVE_POLARITY: bool = false;

/// Drive duration before draining back to white and running a factory full refresh.
const FULL_REFRESH_INTERVAL: Duration = Duration::from_secs(60);

/// Serial log cadence (in refreshes) inside a drive cycle.
const STATS_EVERY: u32 = 50;

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
enum Phase {
    FullRefresh,
    DriveCycle,
}

/// Experimental 20+ Hz grayscale boids application for 7.5″ 800×480 e-Paper boards.
pub struct GrayscaleApp {
    phase: Phase,
    luts: DriveLuts,
    planner: DrivePlanner,
    new_half: Vec<u8>,
    flock: Flock,
    triangles: Vec<RenderTriangle>,
    row_luma: Vec<u8>,
}

impl<B: Board + HasEpd75> App<B> for GrayscaleApp {
    const APP_NAME: &'static str = "grayscale";
    const FIRMWARE_ID: &'static str = GRAYSCALE_FIRMWARE_ID;

    fn run_mode() -> RunMode {
        RunMode::Continuous {
            burst_ms: 500,
            min_step_ms: 0,
        }
    }

    fn init(_board: &mut B) -> Result<Self> {
        info!("{GRAYSCALE_FIRMWARE_ID} init spi_mhz={SPI_MHZ} frames_per_step={FRAMES_PER_STEP}");
        let luts = DriveLuts::new(FRAMES_PER_STEP, SWAP_DRIVE_POLARITY);
        let planner = DrivePlanner::new(LOGICAL_WIDTH, LOGICAL_HEIGHT, DriveConfig::default());
        let new_half = vec![0u8; planner.half_plane_bytes()];
        let flock = Flock::new(FlockConfig::default(), FLOCK_SEED);
        let mut triangles = Vec::new();
        flock.prepare_triangles(LOGICAL_WIDTH, LOGICAL_HEIGHT, &mut triangles);
        let row_luma = vec![255u8; LOGICAL_WIDTH];
        Ok(Self {
            phase: Phase::FullRefresh,
            luts,
            planner,
            new_half,
            flock,
            triangles,
            row_luma,
        })
    }

    fn self_test(&mut self, _board: &mut B) -> Result<()> {
        // Verify triangle preparation and one row render succeed before OTA verify.
        self.flock
            .prepare_triangles(LOGICAL_WIDTH, LOGICAL_HEIGHT, &mut self.triangles);
        self.flock
            .render_luma_row(&self.triangles, 0, &mut self.row_luma);
        Ok(())
    }

    fn step(&mut self, board: &mut B, ctx: &mut StepContext<'_>) -> Result<StepOutput> {
        match self.phase {
            Phase::FullRefresh => self.step_full_refresh(board, ctx),
            Phase::DriveCycle => self.step_drive_cycle(board, ctx),
        }
    }
}

impl GrayscaleApp {
    fn step_full_refresh<B: Board + HasEpd75>(
        &mut self,
        board: &mut B,
        ctx: &mut StepContext<'_>,
    ) -> Result<StepOutput> {
        ctx.record_attr("grayscale.phase", "full_refresh");

        let start = now_us();
        let res = board.panel().full_refresh_white();
        let end = now_us();
        ctx.record_span("grayscale.full_refresh", "epd_refresh", start, end);
        ctx.feed_watchdog();
        res?;

        if let Err(err) = board.panel().power_off() {
            error!("grayscale: power off after full refresh failed: {err:#}");
        }
        self.planner.reset_white();
        self.phase = Phase::DriveCycle;

        let epd_refresh_us = u32::try_from(end.saturating_sub(start)).unwrap_or(u32::MAX);
        info!("full refresh ms={}", epd_refresh_us / 1_000);

        Ok(StepOutput {
            sensor_us: 0,
            compute_us: 0,
            epd_refresh_us,
            battery_mv: 0,
            flags: 0,
            post_burst_delay_ms: 0,
        })
    }

    fn step_drive_cycle<B: Board + HasEpd75>(
        &mut self,
        board: &mut B,
        ctx: &mut StepContext<'_>,
    ) -> Result<StepOutput> {
        ctx.record_attr("grayscale.phase", "drive_cycle");
        // Always start the next step with a clean full refresh, even on error.
        self.phase = Phase::FullRefresh;

        let init_start = now_us();
        if let Err(err) = board.panel().init_drive(&self.luts) {
            let _ = board.panel().power_off();
            return Err(err);
        }
        let init_end = now_us();
        ctx.record_span("grayscale.init_drive", "epd_refresh", init_start, init_end);
        ctx.feed_watchdog();

        let cycle_start_us = now_us();
        let cycle_res = self.run_drive_loop(board, ctx);
        let cycle_end_us = now_us();
        ctx.record_span(
            "grayscale.drive_cycle",
            "epd_refresh",
            cycle_start_us,
            cycle_end_us,
        );

        if let Err(err) = board.panel().power_off() {
            error!("grayscale: power off after drive cycle failed: {err:#}");
        }
        ctx.feed_watchdog();

        let totals = cycle_res?;
        let n = totals.refreshes.max(1);
        let total_secs = totals.total.as_secs_f64().max(f64::EPSILON);
        let drive_millihz = ((f64::from(n) / total_secs) * 1000.0).round() as i64;
        let avg_driven = (totals.driven / u64::from(n)) as i64;
        let spi_avg_us = (totals.spi.as_micros() / u128::from(n)) as i64;
        let plan_avg_us = (totals.plan.as_micros() / u128::from(n)) as i64;
        let wait_avg_us = (totals.wait.as_micros() / u128::from(n)) as i64;

        ctx.record_metric("grayscale.drive_millihz", drive_millihz, "mHz", &[]);
        ctx.record_metric("grayscale.refreshes", i64::from(totals.refreshes), "1", &[]);
        ctx.record_metric(
            "grayscale.old_rewrites",
            i64::from(totals.rewrites),
            "1",
            &[],
        );
        ctx.record_metric("grayscale.avg_driven", avg_driven, "1", &[]);
        ctx.record_metric("grayscale.spi_avg_us", spi_avg_us, "us", &[]);
        ctx.record_metric("grayscale.plan_avg_us", plan_avg_us, "us", &[]);
        ctx.record_metric("grayscale.wait_avg_us", wait_avg_us, "us", &[]);

        let compute_us = u32::try_from(totals.plan.as_micros()).unwrap_or(u32::MAX);
        let epd_refresh_us =
            u32::try_from((totals.spi + totals.wait).as_micros()).unwrap_or(u32::MAX);

        Ok(StepOutput {
            sensor_us: 0,
            compute_us,
            epd_refresh_us,
            battery_mv: 0,
            flags: FLAG_EPD_PARTIAL,
            post_burst_delay_ms: 0,
        })
    }

    fn run_drive_loop<B: Board + HasEpd75>(
        &mut self,
        board: &mut B,
        ctx: &mut StepContext<'_>,
    ) -> Result<Stats> {
        let row_bytes = self.planner.row_bytes();
        let cycle_start = Instant::now();
        let mut draining = false;
        let mut window_stats = Stats::default();
        let mut cycle_stats = Stats::default();

        self.flock
            .prepare_triangles(LOGICAL_WIDTH, LOGICAL_HEIGHT, &mut self.triangles);
        let mut plan = {
            let flock = &self.flock;
            let triangles = &self.triangles;
            self.planner.plan_tick_compact(
                |y, row| flock.render_luma_row(triangles, y, row),
                &mut self.row_luma,
                &mut self.new_half,
            )
        };

        loop {
            let refresh_start = Instant::now();
            if plan.rewrite_old {
                let planner = &self.planner;
                board
                    .panel()
                    .write_old_rows(LOGICAL_HEIGHT, row_bytes, |y, dst| {
                        planner.pack_old_row(y, dst);
                    })?;
            }
            board
                .panel()
                .write_new_half_plane(&self.new_half, LOGICAL_HEIGHT, row_bytes)?;
            let sent = Instant::now();
            board.panel().start_drive()?;

            if draining && plan.undrained == 0 {
                board.panel().wait_drive()?;
                info!("drained after ms={}", cycle_start.elapsed().as_millis());
                return Ok(cycle_stats);
            }
            let sent_plan = plan;

            draining |= cycle_start.elapsed() >= FULL_REFRESH_INTERVAL;
            plan = if draining {
                self.planner.plan_tick_compact(
                    |_, row| row.fill(255),
                    &mut self.row_luma,
                    &mut self.new_half,
                )
            } else {
                self.flock.step();
                self.flock
                    .prepare_triangles(LOGICAL_WIDTH, LOGICAL_HEIGHT, &mut self.triangles);
                let flock = &self.flock;
                let triangles = &self.triangles;
                self.planner.plan_tick_compact(
                    |y, row| flock.render_luma_row(triangles, y, row),
                    &mut self.row_luma,
                    &mut self.new_half,
                )
            };
            let planned = Instant::now();

            board.panel().wait_drive()?;
            ctx.feed_watchdog();
            // Let the idle task run so the system stays responsive.
            FreeRtos::delay_ms(1);
            let done = Instant::now();

            let spi = sent - refresh_start;
            let plan_dur = planned - sent;
            let wait = done - planned;
            let total = done - refresh_start;

            window_stats.add(
                sent_plan.rewrite_old,
                sent_plan.driven,
                spi,
                plan_dur,
                wait,
                total,
            );
            cycle_stats.add(
                sent_plan.rewrite_old,
                sent_plan.driven,
                spi,
                plan_dur,
                wait,
                total,
            );

            if window_stats.refreshes == STATS_EVERY {
                window_stats.log(sent_plan.pending_flips);
                window_stats = Stats::default();
            }
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
    fn add(
        &mut self,
        rewrite_old: bool,
        driven: usize,
        spi: Duration,
        plan: Duration,
        wait: Duration,
        total: Duration,
    ) {
        self.refreshes += 1;
        self.rewrites += u32::from(rewrite_old);
        self.driven += driven as u64;
        self.spi += spi;
        self.plan += plan;
        self.wait += wait;
        self.total += total;
    }

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
