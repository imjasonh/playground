//! `GrayscaleApp` — experimental grayscale video drive with a flocking boids
//! scene on any board implementing [`Board`] + [`HasEpd75`].
//!
//! Alternates between two steps:
//! 1. **Full refresh**: factory full refresh to white + power off (~4 s), so
//!    boot-time BLE telemetry and OTA rollback verification complete quickly.
//! 2. **Drive segments**: loads the custom one-frame waveform LUTs and drives the
//!    boids flock in ~8 s segments (a BLE window follows each). Every ~30 s it drains
//!    every pixel back to white without flashing, and every 20 drains it runs a full refresh.
//!    The panel powers off at the end of each segment.
//!
//! Uses row-by-row triangle rendering and compact half-plane planning (~128 KiB
//! peak during drive). The 24 KiB half-plane buffer is freed after every segment,
//! and the 96 KiB [`DrivePlanner`] is allocated lazily and released via
//! [`App::memory_reclaimer`] before BLE OTA or coredump uploads so the 43 KiB
//! deflate decoder never OOMs on a no-PSRAM ESP32.

use std::sync::{Arc, Mutex};
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
const DRAIN_INTERVAL: Duration = Duration::from_secs(30);

/// Longest uninterrupted drive segment. Between segments the app returns to the
/// platform loop, which advertises a BLE burst so OTA can connect.
const DRIVE_SEGMENT: Duration = Duration::from_secs(8);

/// Non-flashing drains (every pixel driven back to white) between factory full refreshes.
const DRAINS_PER_FULL_REFRESH: u32 = 20;

/// Serial log cadence (in refreshes) inside a drive cycle.
const STATS_EVERY: u32 = 50;

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
enum Phase {
    FullRefresh,
    DriveCycle,
}

#[derive(Default)]
struct PlannerSlot {
    planner: Option<DrivePlanner>,
    reclaimed: bool,
}

/// Experimental 20+ Hz grayscale boids application for 7.5″ 800×480 e-Paper boards.
pub struct GrayscaleApp {
    phase: Phase,
    luts: DriveLuts,
    /// Allocated lazily on entering `DriveCycle` (after `BleOtaNode::init`) and
    /// released via [`App::memory_reclaimer`] before BLE OTA or coredump reads
    /// so the 32 KiB deflate dictionary + 11 KiB decompressor never OOM on a
    /// no-PSRAM ESP32.
    planner: Arc<Mutex<PlannerSlot>>,
    flock: Flock,
    triangles: Vec<RenderTriangle>,
    row_luma: Vec<u8>,
    /// Drive time since the last drain.
    drive_elapsed: Duration,
    draining: bool,
    drains: u32,
}

impl<B: Board + HasEpd75> App<B> for GrayscaleApp {
    const APP_NAME: &'static str = "grayscale";
    const FIRMWARE_ID: &'static str = GRAYSCALE_FIRMWARE_ID;

    fn run_mode() -> RunMode {
        RunMode::Continuous {
            burst_ms: 1500,
            min_step_ms: 0,
        }
    }

    fn init(_board: &mut B) -> Result<Self> {
        info!("{GRAYSCALE_FIRMWARE_ID} init spi_mhz={SPI_MHZ} frames_per_step={FRAMES_PER_STEP}");
        let luts = DriveLuts::new(FRAMES_PER_STEP, SWAP_DRIVE_POLARITY);
        let flock = Flock::new(FlockConfig::default(), FLOCK_SEED);
        let mut triangles = Vec::new();
        flock.prepare_triangles(LOGICAL_WIDTH, LOGICAL_HEIGHT, &mut triangles);
        let row_luma = vec![255u8; LOGICAL_WIDTH];
        Ok(Self {
            phase: Phase::FullRefresh,
            luts,
            planner: Arc::new(Mutex::new(PlannerSlot::default())),
            flock,
            triangles,
            row_luma,
            drive_elapsed: Duration::ZERO,
            draining: false,
            drains: 0,
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

    fn memory_reclaimer(&self) -> Option<Arc<dyn Fn() + Send + Sync>> {
        let planner = Arc::clone(&self.planner);
        Some(Arc::new(move || {
            if let Ok(mut slot) = planner.try_lock() {
                if slot.planner.take().is_some() {
                    slot.reclaimed = true;
                    info!("grayscale: released DrivePlanner for BLE OTA/coredump");
                }
            }
        }))
    }

    fn step(&mut self, board: &mut B, ctx: &mut StepContext<'_>) -> Result<StepOutput> {
        if self.phase == Phase::DriveCycle {
            let reclaimed = self
                .planner
                .lock()
                .unwrap_or_else(|e| e.into_inner())
                .reclaimed;
            if reclaimed {
                // Planner was released during BLE OTA/coredump; recover cleanly
                // with a full refresh so physical ink matches zeroed levels.
                self.phase = Phase::FullRefresh;
            }
        }
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
        {
            let mut slot = self.planner.lock().unwrap_or_else(|e| e.into_inner());
            if let Some(planner) = slot.planner.as_mut() {
                planner.reset_white();
            }
            slot.reclaimed = false;
        }
        self.drive_elapsed = Duration::ZERO;
        self.draining = false;
        self.drains = 0;
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
        // On error, recover with a clean full refresh.
        self.phase = Phase::FullRefresh;

        let planner_arc = Arc::clone(&self.planner);
        let mut slot = planner_arc.lock().unwrap_or_else(|e| e.into_inner());
        let planner = slot.planner.get_or_insert_with(|| {
            DrivePlanner::new(LOGICAL_WIDTH, LOGICAL_HEIGHT, DriveConfig::default())
        });
        // Keep the 24 KiB half-plane buffer local to the drive cycle so it is
        // always freed before the platform BLE burst / OTA window.
        let mut new_half = vec![0u8; planner.half_plane_bytes()];

        let init_start = now_us();
        if let Err(err) = board.panel().init_drive(&self.luts) {
            let _ = board.panel().power_off();
            return Err(err);
        }
        // The controller reset in init_drive lost its old plane.
        planner.invalidate_old();
        let init_end = now_us();
        ctx.record_span("grayscale.init_drive", "epd_refresh", init_start, init_end);
        ctx.feed_watchdog();

        let cycle_start_us = now_us();
        let cycle_res = self.run_drive_loop(board, ctx, planner, &mut new_half);
        let cycle_end_us = now_us();
        ctx.record_span(
            "grayscale.drive_cycle",
            "epd_refresh",
            cycle_start_us,
            cycle_end_us,
        );
        drop(new_half);
        drop(slot);

        if let Err(err) = board.panel().power_off() {
            error!("grayscale: power off after drive cycle failed: {err:#}");
        }
        ctx.feed_watchdog();

        let totals = cycle_res?;
        self.drive_elapsed += totals.total;
        if self.drive_elapsed >= DRAIN_INTERVAL {
            self.draining = true;
        }
        self.phase = if self.drains >= DRAINS_PER_FULL_REFRESH {
            Phase::FullRefresh
        } else {
            Phase::DriveCycle
        };
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
        planner: &mut DrivePlanner,
        new_half: &mut [u8],
    ) -> Result<Stats> {
        let row_bytes = planner.row_bytes();
        let cycle_start = Instant::now();
        let mut window_stats = Stats::default();
        let mut cycle_stats = Stats::default();

        self.flock
            .prepare_triangles(LOGICAL_WIDTH, LOGICAL_HEIGHT, &mut self.triangles);
        let mut plan = {
            let flock = &self.flock;
            let triangles = &self.triangles;
            planner.plan_tick_compact(
                |y, row| flock.render_luma_row(triangles, y, row),
                &mut self.row_luma,
                new_half,
            )
        };

        loop {
            let refresh_start = Instant::now();
            if plan.rewrite_old {
                board
                    .panel()
                    .write_old_rows(LOGICAL_HEIGHT, row_bytes, |y, dst| {
                        planner.pack_old_row(y, dst);
                    })?;
            }
            board
                .panel()
                .write_new_half_plane(new_half, LOGICAL_HEIGHT, row_bytes)?;
            let sent = Instant::now();
            board.panel().start_drive()?;

            if self.draining && plan.undrained == 0 {
                board.panel().wait_drive()?;
                self.drains += 1;
                self.drive_elapsed = Duration::ZERO;
                self.draining = false;
                info!("drained after ms={}", cycle_start.elapsed().as_millis());
                return Ok(cycle_stats);
            }
            if cycle_start.elapsed() >= DRIVE_SEGMENT {
                // Finish the plan already sent; never leave a planned tick unsent.
                board.panel().wait_drive()?;
                return Ok(cycle_stats);
            }
            let sent_plan = plan;

            plan = if self.draining {
                planner.plan_tick_compact(|_, row| row.fill(255), &mut self.row_luma, new_half)
            } else {
                self.flock.step();
                self.flock
                    .prepare_triangles(LOGICAL_WIDTH, LOGICAL_HEIGHT, &mut self.triangles);
                let flock = &self.flock;
                let triangles = &self.triangles;
                planner.plan_tick_compact(
                    |y, row| flock.render_luma_row(triangles, y, row),
                    &mut self.row_luma,
                    new_half,
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
