//! `MazeApp` — generates, solves, and animates mazes on any board implementing
//! [`Board`] + [`HasEpd75`], without hardcoding any GPIO pins or SPI setup.

use anyhow::Result;
use esp_idf_svc::sys::esp_random;
use log::info;

use crate::boards::{Board, HasEpd75};
use crate::maze::{
    crop_packed, dirty_rect, generate, layout_for, render_empty, render_progress, solve, Cell,
    Layout, Maze, CELLS_PER_TICK, HOLD_COMPLETE_MS, MAZE_COLS, MAZE_FIRMWARE_ID, MAZE_ROWS,
    TICK_MS,
};
use crate::platform::{McuApp, RunMode, StepContext, StepOutput};
use crate::profiler::now_us;
use crate::protocol::FLAG_EPD_PARTIAL;

struct ActiveMaze {
    maze: Maze,
    layout: Layout,
    path: Vec<Cell>,
    shown: usize,
}

/// Animated maze solver application for 7.5″ 800×480 e-Paper boards.
pub struct MazeApp {
    active: Option<ActiveMaze>,
}

impl<B: Board + HasEpd75> McuApp<B> for MazeApp {
    const APP_NAME: &'static str = "maze";
    const FIRMWARE_ID: &'static str = MAZE_FIRMWARE_ID;

    fn run_mode() -> RunMode {
        RunMode::Continuous {
            burst_ms: 500,
            min_step_ms: TICK_MS,
        }
    }

    fn init(_board: &mut B) -> Result<Self> {
        Ok(Self { active: None })
    }

    fn step(&mut self, board: &mut B, ctx: &mut StepContext<'_>) -> Result<StepOutput> {
        if let Some(mut state) = self.active.take() {
            let step = CELLS_PER_TICK.max(1);
            let next = (state.shown + step).min(state.path.len());

            let ((window, rect_opt), compute_us) =
                ctx.measure_span("maze.render_progress", "compute", || {
                    let frame = render_progress(&state.maze, &state.layout, &state.path, next);
                    match dirty_rect(&state.layout, &state.path, state.shown, next).clamped() {
                        Some(rect) => (crop_packed(&frame, rect), Some(rect)),
                        None => (Vec::new(), None),
                    }
                });

            let mut epd_us = 0u32;
            if let Some(rect) = rect_opt {
                if !window.is_empty() {
                    let p_start = now_us();
                    board.panel().show_partial(&window, rect)?;
                    let p_end = now_us();
                    ctx.record_span("epd.partial_refresh", "epd_refresh", p_start, p_end);
                    epd_us = u32::try_from(p_end.saturating_sub(p_start)).unwrap_or(u32::MAX);
                }
            }

            state.shown = next;
            let finished = state.shown >= state.path.len();
            let post_burst_delay_ms = if finished {
                board.panel().sleep()?;
                HOLD_COMPLETE_MS
            } else {
                self.active = Some(state);
                0
            };

            return Ok(StepOutput {
                sensor_us: 0,
                compute_us,
                epd_refresh_us: epd_us,
                battery_mv: 0,
                flags: FLAG_EPD_PARTIAL,
                post_burst_delay_ms,
            });
        }

        // Start a fresh maze cycle: seed -> generate -> solve -> full refresh -> enter partial mode.
        let (seed, sensor_us) = ctx.measure_span("maze.seed", "sensor", mix_seed);

        let compute_start = now_us();
        let (maze, _) = ctx.measure_span("maze.generate", "compute", || {
            generate(MAZE_COLS, MAZE_ROWS, seed)
        });
        let (path, _) = ctx.measure_span("maze.solve", "compute", || solve(&maze));
        let ((layout, empty), _) = ctx.measure_span("maze.render_empty", "compute", || {
            let layout = layout_for(maze.cols, maze.rows);
            let empty = render_empty(&maze, &layout);
            (layout, empty)
        });
        let compute_us = u32::try_from(now_us().saturating_sub(compute_start)).unwrap_or(u32::MAX);

        info!(
            "maze {}x{} seed={seed:#x} path={} pace={}/{TICK_MS}ms",
            maze.cols,
            maze.rows,
            path.len(),
            CELLS_PER_TICK.max(1)
        );

        let epd_start = now_us();
        board.panel().show_frame_awake(&empty)?;
        let epd_end = now_us();
        ctx.record_span("epd.full_refresh", "epd_refresh", epd_start, epd_end);
        ctx.feed_watchdog();
        let epd_us = u32::try_from(epd_end.saturating_sub(epd_start)).unwrap_or(u32::MAX);

        let post_burst_delay_ms = if path.is_empty() {
            board.panel().sleep()?;
            HOLD_COMPLETE_MS
        } else {
            board.panel().enter_partial_mode()?;
            self.active = Some(ActiveMaze {
                maze,
                layout,
                path,
                shown: 0,
            });
            0
        };

        Ok(StepOutput {
            sensor_us,
            compute_us,
            epd_refresh_us: epd_us,
            battery_mv: 0,
            flags: 0,
            post_burst_delay_ms,
        })
    }
}

fn mix_seed() -> u64 {
    let a = u64::from(unsafe { esp_random() });
    let b = u64::from(unsafe { esp_random() });
    a | (b << 32)
}
