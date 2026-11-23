//! epd-maze — Waveshare 7.5″ 800×480 e-Paper (ESP32 Xtensa) maze animator built
//! on [`mcu_lab::platform::McuApp`].

use anyhow::Result;
use esp_idf_svc::hal::peripherals::Peripherals;
use esp_idf_svc::sys::esp_random;
use log::info;
use mcu_lab::epd_display::Panel;
use mcu_lab::maze::{
    crop_packed, dirty_rect, generate, layout_for, render_empty, render_progress, solve, Layout,
    Maze, CELLS_PER_TICK, HOLD_COMPLETE_MS, MAZE_COLS, MAZE_FIRMWARE_ID, MAZE_ROWS, TICK_MS,
};
use mcu_lab::platform::{McuApp, RunMode, StepContext, StepOutput};
use mcu_lab::profiler::now_us;
use mcu_lab::protocol::{
    BoardConfig, BOARD_WAVESHARE_EPD75, CHIP_ID_ESP32, FLAG_EPD_ATTACHED, FLAG_EPD_PARTIAL,
};

/// Nominal USB rail voltage reported in `battery_mv` (5.0 V USB-powered board).
const USB_RAIL_MV: u16 = 5000;

struct ActiveMaze {
    maze: Maze,
    layout: Layout,
    path: Vec<usize>,
    shown: usize,
}

struct EpdMazeApp {
    panel: Panel,
    active: Option<ActiveMaze>,
}

impl McuApp for EpdMazeApp {
    const BOARD: BoardConfig = BoardConfig {
        board_id: BOARD_WAVESHARE_EPD75,
        board: "waveshare-epd-75",
        chip: "esp32",
        app: "epd-maze",
        gap_name: "EPD-75",
        chip_id: CHIP_ID_ESP32,
        cpu_mhz: 240,
        min_ota_battery_mv: 0, // USB-powered board
    };

    const FIRMWARE_ID: &'static str = MAZE_FIRMWARE_ID;

    const RUN_MODE: RunMode = RunMode::Continuous {
        burst_ms: 500,
        min_step_ms: TICK_MS,
    };

    fn init(peripherals: Peripherals) -> Result<Self> {
        let panel = Panel::new(
            peripherals.spi2,
            peripherals.pins.gpio13,
            peripherals.pins.gpio14,
            peripherals.pins.gpio15,
            peripherals.pins.gpio25,
            peripherals.pins.gpio27,
            peripherals.pins.gpio26,
        )?;
        Ok(Self {
            panel,
            active: None,
        })
    }

    fn step(&mut self, ctx: &mut StepContext<'_>) -> Result<StepOutput> {
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
                    self.panel.show_partial(&window, rect)?;
                    let p_end = now_us();
                    ctx.record_span("epd.partial_refresh", "epd_refresh", p_start, p_end);
                    epd_us = u32::try_from(p_end.saturating_sub(p_start)).unwrap_or(u32::MAX);
                }
            }

            state.shown = next;
            let finished = state.shown >= state.path.len();
            let post_burst_delay_ms = if finished {
                self.panel.sleep()?;
                HOLD_COMPLETE_MS
            } else {
                self.active = Some(state);
                0
            };

            return Ok(StepOutput {
                sensor_us: 0,
                compute_us,
                epd_refresh_us: epd_us,
                battery_mv: USB_RAIL_MV,
                flags: FLAG_EPD_ATTACHED | FLAG_EPD_PARTIAL,
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
        self.panel.show_frame_awake(&empty)?;
        let epd_end = now_us();
        ctx.record_span("epd.full_refresh", "epd_refresh", epd_start, epd_end);
        ctx.feed_watchdog();
        let epd_us = u32::try_from(epd_end.saturating_sub(epd_start)).unwrap_or(u32::MAX);

        let post_burst_delay_ms = if path.is_empty() {
            self.panel.sleep()?;
            HOLD_COMPLETE_MS
        } else {
            self.panel.enter_partial_mode()?;
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
            battery_mv: USB_RAIL_MV,
            flags: FLAG_EPD_ATTACHED,
            post_burst_delay_ms,
        })
    }
}

fn mix_seed() -> u64 {
    let a = u64::from(unsafe { esp_random() });
    let b = u64::from(unsafe { esp_random() });
    a | (b << 32)
}

fn main() -> Result<()> {
    mcu_lab::platform::run::<EpdMazeApp>()
}
