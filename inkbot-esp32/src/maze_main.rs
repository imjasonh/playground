//! maze-esp32 — generate a maze on the Waveshare 7.5″ and animate the solution.
//!
//! No Wi-Fi, HTTP, or Worker: flash, power the board, and the panel loops
//! empty maze → correct solve (~1 s partials) → hold → next maze.

mod maze_display;

use std::thread;
use std::time::{Duration, Instant};

use anyhow::Result;
use esp_idf_svc::hal::peripherals::Peripherals;
use esp_idf_svc::sys::esp_random;
use log::info;

use inkbot_esp32::maze::{
    cells_per_frame, crop_packed, dirty_rect, generate, layout_for, render_empty, render_progress,
    solve, HOLD_COMPLETE_MS, MAZE_COLS, MAZE_FIRMWARE_ID, MAZE_ROWS, TARGET_FRAMES, TICK_MS,
};
use maze_display::Panel;

fn main() -> Result<()> {
    esp_idf_svc::sys::link_patches();
    esp_idf_svc::log::EspLogger::initialize_default();
    info!("{MAZE_FIRMWARE_ID} boot");

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

    loop {
        let seed = mix_seed();
        let maze = generate(MAZE_COLS, MAZE_ROWS, seed);
        let path = solve(&maze);
        let layout = layout_for(maze.cols, maze.rows);
        info!(
            "maze {}x{} seed={seed:#x} path={}",
            maze.cols,
            maze.rows,
            path.len()
        );

        let empty = render_empty(&maze, &layout);
        panel.show_frame_awake(&empty)?;
        thread::sleep(Duration::from_millis(TICK_MS));

        if path.is_empty() {
            info!("no path; holding empty maze");
            thread::sleep(Duration::from_millis(HOLD_COMPLETE_MS));
            panel.sleep()?;
            continue;
        }

        panel.enter_partial_mode()?;
        let step = cells_per_frame(path.len(), TARGET_FRAMES);
        let mut shown = 0usize;
        while shown < path.len() {
            let tick = Instant::now();
            let next = (shown + step).min(path.len());
            let frame = render_progress(&maze, &layout, &path, next);
            let rect = dirty_rect(&layout, &path, shown, next);
            let window = crop_packed(&frame, rect);
            panel.show_partial(&window, rect)?;
            shown = next;
            let wait = Duration::from_millis(TICK_MS).saturating_sub(tick.elapsed());
            if !wait.is_zero() {
                thread::sleep(wait);
            }
        }

        thread::sleep(Duration::from_millis(HOLD_COMPLETE_MS));
        panel.sleep()?;
    }
}

fn mix_seed() -> u64 {
    let a = u64::from(unsafe { esp_random() });
    let b = u64::from(unsafe { esp_random() });
    a | (b << 32)
}
