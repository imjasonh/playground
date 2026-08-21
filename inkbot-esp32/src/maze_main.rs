//! maze-esp32 — generate a maze on the Waveshare 7.5″ and animate the solution.
//!
//! No Wi-Fi, HTTP, or Worker: this image never polls GHCR. inkbot can OTA
//! *into* maze; returning to inkbot is a USB flash (`make flash`).

mod maze_display;
mod nvs_util;
mod ota_slot;

use std::thread;
use std::time::{Duration, Instant};

use anyhow::Result;
use esp_idf_svc::hal::peripherals::Peripherals;
use esp_idf_svc::nvs::EspDefaultNvsPartition;
use esp_idf_svc::sys::esp_random;
use log::{error, info, warn};

use inkbot_esp32::maze::{
    crop_packed, dirty_rect, generate, layout_for, render_empty, render_progress, solve,
    CELLS_PER_TICK, HOLD_COMPLETE_MS, MAZE_COLS, MAZE_FIRMWARE_ID, MAZE_ROWS, TICK_MS,
};
use maze_display::Panel;

fn main() -> Result<()> {
    esp_idf_svc::sys::link_patches();
    esp_idf_svc::log::EspLogger::initialize_default();
    info!("{MAZE_FIRMWARE_ID} boot");

    let nvs_part = EspDefaultNvsPartition::take()?;
    let pending_verify = ota_slot::is_pending_verify();
    if pending_verify {
        info!("ota: image is PENDING_VERIFY — first successful paint will mark valid");
    } else if let Err(e) = ota_slot::remember_rolled_back_digest(nvs_part.clone()) {
        warn!("ota: reconcile rolled-back digest: {e:#}");
    }

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

    let mut marked_valid = !pending_verify;
    loop {
        let result = run_cycle(&mut panel, || {
            if marked_valid {
                return Ok(());
            }
            match ota_slot::mark_valid_after_pending_verify_passed(nvs_part.clone()) {
                Ok(()) => {
                    info!("ota: pending-verify passed (panel painted)");
                    marked_valid = true;
                    Ok(())
                }
                Err(e) => {
                    error!("ota: mark-valid failed ({e:#}); rolling back");
                    thread::sleep(Duration::from_secs(2));
                    ota_slot::reject_pending_and_reboot(nvs_part.clone());
                }
            }
        });
        if let Err(e) = result {
            warn!("maze cycle failed: {e:#}");
            thread::sleep(Duration::from_secs(2));
        }
    }
}

fn run_cycle(panel: &mut Panel, mut on_first_paint: impl FnMut() -> Result<()>) -> Result<()> {
    let seed = mix_seed();
    let maze = generate(MAZE_COLS, MAZE_ROWS, seed);
    let path = solve(&maze);
    let layout = layout_for(maze.cols, maze.rows);
    let step = CELLS_PER_TICK.max(1);
    info!(
        "maze {}x{} seed={seed:#x} path={} pace={}/{TICK_MS}ms",
        maze.cols,
        maze.rows,
        path.len(),
        step
    );

    let empty = render_empty(&maze, &layout);
    panel.show_frame_awake(&empty)?;
    on_first_paint()?;
    thread::sleep(Duration::from_millis(TICK_MS));

    if path.is_empty() {
        info!("no path; holding empty maze");
        thread::sleep(Duration::from_millis(HOLD_COMPLETE_MS));
        panel.sleep()?;
        return Ok(());
    }

    panel.enter_partial_mode()?;
    let mut shown = 0usize;
    while shown < path.len() {
        let tick = Instant::now();
        let next = (shown + step).min(path.len());
        let frame = render_progress(&maze, &layout, &path, next);
        let Some(rect) = dirty_rect(&layout, &path, shown, next).clamped() else {
            shown = next;
            continue;
        };
        let window = crop_packed(&frame, rect);
        if window.is_empty() {
            shown = next;
            continue;
        }
        panel.show_partial(&window, rect)?;
        shown = next;
        let wait = Duration::from_millis(TICK_MS).saturating_sub(tick.elapsed());
        if !wait.is_zero() {
            thread::sleep(wait);
        }
    }

    thread::sleep(Duration::from_millis(HOLD_COMPLETE_MS));
    panel.sleep()?;
    Ok(())
}

fn mix_seed() -> u64 {
    let a = u64::from(unsafe { esp_random() });
    let b = u64::from(unsafe { esp_random() });
    a | (b << 32)
}
