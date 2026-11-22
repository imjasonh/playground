//! epd-maze — Waveshare 7.5″ 800×480 e-Paper (ESP32 Xtensa) maze animator with
//! shared mcu-lab BLE telemetry, 1 kHz Xtensa PC profiler, and on-demand BLE GATT OTA.

use std::thread;
use std::time::{Duration, Instant};

use anyhow::Result;
use esp_idf_svc::hal::peripherals::Peripherals;
use esp_idf_svc::sys::{esp_random, esp_reset_reason};
use log::{info, warn};
use mcu_lab::ble_ota::{mark_ota_slot_valid_if_pending, BleOtaNode};
use mcu_lab::epd_display::Panel;
use mcu_lab::maze::{
    crop_packed, dirty_rect, generate, layout_for, render_empty, render_progress, solve,
    CELLS_PER_TICK, HOLD_COMPLETE_MS, MAZE_COLS, MAZE_FIRMWARE_ID, MAZE_ROWS, TICK_MS,
};
use mcu_lab::profiler::{now_us, WakeProfiler};
use mcu_lab::protocol::{
    encode_board_flags, format_status_line, reset_reason_name, BoardConfig, PhaseAccumulator,
    BOARD_WAVESHARE_EPD75, CHIP_ID_ESP32, FLAG_BROWNOUT_RESET, FLAG_EPD_ATTACHED, FLAG_EPD_PARTIAL,
};

const BOARD: BoardConfig = BoardConfig {
    board_id: BOARD_WAVESHARE_EPD75,
    board: "waveshare-epd-75",
    chip: "esp32",
    app: "epd-maze",
    gap_name: "EPD-75",
    chip_id: CHIP_ID_ESP32,
    cpu_mhz: 240,
};

/// USB-powered Waveshare board advertises for 500 ms per cycle so the iPhone
/// easily catches the BLE OTA / profile pull window without deep-sleep races.
const BLE_BURST_MS: u32 = 500;

/// Nominal USB rail voltage reported in `battery_mv` (5.0 V USB-powered board).
const USB_RAIL_MV: u16 = 5000;

fn main() -> Result<()> {
    esp_idf_svc::sys::link_patches();
    esp_idf_svc::log::EspLogger::initialize_default();

    let reset_code = unsafe { esp_reset_reason() } as i32;
    let reset_name = reset_reason_name(reset_code);
    info!(
        "{MAZE_FIRMWARE_ID} boot (board={}, reset={reset_name}({reset_code}))",
        BOARD.board
    );

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

    let ble = BleOtaNode::init(BOARD);
    let mut acc = PhaseAccumulator::new();
    let mut ota_verified = false;

    loop {
        if let Err(err) = run_cycle(&mut panel, &ble, &mut acc, reset_code, &mut ota_verified) {
            warn!("epd-maze cycle failed: {err:#}");
            thread::sleep(Duration::from_secs(2));
        }
    }
}

fn run_cycle(
    panel: &mut Panel,
    ble: &BleOtaNode,
    acc: &mut PhaseAccumulator,
    reset_code: i32,
    ota_verified: &mut bool,
) -> Result<()> {
    let cycle_start = now_us();
    let mut prof = WakeProfiler::start(BOARD, cycle_start);

    // Phase 1 (sensor): entropy seed generation.
    let seed_start = now_us();
    let seed = mix_seed();
    let sensor_us = u32::try_from(now_us().saturating_sub(seed_start)).unwrap_or(u32::MAX);
    prof.record("maze.seed", "sensor", seed_start, now_us());

    // Phase 2 (compute): generate + solve + render initial empty maze.
    let compute_start = now_us();
    let gen_start = now_us();
    let maze = generate(MAZE_COLS, MAZE_ROWS, seed);
    prof.record("maze.generate", "compute", gen_start, now_us());

    let solve_start = now_us();
    let path = solve(&maze);
    prof.record("maze.solve", "compute", solve_start, now_us());

    let render_start = now_us();
    let layout = layout_for(maze.cols, maze.rows);
    let empty = render_empty(&maze, &layout);
    prof.record("maze.render_empty", "compute", render_start, now_us());
    let compute_us = u32::try_from(now_us().saturating_sub(compute_start)).unwrap_or(u32::MAX);

    let step = CELLS_PER_TICK.max(1);
    info!(
        "maze {}x{} seed={seed:#x} path={} pace={}/{TICK_MS}ms",
        maze.cols,
        maze.rows,
        path.len(),
        step
    );

    // Phase 3 (epd_refresh): full refresh of empty maze + partial refreshes for path animation.
    let epd_start = now_us();
    panel.show_frame_awake(&empty)?;
    let full_end = now_us();
    prof.record("epd.full_refresh", "epd_refresh", epd_start, full_end);

    if !*ota_verified {
        mark_ota_slot_valid_if_pending();
        *ota_verified = true;
    }

    // Broadcast BLE telemetry right after the initial full paint so an armed iPhone
    // doesn't have to wait for the entire maze animation to finish before OTA-ing.
    let mut flags = FLAG_EPD_ATTACHED | encode_board_flags(BOARD.board_id);
    if reset_code == 9 {
        flags |= FLAG_BROWNOUT_RESET;
    }
    let full_epd_us = u32::try_from(full_end.saturating_sub(epd_start)).unwrap_or(u32::MAX);
    let initial_metrics = acc.record_wake(sensor_us, compute_us, full_epd_us, USB_RAIL_MV, flags);
    let initial_profile = prof.finish_json(&initial_metrics);
    info!("{}", format_status_line(&initial_metrics));

    let radio_start = now_us();
    ble.broadcast_burst(&initial_metrics, initial_profile.as_deref(), BLE_BURST_MS);
    acc.record_radio_tx(u32::try_from(now_us().saturating_sub(radio_start)).unwrap_or(u32::MAX));

    if path.is_empty() {
        thread::sleep(Duration::from_millis(HOLD_COMPLETE_MS));
        panel.sleep()?;
        return Ok(());
    }

    panel.enter_partial_mode()?;
    let mut shown = 0usize;
    while shown < path.len() {
        let tick = Instant::now();
        let next = (shown + step).min(path.len());

        let tick_start = now_us();
        let mut tick_prof = WakeProfiler::start(BOARD, tick_start);

        let r_start = now_us();
        let frame = render_progress(&maze, &layout, &path, next);
        let Some(rect) = dirty_rect(&layout, &path, shown, next).clamped() else {
            shown = next;
            continue;
        };
        let window = crop_packed(&frame, rect);
        let r_end = now_us();
        tick_prof.record("maze.render_progress", "compute", r_start, r_end);
        let tick_compute_us = u32::try_from(r_end.saturating_sub(r_start)).unwrap_or(u32::MAX);

        if window.is_empty() {
            shown = next;
            continue;
        }

        let p_start = now_us();
        panel.show_partial(&window, rect)?;
        let p_end = now_us();
        tick_prof.record("epd.partial_refresh", "epd_refresh", p_start, p_end);
        let tick_epd_us = u32::try_from(p_end.saturating_sub(p_start)).unwrap_or(u32::MAX);

        let part_flags = flags | FLAG_EPD_PARTIAL;
        let tick_metrics =
            acc.record_wake(0, tick_compute_us, tick_epd_us, USB_RAIL_MV, part_flags);
        let tick_profile = tick_prof.finish_json(&tick_metrics);

        let tx_start = now_us();
        ble.broadcast_burst(&tick_metrics, tick_profile.as_deref(), BLE_BURST_MS);
        acc.record_radio_tx(u32::try_from(now_us().saturating_sub(tx_start)).unwrap_or(u32::MAX));

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
