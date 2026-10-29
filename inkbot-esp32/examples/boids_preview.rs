//! Host preview of what grayscale-esp32's boids scene looks like after the
//! drive planner, at one frame per panel refresh. Not part of the firmware.
//!
//! Writes raw 800×480 gray frames to stdout. The planner's level is the
//! estimated ink: 0 is white, `swing` is black.

use std::io::{self, Write};

use inkbot_esp32::grayscale::drive::{DriveConfig, DrivePlanner};
use inkbot_esp32::grayscale::scene::BoidsScene;
use inkbot_esp32::grayscale::{LOGICAL_HEIGHT, LOGICAL_WIDTH};

const PANEL_W: usize = LOGICAL_WIDTH * 2;
const PANEL_H: usize = LOGICAL_HEIGHT * 2;

fn main() {
    let frames: usize = std::env::args()
        .nth(1)
        .and_then(|s| s.parse().ok())
        .unwrap_or(484);
    let config = DriveConfig::default();
    let mut scene = BoidsScene::new(0x5EED_B01D);
    let mut planner = DrivePlanner::new(LOGICAL_WIDTH, LOGICAL_HEIGHT, config);
    let mut old = vec![0u8; planner.plane_bytes()];
    let mut new = vec![0u8; planner.plane_bytes()];
    let mut frame = vec![255u8; PANEL_W * PANEL_H];
    let mut out = io::BufWriter::new(io::stdout());
    let swing = u16::from(config.swing);

    let mut prev_cx = 0.0f32;
    for i in 0..frames {
        planner.plan_tick(|x, y| scene.luma(x, y), &mut old, &mut new);

        let mut mass = 0u64;
        let mut sum_x = 0u64;
        let mut sum_level = 0u64;
        let mut lag = 0u64;
        let mut max_level = 0u8;
        for y in 0..LOGICAL_HEIGHT {
            for x in 0..LOGICAL_WIDTH {
                let level = planner.level(x, y);
                max_level = max_level.max(level);
                let target = planner.target_level(scene.luma(x, y));
                lag += u64::from(level.abs_diff(target));
                sum_level += u64::from(level);
                if level > 0 {
                    mass += u64::from(level);
                    sum_x += u64::from(level) * x as u64;
                }
                let g = 255 - ((u16::from(level) * 255) / swing) as u8;
                let px = x * 2;
                let row0 = (y * 2) * PANEL_W + px;
                let row1 = row0 + PANEL_W;
                frame[row0] = g;
                frame[row0 + 1] = g;
                frame[row1] = g;
                frame[row1 + 1] = g;
            }
        }
        out.write_all(&frame).unwrap();

        if i > 0 && i % 22 == 0 {
            let cx = if mass == 0 {
                0.0
            } else {
                sum_x as f32 / mass as f32
            };
            eprintln!(
                "t={:.1}s mean_level={:.2} max_level={max_level} mean_lag={:.2} centroid_x={:.1} dx={:.2}px/s",
                i as f32 / 22.0,
                sum_level as f32 / (LOGICAL_WIDTH * LOGICAL_HEIGHT) as f32,
                lag as f32 / (LOGICAL_WIDTH * LOGICAL_HEIGHT) as f32,
                cx,
                (cx - prev_cx) * 22.0,
            );
            prev_cx = cx;
        }
        if i + 1 != frames {
            scene.step();
        }
    }
    out.flush().unwrap();
}
