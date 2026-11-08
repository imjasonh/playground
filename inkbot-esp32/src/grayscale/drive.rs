//! Per-pixel drive planner for the custom waveform in [`super::lut`].
//!
//! Each refresh moves a pixel one step toward black, one step toward
//! white, or not at all. The planner estimates every logical pixel's level
//! as a step count: `0` is white right after a factory full refresh, and
//! [`DriveConfig::swing`] steps reach black. It never steps past either
//! end, so a pixel's level is also its net drive: black-ward steps minus
//! white-ward steps since the last full refresh. Driving every pixel back
//! to level `0` (see [`TickPlan::undrained`]) before the next full refresh
//! leaves each pixel with exactly as much white-ward as black-ward drive.
//!
//! The old plane (`DTM1`) holds each pixel's direction and the new plane
//! (`DTM2`) differs from it only where the pixel moves, so a normal refresh
//! sends one 48 KB plane. A pixel that has to reverse waits until the
//! planner rewrites the old plane, at most once every
//! [`DriveConfig::flip_interval`] refreshes; those refreshes send both
//! planes.

use super::LOGICAL_BLOCK;

const WHITE_WARD: u8 = 0x80;
const LEVEL_MASK: u8 = 0x7F;

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub struct DriveConfig {
    /// Steps from white to black. GxEPD2's balanced partial waveform for
    /// this panel spends 30 frames on the color change, so with one frame
    /// per step this is the step count of a full black-white swing.
    pub swing: u8,
    /// A pixel moving the wrong way requests an old-plane rewrite only
    /// when it is more than this many steps from its target.
    pub flip_hysteresis: u8,
    /// Minimum refreshes between old-plane rewrites.
    pub flip_interval: u32,
}

impl Default for DriveConfig {
    fn default() -> Self {
        Self {
            swing: 30,
            flip_hysteresis: 2,
            flip_interval: 4,
        }
    }
}

/// What one [`DrivePlanner::plan_tick`] call produced.
#[derive(Clone, Copy, Debug, Default, PartialEq, Eq)]
pub struct TickPlan {
    /// Send the old plane before the new plane on this refresh.
    pub rewrite_old: bool,
    /// Logical pixels this refresh drives.
    pub driven: usize,
    /// Logical pixels waiting for an old-plane rewrite.
    pub pending_flips: usize,
    /// Logical pixels not at level `0` after this refresh.
    pub undrained: usize,
}

pub struct DrivePlanner {
    width: usize,
    height: usize,
    config: DriveConfig,
    /// One allocation per logical row: bit 7 is the direction, bits 0-6
    /// the level. Row-sized allocations avoid a 96 KB contiguous block,
    /// which a no-PSRAM ESP32 heap may not have.
    rows: Vec<Box<[u8]>>,
    pending_flips: usize,
    ticks_since_flip: u32,
    old_stale: bool,
}

impl DrivePlanner {
    pub fn new(width: usize, height: usize, config: DriveConfig) -> Self {
        assert_eq!(LOGICAL_BLOCK, 2, "plane packing assumes 2x2 blocks");
        assert!(width % 4 == 0, "4 logical pixels fill one plane byte");
        assert!(config.swing > 0 && config.swing <= LEVEL_MASK);
        Self {
            width,
            height,
            config,
            rows: (0..height)
                .map(|_| vec![0u8; width].into_boxed_slice())
                .collect(),
            pending_flips: 0,
            ticks_since_flip: 0,
            old_stale: true,
        }
    }

    /// Bytes in each plane [`DrivePlanner::plan_tick`] writes.
    pub fn plane_bytes(&self) -> usize {
        self.width * self.height * LOGICAL_BLOCK * LOGICAL_BLOCK / 8
    }

    /// Call after a factory full refresh to white. The next plan rewrites
    /// the old plane.
    pub fn reset_white(&mut self) {
        for row in &mut self.rows {
            row.fill(0);
        }
        self.pending_flips = 0;
        self.ticks_since_flip = 0;
        self.old_stale = true;
    }

    /// Steps from white for an 8-bit luma sample (`255` = white).
    pub fn target_level(&self, luma: u8) -> u8 {
        let swing = u16::from(self.config.swing);
        ((u16::from(255 - luma) * swing + 127) / 255) as u8
    }

    pub fn level(&self, x: usize, y: usize) -> u8 {
        self.rows[y][x] & LEVEL_MASK
    }

    /// Plan one refresh toward the image `luma(x, y)` and write both
    /// planes. Send `old` only when [`TickPlan::rewrite_old`] is set; it
    /// always matches what the controller should hold.
    pub fn plan_tick(
        &mut self,
        mut luma: impl FnMut(usize, usize) -> u8,
        old: &mut [u8],
        new: &mut [u8],
    ) -> TickPlan {
        let plane_bytes = self.plane_bytes();
        assert_eq!(old.len(), plane_bytes, "old plane size");
        assert_eq!(new.len(), plane_bytes, "new plane size");

        self.ticks_since_flip = self.ticks_since_flip.saturating_add(1);
        let rewrite_old = self.old_stale
            || (self.pending_flips > 0 && self.ticks_since_flip >= self.config.flip_interval);
        if rewrite_old {
            self.ticks_since_flip = 0;
            self.old_stale = false;
        }

        let mut plan = TickPlan {
            rewrite_old,
            ..TickPlan::default()
        };
        let hysteresis = self.config.flip_hysteresis;
        let row_bytes = self.width / 4;

        for y in 0..self.height {
            let start = y * LOGICAL_BLOCK * row_bytes;
            let (old_row, new_row) = (
                &mut old[start..start + row_bytes],
                &mut new[start..start + row_bytes],
            );
            let mut old_byte = 0u8;
            let mut new_byte = 0u8;
            for x in 0..self.width {
                let target = self.target_level(luma(x, y));
                let cell = &mut self.rows[y][x];
                let mut level = *cell & LEVEL_MASK;
                let mut white_ward = *cell & WHITE_WARD != 0;

                let wants_white = target < level;
                let wants_black = target > level;
                if (white_ward && wants_black) || (!white_ward && wants_white) {
                    if rewrite_old {
                        white_ward = !white_ward;
                    } else if target.abs_diff(level) > hysteresis {
                        plan.pending_flips += 1;
                    }
                }

                let drive = if white_ward { wants_white } else { wants_black };
                if drive {
                    if white_ward {
                        level -= 1;
                    } else {
                        level += 1;
                    }
                    plan.driven += 1;
                }
                if level != 0 {
                    plan.undrained += 1;
                }
                *cell = level | if white_ward { WHITE_WARD } else { 0 };

                old_byte = (old_byte << 2) | if white_ward { 0b11 } else { 0 };
                new_byte = (new_byte << 2) | if white_ward != drive { 0b11 } else { 0 };
                if x % 4 == 3 {
                    old_row[x / 4] = old_byte;
                    new_row[x / 4] = new_byte;
                }
            }
            old.copy_within(start..start + row_bytes, start + row_bytes);
            new.copy_within(start..start + row_bytes, start + row_bytes);
        }

        self.pending_flips = plan.pending_flips;
        plan
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    /// Applies planes the way the custom tables do: a pixel whose old and
    /// new bits differ moves toward black when its old bit is 0 (`WK`) and
    /// toward white when it is 1 (`KW`).
    struct Controller {
        old: Vec<u8>,
        net: Vec<i32>,
    }

    impl Controller {
        fn new(bytes: usize) -> Self {
            Self {
                old: vec![0; bytes],
                net: vec![0; bytes * 8],
            }
        }

        fn refresh(&mut self, plan: TickPlan, old: &[u8], new: &[u8]) {
            if plan.rewrite_old {
                self.old.copy_from_slice(old);
            } else {
                assert_eq!(self.old, old, "old plane changed without a rewrite");
            }
            for (i, net) in self.net.iter_mut().enumerate() {
                let bit = |plane: &[u8]| plane[i / 8] & (0x80 >> (i % 8)) != 0;
                let (o, n) = (bit(&self.old), bit(new));
                if o != n {
                    *net += if o { -1 } else { 1 };
                }
            }
        }
    }

    struct Rig {
        planner: DrivePlanner,
        controller: Controller,
        old: Vec<u8>,
        new: Vec<u8>,
    }

    impl Rig {
        fn new(width: usize, height: usize, config: DriveConfig) -> Self {
            let planner = DrivePlanner::new(width, height, config);
            let bytes = planner.plane_bytes();
            Self {
                planner,
                controller: Controller::new(bytes),
                old: vec![0; bytes],
                new: vec![0; bytes],
            }
        }

        fn tick(&mut self, luma: impl FnMut(usize, usize) -> u8) -> TickPlan {
            let plan = self.planner.plan_tick(luma, &mut self.old, &mut self.new);
            self.controller.refresh(plan, &self.old, &self.new);
            self.check_net_matches_levels();
            plan
        }

        fn check_net_matches_levels(&self) {
            let width = self.planner.width;
            let physical_width = width * LOGICAL_BLOCK;
            for (i, &net) in self.controller.net.iter().enumerate() {
                let (px, py) = (i % physical_width, i / physical_width);
                let level = self.planner.level(px / LOGICAL_BLOCK, py / LOGICAL_BLOCK);
                assert_eq!(net, i32::from(level), "physical pixel ({px}, {py})");
                assert!(level <= self.planner.config.swing);
            }
        }
    }

    /// Deterministic pseudo-random luma, so failures reproduce.
    fn noise(seed: u32, x: usize, y: usize) -> u8 {
        let mut h =
            seed ^ (x as u32).wrapping_mul(0x9E37_79B9) ^ (y as u32).wrapping_mul(0x85EB_CA6B);
        h ^= h >> 15;
        h = h.wrapping_mul(0x2C1B_3C6D);
        h ^= h >> 12;
        (h >> 24) as u8
    }

    #[test]
    fn full_panel_planes_are_frame_sized() {
        let planner = DrivePlanner::new(
            super::super::LOGICAL_WIDTH,
            super::super::LOGICAL_HEIGHT,
            DriveConfig::default(),
        );
        assert_eq!(planner.plane_bytes(), crate::panel::FRAME_BYTES);
    }

    #[test]
    fn target_level_spans_white_to_black() {
        let planner = DrivePlanner::new(4, 1, DriveConfig::default());
        assert_eq!(planner.target_level(255), 0);
        assert_eq!(planner.target_level(0), 30);
        assert_eq!(planner.target_level(128), 15);
    }

    #[test]
    fn first_tick_after_reset_rewrites_old() {
        let mut rig = Rig::new(8, 2, DriveConfig::default());
        assert!(rig.tick(|_, _| 255).rewrite_old);
        assert!(!rig.tick(|_, _| 255).rewrite_old);
        rig.planner.reset_white();
        assert!(rig.tick(|_, _| 255).rewrite_old);
    }

    #[test]
    fn static_image_converges_in_swing_ticks() {
        let config = DriveConfig::default();
        let mut rig = Rig::new(8, 4, config);
        let image = |x: usize, y: usize| noise(7, x, y);
        for _ in 0..config.swing {
            rig.tick(image);
        }
        for y in 0..4 {
            for x in 0..8 {
                let want = rig.planner.target_level(image(x, y));
                assert_eq!(rig.planner.level(x, y), want, "pixel ({x}, {y})");
            }
        }
        assert_eq!(rig.tick(image).driven, 0, "a settled image drives nothing");
    }

    #[test]
    fn random_video_stays_balanced_and_drains_to_zero() {
        let config = DriveConfig::default();
        let mut rig = Rig::new(16, 8, config);
        for frame in 0..400 {
            let plan = rig.tick(|x, y| noise(frame / 3, x, y));
            assert!(plan.driven <= 16 * 8);
        }
        let mut drain_ticks = 0;
        while rig.tick(|_, _| 255).undrained != 0 {
            drain_ticks += 1;
            assert!(
                drain_ticks <= config.flip_interval + u32::from(config.swing),
                "drain took too long"
            );
        }
        assert!(rig.controller.net.iter().all(|&n| n == 0));
    }

    #[test]
    fn old_plane_rewrites_are_spaced_by_flip_interval() {
        let config = DriveConfig::default();
        let mut rig = Rig::new(8, 4, config);
        let mut last_rewrite = None;
        for frame in 0..200u32 {
            let plan = rig.tick(|x, y| noise(frame, x, y));
            if plan.rewrite_old {
                if let Some(last) = last_rewrite {
                    assert!(frame - last >= config.flip_interval, "frame {frame}");
                }
                last_rewrite = Some(frame);
            }
        }
        assert!(last_rewrite.is_some(), "noise should need reversals");
    }

    #[test]
    fn small_reversals_do_not_request_a_rewrite() {
        let config = DriveConfig::default();
        let mut rig = Rig::new(4, 1, config);
        for _ in 0..config.swing {
            rig.tick(|_, _| 0);
        }
        let near_black = 16;
        assert_eq!(
            rig.planner.target_level(near_black),
            config.swing - config.flip_hysteresis
        );
        assert_eq!(rig.tick(|_, _| near_black).pending_flips, 0);
        assert_eq!(rig.tick(|_, _| 0).pending_flips, 0, "already black");
        assert_eq!(rig.tick(|_, _| 128).pending_flips, 4);
    }
}
