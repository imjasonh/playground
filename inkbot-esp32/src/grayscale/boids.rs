//! A small flock of boids (Reynolds' separation, alignment, and cohesion),
//! stepped once per refresh and rendered as acute triangles that point in
//! each boid's direction of travel.
//!
//! Speeds in [`FlockConfig::default`] are set for the one-step drive: a
//! triangle has to sit on a pixel for about a full 30-step swing before the
//! ink reaches the gray the scene asked for.
//!
//! Boids steer away from the edges of the logical canvas, more sharply the
//! closer they get, and bounce off as a fallback, so the flock turns back
//! toward the middle instead of lining up along the walls.
//!
//! The flock starts as several smaller flocks and splits back into them
//! after it has merged. How far, how hard, and how long the split itself
//! lasts come from the other fields of [`FlockConfig`]: see
//! [`FlockConfig::split_duration`].

use std::f32::consts::PI;

#[derive(Clone, Copy, Debug, PartialEq)]
struct Boid {
    x: f32,
    y: f32,
    vx: f32,
    vy: f32,
    /// Which starting flock this boid spawned into. Fixed for the boid's
    /// lifetime. During a split, alignment and cohesion only count
    /// neighbors with the same `group`.
    group: u8,
}

#[derive(Clone, Copy, Debug, PartialEq)]
pub struct FlockConfig {
    pub count: usize,
    /// Number of separate flocks `count` boids start in. The count splits
    /// evenly across them (any remainder goes to the first few flocks);
    /// each starts at its own spot on the canvas with its own shared
    /// heading. Alignment and cohesion can still merge them later if they
    /// come within `perception_radius` of each other.
    pub flock_count: usize,
    pub width: f32,
    pub height: f32,
    /// Fastest a boid may move, in logical pixels per step.
    pub max_speed: f32,
    /// Slowest a boid may move; keeps the flock gliding instead of stalling.
    pub min_speed: f32,
    /// Steering acceleration limit per step.
    pub max_force: f32,
    /// A small random steering force, fresh and independent each step for
    /// every boid, so alignment pulls headings together without ever
    /// letting them lock to the exact same direction.
    pub wander_strength: f32,
    /// Alignment and cohesion only see neighbors within this radius.
    pub perception_radius: f32,
    /// Separation pushes away from neighbors closer than this.
    pub separation_radius: f32,
    pub separation_weight: f32,
    pub alignment_weight: f32,
    pub cohesion_weight: f32,
    /// Distance from an edge at which boids start steering away from it.
    /// The push grows with the square of how far into this margin a boid
    /// has come, so it stays gentle in open water and sharp right at the
    /// wall.
    pub edge_margin: f32,
    pub edge_weight: f32,
    /// Tip-to-base length of the triangle, along the direction of travel.
    pub triangle_length: f32,
    /// Half the triangle's width at the base. Must be less than
    /// `triangle_length` for the triangle to stay acute.
    pub triangle_half_width: f32,
    /// Luma inside the triangle (0 = black). The edge fades to white (255).
    pub shape_min_luma: u8,
}

impl Default for FlockConfig {
    fn default() -> Self {
        Self {
            count: 36,
            flock_count: 3,
            width: super::LOGICAL_WIDTH as f32,
            height: super::LOGICAL_HEIGHT as f32,
            // One refresh moves the ink one step of a 30-step swing. At
            // this speed a triangle's length (9 logical pixels) covers a
            // pixel on its central axis for one full swing before the
            // shape moves past, and a boid crosses the panel in about 63
            // seconds at 22 refreshes a second. 0.29 rather than 0.3 keeps
            // `length / max_speed` above the swing in f32, where 0.3 is
            // not exact.
            max_speed: 0.29,
            min_speed: 0.16,
            max_force: 0.0075,
            // Under half of max_force: enough that alignment never fully
            // settles two boids onto the same heading, not so much that
            // the flock looks jittery instead of gliding.
            wander_strength: 0.003,
            // Wide enough that a flock spread across the panel still
            // counts as one neighborhood, so it gathers instead of
            // splitting into groups that can no longer see each other.
            perception_radius: 320.0,
            // About one arrow length, so neighbors can fly nearly
            // alongside instead of holding a wide gap.
            separation_radius: 10.0,
            separation_weight: 1.4,
            alignment_weight: 1.2,
            cohesion_weight: 0.45,
            // A U-turn at max_force covers about 35 logical pixels. This
            // margin is that distance plus a little, so the flock wheels
            // before the wall and still has open water in the middle of
            // the 240-pixel height.
            edge_margin: 48.0,
            edge_weight: 0.6,
            triangle_length: 9.0,
            triangle_half_width: 2.5,
            shape_min_luma: 36,
        }
    }
}

impl FlockConfig {
    /// Neighbors at `separation_radius` pack six around one boid (a hex
    /// ring). The split pull is that many neighbors' worth of separation,
    /// so it beats a crowd sitting between a boid and its target, and
    /// loses if the crowd is denser than a full ring.
    fn split_target_weight(self) -> f32 {
        const HEX_RING: f32 = 6.0;
        self.separation_weight * HEX_RING
    }

    /// Radius of the largest circle that fits in the open water inside
    /// the edge margin. Split targets sit on that circle.
    fn split_target_radius(self) -> f32 {
        let half = |extent: f32| (extent - 2.0 * self.edge_margin).max(0.0) * 0.5;
        half(self.width).min(half(self.height))
    }

    /// Distance between two neighboring split targets on that circle.
    fn split_chord(self) -> f32 {
        if self.flock_count < 2 {
            return 0.0;
        }
        let n = self.flock_count as f32;
        2.0 * self.split_target_radius() * (PI / n).sin()
    }

    /// Steps to make a U-turn and then fly `distance` at `max_speed`.
    /// The turn is budgeted as making no progress toward the target, so
    /// this is an upper bound on the trip.
    fn leg_steps(self, distance: f32) -> f32 {
        if distance <= 0.0 || self.max_speed <= f32::EPSILON {
            return 0.0;
        }
        let turn = if self.max_force <= f32::EPSILON {
            0.0
        } else {
            PI * self.max_speed / self.max_force
        };
        turn + distance / self.max_speed
    }

    /// Steps of one trip over `distance`: a U-turn that is not credited
    /// with progress, then the flight at `max_speed`.
    fn phase_steps(self, distance: f32) -> u32 {
        let steps = self.leg_steps(distance);
        if !steps.is_finite() || steps <= 0.0 || steps > u32::MAX as f32 {
            return 0;
        }
        steps.ceil() as u32
    }

    /// How long a split lasts, in steps. Alignment and cohesion only look
    /// at a boid's own starting flock for this long: enough to turn around
    /// and fly out to the split targets. The following merge has no
    /// fixed length. It runs until those flocks have come back within
    /// half a target-gap of each other, and the next split starts then.
    /// `0` when there is nothing to split into.
    pub fn split_duration(self) -> u32 {
        if self.flock_count < 2 {
            return 0;
        }
        self.phase_steps(self.split_target_radius())
    }

    /// Gap below which the starting flocks count as one flock again.
    /// Half the distance between neighboring split targets.
    fn merged_gap(self) -> f32 {
        self.split_chord() * 0.5
    }
}

/// `xorshift32`: small, deterministic, and good enough to scatter initial
/// positions and headings. Not used for anything that needs real entropy.
struct Rng(u32);

impl Rng {
    fn new(seed: u32) -> Self {
        Self(seed | 1)
    }

    fn next_u32(&mut self) -> u32 {
        let mut x = self.0;
        x ^= x << 13;
        x ^= x >> 17;
        x ^= x << 5;
        self.0 = x;
        x
    }

    /// Uniform in `[0, 1)`.
    fn next_f32(&mut self) -> f32 {
        (self.next_u32() >> 8) as f32 / (1u32 << 24) as f32
    }

    fn next_range(&mut self, lo: f32, hi: f32) -> f32 {
        lo + self.next_f32() * (hi - lo)
    }
}

pub struct Flock {
    config: FlockConfig,
    boids: Vec<Boid>,
    rng: Rng,
    step_count: u64,
    /// `step_count` at which the current split ends. Ignored while
    /// `splitting` is false.
    split_ends_at: u64,
    splitting: bool,
    /// Where each sub-flock (indexed by `Boid::group`) heads during the
    /// current split phase. Recomputed from the flock's centroid each
    /// time a split phase starts.
    split_targets: Vec<(f32, f32)>,
}

impl Flock {
    /// `flock_count` flocks, each gathered near its own spot on the canvas
    /// and sharing one heading with a little jitter. `seed` makes the
    /// starting layout reproducible.
    pub fn new(config: FlockConfig, seed: u32) -> Self {
        let mut rng = Rng::new(seed);
        let groups = config.flock_count.clamp(1, config.count.max(1));
        // Keep the spawn box on the canvas for the small test field too.
        let spread = 18.0_f32.min(config.width * 0.22).min(config.height * 0.22);
        // About 20 degrees either way, so each group starts as one flight
        // rather than independent travelers.
        let jitter = 0.35_f32;
        // One band per flock, left to right, so starting flocks don't spawn
        // on top of each other.
        let band_width = config.width / groups as f32;
        let cy = config.height * 0.5;

        let mut boids = Vec::with_capacity(config.count);
        for g in 0..groups {
            let group_count = config.count / groups + usize::from(g < config.count % groups);
            if group_count == 0 {
                continue;
            }
            let cx =
                (band_width * (g as f32 + 0.5)).clamp(spread, (config.width - spread).max(spread));
            let heading = rng.next_range(0.0, 2.0 * PI);
            boids.extend((0..group_count).map(|_| {
                let angle = heading + rng.next_range(-jitter, jitter);
                let speed = rng.next_range(config.min_speed, config.max_speed);
                Boid {
                    x: (cx + rng.next_range(-spread, spread)).clamp(0.0, config.width),
                    y: (cy + rng.next_range(-spread, spread)).clamp(0.0, config.height),
                    vx: angle.cos() * speed,
                    vy: angle.sin() * speed,
                    group: g as u8,
                }
            }));
        }
        let flock_count = config.flock_count.max(1);
        let duration = u64::from(config.split_duration());
        Self {
            config,
            boids,
            rng,
            step_count: 0,
            split_ends_at: duration,
            splitting: duration > 0,
            split_targets: vec![(0.0, 0.0); flock_count],
        }
    }

    /// True when every pair of starting-flock centroids is closer than
    /// [`FlockConfig::merged_gap`].
    fn flocks_together(&self) -> bool {
        let groups = self.config.flock_count.max(1);
        if groups < 2 {
            return false;
        }
        let mut acc = vec![(0.0f32, 0.0f32, 0u32); groups];
        for boid in &self.boids {
            let g = boid.group as usize;
            if g < groups {
                acc[g].0 += boid.x;
                acc[g].1 += boid.y;
                acc[g].2 += 1;
            }
        }
        let centroids: Vec<(f32, f32)> = acc
            .into_iter()
            .filter(|(_, _, n)| *n > 0)
            .map(|(x, y, n)| (x / n as f32, y / n as f32))
            .collect();
        if centroids.len() < 2 {
            return false;
        }
        let gap = self.config.merged_gap();
        for (i, a) in centroids.iter().enumerate() {
            for b in &centroids[i + 1..] {
                if (a.0 - b.0).hypot(a.1 - b.1) >= gap {
                    return false;
                }
            }
        }
        true
    }

    /// Picks a fresh target point for each sub-flock, spread evenly
    /// around the flock's current centroid at `split_target_radius`, with
    /// a random starting angle so successive splits don't all fan out the
    /// same way.
    fn pick_split_targets(&mut self) {
        let c = &self.config;
        let groups = c.flock_count.max(1);
        if self.boids.is_empty() {
            self.split_targets = vec![(0.0, 0.0); groups];
            return;
        }
        let n = self.boids.len() as f32;
        let (sx, sy) = self
            .boids
            .iter()
            .fold((0.0, 0.0), |(sx, sy), b| (sx + b.x, sy + b.y));
        let (cx, cy) = (sx / n, sy / n);
        let start_angle = self.rng.next_range(0.0, 2.0 * PI);
        let radius = c.split_target_radius();
        // Stay inside the edge margin so a target doesn't fight the edge
        // force by sitting right at (or past) the wall.
        let (x_lo, x_hi) = (c.edge_margin, (c.width - c.edge_margin).max(c.edge_margin));
        let (y_lo, y_hi) = (c.edge_margin, (c.height - c.edge_margin).max(c.edge_margin));
        self.split_targets = (0..groups)
            .map(|g| {
                let angle = start_angle + 2.0 * PI * g as f32 / groups as f32;
                (
                    (cx + angle.cos() * radius).clamp(x_lo, x_hi),
                    (cy + angle.sin() * radius).clamp(y_lo, y_hi),
                )
            })
            .collect();
    }

    /// Advance the flock by one step.
    pub fn step(&mut self) {
        // Copied out so the wander loop below can borrow `self.rng`
        // mutably while this stays in scope.
        let c = self.config;
        let duration = u64::from(c.split_duration());
        if duration > 0 && !self.splitting && self.flocks_together() {
            self.splitting = true;
            self.split_ends_at = self.step_count + duration;
            self.pick_split_targets();
        } else if self.splitting && self.step_count == 0 {
            self.pick_split_targets();
        }
        let steering: Vec<(f32, f32)> = (0..self.boids.len())
            .map(|i| self.steering_for(i))
            .collect();
        let wander: Vec<(f32, f32)> = (0..self.boids.len())
            .map(|_| {
                let angle = self.rng.next_range(0.0, 2.0 * PI);
                let magnitude = self.rng.next_range(0.0, c.wander_strength);
                (angle.cos() * magnitude, angle.sin() * magnitude)
            })
            .collect();

        for ((boid, (steer_x, steer_y)), (wx, wy)) in
            self.boids.iter_mut().zip(steering).zip(wander)
        {
            let mut ax = steer_x + wx;
            let mut ay = steer_y + wy;
            let force = ax.hypot(ay);
            if force > c.max_force {
                let scale = c.max_force / force;
                ax *= scale;
                ay *= scale;
            }
            boid.vx += ax;
            boid.vy += ay;

            let speed = boid.vx.hypot(boid.vy);
            if speed > c.max_speed {
                let scale = c.max_speed / speed;
                boid.vx *= scale;
                boid.vy *= scale;
            } else if speed > 0.0 && speed < c.min_speed {
                let scale = c.min_speed / speed;
                boid.vx *= scale;
                boid.vy *= scale;
            }

            boid.x += boid.vx;
            boid.y += boid.vy;

            // A hard wall is the fallback the edge force is meant to make
            // rare: it keeps the flock bounded even if several boids push
            // each other toward a corner at once.
            if boid.x < 0.0 {
                boid.x = 0.0;
                boid.vx = -boid.vx * 0.5;
            } else if boid.x > c.width {
                boid.x = c.width;
                boid.vx = -boid.vx * 0.5;
            }
            if boid.y < 0.0 {
                boid.y = 0.0;
                boid.vy = -boid.vy * 0.5;
            } else if boid.y > c.height {
                boid.y = c.height;
                boid.vy = -boid.vy * 0.5;
            }
        }
        self.step_count += 1;
        if self.splitting && self.step_count >= self.split_ends_at {
            self.splitting = false;
        }
    }

    fn steering_for(&self, i: usize) -> (f32, f32) {
        let c = &self.config;
        let me = self.boids[i];
        // During a split phase, alignment and cohesion only hear from
        // flockmates (same starting group), so the merged flock pulls
        // itself apart; separation stays global below so the flocks don't
        // overlap on the way.
        let splitting = self.splitting;
        let (mut sep_x, mut sep_y) = (0.0, 0.0);
        let (mut avg_vx, mut avg_vy) = (0.0, 0.0);
        let (mut avg_x, mut avg_y) = (0.0, 0.0);
        let mut neighbors = 0u32;

        for (j, other) in self.boids.iter().enumerate() {
            if i == j {
                continue;
            }
            let dx = me.x - other.x;
            let dy = me.y - other.y;
            let dist = dx.hypot(dy);
            if dist > 0.0 && dist < c.separation_radius {
                sep_x += dx / dist;
                sep_y += dy / dist;
            }
            if dist < c.perception_radius && (!splitting || other.group == me.group) {
                avg_vx += other.vx;
                avg_vy += other.vy;
                avg_x += other.x;
                avg_y += other.y;
                neighbors += 1;
            }
        }

        let (mut ax, mut ay) = (sep_x * c.separation_weight, sep_y * c.separation_weight);
        if neighbors > 0 {
            let n = neighbors as f32;
            ax += (avg_vx / n - me.vx) * c.alignment_weight;
            ay += (avg_vy / n - me.vy) * c.alignment_weight;
            ax += (avg_x / n - me.x) * c.cohesion_weight / c.perception_radius;
            ay += (avg_y / n - me.y) * c.cohesion_weight / c.perception_radius;
        }

        if splitting {
            if let Some(&(tx, ty)) = self.split_targets.get(me.group as usize) {
                let dx = tx - me.x;
                let dy = ty - me.y;
                let dist = dx.hypot(dy);
                // Skip once close: a constant-magnitude pull this near
                // its target would just make the boid orbit it.
                if dist > c.separation_radius {
                    let weight = c.split_target_weight();
                    ax += dx / dist * weight;
                    ay += dy / dist * weight;
                }
            }
        }

        // Squared so the push stays gentle through most of the margin and
        // only takes over right at the wall, instead of constantly
        // fighting cohesion across the whole margin width.
        let edge_push = |pos: f32, extent: f32| -> f32 {
            if pos < c.edge_margin {
                let t = (c.edge_margin - pos) / c.edge_margin;
                t * t
            } else if pos > extent - c.edge_margin {
                let t = (pos - (extent - c.edge_margin)) / c.edge_margin;
                -(t * t)
            } else {
                0.0
            }
        };
        ax += edge_push(me.x, c.width) * c.edge_weight;
        ay += edge_push(me.y, c.height) * c.edge_weight;

        let force = ax.hypot(ay);
        if force > c.max_force {
            let scale = c.max_force / force;
            ax *= scale;
            ay *= scale;
        }
        (ax, ay)
    }

    /// Render the flock as acute triangles on white, each pointing along
    /// its boid's heading. `buffer` must be `width * height` bytes,
    /// row-major.
    pub fn render_luma(&self, buffer: &mut [u8], width: usize, height: usize) {
        assert_eq!(buffer.len(), width * height);
        buffer.fill(255);

        let length = self.config.triangle_length;
        let half_width = self.config.triangle_half_width;
        let min_luma = self.config.shape_min_luma;
        let span = (length + half_width).ceil() as isize + 1;

        for boid in &self.boids {
            let speed = boid.vx.hypot(boid.vy).max(f32::EPSILON);
            let (fx, fy) = (boid.vx / speed, boid.vy / speed);
            let (px_perp, py_perp) = (-fy, fx);

            let tip = (boid.x, boid.y);
            let base_center = (boid.x - fx * length, boid.y - fy * length);
            let mut base_l = (
                base_center.0 + px_perp * half_width,
                base_center.1 + py_perp * half_width,
            );
            let mut base_r = (
                base_center.0 - px_perp * half_width,
                base_center.1 - py_perp * half_width,
            );
            // Put the vertices in counter-clockwise order so the edge
            // functions below agree on which side is "inside".
            if signed_area2(tip, base_l, base_r) < 0.0 {
                std::mem::swap(&mut base_l, &mut base_r);
            }

            let (icx, icy) = (boid.x.round() as isize, boid.y.round() as isize);
            for dy in -span..=span {
                let py = icy + dy;
                if py < 0 || py >= height as isize {
                    continue;
                }
                for dx in -span..=span {
                    let px = icx + dx;
                    if px < 0 || px >= width as isize {
                        continue;
                    }
                    let p = (px as f32 + 0.5, py as f32 + 0.5);
                    let coverage = triangle_coverage(p, tip, base_l, base_r);
                    if coverage <= 0.0 {
                        continue;
                    }
                    let luma = 255 - ((255 - min_luma as i32) as f32 * coverage).round() as i32;
                    let idx = py as usize * width + px as usize;
                    buffer[idx] = buffer[idx].min(luma.clamp(0, 255) as u8);
                }
            }
        }
    }

    #[cfg(test)]
    fn positions(&self) -> Vec<(f32, f32)> {
        self.boids.iter().map(|b| (b.x, b.y)).collect()
    }

    #[cfg(test)]
    fn speeds(&self) -> Vec<f32> {
        self.boids.iter().map(|b| b.vx.hypot(b.vy)).collect()
    }

    #[cfg(test)]
    fn headings(&self) -> Vec<f32> {
        self.boids.iter().map(|b| b.vy.atan2(b.vx)).collect()
    }
}

/// Twice the signed area of triangle `abc`. Positive when `a, b, c` wind
/// counter-clockwise.
fn signed_area2(a: (f32, f32), b: (f32, f32), c: (f32, f32)) -> f32 {
    (b.0 - a.0) * (c.1 - a.1) - (b.1 - a.1) * (c.0 - a.0)
}

/// Approximate antialiased coverage of point `p` by the counter-clockwise
/// triangle `a, b, c`, in `[0, 1]`. `0` is fully outside, `1` fully inside,
/// with about a one-pixel-wide soft edge in between.
fn triangle_coverage(p: (f32, f32), a: (f32, f32), b: (f32, f32), c: (f32, f32)) -> f32 {
    let edge_distance = |u: (f32, f32), v: (f32, f32)| -> f32 {
        let len = (v.0 - u.0).hypot(v.1 - u.1);
        if len <= f32::EPSILON {
            return f32::NEG_INFINITY;
        }
        signed_area2(u, v, p) / len
    };
    let min_distance = edge_distance(a, b)
        .min(edge_distance(b, c))
        .min(edge_distance(c, a));
    (min_distance + 0.5).clamp(0.0, 1.0)
}

#[cfg(test)]
mod tests {
    use super::*;

    fn small_config() -> FlockConfig {
        FlockConfig {
            count: 10,
            flock_count: 1,
            width: 80.0,
            height: 60.0,
            edge_margin: 8.0,
            perception_radius: 24.0,
            separation_radius: 8.0,
            triangle_length: 6.0,
            triangle_half_width: 2.0,
            ..FlockConfig::default()
        }
    }

    #[test]
    fn default_motion_is_slow_enough_for_one_step_drive() {
        let flock = FlockConfig::default();
        let swing = super::super::drive::DriveConfig::default().swing as f32;
        // A point on the triangle's central axis is covered for roughly
        // `length / max_speed` refreshes as the shape translates past it;
        // that needs to be at least one full white-to-black swing, or the
        // ink stays a pale streak behind a shape that has already moved on.
        let dwell_frames = flock.triangle_length / flock.max_speed;
        assert!(
            dwell_frames >= swing,
            "shape covers a pixel for {dwell_frames} frames, swing is {swing}"
        );
    }

    #[test]
    fn default_triangle_is_acute() {
        let flock = FlockConfig::default();
        assert!(
            flock.triangle_half_width < flock.triangle_length,
            "a half-width this wide relative to the length makes the apex angle obtuse"
        );
    }

    /// Largest pairwise angular gap, in `[0, PI]`, among `headings`.
    fn max_heading_gap(headings: &[f32]) -> f32 {
        let mut max_gap = 0.0f32;
        for (i, a) in headings.iter().enumerate() {
            for b in &headings[i + 1..] {
                let mut d = (a - b).abs() % (2.0 * PI);
                if d > PI {
                    d = 2.0 * PI - d;
                }
                max_gap = max_gap.max(d);
            }
        }
        max_gap
    }

    #[test]
    fn default_flock_starts_as_separate_groups() {
        let config = FlockConfig::default();
        assert!(
            config.separation_radius <= config.triangle_length + 2.0,
            "separation {} is wide next to an arrow of length {}",
            config.separation_radius,
            config.triangle_length
        );
        assert_eq!(
            config.count % config.flock_count,
            0,
            "test assumes count splits evenly across flocks"
        );
        let group_size = config.count / config.flock_count;

        let flock = Flock::new(config, 4);
        let pos = flock.positions();
        let headings = flock.headings();

        // Each starting flock is internally tight and shares one heading,
        // same as a single flock would.
        let mut centroids = Vec::with_capacity(config.flock_count);
        for group in 0..config.flock_count {
            let range = group * group_size..(group + 1) * group_size;
            let group_pos = &pos[range.clone()];
            let mut max_dist = 0.0f32;
            for (i, a) in group_pos.iter().enumerate() {
                for b in &group_pos[i + 1..] {
                    max_dist = max_dist.max((a.0 - b.0).hypot(a.1 - b.1));
                }
            }
            assert!(max_dist < 40.0, "group {group} start spread {max_dist}");
            assert!(
                max_heading_gap(&headings[range]) < 0.8,
                "group {group} heading gap too wide"
            );

            let (sx, sy) = group_pos
                .iter()
                .fold((0.0, 0.0), |(sx, sy), (x, y)| (sx + x, sy + y));
            let n = group_pos.len() as f32;
            centroids.push((sx / n, sy / n));
        }

        // The flocks themselves start apart from each other, not stacked
        // on the same spot.
        let mut max_centroid_dist = 0.0f32;
        for (i, a) in centroids.iter().enumerate() {
            for b in &centroids[i + 1..] {
                max_centroid_dist = max_centroid_dist.max((a.0 - b.0).hypot(a.1 - b.1));
            }
        }
        assert!(
            max_centroid_dist > 60.0,
            "starting flocks should be spread across the canvas, got {max_centroid_dist}"
        );
    }

    #[test]
    fn wander_keeps_headings_from_fully_converging() {
        let config = FlockConfig::default();
        let mut flock = Flock::new(config, 23);
        for _ in 0..600 {
            flock.step();
        }
        let max_gap = max_heading_gap(&flock.headings());
        // Without wander, alignment alone drives every heading gap toward
        // zero; some spread after 600 steps shows the noise keeps working,
        // not just scattering the initial headings before they settle.
        assert!(
            max_gap > 0.01,
            "headings converged to a single direction: max gap {max_gap}"
        );
    }

    /// Steps `flock` until its step counter reaches `target`.
    fn step_to(flock: &mut Flock, target: u64) {
        while flock.step_count < target {
            flock.step();
        }
    }

    /// `(min, max)` distance between starting-flock centroids.
    fn centroid_gaps(flock: &Flock) -> (f32, f32) {
        let groups = flock.config.flock_count.max(1);
        let mut acc = vec![(0.0f32, 0.0f32, 0u32); groups];
        for boid in &flock.boids {
            let g = boid.group as usize;
            if g < groups {
                acc[g].0 += boid.x;
                acc[g].1 += boid.y;
                acc[g].2 += 1;
            }
        }
        let centroids: Vec<(f32, f32)> = acc
            .into_iter()
            .filter(|(_, _, n)| *n > 0)
            .map(|(x, y, n)| (x / n as f32, y / n as f32))
            .collect();
        let mut min_gap = f32::MAX;
        let mut max_gap = 0.0f32;
        for (i, a) in centroids.iter().enumerate() {
            for b in &centroids[i + 1..] {
                let d = (a.0 - b.0).hypot(a.1 - b.1);
                min_gap = min_gap.min(d);
                max_gap = max_gap.max(d);
            }
        }
        (min_gap, max_gap)
    }

    #[test]
    fn split_schedule_follows_the_canvas_and_the_speed() {
        let config = FlockConfig::default();
        let radius = {
            let half = |extent: f32| (extent - 2.0 * config.edge_margin).max(0.0) * 0.5;
            half(config.width).min(half(config.height))
        };
        let chord = 2.0 * radius * (PI / config.flock_count as f32).sin();
        let turn = PI * config.max_speed / config.max_force;
        let phase = |distance: f32| (turn + distance / config.max_speed).ceil() as u32;
        let duration = phase(radius);
        assert_eq!(config.split_duration(), duration);
        assert!(
            chord > radius,
            "neighboring targets must sit further apart than the radius"
        );

        let single = FlockConfig {
            flock_count: 1,
            ..config
        };
        assert_eq!(single.split_duration(), 0);
    }

    #[test]
    fn default_flock_periodically_splits_and_remerges() {
        let config = FlockConfig::default();
        let mut flock = Flock::new(config, 4);
        let apart = config.merged_gap();
        let split = u64::from(config.split_duration());

        // End of the first split: still separate. This phase starts from
        // the spawn layout, so it does not prove a merged flock can re-split.
        step_to(&mut flock, split);
        let (min_gap, _) = centroid_gaps(&flock);
        assert!(
            min_gap >= apart,
            "end of first split: closest flocks are {min_gap} apart, need {apart}"
        );
        assert!(!flock.splitting, "split still running at step {split}");

        // Merge runs until the starting flocks are one flock again. Three
        // crossings of the canvas diagonal is past the longest merge this
        // default seed needs; a miss means they never came back together.
        let patience = (config.width.hypot(config.height) / config.max_speed * 3.0).ceil() as u64;
        let merge_start = flock.step_count;
        let mut gap_when_split_started = 0.0f32;
        while !flock.splitting {
            assert!(
                flock.step_count - merge_start < patience,
                "flocks did not merge within {patience} steps"
            );
            let (_, max_gap) = centroid_gaps(&flock);
            flock.step();
            if flock.splitting {
                gap_when_split_started = max_gap;
            }
        }
        assert!(
            gap_when_split_started < apart,
            "split restarted while flocks were still {gap_when_split_started} apart"
        );

        // End of that next split. The flock was mixed, so this is the case
        // local alignment and cohesion do not pull apart on their own.
        let split_end = flock.split_ends_at;
        step_to(&mut flock, split_end);
        let (min_gap, _) = centroid_gaps(&flock);
        assert!(
            min_gap >= apart,
            "end of second split: closest flocks are {min_gap} apart, need {apart}"
        );
    }

    #[test]
    fn flock_stays_close_after_flying() {
        let config = FlockConfig::default();
        let mut flock = Flock::new(config, 11);
        for _ in 0..400 {
            flock.step();
        }
        let pos = flock.positions();
        let mut nearest_sum = 0.0f32;
        for (i, a) in pos.iter().enumerate() {
            let mut nearest = f32::MAX;
            for (j, b) in pos.iter().enumerate() {
                if i == j {
                    continue;
                }
                nearest = nearest.min((a.0 - b.0).hypot(a.1 - b.1));
            }
            nearest_sum += nearest;
        }
        let mean_nearest = nearest_sum / pos.len() as f32;
        assert!(
            mean_nearest < config.separation_radius * 2.0,
            "mean nearest neighbor {mean_nearest}"
        );
    }

    #[test]
    fn same_seed_is_deterministic() {
        let mut a = Flock::new(small_config(), 42);
        let mut b = Flock::new(small_config(), 42);
        for _ in 0..200 {
            a.step();
            b.step();
        }
        assert_eq!(a.positions(), b.positions());
    }

    #[test]
    fn different_seeds_diverge() {
        let mut a = Flock::new(small_config(), 1);
        let mut b = Flock::new(small_config(), 2);
        for _ in 0..50 {
            a.step();
            b.step();
        }
        assert_ne!(a.positions(), b.positions());
    }

    #[test]
    fn flock_stays_on_the_canvas() {
        let config = small_config();
        let mut flock = Flock::new(config, 7);
        for _ in 0..2000 {
            flock.step();
            for (x, y) in flock.positions() {
                assert!((0.0..=config.width).contains(&x), "x={x}");
                assert!((0.0..=config.height).contains(&y), "y={y}");
            }
        }
    }

    #[test]
    fn speed_stays_within_configured_bounds() {
        let config = small_config();
        let mut flock = Flock::new(config, 3);
        for _ in 0..500 {
            flock.step();
        }
        for speed in flock.speeds() {
            assert!(
                speed <= config.max_speed + 1e-3,
                "speed {speed} exceeds max"
            );
        }
    }

    #[test]
    fn the_flock_moves() {
        let mut flock = Flock::new(small_config(), 9);
        let start = flock.positions();
        for _ in 0..30 {
            flock.step();
        }
        assert_ne!(flock.positions(), start);
    }

    #[test]
    fn render_fills_the_whole_buffer_and_stays_in_range() {
        let config = small_config();
        let flock = Flock::new(config, 5);
        let (w, h) = (config.width as usize, config.height as usize);
        let mut buffer = vec![0u8; w * h];
        flock.render_luma(&mut buffer, w, h);
        assert_eq!(buffer.len(), w * h);
        assert!(buffer.contains(&255), "background should show through");
    }

    #[test]
    fn a_boid_renders_darker_than_the_background() {
        let mut config = small_config();
        config.count = 1;
        let flock = Flock::new(config, 11);
        let (w, h) = (config.width as usize, config.height as usize);
        let mut buffer = vec![0u8; w * h];
        flock.render_luma(&mut buffer, w, h);
        let darkest = *buffer.iter().min().unwrap();
        assert!(darkest < 255, "the one boid should darken some pixel");
        assert!(
            darkest >= config.shape_min_luma,
            "never darker than configured"
        );
    }

    #[test]
    fn triangle_coverage_is_inside_center_outside_far_away() {
        let a = (10.0, 0.0);
        let b = (0.0, 10.0);
        let c = (0.0, -10.0);
        assert_eq!(triangle_coverage((3.0, 0.0), a, b, c), 1.0);
        assert_eq!(triangle_coverage((100.0, 100.0), a, b, c), 0.0);
    }
}
