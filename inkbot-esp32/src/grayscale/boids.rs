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

use std::f32::consts::PI;

#[derive(Clone, Copy, Debug, PartialEq)]
struct Boid {
    x: f32,
    y: f32,
    vx: f32,
    vy: f32,
}

#[derive(Clone, Copy, Debug, PartialEq)]
pub struct FlockConfig {
    pub count: usize,
    pub width: f32,
    pub height: f32,
    /// Fastest a boid may move, in logical pixels per step.
    pub max_speed: f32,
    /// Slowest a boid may move; keeps the flock gliding instead of stalling.
    pub min_speed: f32,
    /// Steering acceleration limit per step.
    pub max_force: f32,
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
            count: 12,
            width: super::LOGICAL_WIDTH as f32,
            height: super::LOGICAL_HEIGHT as f32,
            // One refresh moves the ink one step of a 30-step swing. At
            // this speed a triangle's length (30 logical pixels) covers a
            // pixel on its central axis for about a full swing before the
            // shape moves past, and a boid crosses the panel in about 22
            // seconds at 22 refreshes a second.
            max_speed: 0.80,
            min_speed: 0.44,
            max_force: 0.020,
            // Wide enough that a flock spread across the panel still
            // counts as one neighborhood, so it gathers instead of
            // splitting into groups that can no longer see each other.
            perception_radius: 320.0,
            separation_radius: 46.0,
            separation_weight: 1.4,
            alignment_weight: 1.2,
            cohesion_weight: 0.45,
            // At this speed a boid needs on the order of a hundred
            // refreshes to turn around; this margin gives it that much
            // room before the hard wall.
            edge_margin: 90.0,
            edge_weight: 0.6,
            triangle_length: 30.0,
            triangle_half_width: 10.0,
            shape_min_luma: 36,
        }
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
}

impl Flock {
    /// A flock scattered across the canvas with random headings. `seed`
    /// makes the starting layout reproducible.
    pub fn new(config: FlockConfig, seed: u32) -> Self {
        let mut rng = Rng::new(seed);
        let margin = config.edge_margin;
        let boids = (0..config.count)
            .map(|_| {
                let angle = rng.next_range(0.0, 2.0 * PI);
                let speed = rng.next_range(config.min_speed, config.max_speed);
                Boid {
                    x: rng.next_range(margin, (config.width - margin).max(margin)),
                    y: rng.next_range(margin, (config.height - margin).max(margin)),
                    vx: angle.cos() * speed,
                    vy: angle.sin() * speed,
                }
            })
            .collect();
        Self { config, boids }
    }

    /// Advance the flock by one step.
    pub fn step(&mut self) {
        let c = &self.config;
        let steering: Vec<(f32, f32)> = (0..self.boids.len())
            .map(|i| self.steering_for(i))
            .collect();

        for (boid, (ax, ay)) in self.boids.iter_mut().zip(steering) {
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
    }

    fn steering_for(&self, i: usize) -> (f32, f32) {
        let c = &self.config;
        let me = self.boids[i];
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
            if dist < c.perception_radius {
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
