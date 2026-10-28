//! A small flock of boids (Reynolds' separation/alignment/cohesion), stepped
//! once per refresh and rendered as soft gray blobs — a smoothly moving
//! scene to show off the drive mode's grayscale instead of a fixed test
//! pattern.
//!
//! Boids steer gently away from the edges of the logical canvas and bounce
//! off them as a fallback, so the flock stays on screen without the
//! discontinuous pop of wrapping around.

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
    pub edge_margin: f32,
    pub edge_weight: f32,
    /// Blob radius in logical pixels.
    pub blob_radius: f32,
    /// Luma at a blob's center (0 = black). Edges fade to white (255).
    pub blob_min_luma: u8,
}

impl Default for FlockConfig {
    fn default() -> Self {
        Self {
            count: 16,
            width: super::LOGICAL_WIDTH as f32,
            height: super::LOGICAL_HEIGHT as f32,
            max_speed: 2.2,
            min_speed: 1.0,
            max_force: 0.15,
            perception_radius: 48.0,
            separation_radius: 16.0,
            separation_weight: 1.6,
            alignment_weight: 1.0,
            cohesion_weight: 0.9,
            edge_margin: 30.0,
            edge_weight: 0.3,
            blob_radius: 7.0,
            blob_min_luma: 20,
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

            // A hard wall is the fallback the soft edge force is meant to
            // make rare: it keeps the flock bounded even if several boids
            // push each other toward a corner at once.
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

        let edge_push = |pos: f32, extent: f32| -> f32 {
            if pos < c.edge_margin {
                (c.edge_margin - pos) / c.edge_margin
            } else if pos > extent - c.edge_margin {
                -(pos - (extent - c.edge_margin)) / c.edge_margin
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

    /// Render the flock as soft gray blobs on white. `buffer` must be
    /// `width * height` bytes, row-major.
    pub fn render_luma(&self, buffer: &mut [u8], width: usize, height: usize) {
        assert_eq!(buffer.len(), width * height);
        buffer.fill(255);

        let radius = self.config.blob_radius;
        let span = radius.ceil() as isize;
        let min_luma = self.config.blob_min_luma;
        for boid in &self.boids {
            let (cx, cy) = (boid.x, boid.y);
            let (icx, icy) = (cx.round() as isize, cy.round() as isize);
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
                    let dist = (px as f32 - cx).hypot(py as f32 - cy);
                    if dist > radius {
                        continue;
                    }
                    let t = dist / radius;
                    let falloff = 0.5 * (1.0 + (PI * t).cos());
                    let luma = 255 - ((255 - min_luma as i32) as f32 * falloff).round() as i32;
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

#[cfg(test)]
mod tests {
    use super::*;

    fn small_config() -> FlockConfig {
        FlockConfig {
            count: 10,
            width: 80.0,
            height: 60.0,
            ..FlockConfig::default()
        }
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
            darkest >= config.blob_min_luma,
            "never darker than configured"
        );
    }
}
