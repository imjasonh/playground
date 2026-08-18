use stl_io::Triangle;

/// Closed polyline at one height, sampled at equal angles around the axis.
#[derive(Debug, Clone)]
pub struct Contour {
    pub z: f32,
    /// Radius at sample `i` corresponding to angle `2π i / n`.
    pub radii: Vec<f32>,
}

impl Contour {
    pub fn sample_count(&self) -> usize {
        self.radii.len()
    }

    pub fn point_xy(&self, i: usize, cx: f32, cy: f32) -> [f32; 2] {
        let n = self.radii.len() as f32;
        let theta = std::f32::consts::TAU * (i as f32) / n;
        let r = self.radii[i];
        [cx + r * theta.cos(), cy + r * theta.sin()]
    }
}

/// Stack of radial contours forming a vase envelope.
#[derive(Debug, Clone)]
pub struct Envelope {
    pub axis_xy: [f32; 2],
    pub contours: Vec<Contour>,
}

/// Parameters for radial envelope extraction.
#[derive(Debug, Clone)]
pub struct EnvelopeOptions {
    /// Vertical step between slices (mm).
    pub layer_height: f32,
    /// Number of angular samples around the axis.
    pub angular_samples: usize,
    /// Floor under every radius so thin features still print (mm).
    pub min_radius: f32,
    /// Extra padding added to every radius (mm). Useful for nozzle width.
    pub inflate: f32,
    /// Optional Gaussian-ish angular blur kernel half-width in samples.
    pub smooth_angular: usize,
    /// Blend each contour with neighbors (0 = none, 1 = full average).
    pub smooth_vertical: f32,
}

impl Default for EnvelopeOptions {
    fn default() -> Self {
        Self {
            layer_height: 0.2,
            angular_samples: 96,
            min_radius: 0.4,
            inflate: 0.0,
            smooth_angular: 1,
            smooth_vertical: 0.25,
        }
    }
}

/// Extract the radial envelope of `triangles` (already Z-up, mm units).
///
/// For each slice plane `z` and angle `θ`, keep the farthest XY distance from
/// `axis_xy` among all triangle–plane intersection points that land in that
/// angular bin. Empty bins inherit from neighbors / previous layer so the
/// wall stays continuous for vase mode.
pub fn extract_radial_envelope(
    triangles: &[Triangle],
    axis_xy: [f32; 2],
    z_min: f32,
    z_max: f32,
    opts: &EnvelopeOptions,
) -> Envelope {
    let n_ang = opts.angular_samples.max(8);
    let dz = opts.layer_height.max(1e-3);
    let mut zs = Vec::new();
    let mut z = z_min;
    // Inclusive top: always finish on (or very near) z_max.
    while z < z_max - 1e-5 {
        zs.push(z);
        z += dz;
    }
    if zs.last().copied().unwrap_or(z_min) < z_max - 1e-4 {
        zs.push(z_max);
    }
    if zs.is_empty() {
        zs.push(z_min);
    }

    let mut contours = Vec::with_capacity(zs.len());
    let mut prev_radii: Option<Vec<f32>> = None;

    for &z in &zs {
        let hits = plane_intersections(triangles, z);
        let mut radii = vec![0.0_f32; n_ang];
        let mut counts = vec![0_u32; n_ang];

        for p in hits {
            let dx = p[0] - axis_xy[0];
            let dy = p[1] - axis_xy[1];
            let r = (dx * dx + dy * dy).sqrt();
            if r < 1e-8 {
                continue;
            }
            let mut theta = dy.atan2(dx);
            if theta < 0.0 {
                theta += std::f32::consts::TAU;
            }
            let mut idx = ((theta / std::f32::consts::TAU) * n_ang as f32).floor() as isize;
            if idx < 0 {
                idx = 0;
            }
            let idx = (idx as usize) % n_ang;
            if r > radii[idx] {
                radii[idx] = r;
            }
            counts[idx] += 1;
        }

        // Fill empty bins from nearest non-empty, then previous layer.
        fill_empty_bins(&mut radii, &counts, prev_radii.as_deref());

        if opts.smooth_angular > 0 {
            radii = smooth_circular(&radii, opts.smooth_angular);
        }

        for r in &mut radii {
            *r = (*r + opts.inflate).max(opts.min_radius);
        }

        prev_radii = Some(radii.clone());
        contours.push(Contour { z, radii });
    }

    if opts.smooth_vertical > 0.0 && contours.len() > 2 {
        smooth_vertical(&mut contours, opts.smooth_vertical.clamp(0.0, 1.0));
    }

    Envelope { axis_xy, contours }
}

fn fill_empty_bins(radii: &mut [f32], counts: &[u32], prev: Option<&[f32]>) {
    let n = radii.len();
    if counts.iter().all(|&c| c == 0) {
        if let Some(prev) = prev {
            radii.copy_from_slice(prev);
        }
        return;
    }

    for i in 0..n {
        if counts[i] > 0 {
            continue;
        }
        // Search outward for nearest filled bin.
        let mut found = None;
        for d in 1..n {
            let l = (i + n - d) % n;
            let r = (i + d) % n;
            if counts[l] > 0 {
                found = Some(radii[l]);
                break;
            }
            if counts[r] > 0 {
                found = Some(radii[r]);
                break;
            }
        }
        if let Some(v) = found {
            radii[i] = v;
        } else if let Some(prev) = prev {
            radii[i] = prev[i];
        }
    }
}

fn smooth_circular(radii: &[f32], half_width: usize) -> Vec<f32> {
    let n = radii.len();
    let w = half_width.max(1);
    let mut out = vec![0.0; n];
    for (i, slot) in out.iter_mut().enumerate() {
        let mut sum = 0.0;
        let mut weight = 0.0;
        for d in -(w as isize)..=(w as isize) {
            let j = (i as isize + d).rem_euclid(n as isize) as usize;
            let wd = 1.0 + (w as f32) - (d.unsigned_abs() as f32);
            sum += radii[j] * wd;
            weight += wd;
        }
        *slot = sum / weight;
    }
    out
}

fn smooth_vertical(contours: &mut [Contour], amount: f32) {
    let original: Vec<Vec<f32>> = contours.iter().map(|c| c.radii.clone()).collect();
    let n_layers = contours.len();
    for i in 0..n_layers {
        let n = contours[i].radii.len();
        for j in 0..n {
            let mut sum = original[i][j];
            let mut w = 1.0_f32;
            if i > 0 {
                sum += original[i - 1][j];
                w += 1.0;
            }
            if i + 1 < n_layers {
                sum += original[i + 1][j];
                w += 1.0;
            }
            let avg = sum / w;
            contours[i].radii[j] = original[i][j] * (1.0 - amount) + avg * amount;
        }
    }
}

/// Collect XY points where triangles cross the plane `z = const`.
fn plane_intersections(triangles: &[Triangle], z: f32) -> Vec<[f32; 2]> {
    let mut pts = Vec::new();
    for tri in triangles {
        let v = [tri.vertices[0].0, tri.vertices[1].0, tri.vertices[2].0];
        for e in 0..3 {
            let a = v[e];
            let b = v[(e + 1) % 3];
            if let Some(p) = edge_plane_hit(a, b, z) {
                pts.push([p[0], p[1]]);
            }
        }
    }
    pts
}

fn edge_plane_hit(a: [f32; 3], b: [f32; 3], z: f32) -> Option<[f32; 3]> {
    let za = a[2] - z;
    let zb = b[2] - z;
    // Require a strict crossing so vertices shared by edges aren't double-counted
    // in a harmful way; equal-z edges are ignored (silhouette handled by other edges).
    if za == 0.0 && zb == 0.0 {
        return None;
    }
    if za * zb > 0.0 {
        return None;
    }
    if za == 0.0 {
        return Some(a);
    }
    if zb == 0.0 {
        return Some(b);
    }
    let t = za / (za - zb);
    Some([a[0] + t * (b[0] - a[0]), a[1] + t * (b[1] - a[1]), z])
}

#[cfg(test)]
mod tests {
    use super::*;
    use stl_io::{Normal, Triangle, Vertex};

    fn unit_cube() -> Vec<Triangle> {
        // 1×1×1 cube from (0,0,0) to (1,1,1), 12 triangles.
        let faces = [
            // -Z
            ([0., 0., 0.], [1., 0., 0.], [1., 1., 0.]),
            ([0., 0., 0.], [1., 1., 0.], [0., 1., 0.]),
            // +Z
            ([0., 0., 1.], [0., 1., 1.], [1., 1., 1.]),
            ([0., 0., 1.], [1., 1., 1.], [1., 0., 1.]),
            // -Y
            ([0., 0., 0.], [0., 0., 1.], [1., 0., 1.]),
            ([0., 0., 0.], [1., 0., 1.], [1., 0., 0.]),
            // +Y
            ([0., 1., 0.], [1., 1., 0.], [1., 1., 1.]),
            ([0., 1., 0.], [1., 1., 1.], [0., 1., 1.]),
            // -X
            ([0., 0., 0.], [0., 1., 0.], [0., 1., 1.]),
            ([0., 0., 0.], [0., 1., 1.], [0., 0., 1.]),
            // +X
            ([1., 0., 0.], [1., 0., 1.], [1., 1., 1.]),
            ([1., 0., 0.], [1., 1., 1.], [1., 1., 0.]),
        ];
        faces
            .into_iter()
            .map(|(a, b, c)| Triangle {
                normal: Normal::new([0., 0., 1.]),
                vertices: [Vertex::new(a), Vertex::new(b), Vertex::new(c)],
            })
            .collect()
    }

    #[test]
    fn cube_envelope_is_roughly_square_radius() {
        let tris = unit_cube();
        let opts = EnvelopeOptions {
            layer_height: 0.25,
            angular_samples: 64,
            min_radius: 0.05,
            inflate: 0.0,
            smooth_angular: 0,
            smooth_vertical: 0.0,
        };
        let env = extract_radial_envelope(&tris, [0.5, 0.5], 0.0, 1.0, &opts);
        assert!(env.contours.len() >= 4);
        // Along axes, half-width is 0.5; along diagonals ~0.707.
        let mid = &env.contours[env.contours.len() / 2];
        let min_r = mid.radii.iter().cloned().fold(f32::INFINITY, f32::min);
        let max_r = mid.radii.iter().cloned().fold(0.0, f32::max);
        assert!(min_r > 0.45 && min_r < 0.55, "min_r={min_r}");
        assert!(max_r > 0.65 && max_r < 0.8, "max_r={max_r}");
    }
}
