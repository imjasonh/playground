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
    /// Prefer `0` when you want to keep silhouette detail.
    pub smooth_angular: usize,
    /// Blend each contour with neighbors (0 = none, 1 = full average).
    /// Prefer `0` when you want to keep silhouette detail.
    pub smooth_vertical: f32,
    /// Exaggerate local radius deviations from a low-pass baseline.
    /// `1.0` = faithful envelope; `>1` makes shallow grooves/crests more
    /// printable in vase mode; `<1` softens them.
    pub detail_gain: f32,
}

impl Default for EnvelopeOptions {
    fn default() -> Self {
        Self {
            layer_height: 0.2,
            angular_samples: 256,
            min_radius: 0.4,
            inflate: 0.0,
            // No blur by default — vase mode already forces a single perimeter;
            // extra smoothing just erases printable silhouette detail.
            smooth_angular: 0,
            smooth_vertical: 0.0,
            detail_gain: 1.0,
        }
    }
}

/// Extract the radial envelope of `triangles` (already Z-up, mm units).
///
/// For each slice plane `z`, collect triangle–plane intersection *segments*,
/// then for every angular sample `θ` take the farthest ray hit against those
/// segments. Empty angles are filled by polar interpolation between the
/// nearest measured samples (no blur).
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
        let segments = plane_segments(triangles, z);
        let mut radii = vec![0.0_f32; n_ang];
        let mut hit = vec![false; n_ang];

        for &(a, b) in &segments {
            accumulate_segment_max_radius(a, b, axis_xy, &mut radii, &mut hit);
        }

        // Also keep dense samples along each segment as a fallback for bins
        // the exact ray test might miss at grazing angles.
        for &(a, b) in &segments {
            densify_segment_into_bins(a, b, axis_xy, n_ang, &mut radii, &mut hit);
        }

        fill_empty_bins_polar(&mut radii, &hit, prev_radii.as_deref());

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

    if (opts.detail_gain - 1.0).abs() > 1e-6 {
        apply_detail_gain(&mut contours, opts.detail_gain, opts.min_radius);
    }

    Envelope { axis_xy, contours }
}

/// Amplify high-frequency radius variation relative to a mild angular baseline.
fn apply_detail_gain(contours: &mut [Contour], gain: f32, min_radius: f32) {
    let gain = gain.max(0.0);
    // Baseline half-width ~3% of the circle, at least 2 samples.
    for c in contours.iter_mut() {
        let half = ((c.radii.len() as f32) * 0.03).round().max(2.0) as usize;
        let base = smooth_circular(&c.radii, half);
        for (i, slot) in c.radii.iter_mut().enumerate() {
            let r = base[i] + gain * (*slot - base[i]);
            *slot = r.max(min_radius);
        }
    }
}

/// For each angular bin whose ray intersects segment AB, keep max radius.
fn accumulate_segment_max_radius(
    a: [f32; 2],
    b: [f32; 2],
    origin: [f32; 2],
    radii: &mut [f32],
    hit: &mut [bool],
) {
    let n = radii.len();
    let aa = [a[0] - origin[0], a[1] - origin[1]];
    let bb = [b[0] - origin[0], b[1] - origin[1]];
    let ra = (aa[0] * aa[0] + aa[1] * aa[1]).sqrt();
    let rb = (bb[0] * bb[0] + bb[1] * bb[1]).sqrt();
    if ra < 1e-8 && rb < 1e-8 {
        return;
    }

    let theta_a = positive_atan2(aa[1], aa[0]);
    let theta_b = positive_atan2(bb[1], bb[0]);

    // Walk bins covering the shorter angular arc from A to B.
    let (start, steps) = angular_span_bins(theta_a, theta_b, n);
    for k in 0..=steps {
        let idx = (start + k) % n;
        let theta = std::f32::consts::TAU * (idx as f32) / (n as f32);
        if let Some(r) = ray_segment_hit(origin, theta, a, b) {
            if r > radii[idx] {
                radii[idx] = r;
            }
            hit[idx] = true;
        }
    }
}

fn densify_segment_into_bins(
    a: [f32; 2],
    b: [f32; 2],
    origin: [f32; 2],
    n_ang: usize,
    radii: &mut [f32],
    hit: &mut [bool],
) {
    let dx = b[0] - a[0];
    let dy = b[1] - a[1];
    let len = (dx * dx + dy * dy).sqrt();
    // ~4 samples per angular bin width along the chord.
    let steps = ((len
        / (std::f32::consts::TAU * 0.25_f32.max((a[0] - origin[0]).hypot(a[1] - origin[1]))
            / n_ang as f32))
        .ceil() as usize)
        .clamp(2, 64);

    for i in 0..=steps {
        let t = i as f32 / steps as f32;
        let p = [a[0] + t * dx, a[1] + t * dy];
        let rx = p[0] - origin[0];
        let ry = p[1] - origin[1];
        let r = (rx * rx + ry * ry).sqrt();
        if r < 1e-8 {
            continue;
        }
        let theta = positive_atan2(ry, rx);
        let idx = ((theta / std::f32::consts::TAU) * n_ang as f32).floor() as usize % n_ang;
        if r > radii[idx] {
            radii[idx] = r;
        }
        hit[idx] = true;
    }
}

fn ray_segment_hit(origin: [f32; 2], theta: f32, a: [f32; 2], b: [f32; 2]) -> Option<f32> {
    let dir = [theta.cos(), theta.sin()];
    // Solve origin + t*dir = a + s*(b-a), t>=0, s in [0,1]
    let ax = a[0] - origin[0];
    let ay = a[1] - origin[1];
    let bx = b[0] - a[0];
    let by = b[1] - a[1];
    let det = dir[0] * by - dir[1] * bx;
    if det.abs() < 1e-10 {
        return None;
    }
    let t = (ax * by - ay * bx) / det;
    let s = (ax * dir[1] - ay * dir[0]) / det;
    if t >= 0.0 && (0.0..=1.0).contains(&s) {
        Some(t)
    } else {
        None
    }
}

fn positive_atan2(y: f32, x: f32) -> f32 {
    let mut t = y.atan2(x);
    if t < 0.0 {
        t += std::f32::consts::TAU;
    }
    t
}

/// Return (start_bin, number_of_steps) covering the shorter arc A→B.
fn angular_span_bins(theta_a: f32, theta_b: f32, n: usize) -> (usize, usize) {
    let ia = ((theta_a / std::f32::consts::TAU) * n as f32).floor() as isize;
    let ib = ((theta_b / std::f32::consts::TAU) * n as f32).floor() as isize;
    let ia = ia.rem_euclid(n as isize) as usize;
    let ib = ib.rem_euclid(n as isize) as usize;
    let cw = (ib + n - ia) % n;
    let ccw = (ia + n - ib) % n;
    if cw <= ccw {
        (ia, cw)
    } else {
        (ib, ccw)
    }
}

/// Fill empty bins by polar-radius lerp between nearest measured neighbors.
fn fill_empty_bins_polar(radii: &mut [f32], hit: &[bool], prev: Option<&[f32]>) {
    let n = radii.len();
    if hit.iter().all(|&h| !h) {
        if let Some(prev) = prev {
            radii.copy_from_slice(prev);
        }
        return;
    }

    // Precompute nearest filled index to the left and right for each i.
    let mut left = vec![0usize; n];
    let mut right = vec![0usize; n];
    let mut last = None;
    for i in 0..(2 * n) {
        let idx = i % n;
        if hit[idx] {
            last = Some(idx);
        }
        if i >= n {
            left[idx] = last.expect("at least one hit");
        }
    }
    last = None;
    for i in (0..(2 * n)).rev() {
        let idx = i % n;
        if hit[idx] {
            last = Some(idx);
        }
        if i < n {
            right[idx] = last.expect("at least one hit");
        }
    }

    for i in 0..n {
        if hit[i] {
            continue;
        }
        let l = left[i];
        let r = right[i];
        if l == r {
            radii[i] = radii[l];
            continue;
        }
        // Circular distance from l → i → r.
        let dl = (i + n - l) % n;
        let dr = (r + n - i) % n;
        let span = dl + dr;
        if span == 0 {
            radii[i] = radii[l];
            continue;
        }
        let t = dl as f32 / span as f32;
        radii[i] = radii[l] * (1.0 - t) + radii[r] * t;
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

/// Collect XY segments where triangles cross the plane `z = const`.
fn plane_segments(triangles: &[Triangle], z: f32) -> Vec<([f32; 2], [f32; 2])> {
    let mut segs = Vec::new();
    for tri in triangles {
        let v = [tri.vertices[0].0, tri.vertices[1].0, tri.vertices[2].0];
        let mut hits: Vec<[f32; 2]> = Vec::with_capacity(3);
        for e in 0..3 {
            let a = v[e];
            let b = v[(e + 1) % 3];
            if let Some(p) = edge_plane_hit(a, b, z) {
                // Dedup vertices shared by two edges of the same triangle.
                if hits
                    .iter()
                    .all(|q| (q[0] - p[0]).abs() > 1e-7 || (q[1] - p[1]).abs() > 1e-7)
                {
                    hits.push([p[0], p[1]]);
                }
            }
        }
        if hits.len() == 2 {
            segs.push((hits[0], hits[1]));
        } else if hits.len() == 3 {
            // Rare: plane through a vertex + opposite edge, or coplanar-ish.
            // Keep the longest pair.
            let mut best = (0usize, 1usize, 0.0_f32);
            for i in 0..3 {
                for j in (i + 1)..3 {
                    let d = (hits[i][0] - hits[j][0]).hypot(hits[i][1] - hits[j][1]);
                    if d > best.2 {
                        best = (i, j, d);
                    }
                }
            }
            segs.push((hits[best.0], hits[best.1]));
        }
    }
    segs
}

fn edge_plane_hit(a: [f32; 3], b: [f32; 3], z: f32) -> Option<[f32; 3]> {
    let za = a[2] - z;
    let zb = b[2] - z;
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
        let faces = [
            ([0., 0., 0.], [1., 0., 0.], [1., 1., 0.]),
            ([0., 0., 0.], [1., 1., 0.], [0., 1., 0.]),
            ([0., 0., 1.], [0., 1., 1.], [1., 1., 1.]),
            ([0., 0., 1.], [1., 1., 1.], [1., 0., 1.]),
            ([0., 0., 0.], [0., 0., 1.], [1., 0., 1.]),
            ([0., 0., 0.], [1., 0., 1.], [1., 0., 0.]),
            ([0., 1., 0.], [1., 1., 0.], [1., 1., 1.]),
            ([0., 1., 0.], [1., 1., 1.], [0., 1., 1.]),
            ([0., 0., 0.], [0., 1., 0.], [0., 1., 1.]),
            ([0., 0., 0.], [0., 1., 1.], [0., 0., 1.]),
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
            detail_gain: 1.0,
        };
        let env = extract_radial_envelope(&tris, [0.5, 0.5], 0.0, 1.0, &opts);
        assert!(env.contours.len() >= 4);
        let mid = &env.contours[env.contours.len() / 2];
        let min_r = mid.radii.iter().cloned().fold(f32::INFINITY, f32::min);
        let max_r = mid.radii.iter().cloned().fold(0.0, f32::max);
        assert!(min_r > 0.45 && min_r < 0.55, "min_r={min_r}");
        assert!(max_r > 0.65 && max_r < 0.8, "max_r={max_r}");
    }

    #[test]
    fn ray_hits_unit_segment() {
        let r = ray_segment_hit([0.0, 0.0], 0.0, [1.0, -1.0], [1.0, 1.0]).unwrap();
        assert!((r - 1.0).abs() < 1e-5);
    }
}
