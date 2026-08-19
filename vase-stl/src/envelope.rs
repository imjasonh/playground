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
    /// Vertical step between slices (mm) — one vase "band" thick.
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
    /// Legacy neighbor-blend amount along Z (`0`–`1`). Prefer `couple_weight`.
    pub smooth_vertical: f32,
    /// Spatial σ along Z in millimeters for vertical smoothing (`0` disables).
    pub smooth_vertical_mm: f32,
    /// Bilateral *range* σ on radius (mm). When `>0` with `smooth_vertical_mm`,
    /// vertical smoothing is edge-preserving.
    pub smooth_vertical_range_mm: f32,
    /// How many Z samples inside each layer-height band (max radius kept).
    /// `1` = single mid-plane; `4`–`8` better captures round ridges.
    pub band_subsamples: usize,
    /// Spring weight pulling consecutive layer bands together along Z.
    /// Solves `(I + w L) r = r₀` per angle. Higher = smoother, less step.
    /// Tune with `--optimize` (hull-error minimum under a gap budget).
    pub couple_weight: f32,
    /// Soft gap budget (mm of |Δr| between layers). Used by optimize scoring;
    /// also scales an extra pull when `|Δr|` exceeds this during coupling.
    pub couple_gap_mm: f32,
    /// Subdivide each layer interval this many times with Catmull-Rom before
    /// lofting, so the STL surface isn't a coarse frustum staircase.
    pub loft_subdivide: usize,
    /// Exaggerate local radius deviations from a low-pass baseline.
    /// `1.0` = faithful envelope; `>1` makes shallow grooves/crests more
    /// printable in vase mode; `<1` softens them.
    pub detail_gain: f32,
}

impl Default for EnvelopeOptions {
    fn default() -> Self {
        Self {
            layer_height: 0.15,
            angular_samples: 360,
            min_radius: 0.4,
            inflate: 0.0,
            smooth_angular: 0,
            smooth_vertical: 0.0,
            smooth_vertical_mm: 0.0,
            smooth_vertical_range_mm: 0.0,
            band_subsamples: 5,
            couple_weight: 0.25,
            couple_gap_mm: 0.35,
            loft_subdivide: 3,
            detail_gain: 1.0,
        }
    }
}

/// Extract the radial envelope of `triangles` (already Z-up, mm units).
///
/// Pipeline (layer bands → vase coupling):
/// 1. Partition height into bands of `layer_height`.
/// 2. Inside each band, sample several Z planes and keep the **max** radius
///    per angle (outer silhouette of that band).
/// 3. Pull consecutive bands together with spring weight `couple_weight` so
///    vase-illegal radial gaps close smoothly (no staircase on round ridges).
/// 4. Optionally densify along Z with Catmull-Rom before lofting.
pub fn extract_radial_envelope(
    triangles: &[Triangle],
    axis_xy: [f32; 2],
    z_min: f32,
    z_max: f32,
    opts: &EnvelopeOptions,
) -> Envelope {
    let n_ang = opts.angular_samples.max(8);
    let dz = opts.layer_height.max(1e-3);
    let subs = opts.band_subsamples.max(1);

    // Band bottoms: [z_min, z_min+dz, ...]; last band may be shorter.
    let mut band_z0 = Vec::new();
    let mut z = z_min;
    while z < z_max - 1e-5 {
        band_z0.push(z);
        z += dz;
    }
    if band_z0.is_empty() {
        band_z0.push(z_min);
    }

    let mut contours = Vec::with_capacity(band_z0.len());
    let mut prev_radii: Option<Vec<f32>> = None;

    for (bi, &z0) in band_z0.iter().enumerate() {
        let z1 = if bi + 1 < band_z0.len() {
            band_z0[bi + 1]
        } else {
            z_max
        };
        let z1 = z1.max(z0 + 1e-6);

        let mut radii = vec![0.0_f32; n_ang];
        let mut hit = vec![false; n_ang];

        for s in 0..subs {
            let t = (s as f32 + 0.5) / subs as f32;
            let z_s = z0 + (z1 - z0) * t;
            let segments = plane_segments(triangles, z_s);
            for &(a, b) in &segments {
                accumulate_segment_max_radius(a, b, axis_xy, &mut radii, &mut hit);
            }
            for &(a, b) in &segments {
                densify_segment_into_bins(a, b, axis_xy, n_ang, &mut radii, &mut hit);
            }
        }

        fill_empty_bins_polar(&mut radii, &hit, prev_radii.as_deref());

        if opts.smooth_angular > 0 {
            radii = smooth_circular(&radii, opts.smooth_angular);
        }

        for r in &mut radii {
            *r = (*r + opts.inflate).max(opts.min_radius);
        }

        prev_radii = Some(radii.clone());
        // Contour sits at band mid-height for lofting.
        let z_mid = 0.5 * (z0 + z1);
        contours.push(Contour { z: z_mid, radii });
    }

    if (opts.detail_gain - 1.0).abs() > 1e-6 {
        apply_detail_gain(&mut contours, opts.detail_gain, opts.min_radius);
    }

    // Primary continuity: curvature coupling + gap-only pulls between bands.
    if (opts.couple_weight > 0.0 || opts.couple_gap_mm > 0.0) && contours.len() > 2 {
        couple_layer_bands(
            &mut contours,
            opts.couple_weight,
            opts.couple_gap_mm,
            opts.min_radius,
        );
    } else if opts.smooth_vertical_mm > 0.0 && contours.len() > 2 {
        if opts.smooth_vertical_range_mm > 0.0 {
            bilateral_smooth_vertical(
                &mut contours,
                opts.smooth_vertical_mm,
                opts.smooth_vertical_range_mm,
                opts.min_radius,
            );
        } else {
            gaussian_smooth_vertical(&mut contours, opts.smooth_vertical_mm, opts.min_radius);
        }
    } else if opts.smooth_vertical > 0.0 && contours.len() > 2 {
        smooth_vertical_blend(&mut contours, opts.smooth_vertical.clamp(0.0, 1.0));
    }

    // Loft densification happens in `mesh` so metrics stay on band resolution.
    Envelope { axis_xy, contours }
}

/// Make consecutive layer bands vase-continuous without melting the hull.
///
/// 1. **Curvature springs** (`weight`): minimize `‖r−r₀‖² + w Σ (Δ²r)²` so
///    linear slopes (round ridges that change steadily) stay put, while
///    stair-steps (sign-flipping Δr) are pulled flat.
/// 2. **Gap clamp** (`gap_mm`): if `|rᵢ₊₁−rᵢ|` still exceeds the budget after
///    that, iteratively drag that pair toward each other (only those pairs).
fn couple_layer_bands(contours: &mut [Contour], weight: f32, gap_mm: f32, min_radius: f32) {
    let n = contours.len();
    if n < 3 {
        return;
    }

    if weight > 0.0 {
        curvature_couple(contours, weight, min_radius);
    }

    if gap_mm > 0.0 {
        // Hard constraint: keep iterating until every consecutive |Δr| ≤ gap_mm
        // (or we hit the iteration cap). 12 passes was not enough for steep
        // helmet features — those left floating vase walls.
        enforce_max_step(contours, gap_mm, min_radius, 400);
    }
}

/// Jacobi solve of `(I + w K) r = r₀` with `K = L₂ᵀ L₂` (2nd-difference Gram).
/// Interior stencil of `K` is `[1, -4, 6, -4, 1]`. Uses under-relaxation and a
/// hard clamp to `r₀ ± 1.5 mm` so large `w` cannot explode the hull.
fn curvature_couple(contours: &mut [Contour], weight: f32, min_radius: f32) {
    let n = contours.len();
    let n_ang = contours[0].radii.len();
    // Keep w modest — beyond ~1 the discrete operator needs a direct solve.
    let w = weight.clamp(0.0, 1.0);
    if w == 0.0 {
        return;
    }
    let r0: Vec<Vec<f32>> = contours.iter().map(|c| c.radii.clone()).collect();
    let mut cur = r0.clone();
    let omega = 0.5_f32; // under-relaxation
    let max_dev = 1.5_f32;

    for _ in 0..32 {
        let prev = cur.clone();
        for j in 0..n_ang {
            for i in 0..n {
                let (diag, off) = k_apply_offdiag(i, n, &prev, j);
                let denom = 1.0 + w * diag;
                let target = (r0[i][j] - w * off) / denom;
                let blended = (1.0 - omega) * prev[i][j] + omega * target;
                cur[i][j] = blended
                    .clamp(r0[i][j] - max_dev, r0[i][j] + max_dev)
                    .max(min_radius);
            }
        }
    }

    for (c, col) in contours.iter_mut().zip(cur.iter()) {
        c.radii.clone_from(col);
    }
}

/// `(K_ii, Σ_{m≠i} K_im r_m)` for the 2nd-difference Gram matrix.
fn k_apply_offdiag(i: usize, n: usize, r: &[Vec<f32>], j: usize) -> (f32, f32) {
    // Ends: little/no curvature coupling.
    if i == 0 || i + 1 == n {
        return (0.0, 0.0);
    }
    if i == 1 || i + 2 == n {
        // One-sided: K ~ [1, -2, 1] Gram → diag 5? Use soft [1,-2,1] energy only.
        // Energy (r[i-1]-2r[i]+r[i+1])² once: diag=4 for center of that triple when
        // i is the middle — here i is near boundary; use diag=5 stencil approx.
        let im1 = r[i - 1][j];
        let ii = r[i][j];
        let ip1 = r[i + 1][j];
        // For row of L2^T L2 at boundary-adjacent index, use:
        // off = -2*im1 + -2*ip1 + (contribution without self from expanded form)
        // Simpler Jacobi using energy of the single Δ² involving this point as center:
        // (I + w*[...]) with diag 4, off = -2 im1 - 2 ip1  ... wait
        // x = (r0 - w*(-2 im1 - 2 ip1)) / (1+4w) if we only couple as center.
        let _ = ii;
        return (4.0, -2.0 * im1 - 2.0 * ip1);
    }
    // Interior: stencil 1, -4, 6, -4, 1
    let off = r[i - 2][j] - 4.0 * r[i - 1][j] - 4.0 * r[i + 1][j] + r[i + 2][j];
    (6.0, off)
}

/// Project each angular column onto `|r[i+1] − r[i]| ≤ max_step`.
///
/// One forward + one backward clamp pass is exact for a 1-D chain (Lipschitz
/// projection). Multiple sweeps cover any residual from `min_radius` clamps.
fn enforce_max_step(contours: &mut [Contour], max_step: f32, min_radius: f32, max_iters: usize) {
    let n = contours.len();
    let n_ang = contours[0].radii.len();
    let max_step = max_step.max(1e-6);
    for _ in 0..max_iters.max(1) {
        let mut worst = 0.0_f32;
        for j in 0..n_ang {
            // Forward: each band within max_step of the previous.
            for i in 1..n {
                let lo = contours[i - 1].radii[j] - max_step;
                let hi = contours[i - 1].radii[j] + max_step;
                let r = contours[i].radii[j].clamp(lo, hi).max(min_radius);
                contours[i].radii[j] = r;
            }
            // Backward: each band within max_step of the next.
            for i in (0..n - 1).rev() {
                let lo = contours[i + 1].radii[j] - max_step;
                let hi = contours[i + 1].radii[j] + max_step;
                let r = contours[i].radii[j].clamp(lo, hi).max(min_radius);
                contours[i].radii[j] = r;
            }
            for i in 0..n - 1 {
                worst = worst.max((contours[i + 1].radii[j] - contours[i].radii[j]).abs());
            }
        }
        if worst <= max_step + 1e-6 {
            break;
        }
    }
}

/// Max consecutive `|Δr|` over the envelope (mm). Used for vase validation.
pub fn max_layer_step(contours: &[Contour]) -> f32 {
    if contours.len() < 2 {
        return 0.0;
    }
    let n_ang = contours[0].radii.len();
    let mut worst = 0.0_f32;
    for w in contours.windows(2) {
        for j in 0..n_ang {
            worst = worst.max((w[1].radii[j] - w[0].radii[j]).abs());
        }
    }
    worst
}

/// Insert `subdivide` Catmull-Rom samples between each pair of band contours.
pub fn densify_catmull_rom(
    contours: &[Contour],
    subdivide: usize,
    min_radius: f32,
) -> Vec<Contour> {
    let n = contours.len();
    let n_ang = contours[0].radii.len();
    let sub = subdivide.max(1);
    if n < 2 || sub <= 1 {
        return contours.to_vec();
    }

    let mut out = Vec::with_capacity((n - 1) * sub + 1);
    for i in 0..n - 1 {
        let c0 = if i == 0 {
            &contours[0]
        } else {
            &contours[i - 1]
        };
        let c1 = &contours[i];
        let c2 = &contours[i + 1];
        let c3 = if i + 2 < n {
            &contours[i + 2]
        } else {
            &contours[n - 1]
        };

        for s in 0..sub {
            let t = s as f32 / sub as f32;
            let z = c1.z * (1.0 - t) + c2.z * t;
            let mut radii = vec![0.0_f32; n_ang];
            for (j, slot) in radii.iter_mut().enumerate() {
                let v = catmull(c0.radii[j], c1.radii[j], c2.radii[j], c3.radii[j], t);
                // Clamp to the segment's endpoint range so Catmull can't overshoot
                // (which would spike the vase radius on sharp Z features).
                let lo = c1.radii[j].min(c2.radii[j]);
                let hi = c1.radii[j].max(c2.radii[j]);
                *slot = v.clamp(lo, hi).max(min_radius);
            }
            out.push(Contour { z, radii });
        }
    }
    out.push(contours[n - 1].clone());
    out
}

fn catmull(p0: f32, p1: f32, p2: f32, p3: f32, t: f32) -> f32 {
    let t2 = t * t;
    let t3 = t2 * t;
    0.5 * ((2.0 * p1)
        + (-p0 + p2) * t
        + (2.0 * p0 - 5.0 * p1 + 4.0 * p2 - p3) * t2
        + (-p0 + 3.0 * p1 - 3.0 * p2 + p3) * t3)
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

fn smooth_vertical_blend(contours: &mut [Contour], amount: f32) {
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

/// Gaussian blur of radius along Z, independently per angular column.
fn gaussian_smooth_vertical(contours: &mut [Contour], sigma_mm: f32, min_radius: f32) {
    bilateral_smooth_vertical(contours, sigma_mm, f32::INFINITY, min_radius);
}

/// Edge-preserving blur along Z: spatial Gaussian × range Gaussian on |Δr|.
///
/// Real armor creases (large |Δr| across a few layers) keep their weight near
/// zero from neighbors; slice-sampling jitter (tiny |Δr|) is averaged away.
fn bilateral_smooth_vertical(
    contours: &mut [Contour],
    sigma_z_mm: f32,
    sigma_r_mm: f32,
    min_radius: f32,
) {
    let sigma_z = sigma_z_mm.max(1e-4);
    let sigma_r = sigma_r_mm.max(1e-4);
    let n_layers = contours.len();
    let n_ang = contours[0].radii.len();
    let zs: Vec<f32> = contours.iter().map(|c| c.z).collect();
    let original: Vec<Vec<f32>> = contours.iter().map(|c| c.radii.clone()).collect();

    let z_radius = (3.0 * sigma_z).max(sigma_z);

    for i in 0..n_layers {
        for j in 0..n_ang {
            let center = original[i][j];
            let mut sum = 0.0_f32;
            let mut wsum = 0.0_f32;
            for k in 0..n_layers {
                let dz = (zs[k] - zs[i]).abs();
                if dz > z_radius {
                    continue;
                }
                let w_z = (-0.5 * (dz / sigma_z) * (dz / sigma_z)).exp();
                let dr = (original[k][j] - center).abs();
                let w_r = if sigma_r.is_finite() {
                    (-0.5 * (dr / sigma_r) * (dr / sigma_r)).exp()
                } else {
                    1.0
                };
                let w = w_z * w_r;
                sum += original[k][j] * w;
                wsum += w;
            }
            contours[i].radii[j] = if wsum > 0.0 {
                (sum / wsum).max(min_radius)
            } else {
                center.max(min_radius)
            };
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
            smooth_vertical_mm: 0.0,
            smooth_vertical_range_mm: 0.0,
            band_subsamples: 1,
            couple_weight: 0.0,
            couple_gap_mm: 0.0,
            loft_subdivide: 1,
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

    #[test]
    fn enforce_max_step_caps_consecutive_delta() {
        let n = 20;
        let mut contours: Vec<Contour> = (0..n)
            .map(|i| {
                let r = if i == 10 { 10.0_f32 } else { 1.0_f32 };
                Contour {
                    z: i as f32 * 0.15,
                    radii: vec![r; 8],
                }
            })
            .collect();
        enforce_max_step(&mut contours, 0.35, 0.4, 8);
        let worst = max_layer_step(&contours);
        assert!(worst <= 0.35 + 1e-5, "expected ≤0.35, got {worst}");
    }
}
