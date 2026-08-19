use crate::envelope::Envelope;

/// How closely a vase envelope matches a reference (usually the raw
/// radial envelope of the scaled source — the best vase mode can do).
#[derive(Debug, Clone, Copy)]
pub struct EnvelopeMetrics {
    /// Mean |Δr| over all (θ, z) samples (mm).
    pub mean_abs_r_err: f32,
    /// Max |Δr| (mm).
    pub max_abs_r_err: f32,
    /// RMS |Δr| (mm).
    pub rms_r_err: f32,
    /// Mean |Δ half-width| between consecutive layers (mm) — terrace proxy.
    pub mean_abs_dr_dz: f32,
    /// Approximate solid-of-revolution volume of the candidate (mm³).
    pub volume_mm3: f32,
    /// Approximate volume of the reference (mm³).
    pub ref_volume_mm3: f32,
    /// (volume - ref_volume) / ref_volume.
    pub volume_rel_err: f32,
    /// Samples compared.
    pub sample_count: usize,
}

impl EnvelopeMetrics {
    /// Scalar score to minimize: fidelity first, with a soft choppiness penalty.
    pub fn score(&self, chop_budget_mm: f32) -> f32 {
        let chop_pen = (self.mean_abs_dr_dz - chop_budget_mm).max(0.0);
        self.mean_abs_r_err + 0.15 * self.max_abs_r_err + 0.5 * chop_pen
    }
}

/// Compare `candidate` to `reference` on a shared (θ, z) grid.
///
/// Contours are resampled by nearest-z / linear-z interpolation onto the
/// reference layer heights; angular counts must match (or candidate is
/// angularly resampled).
pub fn compare_envelopes(reference: &Envelope, candidate: &Envelope) -> EnvelopeMetrics {
    let n_ang = reference.contours[0].radii.len();
    let mut cand = candidate.clone();
    if cand.contours[0].radii.len() != n_ang {
        resample_angular(&mut cand, n_ang);
    }

    let mut sum_abs = 0.0_f32;
    let mut sum_sq = 0.0_f32;
    let mut max_abs = 0.0_f32;
    let mut n = 0usize;

    for pref in &reference.contours {
        let rc = sample_radii_at_z(&cand, pref.z);
        for (j, &cand_r) in rc.iter().enumerate().take(n_ang) {
            let e = (cand_r - pref.radii[j]).abs();
            sum_abs += e;
            sum_sq += e * e;
            if e > max_abs {
                max_abs = e;
            }
            n += 1;
        }
    }

    let mean_abs_dr_dz = mean_layer_choppiness(&cand);
    let volume_mm3 = envelope_volume(&cand);
    let ref_volume_mm3 = envelope_volume(reference);
    let volume_rel_err = if ref_volume_mm3 > 1e-6 {
        (volume_mm3 - ref_volume_mm3) / ref_volume_mm3
    } else {
        0.0
    };

    EnvelopeMetrics {
        mean_abs_r_err: if n > 0 { sum_abs / n as f32 } else { 0.0 },
        max_abs_r_err: max_abs,
        rms_r_err: if n > 0 {
            (sum_sq / n as f32).sqrt()
        } else {
            0.0
        },
        mean_abs_dr_dz,
        volume_mm3,
        ref_volume_mm3,
        volume_rel_err,
        sample_count: n,
    }
}

/// Approximate volume of revolution: Σ π r̄² Δz with r̄² = mean r² on the ring.
pub fn envelope_volume(env: &Envelope) -> f32 {
    if env.contours.len() < 2 {
        return 0.0;
    }
    let mut vol = 0.0_f32;
    for w in env.contours.windows(2) {
        let dz = (w[1].z - w[0].z).abs();
        let mean_r2 = 0.5 * (mean_r2(&w[0].radii) + mean_r2(&w[1].radii));
        vol += std::f32::consts::PI * mean_r2 * dz;
    }
    vol
}

fn mean_r2(radii: &[f32]) -> f32 {
    if radii.is_empty() {
        return 0.0;
    }
    radii.iter().map(|r| r * r).sum::<f32>() / radii.len() as f32
}

fn mean_layer_choppiness(env: &Envelope) -> f32 {
    if env.contours.len() < 2 {
        return 0.0;
    }
    let n_ang = env.contours[0].radii.len();
    let mut sum = 0.0_f32;
    let mut n = 0usize;
    for w in env.contours.windows(2) {
        for j in 0..n_ang {
            sum += (w[1].radii[j] - w[0].radii[j]).abs();
            n += 1;
        }
    }
    if n == 0 {
        0.0
    } else {
        sum / n as f32
    }
}

fn sample_radii_at_z(env: &Envelope, z: f32) -> Vec<f32> {
    let cs = &env.contours;
    if cs.is_empty() {
        return Vec::new();
    }
    if z <= cs[0].z {
        return cs[0].radii.clone();
    }
    if z >= cs[cs.len() - 1].z {
        return cs[cs.len() - 1].radii.clone();
    }
    for w in cs.windows(2) {
        if z >= w[0].z && z <= w[1].z {
            let t = if (w[1].z - w[0].z).abs() < 1e-9 {
                0.0
            } else {
                (z - w[0].z) / (w[1].z - w[0].z)
            };
            return w[0]
                .radii
                .iter()
                .zip(w[1].radii.iter())
                .map(|(a, b)| a * (1.0 - t) + b * t)
                .collect();
        }
    }
    cs[cs.len() - 1].radii.clone()
}

fn resample_angular(env: &mut Envelope, n_ang: usize) {
    for c in &mut env.contours {
        let old = c.radii.clone();
        let n0 = old.len();
        let mut neu = vec![0.0_f32; n_ang];
        for (i, slot) in neu.iter_mut().enumerate() {
            let t = (i as f32) / n_ang as f32 * n0 as f32;
            let i0 = t.floor() as usize % n0;
            let i1 = (i0 + 1) % n0;
            let f = t - t.floor();
            *slot = old[i0] * (1.0 - f) + old[i1] * f;
        }
        c.radii = neu;
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::envelope::Contour;

    fn env_cylinder(r: f32, h: f32, layers: usize, n_ang: usize) -> Envelope {
        let mut contours = Vec::new();
        for i in 0..layers {
            let z = h * (i as f32) / (layers - 1).max(1) as f32;
            contours.push(Contour {
                z,
                radii: vec![r; n_ang],
            });
        }
        Envelope {
            axis_xy: [0.0, 0.0],
            contours,
        }
    }

    #[test]
    fn identical_envelopes_have_zero_error() {
        let a = env_cylinder(10.0, 50.0, 10, 32);
        let m = compare_envelopes(&a, &a);
        assert!(m.mean_abs_r_err < 1e-5);
        assert!(m.max_abs_r_err < 1e-5);
        assert!(m.volume_rel_err.abs() < 1e-5);
    }

    #[test]
    fn scaled_cylinder_reports_radius_error() {
        let a = env_cylinder(10.0, 50.0, 10, 32);
        let b = env_cylinder(11.0, 50.0, 10, 32);
        let m = compare_envelopes(&a, &b);
        assert!((m.mean_abs_r_err - 1.0).abs() < 1e-3);
        assert!((m.max_abs_r_err - 1.0).abs() < 1e-3);
    }
}
