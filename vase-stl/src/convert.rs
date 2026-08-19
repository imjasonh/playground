use crate::envelope::{extract_radial_envelope, Envelope, EnvelopeOptions};
use crate::mesh::{loft_hollow, loft_solid, loft_solid_open_top, MeshStats};
use crate::metrics::{compare_envelopes, EnvelopeMetrics};
use crate::orient::{choose_up_axis, reorient_to_z_up, BoundingBox, UpAxis};
use crate::stl::TriMesh;

/// How to finish the lofted mesh.
#[derive(Debug, Clone, Copy)]
pub enum ShellMode {
    /// Closed solid — typical input for slicer spiral-vase mode.
    Solid,
    /// Solid sides + bottom, no top cap.
    OpenTop,
    /// Thin open-top wall of the given thickness (mm).
    Hollow { wall_mm: f32 },
}

impl ShellMode {
    pub fn hollow(wall_mm: f32) -> Self {
        ShellMode::Hollow { wall_mm }
    }
}

/// Conversion knobs.
#[derive(Debug, Clone)]
pub struct ConvertOptions {
    pub layer_height: f32,
    pub angular_samples: usize,
    pub min_radius: f32,
    pub inflate: f32,
    pub smooth_angular: usize,
    pub smooth_vertical: f32,
    /// Spatial σ along Z in mm (`0` = off).
    pub smooth_vertical_mm: f32,
    /// Bilateral range σ on radius in mm (`0` = plain Gaussian).
    pub smooth_vertical_range_mm: f32,
    /// Force a print-up axis; `None` = pick the longest AABB edge.
    pub up_axis: Option<UpAxis>,
    pub shell: ShellMode,
    /// Uniform scale applied after orientation (`1.0` = unchanged).
    pub scale: f32,
    /// If set, overrides `scale` so the oriented height becomes this many mm.
    pub target_height_mm: Option<f32>,
    /// Exaggerate silhouette relief (`1.0` = faithful; try `2.0`–`3.0`).
    pub detail_gain: f32,
}

impl Default for ConvertOptions {
    fn default() -> Self {
        Self {
            layer_height: 0.15,
            angular_samples: 360,
            min_radius: 0.4,
            inflate: 0.0,
            smooth_angular: 0,
            smooth_vertical: 0.0,
            // Off by default — the raw envelope is the closest vase-mode
            // match to the source. Use a small bilateral pass (e.g. 0.25 / 0.2)
            // only if slice terracing is visible.
            smooth_vertical_mm: 0.0,
            smooth_vertical_range_mm: 0.0,
            up_axis: None,
            shell: ShellMode::Solid,
            scale: 1.0,
            target_height_mm: None,
            detail_gain: 1.0,
        }
    }
}

/// Result of a conversion.
#[derive(Debug, Clone)]
pub struct ConvertResult {
    pub mesh: TriMesh,
    pub envelope: Envelope,
    pub stats: MeshStats,
    pub up_axis: UpAxis,
    pub bbox_before: BoundingBox,
    pub bbox_after: BoundingBox,
}

/// One trial from [`optimize_convert`].
#[derive(Debug, Clone)]
pub struct OptimizeTrial {
    pub options: ConvertOptions,
    pub metrics: EnvelopeMetrics,
    pub score: f32,
}

/// Convert `input` into a vase-mode-printable mesh.
pub fn convert(input: &TriMesh, opts: &ConvertOptions) -> Result<ConvertResult, String> {
    let prepared = prepare_mesh(input, opts)?;
    let envelope = extract_envelope(&prepared.oriented, &prepared.bbox, opts);
    if envelope.contours.is_empty() {
        return Err("envelope extraction produced no contours".into());
    }

    let (tris, stats) = match opts.shell {
        ShellMode::Solid => loft_solid(&envelope),
        ShellMode::OpenTop => loft_solid_open_top(&envelope),
        ShellMode::Hollow { wall_mm } => loft_hollow(&envelope, wall_mm),
    };

    let mesh = TriMesh::from_triangles(tris);
    let bbox_after = BoundingBox::from_triangles(&mesh.triangles)
        .ok_or_else(|| "output mesh is empty".to_string())?;

    Ok(ConvertResult {
        mesh,
        envelope,
        stats,
        up_axis: prepared.up_axis,
        bbox_before: prepared.bbox_before,
        bbox_after,
    })
}

/// Sweep smoothing / detail knobs against the raw radial envelope of the
/// (scaled) source — the fairest vase-mode target — and return the best
/// score plus every trial for logging.
///
/// Selection policy (fidelity-first):
/// 1. Prefer candidates with `mean_abs_r_err ≤ fidelity_budget_mm` (default
///    0.02 mm — far below a 0.4 mm nozzle).
/// 2. Among those, minimize terrace choppiness, then max |Δr|.
/// 3. If none meet the budget (shouldn't happen — raw is always in the set),
///    fall back to lowest [`EnvelopeMetrics::score`].
pub fn optimize_convert(
    input: &TriMesh,
    base: &ConvertOptions,
    chop_budget_mm: f32,
) -> Result<(ConvertResult, Vec<OptimizeTrial>), String> {
    optimize_convert_with_budget(input, base, chop_budget_mm, 0.02)
}

/// Like [`optimize_convert`], but with an explicit fidelity budget in mm.
pub fn optimize_convert_with_budget(
    input: &TriMesh,
    base: &ConvertOptions,
    chop_budget_mm: f32,
    fidelity_budget_mm: f32,
) -> Result<(ConvertResult, Vec<OptimizeTrial>), String> {
    let prepared = prepare_mesh(input, base)?;
    let mut ref_opts = base.clone();
    ref_opts.smooth_angular = 0;
    ref_opts.smooth_vertical = 0.0;
    ref_opts.smooth_vertical_mm = 0.0;
    ref_opts.smooth_vertical_range_mm = 0.0;
    ref_opts.detail_gain = 1.0;
    let reference = extract_envelope(&prepared.oriented, &prepared.bbox, &ref_opts);
    if reference.contours.is_empty() {
        return Err("reference envelope is empty".into());
    }

    let sigma_zs = [0.0_f32, 0.2, 0.25, 0.4, 0.7, 1.5, 2.5];
    let sigma_rs = [0.0_f32, 0.15, 0.2, 0.4];
    let gains = [1.0_f32, 1.15];
    let angular = [0usize];

    let mut trials = Vec::new();

    for &sz in &sigma_zs {
        for &sr in &sigma_rs {
            if sz <= 0.0 && sr > 0.0 {
                continue;
            }
            for &gain in &gains {
                for &sa in &angular {
                    let mut opts = base.clone();
                    opts.smooth_vertical_mm = sz;
                    opts.smooth_vertical_range_mm = if sz <= 0.0 { 0.0 } else { sr };
                    opts.detail_gain = gain;
                    opts.smooth_angular = sa;
                    let env = extract_envelope(&prepared.oriented, &prepared.bbox, &opts);
                    let metrics = compare_envelopes(&reference, &env);
                    let score = metrics.score(chop_budget_mm);
                    trials.push(OptimizeTrial {
                        options: opts.clone(),
                        metrics,
                        score,
                    });
                }
            }
        }
    }

    // Rank for reporting: lowest score first.
    trials.sort_by(|a, b| {
        a.score
            .partial_cmp(&b.score)
            .unwrap_or(std::cmp::Ordering::Equal)
    });

    // Pick balanced winner under fidelity budget.
    let best_idx = pick_fidelity_first(&trials, fidelity_budget_mm);
    let winner = &trials[best_idx];
    let opts = winner.options.clone();
    let envelope = extract_envelope(&prepared.oriented, &prepared.bbox, &opts);

    let (tris, stats) = match opts.shell {
        ShellMode::Solid => loft_solid(&envelope),
        ShellMode::OpenTop => loft_solid_open_top(&envelope),
        ShellMode::Hollow { wall_mm } => loft_hollow(&envelope, wall_mm),
    };
    let mesh = TriMesh::from_triangles(tris);
    let bbox_after = BoundingBox::from_triangles(&mesh.triangles)
        .ok_or_else(|| "output mesh is empty".to_string())?;

    // Move the winner to the front of the report list for CLI convenience.
    if best_idx != 0 {
        let w = trials.remove(best_idx);
        trials.insert(0, w);
    }

    Ok((
        ConvertResult {
            mesh,
            envelope,
            stats,
            up_axis: prepared.up_axis,
            bbox_before: prepared.bbox_before,
            bbox_after,
        },
        trials,
    ))
}

fn pick_fidelity_first(trials: &[OptimizeTrial], fidelity_budget_mm: f32) -> usize {
    // Primary: lowest mean |Δr|. Among near-ties (within 25% of budget or
    // 0.005 mm), prefer lower chop, then lower max |Δr|.
    let mut best_mean = f32::INFINITY;
    for t in trials {
        if t.metrics.mean_abs_r_err < best_mean {
            best_mean = t.metrics.mean_abs_r_err;
        }
    }
    let tie = (0.25 * fidelity_budget_mm).max(0.005);

    let mut best: Option<(usize, f32, f32, f32)> = None; // idx, mean, chop, max
    for (i, t) in trials.iter().enumerate() {
        if t.metrics.mean_abs_r_err > best_mean + tie {
            continue;
        }
        if t.metrics.mean_abs_r_err > fidelity_budget_mm && best_mean <= fidelity_budget_mm {
            continue;
        }
        let key = (
            t.metrics.mean_abs_r_err,
            t.metrics.mean_abs_dr_dz,
            t.metrics.max_abs_r_err,
        );
        let better = match best {
            None => true,
            Some((_, m, c, x)) => {
                key.0 < m - 1e-6
                    || ((key.0 - m).abs() < 1e-6 && key.1 < c - 1e-6)
                    || ((key.0 - m).abs() < 1e-6 && (key.1 - c).abs() < 1e-6 && key.2 < x)
            }
        };
        if better {
            best = Some((i, key.0, key.1, key.2));
        }
    }
    best.map(|(i, _, _, _)| i).unwrap_or(0)
}

struct PreparedMesh {
    oriented: Vec<stl_io::Triangle>,
    bbox: BoundingBox,
    bbox_before: BoundingBox,
    up_axis: UpAxis,
}

fn prepare_mesh(input: &TriMesh, opts: &ConvertOptions) -> Result<PreparedMesh, String> {
    if input.is_empty() {
        return Err("input STL has no triangles".into());
    }
    if opts.scale <= 0.0 {
        return Err("scale must be > 0".into());
    }
    if let Some(h) = opts.target_height_mm {
        if h <= 0.0 {
            return Err("target height must be > 0".into());
        }
    }

    let bbox_before = BoundingBox::from_triangles(&input.triangles)
        .ok_or_else(|| "could not compute bounding box".to_string())?;
    let up = opts.up_axis.unwrap_or_else(|| choose_up_axis(&bbox_before));
    let mut oriented = reorient_to_z_up(&input.triangles, up);
    let oriented_bbox = BoundingBox::from_triangles(&oriented)
        .ok_or_else(|| "oriented mesh is empty".to_string())?;

    let scale = if let Some(target) = opts.target_height_mm {
        let h = oriented_bbox.size()[2];
        if h < 1e-6 {
            return Err("oriented mesh has zero height".into());
        }
        target / h
    } else {
        opts.scale
    };
    if (scale - 1.0).abs() > 1e-9 {
        scale_triangles(&mut oriented, scale);
    }

    let bbox =
        BoundingBox::from_triangles(&oriented).ok_or_else(|| "scaled mesh is empty".to_string())?;

    let size = bbox.size();
    if size[2] < opts.layer_height {
        return Err(format!(
            "model height {:.3} mm is smaller than layer height {:.3} mm",
            size[2], opts.layer_height
        ));
    }

    Ok(PreparedMesh {
        oriented,
        bbox,
        bbox_before,
        up_axis: up,
    })
}

fn extract_envelope(
    oriented: &[stl_io::Triangle],
    bbox: &BoundingBox,
    opts: &ConvertOptions,
) -> Envelope {
    let axis_xy = [bbox.center()[0], bbox.center()[1]];
    let env_opts = EnvelopeOptions {
        layer_height: opts.layer_height,
        angular_samples: opts.angular_samples,
        min_radius: opts.min_radius,
        inflate: opts.inflate,
        smooth_angular: opts.smooth_angular,
        smooth_vertical: opts.smooth_vertical,
        smooth_vertical_mm: opts.smooth_vertical_mm,
        smooth_vertical_range_mm: opts.smooth_vertical_range_mm,
        detail_gain: opts.detail_gain,
    };
    extract_radial_envelope(oriented, axis_xy, bbox.min[2], bbox.max[2], &env_opts)
}

fn scale_triangles(triangles: &mut [stl_io::Triangle], scale: f32) {
    for tri in triangles {
        for v in &mut tri.vertices {
            v.0[0] *= scale;
            v.0[1] *= scale;
            v.0[2] *= scale;
        }
    }
}
