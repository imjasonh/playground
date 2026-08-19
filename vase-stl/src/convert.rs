use crate::envelope::{extract_radial_envelope, Envelope, EnvelopeOptions};
use crate::mesh::{loft_hollow, loft_solid, loft_solid_open_top, prepare_loft_envelope, MeshStats};
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
    /// Spatial σ along Z in mm (`0` = off). Legacy; prefer `couple_weight`.
    pub smooth_vertical_mm: f32,
    /// Bilateral range σ on radius in mm (`0` = plain Gaussian).
    pub smooth_vertical_range_mm: f32,
    /// Z samples per layer-height band (max radius kept).
    pub band_subsamples: usize,
    /// Spring weight pulling consecutive bands together.
    pub couple_weight: f32,
    /// Soft |Δr| gap budget (mm) between bands.
    pub couple_gap_mm: f32,
    /// Catmull-Rom loft densification factor (`1` = off).
    pub loft_subdivide: usize,
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
            smooth_vertical_mm: 0.0,
            smooth_vertical_range_mm: 0.0,
            band_subsamples: 5,
            couple_weight: 0.25,
            couple_gap_mm: 0.30,
            loft_subdivide: 3,
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

    let loft_env = prepare_loft_envelope(&envelope, opts.loft_subdivide, opts.min_radius);
    let (tris, stats) = match opts.shell {
        ShellMode::Solid => loft_solid(&loft_env),
        ShellMode::OpenTop => loft_solid_open_top(&loft_env),
        ShellMode::Hollow { wall_mm } => loft_hollow(&loft_env, wall_mm),
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

/// Sweep band-coupling weights against the uncoupled band envelope and pick
/// the weight that minimizes hull error + staircasing (round ridges stay round).
pub fn optimize_convert(
    input: &TriMesh,
    base: &ConvertOptions,
    chop_budget_mm: f32,
) -> Result<(ConvertResult, Vec<OptimizeTrial>), String> {
    optimize_convert_with_budget(input, base, chop_budget_mm, 0.15)
}

/// Like [`optimize_convert`], with an explicit mean-|Δr| fidelity budget.
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
    ref_opts.couple_weight = 0.0;
    ref_opts.detail_gain = 1.0;
    let reference = extract_envelope(&prepared.oriented, &prepared.bbox, &ref_opts);
    if reference.contours.is_empty() {
        return Err("reference envelope is empty".into());
    }

    let weights = [0.0_f32, 0.1, 0.25, 0.4, 0.6, 0.8, 1.0];
    let gaps = [0.20_f32, 0.30, 0.45];

    let mut trials = Vec::new();
    for &w in &weights {
        for &gap in &gaps {
            if w <= 0.0 && gap != gaps[0] {
                continue; // uncoupled once
            }
            let mut opts = base.clone();
            opts.couple_weight = w;
            opts.couple_gap_mm = gap;
            opts.smooth_vertical_mm = 0.0;
            opts.smooth_vertical_range_mm = 0.0;
            opts.detail_gain = 1.0;
            opts.smooth_angular = 0;
            let env = extract_envelope(&prepared.oriented, &prepared.bbox, &opts);
            let metrics = compare_envelopes(&reference, &env);
            let score = metrics.score(chop_budget_mm);
            trials.push(OptimizeTrial {
                options: opts,
                metrics,
                score,
            });
        }
    }

    trials.sort_by(|a, b| {
        a.score
            .partial_cmp(&b.score)
            .unwrap_or(std::cmp::Ordering::Equal)
    });

    // Prefer lowest score among trials under the fidelity budget; else best score.
    let best_idx = pick_min_score_under_budget(&trials, fidelity_budget_mm);
    let opts = trials[best_idx].options.clone();
    let envelope = extract_envelope(&prepared.oriented, &prepared.bbox, &opts);
    let loft_env = prepare_loft_envelope(&envelope, opts.loft_subdivide, opts.min_radius);

    let (tris, stats) = match opts.shell {
        ShellMode::Solid => loft_solid(&loft_env),
        ShellMode::OpenTop => loft_solid_open_top(&loft_env),
        ShellMode::Hollow { wall_mm } => loft_hollow(&loft_env, wall_mm),
    };
    let mesh = TriMesh::from_triangles(tris);
    let bbox_after = BoundingBox::from_triangles(&mesh.triangles)
        .ok_or_else(|| "output mesh is empty".to_string())?;

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

fn pick_min_score_under_budget(trials: &[OptimizeTrial], fidelity_budget_mm: f32) -> usize {
    let mut best: Option<(usize, f32)> = None;
    for (i, t) in trials.iter().enumerate() {
        if t.metrics.mean_abs_r_err > fidelity_budget_mm {
            continue;
        }
        if best.map(|(_, s)| t.score < s).unwrap_or(true) {
            best = Some((i, t.score));
        }
    }
    if let Some((i, _)) = best {
        return i;
    }
    // Fallback: lowest score overall.
    let mut idx = 0usize;
    for (i, t) in trials.iter().enumerate() {
        if t.score < trials[idx].score {
            idx = i;
        }
    }
    idx
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
        band_subsamples: opts.band_subsamples,
        couple_weight: opts.couple_weight,
        couple_gap_mm: opts.couple_gap_mm,
        loft_subdivide: opts.loft_subdivide,
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
