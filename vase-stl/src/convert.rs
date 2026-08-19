use crate::envelope::{extract_radial_envelope, max_layer_step, Envelope, EnvelopeOptions};
use crate::mesh::{loft_hollow, loft_solid, loft_solid_open_top, prepare_loft_envelope, MeshStats};
use crate::metrics::{compare_envelopes, EnvelopeMetrics};
use crate::orient::{choose_up_axis, reorient_to_z_up, BoundingBox, UpAxis};
use crate::stl::TriMesh;
use crate::validate::{validate_envelope, VaseValidation};

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
    /// Hard |Δr| budget between bands (mm). Capped at `line_width_mm`.
    pub couple_gap_mm: f32,
    /// Extrusion line width (mm). Consecutive walls must step by ≤ this.
    pub line_width_mm: f32,
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
            // Bonding budget ≤ line width (0.42 for a 0.4 mm nozzle).
            couple_gap_mm: 0.35,
            line_width_mm: 0.42,
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
    /// Layer-step check against the bonding budget.
    pub validation: VaseValidation,
}

/// One trial from [`optimize_convert`].
#[derive(Debug, Clone)]
pub struct OptimizeTrial {
    pub options: ConvertOptions,
    pub metrics: EnvelopeMetrics,
    pub score: f32,
}

fn effective_gap_mm(opts: &ConvertOptions) -> f32 {
    let lw = opts.line_width_mm.max(0.2);
    if opts.couple_gap_mm > 0.0 {
        opts.couple_gap_mm.min(lw)
    } else {
        lw * 0.85
    }
}

/// Convert `input` into a vase-mode-printable mesh.
pub fn convert(input: &TriMesh, opts: &ConvertOptions) -> Result<ConvertResult, String> {
    let prepared = prepare_mesh(input, opts)?;
    let mut opts = opts.clone();
    opts.couple_gap_mm = effective_gap_mm(&opts);

    let mut envelope = extract_envelope(&prepared.oriented, &prepared.bbox, &opts);
    if envelope.contours.is_empty() {
        return Err("envelope extraction produced no contours".into());
    }

    let validation = validate_envelope(&envelope, opts.couple_gap_mm);
    if !validation.ok {
        return Err(format!(
            "vase validation failed: worst layer step {:.3} mm exceeds bonding budget {:.3} mm ({:.1}% of samples over budget)",
            validation.worst_step_mm,
            validation.max_step_mm,
            100.0 * validation.frac_over_budget
        ));
    }

    let loft_env = prepare_loft_envelope(&envelope, opts.loft_subdivide, opts.min_radius);
    let worst_loft = max_layer_step(&loft_env.contours);
    if worst_loft > opts.couple_gap_mm + 1e-3 {
        return Err(format!(
            "loft densify introduced step {:.3} mm > budget {:.3} mm",
            worst_loft, opts.couple_gap_mm
        ));
    }

    let (mut tris, stats) = match opts.shell {
        ShellMode::Solid => loft_solid(&loft_env),
        ShellMode::OpenTop => loft_solid_open_top(&loft_env),
        ShellMode::Hollow { wall_mm } => loft_hollow(&loft_env, wall_mm),
    };

    place_on_bed(&mut tris);

    let z0 = envelope.contours.first().map(|c| c.z).unwrap_or(0.0);
    for c in &mut envelope.contours {
        c.z -= z0;
    }

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
        validation,
    })
}

/// Sweep couple-weight / gap; only keep trials that pass the line-width bonding
/// check, then pick the lowest hull+staircasing score among them.
pub fn optimize_convert(
    input: &TriMesh,
    base: &ConvertOptions,
    chop_budget_mm: f32,
) -> Result<(ConvertResult, Vec<OptimizeTrial>), String> {
    optimize_convert_with_budget(input, base, chop_budget_mm, 0.5)
}

/// Like [`optimize_convert`], with an explicit mean-|Δr| fidelity budget.
pub fn optimize_convert_with_budget(
    input: &TriMesh,
    base: &ConvertOptions,
    chop_budget_mm: f32,
    fidelity_budget_mm: f32,
) -> Result<(ConvertResult, Vec<OptimizeTrial>), String> {
    let prepared = prepare_mesh(input, base)?;
    let bond = effective_gap_mm(base);

    let mut ref_opts = base.clone();
    ref_opts.smooth_angular = 0;
    ref_opts.smooth_vertical = 0.0;
    ref_opts.smooth_vertical_mm = 0.0;
    ref_opts.smooth_vertical_range_mm = 0.0;
    ref_opts.couple_weight = 0.0;
    ref_opts.couple_gap_mm = bond; // still enforce bonding on the reference path
    ref_opts.detail_gain = 1.0;
    // Uncoupled-but-enforced reference for fidelity: gap clamp only.
    let reference = extract_envelope(&prepared.oriented, &prepared.bbox, &ref_opts);
    if reference.contours.is_empty() {
        return Err("reference envelope is empty".into());
    }

    let weights = [0.0_f32, 0.1, 0.25, 0.4, 0.6, 0.8, 1.0];
    // Gaps must be ≤ bonding budget.
    let gaps = [bond * 0.7, bond * 0.85, bond];

    let mut trials = Vec::new();
    for &w in &weights {
        for &gap in &gaps {
            let mut opts = base.clone();
            opts.couple_weight = w;
            opts.couple_gap_mm = gap.min(bond);
            opts.smooth_vertical_mm = 0.0;
            opts.smooth_vertical_range_mm = 0.0;
            opts.detail_gain = 1.0;
            opts.smooth_angular = 0;
            let env = extract_envelope(&prepared.oriented, &prepared.bbox, &opts);
            let v = validate_envelope(&env, bond);
            if !v.ok {
                continue;
            }
            let metrics = compare_envelopes(&reference, &env);
            let score = metrics.score(chop_budget_mm);
            trials.push(OptimizeTrial {
                options: opts,
                metrics,
                score,
            });
        }
    }

    if trials.is_empty() {
        return Err(format!(
            "no couple settings satisfied bonding budget {bond:.3} mm"
        ));
    }

    trials.sort_by(|a, b| {
        a.score
            .partial_cmp(&b.score)
            .unwrap_or(std::cmp::Ordering::Equal)
    });

    let best_idx = pick_min_score_under_budget(&trials, fidelity_budget_mm);
    let mut opts = trials[best_idx].options.clone();
    opts.couple_gap_mm = effective_gap_mm(&opts);
    // Re-run through convert() so bed placement + validation are consistent.
    let result = convert(input, &opts)?;

    if best_idx != 0 {
        let w = trials.remove(best_idx);
        trials.insert(0, w);
    }

    Ok((result, trials))
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

fn place_on_bed(triangles: &mut [stl_io::Triangle]) {
    let Some(bbox) = BoundingBox::from_triangles(triangles) else {
        return;
    };
    let cx = 0.5 * (bbox.min[0] + bbox.max[0]);
    let cy = 0.5 * (bbox.min[1] + bbox.max[1]);
    let z0 = bbox.min[2];
    for tri in triangles {
        for v in &mut tri.vertices {
            v.0[0] -= cx;
            v.0[1] -= cy;
            v.0[2] -= z0;
        }
    }
}
