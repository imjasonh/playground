use crate::envelope::{extract_radial_envelope, EnvelopeOptions};
use crate::mesh::{loft_hollow, loft_solid, loft_solid_open_top, MeshStats};
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
    /// Gaussian σ along Z in mm (`0` = off). Removes layer terraces.
    pub smooth_vertical_mm: f32,
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
            layer_height: 0.2,
            angular_samples: 256,
            min_radius: 0.4,
            inflate: 0.0,
            smooth_angular: 0,
            smooth_vertical: 0.0,
            smooth_vertical_mm: 1.5,
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
    pub stats: MeshStats,
    pub up_axis: UpAxis,
    pub bbox_before: BoundingBox,
    pub bbox_after: BoundingBox,
}

/// Convert `input` into a vase-mode-printable mesh.
pub fn convert(input: &TriMesh, opts: &ConvertOptions) -> Result<ConvertResult, String> {
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

    let axis_xy = [bbox.center()[0], bbox.center()[1]];
    let env_opts = EnvelopeOptions {
        layer_height: opts.layer_height,
        angular_samples: opts.angular_samples,
        min_radius: opts.min_radius,
        inflate: opts.inflate,
        smooth_angular: opts.smooth_angular,
        smooth_vertical: opts.smooth_vertical,
        smooth_vertical_mm: opts.smooth_vertical_mm,
        detail_gain: opts.detail_gain,
    };
    let envelope = extract_radial_envelope(&oriented, axis_xy, bbox.min[2], bbox.max[2], &env_opts);
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
        stats,
        up_axis: up,
        bbox_before,
        bbox_after,
    })
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
