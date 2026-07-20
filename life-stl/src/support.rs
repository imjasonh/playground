//! Breakaway support geometry (not cell-aligned fused voxels).
//!
//! Tips are the bottoms of Life cells with no Life|Base directly underneath.
//! Pillars go straight up from the bed; tree style clusters tips into trunks
//! with diagonal branches. Contacts use a small tip radius so they snap off,
//! leaving the Life|Base mesh as the standing piece (when it has no orphans).

use stl_io::Triangle;

use crate::config::{SupportParams, SupportStyle};
use crate::mesh::{append_capped_cylinder, append_cylinder};
use crate::volume::{CellKind, Volume};

/// A point under a Life cell that needs print support.
#[derive(Debug, Clone, Copy)]
pub struct SupportTip {
    pub cell_x: usize,
    pub cell_y: usize,
    pub cell_z: usize,
    /// Contact point on the underside of the Life cell (mm).
    pub tip: [f32; 3],
}

/// Collect breakaway tips: Life cells whose directly-below cell is not Life/Base.
pub fn collect_tips(volume: &Volume, cell_mm: f32, tip_offset_mm: f32) -> Vec<SupportTip> {
    let mut tips = Vec::new();
    let s = cell_mm;
    let mid = s * 0.5;
    // Keep the tip on the bottom face; offset toward +X/+Y but stay inside the cell.
    let ox = tip_offset_mm.clamp(0.0, mid * 0.8);
    let oy = tip_offset_mm.clamp(0.0, mid * 0.8);

    for z in 1..volume.depth {
        for y in 0..volume.height {
            for x in 0..volume.width {
                if volume.get(x, y, z) != CellKind::Life {
                    continue;
                }
                let below = volume.get(x, y, z - 1);
                if matches!(below, CellKind::Life | CellKind::Base) {
                    continue;
                }
                tips.push(SupportTip {
                    cell_x: x,
                    cell_y: y,
                    cell_z: z,
                    tip: [
                        x as f32 * s + mid + ox,
                        y as f32 * s + mid + oy,
                        z as f32 * s,
                    ],
                });
            }
        }
    }
    tips
}

/// Z height (mm) of the top of the base plate.
pub fn base_top_mm(volume: &Volume, cell_mm: f32) -> f32 {
    // Highest Base layer + 1 cell, or 0 if none.
    let mut max_z = 0usize;
    let mut any = false;
    for z in 0..volume.depth {
        for y in 0..volume.height {
            for x in 0..volume.width {
                if volume.get(x, y, z) == CellKind::Base {
                    any = true;
                    max_z = max_z.max(z);
                }
            }
        }
    }
    if !any {
        0.0
    } else {
        (max_z + 1) as f32 * cell_mm
    }
}

/// Build breakaway support triangles for the given tips.
pub fn triangles_for_tips(
    tips: &[SupportTip],
    base_z: f32,
    params: &SupportParams,
) -> Vec<Triangle> {
    if tips.is_empty() {
        return Vec::new();
    }
    match params.style {
        SupportStyle::Pillar => pillar_supports(tips, base_z, params),
        SupportStyle::Tree => tree_supports(tips, base_z, params),
    }
}

fn pillar_supports(tips: &[SupportTip], base_z: f32, params: &SupportParams) -> Vec<Triangle> {
    let mut tris = Vec::new();
    let segs = params.segments.max(3);
    for tip in tips {
        append_tapered_pillar(
            &mut tris,
            [tip.tip[0], tip.tip[1], base_z],
            tip.tip,
            params.radius_mm,
            params.tip_radius_mm,
            params.tip_height_mm,
            segs,
        );
    }
    tris
}

fn tree_supports(tips: &[SupportTip], base_z: f32, params: &SupportParams) -> Vec<Triangle> {
    let mut tris = Vec::new();
    let segs = params.segments.max(3);
    let clusters = cluster_tips(tips, params.cluster_mm);

    for cluster in &clusters {
        let (cx, cy) = cluster_centroid(cluster);
        let max_tip_z = cluster.iter().map(|t| t.tip[2]).fold(base_z, f32::max);
        // Branch junction just below the lowest tip taper start.
        let mut junction_z = cluster
            .iter()
            .map(|t| t.tip[2] - params.tip_height_mm)
            .fold(f32::INFINITY, f32::min);
        if !junction_z.is_finite() {
            junction_z = base_z;
        }
        junction_z = junction_z
            .max(base_z + params.radius_mm)
            .min(max_tip_z - params.tip_radius_mm);

        let trunk_bottom = [cx, cy, base_z];
        let trunk_top = [cx, cy, junction_z];
        if junction_z > base_z + 1e-3 {
            append_capped_cylinder(
                &mut tris,
                trunk_bottom,
                trunk_top,
                params.trunk_radius_mm,
                params.trunk_radius_mm,
                segs,
            );
        }

        for tip in cluster {
            let branch_start = [cx, cy, junction_z];
            let taper_start_z = (tip.tip[2] - params.tip_height_mm).max(junction_z);
            let mid = [tip.tip[0], tip.tip[1], taper_start_z];
            // Branch shaft (may be diagonal).
            if dist3(branch_start, mid) > 1e-3 {
                append_cylinder(
                    &mut tris,
                    branch_start,
                    mid,
                    params.radius_mm,
                    params.radius_mm,
                    segs,
                );
            }
            // Tip taper to the model.
            if dist3(mid, tip.tip) > 1e-3 {
                append_cylinder(
                    &mut tris,
                    mid,
                    tip.tip,
                    params.radius_mm,
                    params.tip_radius_mm,
                    segs,
                );
            }
        }
    }
    tris
}

fn append_tapered_pillar(
    tris: &mut Vec<Triangle>,
    bottom: [f32; 3],
    tip: [f32; 3],
    shaft_r: f32,
    tip_r: f32,
    tip_h: f32,
    segments: u32,
) {
    let height = tip[2] - bottom[2];
    if height <= 1e-4 {
        return;
    }
    let taper_h = tip_h.clamp(0.0, height);
    let mid_z = tip[2] - taper_h;
    let mid = [tip[0], tip[1], mid_z];
    if mid_z > bottom[2] + 1e-4 {
        append_capped_cylinder(tris, bottom, mid, shaft_r, shaft_r, segments);
    }
    append_cylinder(tris, mid, tip, shaft_r, tip_r, segments);
}

fn cluster_tips(tips: &[SupportTip], cluster_mm: f32) -> Vec<Vec<SupportTip>> {
    let r2 = cluster_mm.max(0.0) * cluster_mm.max(0.0);
    let mut remaining: Vec<SupportTip> = tips.to_vec();
    let mut clusters = Vec::new();
    while let Some(seed) = remaining.pop() {
        let mut cluster = vec![seed];
        let mut i = 0;
        while i < remaining.len() {
            let t = remaining[i];
            let join = cluster.iter().any(|c| {
                let dx = c.tip[0] - t.tip[0];
                let dy = c.tip[1] - t.tip[1];
                dx * dx + dy * dy <= r2
            });
            if join {
                cluster.push(t);
                remaining.swap_remove(i);
            } else {
                i += 1;
            }
        }
        clusters.push(cluster);
    }
    clusters
}

fn cluster_centroid(cluster: &[SupportTip]) -> (f32, f32) {
    let n = cluster.len().max(1) as f32;
    let sx: f32 = cluster.iter().map(|t| t.tip[0]).sum();
    let sy: f32 = cluster.iter().map(|t| t.tip[1]).sum();
    (sx / n, sy / n)
}

fn dist3(a: [f32; 3], b: [f32; 3]) -> f32 {
    let dx = a[0] - b[0];
    let dy = a[1] - b[1];
    let dz = a[2] - b[2];
    (dx * dx + dy * dy + dz * dz).sqrt()
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::config::SupportParams;
    use crate::volume::CellKind;

    fn volume_with_overhang() -> Volume {
        let mut v = Volume::new(3, 3, 3);
        for y in 0..3 {
            for x in 0..3 {
                v.set(x, y, 0, CellKind::Base);
            }
        }
        v.set(0, 0, 1, CellKind::Life);
        // Horizontally bridged birth (orphan-free if connected) with empty below.
        v.set(0, 0, 2, CellKind::Life);
        v.set(1, 0, 2, CellKind::Life);
        v
    }

    #[test]
    fn collects_tip_under_bridged_birth() {
        let v = volume_with_overhang();
        let tips = collect_tips(&v, 4.0, 0.0);
        assert_eq!(tips.len(), 1);
        assert_eq!((tips[0].cell_x, tips[0].cell_y, tips[0].cell_z), (1, 0, 2));
    }

    #[test]
    fn pillar_and_tree_emit_triangles() {
        let v = volume_with_overhang();
        let tips = collect_tips(&v, 4.0, 0.0);
        let base_z = base_top_mm(&v, 4.0);
        let pillar = SupportParams {
            style: SupportStyle::Pillar,
            ..SupportParams::default()
        };
        let tree = SupportParams {
            style: SupportStyle::Tree,
            ..SupportParams::default()
        };
        assert!(!triangles_for_tips(&tips, base_z, &pillar).is_empty());
        assert!(!triangles_for_tips(&tips, base_z, &tree).is_empty());
    }
}
