//! Breakaway support geometry with collision avoidance.
//!
//! Inspired by Cura / Bambu Studio tree supports:
//! - **Collision**: support centers stay ≥ `clearance` from Life voxel footprints
//! - **Layer descent**: tips drop one cell-layer at a time with a max XY move
//!   from the branch angle (so branches lean around obstacles instead of
//!   punching through them)
//! - **Tree attractors**: clustered tips steer toward a shared centroid so
//!   branches merge in free space above the bed
//!
//! Tips are Life cells with no Life|Base directly underneath. Contacts use a
//! small tip radius so they snap off.

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

/// Build breakaway support triangles that avoid intersecting Life voxels.
pub fn triangles_for_tips(
    volume: &Volume,
    tips: &[SupportTip],
    cell_mm: f32,
    base_z: f32,
    params: &SupportParams,
) -> Vec<Triangle> {
    if tips.is_empty() {
        return Vec::new();
    }
    let paths = match params.style {
        SupportStyle::Pillar => route_pillars(volume, tips, cell_mm, base_z, params),
        SupportStyle::Tree => route_trees(volume, tips, cell_mm, base_z, params),
    };
    emit_paths(&paths, base_z, params)
}

fn route_pillars(
    volume: &Volume,
    tips: &[SupportTip],
    cell_mm: f32,
    base_z: f32,
    params: &SupportParams,
) -> Vec<Vec<[f32; 3]>> {
    tips.iter()
        .map(|tip| {
            // Prefer staying under the tip (true pillar); dodge only when blocked.
            route_tip(
                volume,
                tip,
                cell_mm,
                base_z,
                params,
                (tip.tip[0], tip.tip[1]),
                true,
            )
        })
        .collect()
}

fn route_trees(
    volume: &Volume,
    tips: &[SupportTip],
    cell_mm: f32,
    base_z: f32,
    params: &SupportParams,
) -> Vec<Vec<[f32; 3]>> {
    let clusters = cluster_tips(tips, params.cluster_mm);
    let mut paths = Vec::new();
    for cluster in &clusters {
        let attractor = cluster_centroid(cluster);
        for tip in cluster {
            paths.push(route_tip(
                volume, tip, cell_mm, base_z, params, attractor, false,
            ));
        }
    }
    paths
}

/// Drop a tip toward the bed one cell-layer at a time, staying outside the
/// collision margin of Life voxels (Cura/Bambu-style avoidance).
fn route_tip(
    volume: &Volume,
    tip: &SupportTip,
    cell_mm: f32,
    base_z: f32,
    params: &SupportParams,
    attractor: (f32, f32),
    prefer_column: bool,
) -> Vec<[f32; 3]> {
    let clearance = effective_clearance(params);
    let max_move = max_move_per_layer(cell_mm, params.max_branch_angle_deg);
    let mut path = vec![tip.tip];
    let mut x = tip.tip[0];
    let mut y = tip.tip[1];

    // Descend through the empty cell below the tip, then lower Life layers.
    let mut z_layer = tip.cell_z as isize - 1;
    while z_layer >= 0 {
        let z_mm = (z_layer + 1) as f32 * cell_mm; // top of this layer
        if z_mm <= base_z + 1e-3 {
            break;
        }

        // Landing on the bed: snap XY if the straight drop is clear at bed.
        if z_mm - base_z <= cell_mm + 1e-3 {
            // Final approach to base_z — keep current XY if clear above bed.
            path.push([x, y, base_z]);
            return path;
        }

        let z_cell = z_layer as usize;
        if let Some((nx, ny)) = choose_next_xy(
            volume,
            cell_mm,
            clearance,
            x,
            y,
            z_cell,
            max_move,
            attractor,
            prefer_column,
            (tip.tip[0], tip.tip[1]),
        ) {
            x = nx;
            y = ny;
            path.push([x, y, z_mm]);
            z_layer -= 1;
            continue;
        }

        // Stuck: rest on the Life roof at this layer (support-on-model),
        // rather than punching through. Path ends just above that cell.
        if let Some((rx, ry, rest_z)) = find_rest_point(volume, cell_mm, x, y, z_cell, clearance) {
            if rest_z + 1e-3 < tip.tip[2] {
                path.push([rx, ry, rest_z]);
            }
            return path;
        }

        // Last resort: widen search ignoring max_move for this layer.
        if let Some((nx, ny)) = choose_next_xy(
            volume,
            cell_mm,
            clearance,
            x,
            y,
            z_cell,
            cell_mm * 8.0,
            attractor,
            prefer_column,
            (tip.tip[0], tip.tip[1]),
        ) {
            x = nx;
            y = ny;
            path.push([x, y, z_mm]);
            z_layer -= 1;
            continue;
        }

        // Give up further descent; stop in free space above the blockage.
        path.push([x, y, z_mm]);
        return path;
    }

    path.push([x, y, base_z]);
    path
}

#[allow(clippy::too_many_arguments)]
fn choose_next_xy(
    volume: &Volume,
    cell_mm: f32,
    clearance: f32,
    x: f32,
    y: f32,
    z_cell: usize,
    max_move: f32,
    attractor: (f32, f32),
    prefer_column: bool,
    tip_xy: (f32, f32),
) -> Option<(f32, f32)> {
    let mid = cell_mm * 0.5;
    let mut best: Option<(f32, f32, f64)> = None;

    // Candidate set: current position + empty cell centers in a local window.
    let mut candidates = vec![(x, y)];
    let reach_cells = ((max_move / cell_mm).ceil() as isize + 2).max(2);
    let cx0 = (x / cell_mm).floor() as isize;
    let cy0 = (y / cell_mm).floor() as isize;
    for dy in -reach_cells..=reach_cells {
        for dx in -reach_cells..=reach_cells {
            let cx = cx0 + dx;
            let cy = cy0 + dy;
            if cx < 0 || cy < 0 || cx >= volume.width as isize || cy >= volume.height as isize {
                continue;
            }
            let px = cx as f32 * cell_mm + mid;
            let py = cy as f32 * cell_mm + mid;
            candidates.push((px, py));
        }
    }

    for (px, py) in candidates {
        let dist_prev = dist2(px, py, x, y);
        if dist_prev > max_move + 1e-3 {
            continue;
        }
        if collides_life(volume, px, py, z_cell, clearance, cell_mm) {
            continue;
        }
        // Also ensure the segment from (x,y) → (px,py) at this layer doesn't
        // clip a Life footprint (sample midpoints).
        if segment_collides_life(volume, x, y, px, py, z_cell, clearance, cell_mm) {
            continue;
        }

        let d_attr = dist2(px, py, attractor.0, attractor.1);
        let d_tip = dist2(px, py, tip_xy.0, tip_xy.1);
        let score = if prefer_column {
            // Pillar: stay under tip; small penalty for move.
            d_tip + dist_prev * 0.25
        } else {
            // Tree: pull toward cluster centroid; prefer short moves.
            d_attr + dist_prev * 0.5 + d_tip * 0.1
        };

        match best {
            None => best = Some((px, py, score as f64)),
            Some((_, _, best_score)) if (score as f64) < best_score => {
                best = Some((px, py, score as f64));
            }
            _ => {}
        }
    }

    best.map(|(px, py, _)| (px, py))
}

/// True if a support center at (px,py) on layer `z_cell` would intersect Life
/// (expanded by clearance). Base is ignored — we land on it, not cut through it.
fn collides_life(
    volume: &Volume,
    px: f32,
    py: f32,
    z_cell: usize,
    clearance: f32,
    cell_mm: f32,
) -> bool {
    if z_cell >= volume.depth {
        return false;
    }
    // Only need to check nearby cells.
    let cx0 = ((px - clearance) / cell_mm).floor() as isize - 1;
    let cy0 = ((py - clearance) / cell_mm).floor() as isize - 1;
    let cx1 = ((px + clearance) / cell_mm).ceil() as isize + 1;
    let cy1 = ((py + clearance) / cell_mm).ceil() as isize + 1;
    for cy in cy0..=cy1 {
        for cx in cx0..=cx1 {
            if cx < 0 || cy < 0 || cx >= volume.width as isize || cy >= volume.height as isize {
                continue;
            }
            let cx = cx as usize;
            let cy = cy as usize;
            if volume.get(cx, cy, z_cell) != CellKind::Life {
                continue;
            }
            let x0 = cx as f32 * cell_mm;
            let y0 = cy as f32 * cell_mm;
            if dist_point_aabb2(px, py, x0, y0, x0 + cell_mm, y0 + cell_mm) < clearance {
                return true;
            }
        }
    }
    false
}

#[allow(clippy::too_many_arguments)]
fn segment_collides_life(
    volume: &Volume,
    x0: f32,
    y0: f32,
    x1: f32,
    y1: f32,
    z_cell: usize,
    clearance: f32,
    cell_mm: f32,
) -> bool {
    const SAMPLES: u32 = 4;
    for i in 0..=SAMPLES {
        let t = i as f32 / SAMPLES as f32;
        let px = x0 + (x1 - x0) * t;
        let py = y0 + (y1 - y0) * t;
        if collides_life(volume, px, py, z_cell, clearance, cell_mm) {
            return true;
        }
    }
    false
}

/// Air gap above a Life roof when resting on the model (Cura-style top distance).
const REST_AIR_GAP_MM: f32 = 0.2;

/// Point just above a Life roof at the blocking layer (`from_z`).
/// Only considers that layer so we never jump through intermediate Life.
fn find_rest_point(
    volume: &Volume,
    cell_mm: f32,
    x: f32,
    y: f32,
    from_z: usize,
    clearance: f32,
) -> Option<(f32, f32, f32)> {
    let cx = (x / cell_mm).floor() as isize;
    let cy = (y / cell_mm).floor() as isize;
    let z = from_z;
    // Prefer the cell under the current XY, then expanding Moore neighbors.
    let mut offsets: Vec<(isize, isize)> = vec![(0, 0)];
    for dy in -2..=2 {
        for dx in -2..=2 {
            if dx != 0 || dy != 0 {
                offsets.push((dx, dy));
            }
        }
    }
    for (dx, dy) in offsets {
        let nx = cx + dx;
        let ny = cy + dy;
        if nx < 0 || ny < 0 || nx >= volume.width as isize || ny >= volume.height as isize {
            continue;
        }
        let nx = nx as usize;
        let ny = ny as usize;
        if volume.get(nx, ny, z) != CellKind::Life {
            continue;
        }
        let rest_x = nx as f32 * cell_mm + cell_mm * 0.5;
        let rest_y = ny as f32 * cell_mm + cell_mm * 0.5;
        // Stop just above the roof so geometry does not dig into the model.
        let rest_z = (z + 1) as f32 * cell_mm + REST_AIR_GAP_MM;
        if z + 1 < volume.depth && collides_life(volume, rest_x, rest_y, z + 1, clearance, cell_mm)
        {
            continue;
        }
        return Some((rest_x, rest_y, rest_z));
    }
    None
}

fn emit_paths(paths: &[Vec<[f32; 3]>], base_z: f32, params: &SupportParams) -> Vec<Triangle> {
    let mut tris = Vec::new();
    let segs = params.segments.max(3);
    for path in paths {
        if path.len() < 2 {
            continue;
        }
        let lands_on_bed = path.last().is_some_and(|p| (p[2] - base_z).abs() < 1e-2);
        // Path is tip → … → base (or rest-on-model). Emit shaft segments; taper tip.
        for i in 0..path.len() - 1 {
            let a = path[i];
            let b = path[i + 1];
            if dist3(a, b) < 1e-4 {
                continue;
            }
            let at_tip = i == 0;
            let at_foot = i + 1 == path.len() - 1;
            if at_tip {
                let taper_h = params.tip_height_mm;
                let ab = dist3(a, b);
                if ab > taper_h + 1e-3 {
                    let t = taper_h / ab;
                    let mid = [
                        a[0] + (b[0] - a[0]) * t,
                        a[1] + (b[1] - a[1]) * t,
                        a[2] + (b[2] - a[2]) * t,
                    ];
                    // Tip is `a` (model contact); taper from tip radius → shaft.
                    append_cylinder(
                        &mut tris,
                        a,
                        mid,
                        params.tip_radius_mm,
                        params.radius_mm,
                        segs,
                    );
                    if at_foot && lands_on_bed {
                        append_capped_cylinder(
                            &mut tris,
                            mid,
                            b,
                            params.radius_mm,
                            params.trunk_radius_mm.max(params.radius_mm),
                            segs,
                        );
                    } else {
                        append_cylinder(
                            &mut tris,
                            mid,
                            b,
                            params.radius_mm,
                            params.radius_mm,
                            segs,
                        );
                    }
                } else if at_foot && lands_on_bed {
                    append_capped_cylinder(
                        &mut tris,
                        a,
                        b,
                        params.tip_radius_mm,
                        params.trunk_radius_mm.max(params.radius_mm),
                        segs,
                    );
                } else {
                    append_cylinder(
                        &mut tris,
                        a,
                        b,
                        params.tip_radius_mm,
                        params.radius_mm,
                        segs,
                    );
                }
            } else if at_foot && lands_on_bed {
                // Last segment down to bed: capped foot.
                append_capped_cylinder(
                    &mut tris,
                    a,
                    b,
                    params.radius_mm,
                    params.trunk_radius_mm.max(params.radius_mm),
                    segs,
                );
            } else {
                append_cylinder(&mut tris, a, b, params.radius_mm, params.radius_mm, segs);
            }
        }
    }
    tris
}

fn effective_clearance(params: &SupportParams) -> f32 {
    if params.clearance_mm > 0.0 {
        params.clearance_mm
    } else {
        params.radius_mm + 0.4
    }
}

fn max_move_per_layer(cell_mm: f32, angle_deg: f32) -> f32 {
    let angle = angle_deg.clamp(5.0, 60.0).to_radians();
    cell_mm * angle.tan()
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

fn dist2(x0: f32, y0: f32, x1: f32, y1: f32) -> f32 {
    let dx = x0 - x1;
    let dy = y0 - y1;
    (dx * dx + dy * dy).sqrt()
}

fn dist3(a: [f32; 3], b: [f32; 3]) -> f32 {
    let dx = a[0] - b[0];
    let dy = a[1] - b[1];
    let dz = a[2] - b[2];
    (dx * dx + dy * dy + dz * dz).sqrt()
}

fn dist_point_aabb2(px: f32, py: f32, x0: f32, y0: f32, x1: f32, y1: f32) -> f32 {
    let cx = px.clamp(x0, x1);
    let cy = py.clamp(y0, y1);
    dist2(px, py, cx, cy)
}

/// Test helper: true if any segment of the path comes within clearance of Life.
pub fn path_intersects_life(
    volume: &Volume,
    path: &[[f32; 3]],
    cell_mm: f32,
    clearance: f32,
) -> bool {
    let last_seg = path.len().saturating_sub(2);
    for (wi, w) in path.windows(2).enumerate() {
        let a = w[0];
        let b = w[1];
        let samples = 8u32;
        for i in 0..=samples {
            let t = i as f32 / samples as f32;
            let px = a[0] + (b[0] - a[0]) * t;
            let py = a[1] + (b[1] - a[1]) * t;
            let pz = a[2] + (b[2] - a[2]) * t;
            // Skip the tip contact sample (allowed to touch the supported cell).
            if wi == 0 && i == 0 {
                continue;
            }
            // Skip the final sample — rest-on-model ends just above a Life roof.
            if wi == last_seg && i == samples {
                continue;
            }
            // Layer the sample is traveling through.
            let z_cell = ((pz - 1e-4) / cell_mm).floor() as isize;
            if z_cell < 0 {
                continue;
            }
            let z_cell = z_cell as usize;
            if z_cell >= volume.depth {
                continue;
            }
            if collides_life(volume, px, py, z_cell, clearance, cell_mm) {
                return true;
            }
        }
    }
    false
}

/// Route paths for testing / inspection.
pub fn route_tips_for_test(
    volume: &Volume,
    tips: &[SupportTip],
    cell_mm: f32,
    base_z: f32,
    params: &SupportParams,
) -> Vec<Vec<[f32; 3]>> {
    match params.style {
        SupportStyle::Pillar => route_pillars(volume, tips, cell_mm, base_z, params),
        SupportStyle::Tree => route_trees(volume, tips, cell_mm, base_z, params),
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::config::SupportParams;

    fn volume_with_blocked_column() -> Volume {
        let mut v = Volume::new(5, 3, 5);
        for y in 0..3 {
            for x in 0..5 {
                v.set(x, y, 0, CellKind::Base);
            }
        }
        // Column of life at x=2 that a naive pillar would pierce.
        v.set(2, 1, 1, CellKind::Life);
        v.set(2, 1, 2, CellKind::Life);
        // Bridged overhang at x=2,y=1,z=4 with empty at z=3 — tip needs support
        // but (2,1,1) and (2,1,2) block a straight drop.
        v.set(1, 1, 4, CellKind::Life);
        v.set(1, 1, 3, CellKind::Life); // column for anchoring
        v.set(2, 1, 4, CellKind::Life); // overhang tip (empty at 2,1,3)
        v
    }

    #[test]
    fn collects_tip_under_bridged_birth() {
        let mut v = Volume::new(3, 3, 3);
        for y in 0..3 {
            for x in 0..3 {
                v.set(x, y, 0, CellKind::Base);
            }
        }
        v.set(0, 0, 1, CellKind::Life);
        v.set(0, 0, 2, CellKind::Life);
        v.set(1, 0, 2, CellKind::Life);
        let tips = collect_tips(&v, 4.0, 0.0);
        assert_eq!(tips.len(), 1);
        assert_eq!((tips[0].cell_x, tips[0].cell_y, tips[0].cell_z), (1, 0, 2));
    }

    #[test]
    fn routes_dodge_blocking_life_cells() {
        let v = volume_with_blocked_column();
        let cell = 4.0;
        let tips = collect_tips(&v, cell, 0.0);
        assert!(!tips.is_empty());
        let base_z = base_top_mm(&v, cell);
        let params = SupportParams {
            style: SupportStyle::Pillar,
            clearance_mm: 0.8,
            max_branch_angle_deg: 45.0,
            ..SupportParams::default()
        };
        let paths = route_tips_for_test(&v, &tips, cell, base_z, &params);
        let clearance = effective_clearance(&params);
        for path in &paths {
            assert!(
                !path_intersects_life(&v, path, cell, clearance),
                "support path intersected Life: {path:?}"
            );
        }
        assert!(!triangles_for_tips(&v, &tips, cell, base_z, &params).is_empty());
    }

    #[test]
    fn tree_routes_also_avoid_life() {
        let v = volume_with_blocked_column();
        let cell = 4.0;
        let tips = collect_tips(&v, cell, 0.0);
        let base_z = base_top_mm(&v, cell);
        let params = SupportParams {
            style: SupportStyle::Tree,
            clearance_mm: 0.8,
            max_branch_angle_deg: 45.0,
            cluster_mm: 20.0,
            ..SupportParams::default()
        };
        let paths = route_tips_for_test(&v, &tips, cell, base_z, &params);
        let clearance = effective_clearance(&params);
        for path in &paths {
            assert!(
                !path_intersects_life(&v, path, cell, clearance),
                "tree path intersected Life: {path:?}"
            );
        }
    }
}
