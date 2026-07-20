//! Simplified structural model for breakaway supports during FDM printing.
//!
//! This is **not** full FEA. Each support shaft is treated as a circular
//! column/beam under the weight of the Life voxels it holds (PLA density ×
//! volume × g), scaled by a safety factor for print dynamics (extrusion /
//! cooling / nozzle contact). We size radii from:
//! - compressive stress `σ = F / A`
//! - Euler buckling for tall trunks
//! - bending from branch lean (`σ = F/A + M r / I`)
//!
//! Tips are intentionally **not** sized for strength — they stay needle-thin
//! so they snap off after printing. Strength lives in branches and trunks.

use crate::config::PhysicsParams;
use crate::support::SupportTip;
use crate::volume::{CellKind, Volume};

/// Gravity (m/s²).
const G: f32 = 9.81;

/// Result of sizing one support member.
#[derive(Debug, Clone, Copy, PartialEq)]
pub struct MemberSizing {
    /// Required radius (mm) for the working load + safety factor.
    pub radius_mm: f32,
    /// Estimated axial load (N) including safety factor.
    pub load_n: f32,
    /// Estimated worst-case stress (MPa) at the chosen radius.
    pub stress_mpa: f32,
    /// Load / capacity at the chosen radius (≥ 1 means OK).
    pub safety_factor: f32,
}

/// Aggregate physics report for a support set.
#[derive(Debug, Clone, PartialEq)]
pub struct SupportPhysicsReport {
    pub tip_count: usize,
    pub trunk_count: usize,
    pub total_support_load_n: f32,
    pub worst_member_sf: f32,
    pub max_trunk_radius_mm: f32,
    pub max_branch_radius_mm: f32,
    pub clusters_split: usize,
    /// Approximate tip snap force (N) from tip cross-section × allow stress.
    pub tip_snap_force_n: f32,
    pub ok: bool,
}

impl Default for SupportPhysicsReport {
    fn default() -> Self {
        Self {
            tip_count: 0,
            trunk_count: 0,
            total_support_load_n: 0.0,
            worst_member_sf: f32::INFINITY,
            max_trunk_radius_mm: 0.0,
            max_branch_radius_mm: 0.0,
            clusters_split: 0,
            tip_snap_force_n: 0.0,
            ok: true,
        }
    }
}

/// Weight (N) of `cells` solid voxels of edge `cell_mm`, with density + SF.
pub fn voxel_stack_load_n(cells: u32, cell_mm: f32, physics: &PhysicsParams) -> f32 {
    let vol_mm3 = cell_mm * cell_mm * cell_mm * cells as f32;
    // density g/cm³ × mm³ → grams = density * vol / 1000
    let mass_kg = physics.filament_density_g_cm3 * vol_mm3 / 1_000_000.0;
    mass_kg * G * physics.safety_factor
}

/// Count consecutive Life cells upward from a tip (including the tip cell).
pub fn supported_stack_cells(volume: &Volume, tip: &SupportTip) -> u32 {
    let mut n = 1u32;
    let mut z = tip.cell_z + 1;
    while z < volume.depth {
        if volume.get(tip.cell_x, tip.cell_y, z) != CellKind::Life {
            break;
        }
        n += 1;
        z += 1;
    }
    n
}

/// Load carried by one tip contact during printing.
pub fn tip_load_n(volume: &Volume, tip: &SupportTip, cell_mm: f32, physics: &PhysicsParams) -> f32 {
    let cells = supported_stack_cells(volume, tip);
    voxel_stack_load_n(cells, cell_mm, physics)
}

/// Minimum radius (mm) for a vertical column under axial load `force_n`
/// over length `length_mm` (compression + Euler buckling).
pub fn required_column_radius_mm(force_n: f32, length_mm: f32, physics: &PhysicsParams) -> f32 {
    if force_n <= 0.0 {
        return physics.min_shaft_radius_mm;
    }
    let allow = physics.allow_stress_mpa.max(1.0); // N/mm²
    let r_comp = (force_n / (std::f32::consts::PI * allow)).sqrt();

    // Euler buckling, effective length factor K≈0.7 (fixed base, free top-ish).
    let e = physics.youngs_modulus_mpa.max(100.0);
    let k_l = (0.7 * length_mm.max(1.0)).max(1.0);
    // P_cr = π² E I / (KL)² ≥ F, I = π r⁴ / 4
    // r⁴ ≥ 4 F (KL)² / (π³ E)
    let r4 = 4.0 * force_n * k_l * k_l / (std::f32::consts::PI.powi(3) * e);
    let r_buck = r4.max(0.0).powf(0.25);

    r_comp
        .max(r_buck)
        .max(physics.min_shaft_radius_mm)
        .min(physics.max_trunk_radius_mm)
}

/// Minimum radius for a leaning branch: axial + bending from horizontal offset.
pub fn required_branch_radius_mm(
    force_n: f32,
    length_mm: f32,
    horiz_offset_mm: f32,
    physics: &PhysicsParams,
) -> f32 {
    if force_n <= 0.0 {
        return physics.min_shaft_radius_mm;
    }
    let allow = physics.allow_stress_mpa.max(1.0);
    let mut lo = physics.min_shaft_radius_mm;
    let mut hi = physics.max_trunk_radius_mm;
    // Binary search r such that σ(r) ≤ allow.
    for _ in 0..24 {
        let mid = 0.5 * (lo + hi);
        let area = std::f32::consts::PI * mid * mid;
        let i = std::f32::consts::PI * mid.powi(4) / 4.0;
        let moment = force_n * horiz_offset_mm.abs();
        let axial = force_n / area;
        let bending = if i > 1e-12 {
            moment * mid / i
        } else {
            f32::INFINITY
        };
        let stress = axial + bending;
        // Also keep a light buckling floor via column helper.
        let r_col = required_column_radius_mm(force_n, length_mm, physics);
        if stress <= allow && mid >= r_col {
            hi = mid;
        } else {
            lo = mid;
        }
    }
    hi.clamp(physics.min_shaft_radius_mm, physics.max_trunk_radius_mm)
}

/// Safety factor of a circular shaft under axial + bending.
pub fn member_safety_factor(
    force_n: f32,
    radius_mm: f32,
    horiz_offset_mm: f32,
    physics: &PhysicsParams,
) -> f32 {
    if force_n <= 0.0 || radius_mm <= 0.0 {
        return f32::INFINITY;
    }
    let area = std::f32::consts::PI * radius_mm * radius_mm;
    let i = std::f32::consts::PI * radius_mm.powi(4) / 4.0;
    let stress = force_n / area + force_n * horiz_offset_mm.abs() * radius_mm / i.max(1e-12);
    if stress <= 1e-12 {
        return f32::INFINITY;
    }
    physics.allow_stress_mpa / stress
}

/// Approximate tip snap force (N) — smaller tip ⇒ easier breakaway.
pub fn tip_snap_force_n(tip_radius_mm: f32, physics: &PhysicsParams) -> f32 {
    let r = tip_radius_mm.max(0.0);
    let area = std::f32::consts::PI * r * r;
    // Use a fraction of allow stress — tips are meant to fail first.
    area * physics.allow_stress_mpa * 0.5
}

/// Size a trunk for the combined tip loads in a cluster.
pub fn size_trunk(
    volume: &Volume,
    cluster: &[SupportTip],
    cell_mm: f32,
    trunk_length_mm: f32,
    physics: &PhysicsParams,
) -> MemberSizing {
    let load: f32 = cluster
        .iter()
        .map(|t| tip_load_n(volume, t, cell_mm, physics))
        .sum();
    // Moment arm: mean tip distance from base centroid (conservative lean).
    let (cx, cy) = {
        let n = cluster.len().max(1) as f32;
        (
            cluster.iter().map(|t| t.tip[0]).sum::<f32>() / n,
            cluster.iter().map(|t| t.tip[1]).sum::<f32>() / n,
        )
    };
    let mean_offset = if cluster.is_empty() {
        0.0
    } else {
        cluster
            .iter()
            .map(|t| {
                let dx = t.tip[0] - cx;
                let dy = t.tip[1] - cy;
                (dx * dx + dy * dy).sqrt()
            })
            .sum::<f32>()
            / cluster.len() as f32
    };
    // Trunk is mostly axial; fold a fraction of the offset as bending.
    let r = required_branch_radius_mm(load, trunk_length_mm, mean_offset * 0.35, physics)
        .max(physics.min_shaft_radius_mm);
    let sf = member_safety_factor(load, r, mean_offset * 0.35, physics);
    let area = std::f32::consts::PI * r * r;
    let stress = if area > 0.0 { load / area } else { 0.0 };
    MemberSizing {
        radius_mm: r,
        load_n: load,
        stress_mpa: stress,
        safety_factor: sf,
    }
}

/// Size a branch from tip to join/bed.
pub fn size_branch(
    volume: &Volume,
    tip: &SupportTip,
    cell_mm: f32,
    length_mm: f32,
    horiz_offset_mm: f32,
    physics: &PhysicsParams,
) -> MemberSizing {
    let load = tip_load_n(volume, tip, cell_mm, physics);
    let r = required_branch_radius_mm(load, length_mm, horiz_offset_mm, physics);
    let sf = member_safety_factor(load, r, horiz_offset_mm, physics);
    let area = std::f32::consts::PI * r * r;
    MemberSizing {
        radius_mm: r,
        load_n: load,
        stress_mpa: if area > 0.0 { load / area } else { 0.0 },
        safety_factor: sf,
    }
}

/// Split a spatial cluster into load-safe sub-clusters (max tips + max trunk r).
pub fn split_cluster_for_physics(
    volume: &Volume,
    cluster: &[SupportTip],
    cell_mm: f32,
    trunk_length_mm: f32,
    physics: &PhysicsParams,
) -> (Vec<Vec<SupportTip>>, usize) {
    if cluster.is_empty() {
        return (Vec::new(), 0);
    }
    if !physics.auto_size {
        return (vec![cluster.to_vec()], 0);
    }

    let mut parts: Vec<Vec<SupportTip>> = Vec::new();
    let mut splits = 0usize;
    // Greedy: sort by angle around centroid, pack until limits hit.
    let mut remaining = cluster.to_vec();
    while !remaining.is_empty() {
        let (cx, cy) = {
            let n = remaining.len() as f32;
            (
                remaining.iter().map(|t| t.tip[0]).sum::<f32>() / n,
                remaining.iter().map(|t| t.tip[1]).sum::<f32>() / n,
            )
        };
        remaining.sort_by(|a, b| {
            let aa = (a.tip[1] - cy).atan2(a.tip[0] - cx);
            let bb = (b.tip[1] - cy).atan2(b.tip[0] - cx);
            aa.partial_cmp(&bb).unwrap_or(std::cmp::Ordering::Equal)
        });

        let mut group = vec![remaining.remove(0)];
        let mut i = 0;
        while i < remaining.len() {
            if group.len() >= physics.max_tips_per_trunk as usize {
                break;
            }
            let mut trial = group.clone();
            trial.push(remaining[i]);
            let sizing = size_trunk(volume, &trial, cell_mm, trunk_length_mm, physics);
            if sizing.radius_mm <= physics.max_trunk_radius_mm * 0.999
                && sizing.safety_factor >= 1.0
            {
                group.push(remaining.remove(i));
            } else {
                i += 1;
            }
        }
        if !remaining.is_empty() {
            splits += 1;
        }
        parts.push(group);
    }
    (parts, splits)
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::config::PhysicsParams;

    #[test]
    fn heavier_stack_needs_thicker_column() {
        let p = PhysicsParams {
            min_shaft_radius_mm: 0.2,
            max_trunk_radius_mm: 10.0,
            ..PhysicsParams::default()
        };
        let light = required_column_radius_mm(0.05, 20.0, &p);
        let heavy = required_column_radius_mm(5.0, 20.0, &p);
        assert!(heavy > light, "heavy={heavy} should exceed light={light}");
    }

    #[test]
    fn needle_tip_snaps_easier_than_fat_tip() {
        let p = PhysicsParams::default();
        let thin = tip_snap_force_n(0.12, &p);
        let fat = tip_snap_force_n(0.6, &p);
        assert!(thin < fat);
    }

    #[test]
    fn leaning_branch_thicker_than_vertical() {
        let p = PhysicsParams::default();
        let vert = required_branch_radius_mm(0.5, 30.0, 0.0, &p);
        let lean = required_branch_radius_mm(0.5, 30.0, 12.0, &p);
        assert!(lean >= vert);
    }
}
