use crate::volume::{CellKind, Volume};

/// Printability / overhang statistics for a voxel volume.
#[derive(Debug, Clone, PartialEq)]
pub struct PrintabilityReport {
    pub life_voxels: usize,
    pub scaffold_voxels: usize,
    pub base_voxels: usize,
    pub solid_voxels: usize,
    /// Solids with no Moore (3×3) support from the layer below.
    pub moore_unsupported_voxels: usize,
    pub moore_unsupported_area_mm2: f64,
    pub moore_unsupported_pct: f64,
    /// Solids whose directly-below cell is empty (stricter than Moore).
    pub strict_floating_voxels: usize,
    pub strict_floating_area_mm2: f64,
    pub strict_floating_pct: f64,
    /// Life voxels whose directly-below cell is empty (overhanging births).
    pub unsupported_life_voxels: usize,
    pub unsupported_life_pct: f64,
}

/// Analyze unsupported / floating regions.
///
/// Primary “unsupported space” estimate is **strict floating**: bottom-face
/// area of solids with an empty cell directly underneath
/// (`count × cell_mm²` mm²). Those faces need bridging or supports in FDM.
/// Moore-unsupported area is also reported; for unmodified Life stacks it is
/// always zero because births require neighbors in the previous generation.
pub fn analyze(volume: &Volume, cell_mm: f32) -> PrintabilityReport {
    let cell_area = f64::from(cell_mm) * f64::from(cell_mm);
    let mut moore_unsupported = 0usize;
    let mut strict_floating = 0usize;
    let mut unsupported_life = 0usize;

    for z in 0..volume.depth {
        for y in 0..volume.height {
            for x in 0..volume.width {
                let kind = volume.get(x, y, z);
                if !kind.is_solid() {
                    continue;
                }
                if !volume.has_moore_support(x, y, z) {
                    moore_unsupported += 1;
                }
                if !volume.has_vertical_support(x, y, z) {
                    strict_floating += 1;
                    if kind == CellKind::Life {
                        unsupported_life += 1;
                    }
                }
            }
        }
    }

    let life = volume.count_kind(CellKind::Life);
    let scaffold = volume.count_kind(CellKind::Scaffold);
    let base = volume.count_kind(CellKind::Base);
    let solid = volume.solid_count();
    let solid_f = solid.max(1) as f64;
    let life_f = life.max(1) as f64;

    PrintabilityReport {
        life_voxels: life,
        scaffold_voxels: scaffold,
        base_voxels: base,
        solid_voxels: solid,
        moore_unsupported_voxels: moore_unsupported,
        moore_unsupported_area_mm2: moore_unsupported as f64 * cell_area,
        moore_unsupported_pct: 100.0 * moore_unsupported as f64 / solid_f,
        strict_floating_voxels: strict_floating,
        strict_floating_area_mm2: strict_floating as f64 * cell_area,
        strict_floating_pct: 100.0 * strict_floating as f64 / solid_f,
        unsupported_life_voxels: unsupported_life,
        unsupported_life_pct: 100.0 * unsupported_life as f64 / life_f,
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::scaffold::apply_scaffolding;

    #[test]
    fn raw_floating_is_detected() {
        let mut v = Volume::new(2, 2, 2);
        v.set(0, 0, 0, CellKind::Base);
        v.set(1, 1, 1, CellKind::Life); // diagonal — Moore-supported via (0,0)?
                                        // Moore of (1,1) at z=0 includes (0,0) — supported!
        let r = analyze(&v, 2.0);
        assert_eq!(r.moore_unsupported_voxels, 0);

        let mut v2 = Volume::new(3, 3, 2);
        v2.set(0, 0, 0, CellKind::Base);
        v2.set(2, 2, 1, CellKind::Life); // Chebyshev dist 2 → unsupported
        let r2 = analyze(&v2, 1.0);
        assert_eq!(r2.moore_unsupported_voxels, 1);
        assert!((r2.moore_unsupported_area_mm2 - 1.0).abs() < 1e-9);
    }

    #[test]
    fn scaffold_clears_strict_floating() {
        let mut v = Volume::new(3, 3, 3);
        for y in 0..3 {
            for x in 0..3 {
                v.set(x, y, 0, CellKind::Base);
            }
        }
        v.set(0, 0, 1, CellKind::Life);
        v.set(2, 2, 2, CellKind::Life);
        let before = analyze(&v, 2.0);
        assert!(before.strict_floating_voxels > 0);
        apply_scaffolding(&mut v, 1);
        let r = analyze(&v, 2.0);
        assert_eq!(r.strict_floating_voxels, 0);
        assert!(r.scaffold_voxels > 0);
    }
}
