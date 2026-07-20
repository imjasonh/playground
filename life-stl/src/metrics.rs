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
    /// Life voxels whose directly-below cell is empty of *any* solid
    /// (counts scaffold as support — use after scaffolding).
    pub unsupported_life_voxels: usize,
    pub unsupported_life_pct: f64,
    /// Life voxels that are **not** face-connected to the base through
    /// Life|Base only. If this is > 0, removing supports leaves multiple
    /// pieces — not a single standing sculpture. See [`life_self_supporting`].
    pub orphan_life_voxels: usize,
    pub orphan_life_pct: f64,
    /// Number of breakaway support tips generated (0 for raw / fused-only paths).
    pub breakaway_support_tips: usize,
}

impl PrintabilityReport {
    /// True when every Life voxel is face-connected to the bed via Life|Base
    /// only — supports can be removed and one standing piece remains.
    pub fn life_self_supporting(&self) -> bool {
        self.orphan_life_voxels == 0 && self.life_voxels > 0
    }
}

/// Analyze unsupported / floating regions.
///
/// Primary print overhang estimate is **strict floating** (empty cell
/// directly below). Separately, [`PrintabilityReport::orphan_life_voxels`]
/// asks whether the Life sculpture stays one piece after breakaway supports
/// are removed.
pub fn analyze(volume: &Volume, cell_mm: f32) -> PrintabilityReport {
    analyze_with_supports(volume, cell_mm, 0)
}

/// Like [`analyze`], but records how many breakaway tips were generated.
pub fn analyze_with_supports(
    volume: &Volume,
    cell_mm: f32,
    breakaway_support_tips: usize,
) -> PrintabilityReport {
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

    let orphan_life = count_orphan_life(volume);
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
        orphan_life_voxels: orphan_life,
        orphan_life_pct: 100.0 * orphan_life as f64 / life_f,
        breakaway_support_tips,
    }
}

/// Count Life voxels not reachable from the base plate by face adjacency
/// through Life|Base only (scaffold and empty are barriers).
pub fn count_orphan_life(volume: &Volume) -> usize {
    let life = volume.count_kind(CellKind::Life);
    if life == 0 {
        return 0;
    }
    let anchored = count_anchored_life(volume);
    life.saturating_sub(anchored)
}

fn count_anchored_life(volume: &Volume) -> usize {
    let w = volume.width;
    let h = volume.height;
    let d = volume.depth;
    let n = w * h * d;
    let mut seen = vec![false; n];
    let mut stack: Vec<(usize, usize, usize)> = Vec::new();

    let idx = |x: usize, y: usize, z: usize| (z * h + y) * w + x;

    for z in 0..d {
        for y in 0..h {
            for x in 0..w {
                if volume.get(x, y, z) == CellKind::Base {
                    let i = idx(x, y, z);
                    if !seen[i] {
                        seen[i] = true;
                        stack.push((x, y, z));
                    }
                }
            }
        }
    }

    let mut anchored_life = 0usize;
    while let Some((x, y, z)) = stack.pop() {
        if volume.get(x, y, z) == CellKind::Life {
            anchored_life += 1;
        }
        for (nx, ny, nz) in face_neighbors(x, y, z, w, h, d) {
            let kind = volume.get(nx, ny, nz);
            if !matches!(kind, CellKind::Life | CellKind::Base) {
                continue;
            }
            let i = idx(nx, ny, nz);
            if seen[i] {
                continue;
            }
            seen[i] = true;
            stack.push((nx, ny, nz));
        }
    }
    anchored_life
}

fn face_neighbors(
    x: usize,
    y: usize,
    z: usize,
    w: usize,
    h: usize,
    d: usize,
) -> impl Iterator<Item = (usize, usize, usize)> {
    const DIRS: [(isize, isize, isize); 6] = [
        (1, 0, 0),
        (-1, 0, 0),
        (0, 1, 0),
        (0, -1, 0),
        (0, 0, 1),
        (0, 0, -1),
    ];
    DIRS.into_iter().filter_map(move |(dx, dy, dz)| {
        let nx = x as isize + dx;
        let ny = y as isize + dy;
        let nz = z as isize + dz;
        if nx < 0 || ny < 0 || nz < 0 {
            return None;
        }
        let nx = nx as usize;
        let ny = ny as usize;
        let nz = nz as usize;
        if nx >= w || ny >= h || nz >= d {
            return None;
        }
        Some((nx, ny, nz))
    })
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::scaffold::apply_scaffolding;

    #[test]
    fn raw_floating_is_detected() {
        let mut v = Volume::new(2, 2, 2);
        v.set(0, 0, 0, CellKind::Base);
        v.set(1, 1, 1, CellKind::Life);
        let r = analyze(&v, 2.0);
        assert_eq!(r.moore_unsupported_voxels, 0);

        let mut v2 = Volume::new(3, 3, 2);
        v2.set(0, 0, 0, CellKind::Base);
        v2.set(2, 2, 1, CellKind::Life);
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

    #[test]
    fn floating_life_island_is_orphan_even_with_scaffold() {
        let mut v = Volume::new(3, 3, 3);
        for y in 0..3 {
            for x in 0..3 {
                v.set(x, y, 0, CellKind::Base);
            }
        }
        // Life only at z=2, not face-connected down through Life.
        v.set(1, 1, 2, CellKind::Life);
        assert_eq!(count_orphan_life(&v), 1);
        apply_scaffolding(&mut v, 1);
        // Scaffold fills (1,1,1) but orphans ignore scaffold.
        assert_eq!(count_orphan_life(&v), 1);
        let r = analyze(&v, 4.0);
        assert!(!r.life_self_supporting());
    }

    #[test]
    fn stacked_life_on_base_is_self_supporting() {
        let mut v = Volume::new(2, 2, 3);
        for y in 0..2 {
            for x in 0..2 {
                v.set(x, y, 0, CellKind::Base);
            }
        }
        v.set(0, 0, 1, CellKind::Life);
        v.set(0, 0, 2, CellKind::Life);
        assert_eq!(count_orphan_life(&v), 0);
        assert!(analyze(&v, 4.0).life_self_supporting());
    }

    #[test]
    fn horizontal_bridge_to_column_anchors_birth() {
        let mut v = Volume::new(3, 1, 3);
        for x in 0..3 {
            v.set(x, 0, 0, CellKind::Base);
        }
        // Persistent column at x=0.
        v.set(0, 0, 1, CellKind::Life);
        v.set(0, 0, 2, CellKind::Life);
        // Birth at x=1,z=2 face-adjacent to the column — anchored.
        v.set(1, 0, 2, CellKind::Life);
        assert_eq!(count_orphan_life(&v), 0);
    }
}
