//! Make a Life volume easier to FDM-print without supports.
//!
//! ## Why scaffold at all?
//!
//! Conway births always have live neighbors in the previous generation, so every
//! live voxel is automatically **Moore-supported** (something in the 3×3 below)
//! when generations are stacked on Z. That satisfies the usual ~45° *angle*
//! rule on paper — but the contact is often only an **edge or corner** of the
//! cube below, which is a weak overhang in real FDM (and shows up as a large
//! “strict floating” area: empty cell directly underneath).
//!
//! Scaffold mode drops a **vertical column** under every solid that lacks
//! face-on-face support from `(x,y,z-1)`, recursing to the base. That drives
//! strict-floating area to zero. Life cells themselves are never moved or
//! removed.
//!
//! Prior art: Reiss & Price (2013) stack CA generations as cubes and fight
//! overhangs with overlap + mesh smoothing; printable “Conway towers” on
//! Printables (Fernando Jerez, yury.dz, JoergLatte) use the same Z=time idea.
//! We keep exact Life voxels and add explicit scaffold instead of smoothing.

use crate::volume::{CellKind, Volume};

/// Insert vertical scaffold columns so every solid has a solid cell directly
/// beneath it (down to the base). Idempotent; never overwrites Life/Base.
pub fn apply_scaffolding(volume: &mut Volume, base_layers: usize) {
    for z in base_layers..volume.depth {
        for y in 0..volume.height {
            for x in 0..volume.width {
                if volume.is_solid(x, y, z) {
                    ensure_vertical_support(volume, x, y, z);
                }
            }
        }
    }
}

fn ensure_vertical_support(volume: &mut Volume, x: usize, y: usize, z: usize) {
    if volume.has_vertical_support(x, y, z) {
        return;
    }
    debug_assert!(z > 0);
    let below = z - 1;
    volume.fill_empty(x, y, below, CellKind::Scaffold);
    ensure_vertical_support(volume, x, y, below);
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn floating_birth_gets_column() {
        let mut v = Volume::new(3, 3, 3);
        for y in 0..3 {
            for x in 0..3 {
                v.set(x, y, 0, CellKind::Base);
            }
        }
        // Birth-like: supported diagonally by Moore, but not vertically.
        v.set(0, 0, 1, CellKind::Life);
        v.set(1, 1, 2, CellKind::Life);
        assert!(v.has_moore_support(1, 1, 2));
        assert!(!v.has_vertical_support(1, 1, 2));
        apply_scaffolding(&mut v, 1);
        assert_eq!(v.get(1, 1, 1), CellKind::Scaffold);
        assert!(v.has_vertical_support(1, 1, 2));
    }

    #[test]
    fn stacked_life_needs_no_scaffold() {
        let mut v = Volume::new(3, 3, 2);
        v.set(1, 1, 0, CellKind::Life);
        v.set(1, 1, 1, CellKind::Life);
        apply_scaffolding(&mut v, 0);
        assert_eq!(v.count_kind(CellKind::Scaffold), 0);
    }

    #[test]
    fn scaffold_clears_strict_floating() {
        let mut v = Volume::new(5, 5, 6);
        for y in 0..5 {
            for x in 0..5 {
                v.set(x, y, 0, CellKind::Base);
            }
        }
        v.set(0, 0, 1, CellKind::Life);
        v.set(4, 4, 4, CellKind::Life);
        v.set(2, 3, 5, CellKind::Life);
        apply_scaffolding(&mut v, 1);
        for z in 0..v.depth {
            for y in 0..v.height {
                for x in 0..v.width {
                    if v.is_solid(x, y, z) {
                        assert!(
                            v.has_vertical_support(x, y, z),
                            "no vertical support at ({x},{y},{z})"
                        );
                    }
                }
            }
        }
    }
}
