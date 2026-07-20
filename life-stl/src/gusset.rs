//! Self-supporting Life by construction: causality braces (gussets).
//!
//! B3/S23 guarantees that every **birth** at generation `g` has exactly three
//! live parents in its Moore neighborhood at `g-1`, and every **survivor** has
//! itself directly below. Stacked on Z, no Life voxel is ever more than one
//! diagonal step from solid material below — the classic FDM 45° rule.
//!
//! So instead of external supports, gusset mode adds small leaning braces from
//! each birth voxel down to its parents. The result:
//!
//! - **No supports to remove** (removability is trivially perfect).
//! - **One connected piece**: every voxel traces its ancestry down to
//!   generation 0, which sits on the base plate.
//! - The braces *visualize Life causality* — you can read which cells caused
//!   each birth right off the print.

use stl_io::Triangle;

use crate::volume::{CellKind, Volume};

/// One brace: a leaning square strut from a parent cell up to a birth cell.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub struct Brace {
    /// Birth cell (upper end).
    pub child: (usize, usize, usize),
    /// Parent cell (lower end, one layer below, Chebyshev distance 1 in XY).
    pub parent: (usize, usize, usize),
}

/// Collect braces: for every Life voxel whose directly-below cell is empty
/// (a birth), link it to each Life voxel in its Moore neighborhood one layer
/// below — for real Life these are exactly its three B3 parents (voxels near
/// the window edge may have fewer after cropping, but never zero once the
/// volume is pruned to buildable voxels).
pub fn collect_braces(volume: &Volume) -> Vec<Brace> {
    let mut braces = Vec::new();
    for z in 1..volume.depth {
        for y in 0..volume.height {
            for x in 0..volume.width {
                if volume.get(x, y, z) != CellKind::Life {
                    continue;
                }
                if matches!(volume.get(x, y, z - 1), CellKind::Life | CellKind::Base) {
                    continue; // survivor or resting on base: full face contact
                }
                for dy in -1isize..=1 {
                    for dx in -1isize..=1 {
                        if dx == 0 && dy == 0 {
                            continue;
                        }
                        let nx = x as isize + dx;
                        let ny = y as isize + dy;
                        if nx < 0
                            || ny < 0
                            || nx >= volume.width as isize
                            || ny >= volume.height as isize
                        {
                            continue;
                        }
                        let (nx, ny) = (nx as usize, ny as usize);
                        if volume.get(nx, ny, z - 1) == CellKind::Life {
                            braces.push(Brace {
                                child: (x, y, z),
                                parent: (nx, ny, z - 1),
                            });
                        }
                    }
                }
            }
        }
    }
    braces
}

/// Emit a leaning parallelepiped strut per brace.
///
/// The strut's bottom square is embedded in the parent cube and its top square
/// in the child cube, pulled toward each other in XY so the lean stays well
/// under 45° from vertical (max ≈ 35° for corner-diagonal parents).
pub fn brace_triangles(braces: &[Brace], cell_mm: f32, width_mm: f32) -> Vec<Triangle> {
    let s = cell_mm;
    let half = (width_mm.max(0.4) * 0.5).min(0.45 * s * 0.5 + 0.4);
    let h = 0.5 * s; // vertical half-extent: embed half a cell into each cube
    let pull = 0.25 * s; // slide anchor points toward each other in XY

    let mut tris = Vec::with_capacity(braces.len() * 12);
    for b in braces {
        let (cx, cy, cz) = b.child;
        let (px, py, pz) = b.parent;
        debug_assert_eq!(pz + 1, cz);
        let interface_z = cz as f32 * s;

        let child_c = [(cx as f32 + 0.5) * s, (cy as f32 + 0.5) * s];
        let parent_c = [(px as f32 + 0.5) * s, (py as f32 + 0.5) * s];
        let dx = (child_c[0] - parent_c[0]).signum();
        let dy = (child_c[1] - parent_c[1]).signum();
        let dxn = if (child_c[0] - parent_c[0]).abs() < 1e-6 {
            0.0
        } else {
            dx
        };
        let dyn_ = if (child_c[1] - parent_c[1]).abs() < 1e-6 {
            0.0
        } else {
            dy
        };

        let bot = [
            parent_c[0] + dxn * pull,
            parent_c[1] + dyn_ * pull,
            interface_z - h,
        ];
        let top = [
            child_c[0] - dxn * pull,
            child_c[1] - dyn_ * pull,
            interface_z + h,
        ];
        append_parallelepiped(&mut tris, bot, top, half);
    }
    tris
}

/// Axis-aligned square cross-section strut between two centers (sheared box).
fn append_parallelepiped(tris: &mut Vec<Triangle>, bot: [f32; 3], top: [f32; 3], half: f32) {
    let b = [
        [bot[0] - half, bot[1] - half, bot[2]],
        [bot[0] + half, bot[1] - half, bot[2]],
        [bot[0] + half, bot[1] + half, bot[2]],
        [bot[0] - half, bot[1] + half, bot[2]],
    ];
    let t = [
        [top[0] - half, top[1] - half, top[2]],
        [top[0] + half, top[1] - half, top[2]],
        [top[0] + half, top[1] + half, top[2]],
        [top[0] - half, top[1] + half, top[2]],
    ];
    // Bottom (−Z) and top (+Z) caps.
    push_quad(tris, b[0], b[3], b[2], b[1], [0.0, 0.0, -1.0]);
    push_quad(tris, t[0], t[1], t[2], t[3], [0.0, 0.0, 1.0]);
    // Sides (approximate outward normals; slicers recompute from winding).
    push_quad(tris, b[0], b[1], t[1], t[0], [0.0, -1.0, 0.0]);
    push_quad(tris, b[1], b[2], t[2], t[1], [1.0, 0.0, 0.0]);
    push_quad(tris, b[2], b[3], t[3], t[2], [0.0, 1.0, 0.0]);
    push_quad(tris, b[3], b[0], t[0], t[3], [-1.0, 0.0, 0.0]);
}

fn push_quad(
    tris: &mut Vec<Triangle>,
    a: [f32; 3],
    b: [f32; 3],
    c: [f32; 3],
    d: [f32; 3],
    n: [f32; 3],
) {
    use stl_io::{Normal, Vertex};
    let normal = Normal::new(n);
    tris.push(Triangle {
        normal,
        vertices: [Vertex::new(a), Vertex::new(b), Vertex::new(c)],
    });
    tris.push(Triangle {
        normal,
        vertices: [Vertex::new(a), Vertex::new(c), Vertex::new(d)],
    });
}

/// Orphan count with causal (brace) connectivity: Life voxels unreachable from
/// the base through face adjacency **plus** birth→parent diagonal links.
///
/// After [`crate::volume::Volume::prune_unbuildable_life`] this is zero for
/// any real Life stack — every birth has parents below, every survivor has
/// itself below, so ancestry chains reach generation 0 on the base.
pub fn count_orphan_life_causal(volume: &Volume) -> usize {
    let w = volume.width;
    let h = volume.height;
    let d = volume.depth;
    let life_total = volume.count_kind(CellKind::Life);
    if life_total == 0 {
        return 0;
    }

    let idx = |x: usize, y: usize, z: usize| (z * h + y) * w + x;
    let mut seen = vec![false; w * h * d];
    let mut stack = Vec::new();
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

    let mut anchored = 0usize;
    while let Some((x, y, z)) = stack.pop() {
        if volume.get(x, y, z) == CellKind::Life {
            anchored += 1;
        }

        let mut neighbors: Vec<(isize, isize, isize)> = vec![
            (x as isize - 1, y as isize, z as isize),
            (x as isize + 1, y as isize, z as isize),
            (x as isize, y as isize - 1, z as isize),
            (x as isize, y as isize + 1, z as isize),
            (x as isize, y as isize, z as isize - 1),
            (x as isize, y as isize, z as isize + 1),
        ];

        // Causal links downward: if we are a birth, our braced parents anchor us.
        if z >= 1
            && volume.get(x, y, z) == CellKind::Life
            && !matches!(volume.get(x, y, z - 1), CellKind::Life | CellKind::Base)
        {
            for dy in -1isize..=1 {
                for dx in -1isize..=1 {
                    if dx == 0 && dy == 0 {
                        continue;
                    }
                    neighbors.push((x as isize + dx, y as isize + dy, z as isize - 1));
                }
            }
        }

        // Causal links upward: births at z+1 in our Moore ring lean on us.
        if z + 1 < d && volume.get(x, y, z) == CellKind::Life {
            for dy in -1isize..=1 {
                for dx in -1isize..=1 {
                    if dx == 0 && dy == 0 {
                        continue;
                    }
                    let nx = x as isize + dx;
                    let ny = y as isize + dy;
                    if nx < 0 || ny < 0 || nx >= w as isize || ny >= h as isize {
                        continue;
                    }
                    let (bx, by) = (nx as usize, ny as usize);
                    // Only a birth (empty directly below) is braced to us.
                    if !matches!(volume.get(bx, by, z), CellKind::Life | CellKind::Base) {
                        neighbors.push((bx as isize, by as isize, z as isize + 1));
                    }
                }
            }
        }

        for (nx, ny, nz) in neighbors {
            if nx < 0 || ny < 0 || nz < 0 {
                continue;
            }
            let (nx, ny, nz) = (nx as usize, ny as usize, nz as usize);
            if nx >= w || ny >= h || nz >= d {
                continue;
            }
            if !matches!(volume.get(nx, ny, nz), CellKind::Life | CellKind::Base) {
                continue;
            }
            let i = idx(nx, ny, nz);
            if !seen[i] {
                seen[i] = true;
                stack.push((nx, ny, nz));
            }
        }
    }

    life_total.saturating_sub(anchored)
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::config::{Config, Pattern, SupportMode};
    use crate::{build_life_volume, build_model};

    fn glider_config() -> Config {
        Config {
            width: 16,
            height: 16,
            depth: 24,
            pattern: Pattern::Glider,
            mode: SupportMode::Gusset,
            cell_mm: 4.0,
            ..Config::default()
        }
    }

    #[test]
    fn every_birth_has_at_least_three_parents() {
        let volume = build_life_volume(&glider_config());
        let braces = collect_braces(&volume);
        assert!(!braces.is_empty());
        use std::collections::HashMap;
        let mut per_child: HashMap<(usize, usize, usize), usize> = HashMap::new();
        for b in &braces {
            *per_child.entry(b.child).or_default() += 1;
        }
        for (child, n) in per_child {
            assert!(
                n >= 3,
                "birth {child:?} has only {n} parents (B3 promises 3)"
            );
        }
    }

    #[test]
    fn glider_stack_has_no_causal_orphans() {
        let volume = build_life_volume(&glider_config());
        // Face-only connectivity leaves orphans…
        assert!(crate::metrics::count_orphan_life(&volume) > 0);
        // …but causal (braced) connectivity anchors everything.
        assert_eq!(count_orphan_life_causal(&volume), 0);
    }

    #[test]
    fn gusset_model_is_one_piece_with_braces() {
        let model = build_model(&glider_config());
        assert!(model.gusset_braces > 0);
        assert_eq!(model.report.orphan_life_voxels, 0);
        assert!(model.report.life_self_supporting());
        assert_eq!(model.support_tips, 0);
        assert!(model.support_removability.ok);
        // Cubes plus 12 triangles per brace.
        assert!(model.triangles.len() > model.gusset_braces * 12);
    }

    #[test]
    fn shrink_wrapped_base_still_anchors_everything() {
        // Acorn on a large board: the base shrinks well below the board size
        // but must still anchor the whole stack as one piece.
        let config = Config {
            width: 44,
            height: 44,
            depth: 44,
            pattern: Pattern::Acorn,
            mode: SupportMode::Gusset,
            cell_mm: 4.0,
            ..Config::default()
        };
        assert!(!config.full_base);
        let volume = build_life_volume(&config);
        let report = crate::metrics::analyze(&volume, config.cell_mm);
        let (bw, bh) = report.base_extent_cells;
        assert!(
            bw < 44 || bh < 44,
            "expected shrink-wrapped base, got {bw}×{bh}"
        );
        assert_eq!(count_orphan_life_causal(&volume), 0);

        // Full-base override restores the whole board.
        let full = Config {
            full_base: true,
            ..config
        };
        let full_volume = build_life_volume(&full);
        let full_report = crate::metrics::analyze(&full_volume, full.cell_mm);
        assert_eq!(full_report.base_extent_cells, (44, 44));
    }

    #[test]
    fn floating_island_is_still_orphan_under_causal_check() {
        let mut v = Volume::new(5, 5, 4);
        for y in 0..5 {
            for x in 0..5 {
                v.set(x, y, 0, CellKind::Base);
            }
        }
        // A voxel two layers up with nothing below or diagonally below it.
        v.set(2, 2, 3, CellKind::Life);
        assert_eq!(count_orphan_life_causal(&v), 1);
    }
}
