use stl_io::{Normal, Triangle, Vertex};

use crate::volume::Volume;

/// Build an oriented triangle mesh from solid voxels (face-culled cubes).
pub fn triangles_from_volume(volume: &Volume, cell_mm: f32) -> Vec<Triangle> {
    let mut tris = Vec::new();
    let s = cell_mm;

    for z in 0..volume.depth {
        for y in 0..volume.height {
            for x in 0..volume.width {
                if !volume.is_solid(x, y, z) {
                    continue;
                }
                let fx = x as f32 * s;
                let fy = y as f32 * s;
                let fz = z as f32 * s;

                // -X
                if x == 0 || !volume.is_solid(x - 1, y, z) {
                    push_quad(
                        &mut tris,
                        [fx, fy, fz],
                        [fx, fy, fz + s],
                        [fx, fy + s, fz + s],
                        [fx, fy + s, fz],
                        [-1.0, 0.0, 0.0],
                    );
                }
                // +X
                if x + 1 >= volume.width || !volume.is_solid(x + 1, y, z) {
                    push_quad(
                        &mut tris,
                        [fx + s, fy, fz],
                        [fx + s, fy + s, fz],
                        [fx + s, fy + s, fz + s],
                        [fx + s, fy, fz + s],
                        [1.0, 0.0, 0.0],
                    );
                }
                // -Y
                if y == 0 || !volume.is_solid(x, y - 1, z) {
                    push_quad(
                        &mut tris,
                        [fx, fy, fz],
                        [fx + s, fy, fz],
                        [fx + s, fy, fz + s],
                        [fx, fy, fz + s],
                        [0.0, -1.0, 0.0],
                    );
                }
                // +Y
                if y + 1 >= volume.height || !volume.is_solid(x, y + 1, z) {
                    push_quad(
                        &mut tris,
                        [fx, fy + s, fz],
                        [fx, fy + s, fz + s],
                        [fx + s, fy + s, fz + s],
                        [fx + s, fy + s, fz],
                        [0.0, 1.0, 0.0],
                    );
                }
                // -Z
                if z == 0 || !volume.is_solid(x, y, z - 1) {
                    push_quad(
                        &mut tris,
                        [fx, fy, fz],
                        [fx, fy + s, fz],
                        [fx + s, fy + s, fz],
                        [fx + s, fy, fz],
                        [0.0, 0.0, -1.0],
                    );
                }
                // +Z
                if z + 1 >= volume.depth || !volume.is_solid(x, y, z + 1) {
                    push_quad(
                        &mut tris,
                        [fx, fy, fz + s],
                        [fx + s, fy, fz + s],
                        [fx + s, fy + s, fz + s],
                        [fx, fy + s, fz + s],
                        [0.0, 0.0, 1.0],
                    );
                }
            }
        }
    }

    tris
}

fn push_quad(
    tris: &mut Vec<Triangle>,
    a: [f32; 3],
    b: [f32; 3],
    c: [f32; 3],
    d: [f32; 3],
    n: [f32; 3],
) {
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

#[cfg(test)]
mod tests {
    use super::*;
    use crate::volume::CellKind;

    #[test]
    fn unit_cube_has_twelve_triangles() {
        let mut v = Volume::new(1, 1, 1);
        v.set(0, 0, 0, CellKind::Life);
        let tris = triangles_from_volume(&v, 1.0);
        assert_eq!(tris.len(), 12);
    }

    #[test]
    fn two_stacked_share_face() {
        let mut v = Volume::new(1, 1, 2);
        v.set(0, 0, 0, CellKind::Life);
        v.set(0, 0, 1, CellKind::Life);
        let tris = triangles_from_volume(&v, 1.0);
        // 6 faces * 2 tris, minus 2 internal faces * 2 tris = 12*2 - 4 = 20?
        // Two cubes: 12 faces total, 2 internal culled → 10 faces → 20 tris.
        assert_eq!(tris.len(), 20);
    }
}
