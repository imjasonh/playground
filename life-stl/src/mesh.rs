use stl_io::{Normal, Triangle, Vertex};

use crate::volume::{CellKind, Volume};

/// Build an oriented triangle mesh from solid voxels (face-culled cubes).
pub fn triangles_from_volume(volume: &Volume, cell_mm: f32) -> Vec<Triangle> {
    triangles_from_volume_filtered(volume, cell_mm, |_| true)
}

/// Mesh only Life + Base voxels (ignore fused scaffold cells).
pub fn triangles_from_life_base(volume: &Volume, cell_mm: f32) -> Vec<Triangle> {
    triangles_from_volume_filtered(volume, cell_mm, |k| {
        matches!(k, CellKind::Life | CellKind::Base)
    })
}

fn triangles_from_volume_filtered(
    volume: &Volume,
    cell_mm: f32,
    keep: impl Fn(CellKind) -> bool,
) -> Vec<Triangle> {
    let mut tris = Vec::new();
    let s = cell_mm;

    let solid = |x: usize, y: usize, z: usize| keep(volume.get(x, y, z));

    for z in 0..volume.depth {
        for y in 0..volume.height {
            for x in 0..volume.width {
                if !solid(x, y, z) {
                    continue;
                }
                let fx = x as f32 * s;
                let fy = y as f32 * s;
                let fz = z as f32 * s;

                // -X
                if x == 0 || !solid(x - 1, y, z) {
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
                if x + 1 >= volume.width || !solid(x + 1, y, z) {
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
                if y == 0 || !solid(x, y - 1, z) {
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
                if y + 1 >= volume.height || !solid(x, y + 1, z) {
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
                if z == 0 || !solid(x, y, z - 1) {
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
                if z + 1 >= volume.depth || !solid(x, y, z + 1) {
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

/// Open truncated cone / cylinder along an arbitrary segment (no end caps).
pub fn append_cylinder(
    tris: &mut Vec<Triangle>,
    bottom: [f32; 3],
    top: [f32; 3],
    r_bottom: f32,
    r_top: f32,
    segments: u32,
) {
    let axis = sub(top, bottom);
    let len = length(axis);
    if len < 1e-6 || segments < 3 {
        return;
    }
    let dir = scale(axis, 1.0 / len);
    let (u, v) = orthonormal_basis(dir);
    let n = segments as usize;
    let mut ring_b = Vec::with_capacity(n);
    let mut ring_t = Vec::with_capacity(n);
    for i in 0..n {
        let a = std::f32::consts::TAU * (i as f32) / (n as f32);
        let (s, c) = a.sin_cos();
        let rb = add(scale(u, c * r_bottom), scale(v, s * r_bottom));
        let rt = add(scale(u, c * r_top), scale(v, s * r_top));
        ring_b.push(add(bottom, rb));
        ring_t.push(add(top, rt));
    }
    for i in 0..n {
        let j = (i + 1) % n;
        push_quad(
            tris,
            ring_b[i],
            ring_b[j],
            ring_t[j],
            ring_t[i],
            // Approximate outward normal from ring midpoint.
            normalize(sub(
                scale(add(ring_b[i], ring_t[i]), 0.5),
                scale(add(bottom, top), 0.5),
            )),
        );
    }
}

/// Cylinder with end caps (for trunks / pillar shafts).
pub fn append_capped_cylinder(
    tris: &mut Vec<Triangle>,
    bottom: [f32; 3],
    top: [f32; 3],
    r_bottom: f32,
    r_top: f32,
    segments: u32,
) {
    append_cylinder(tris, bottom, top, r_bottom, r_top, segments);
    let axis = sub(top, bottom);
    let len = length(axis);
    if len < 1e-6 || segments < 3 {
        return;
    }
    let dir = scale(axis, 1.0 / len);
    let (u, v) = orthonormal_basis(dir);
    let n = segments as usize;
    let mut ring_b = Vec::with_capacity(n);
    let mut ring_t = Vec::with_capacity(n);
    for i in 0..n {
        let a = std::f32::consts::TAU * (i as f32) / (n as f32);
        let (s, c) = a.sin_cos();
        ring_b.push(add(
            bottom,
            add(scale(u, c * r_bottom), scale(v, s * r_bottom)),
        ));
        ring_t.push(add(top, add(scale(u, c * r_top), scale(v, s * r_top))));
    }
    for i in 0..n {
        let j = (i + 1) % n;
        // Bottom cap (outward = -dir)
        push_tri(tris, bottom, ring_b[j], ring_b[i], scale(dir, -1.0));
        // Top cap
        push_tri(tris, top, ring_t[i], ring_t[j], dir);
    }
}

fn push_tri(tris: &mut Vec<Triangle>, a: [f32; 3], b: [f32; 3], c: [f32; 3], n: [f32; 3]) {
    tris.push(Triangle {
        normal: Normal::new(n),
        vertices: [Vertex::new(a), Vertex::new(b), Vertex::new(c)],
    });
}

fn add(a: [f32; 3], b: [f32; 3]) -> [f32; 3] {
    [a[0] + b[0], a[1] + b[1], a[2] + b[2]]
}
fn sub(a: [f32; 3], b: [f32; 3]) -> [f32; 3] {
    [a[0] - b[0], a[1] - b[1], a[2] - b[2]]
}
fn scale(a: [f32; 3], s: f32) -> [f32; 3] {
    [a[0] * s, a[1] * s, a[2] * s]
}
fn length(a: [f32; 3]) -> f32 {
    (a[0] * a[0] + a[1] * a[1] + a[2] * a[2]).sqrt()
}
fn normalize(a: [f32; 3]) -> [f32; 3] {
    let l = length(a);
    if l < 1e-8 {
        [0.0, 0.0, 1.0]
    } else {
        scale(a, 1.0 / l)
    }
}
fn orthonormal_basis(dir: [f32; 3]) -> ([f32; 3], [f32; 3]) {
    let helper = if dir[0].abs() < 0.9 {
        [1.0, 0.0, 0.0]
    } else {
        [0.0, 1.0, 0.0]
    };
    let u = normalize([
        dir[1] * helper[2] - dir[2] * helper[1],
        dir[2] * helper[0] - dir[0] * helper[2],
        dir[0] * helper[1] - dir[1] * helper[0],
    ]);
    let v = normalize([
        dir[1] * u[2] - dir[2] * u[1],
        dir[2] * u[0] - dir[0] * u[2],
        dir[0] * u[1] - dir[1] * u[0],
    ]);
    (u, v)
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
