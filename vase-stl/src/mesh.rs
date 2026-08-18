use stl_io::Triangle;

use crate::envelope::Envelope;
use crate::stl::make_triangle_auto;

/// Summary of a lofted mesh.
#[derive(Debug, Clone, Copy)]
pub struct MeshStats {
    pub layers: usize,
    pub angular_samples: usize,
    pub triangles: usize,
}

fn empty_stats() -> MeshStats {
    MeshStats {
        layers: 0,
        angular_samples: 0,
        triangles: 0,
    }
}

fn rings(envelope: &Envelope) -> (usize, f32, f32, Vec<Vec<[f32; 3]>>) {
    let contours = &envelope.contours;
    let n = contours[0].radii.len();
    let cx = envelope.axis_xy[0];
    let cy = envelope.axis_xy[1];
    let rings = contours
        .iter()
        .map(|c| {
            (0..n)
                .map(|i| {
                    let [x, y] = c.point_xy(i, cx, cy);
                    [x, y, c.z]
                })
                .collect()
        })
        .collect();
    (n, cx, cy, rings)
}

fn append_wall(tris: &mut Vec<Triangle>, rings: &[Vec<[f32; 3]>], n: usize, outward: bool) {
    for layer in 0..rings.len() - 1 {
        for i in 0..n {
            let j = (i + 1) % n;
            let a = rings[layer][i];
            let b = rings[layer][j];
            let c = rings[layer + 1][j];
            let d = rings[layer + 1][i];
            if outward {
                tris.push(make_triangle_auto(a, b, c));
                tris.push(make_triangle_auto(a, c, d));
            } else {
                tris.push(make_triangle_auto(a, c, b));
                tris.push(make_triangle_auto(a, d, c));
            }
        }
    }
}

/// Loft the envelope into a solid (closed bottom + closed top).
///
/// Slicer spiral-vase mode ignores infill/top/bottom and follows the outer
/// perimeter, so a solid is the usual input.
pub fn loft_solid(envelope: &Envelope) -> (Vec<Triangle>, MeshStats) {
    if envelope.contours.is_empty() {
        return (Vec::new(), empty_stats());
    }
    let (n, cx, cy, outer) = rings(envelope);
    let mut tris = Vec::new();

    // Bottom cap, normal −Z.
    let center_bottom = [cx, cy, envelope.contours[0].z];
    for i in 0..n {
        let j = (i + 1) % n;
        tris.push(make_triangle_auto(center_bottom, outer[0][j], outer[0][i]));
    }

    append_wall(&mut tris, &outer, n, true);

    // Top cap, normal +Z.
    let last = outer.len() - 1;
    let center_top = [cx, cy, envelope.contours[last].z];
    for i in 0..n {
        let j = (i + 1) % n;
        tris.push(make_triangle_auto(
            center_top,
            outer[last][i],
            outer[last][j],
        ));
    }

    let stats = MeshStats {
        layers: envelope.contours.len(),
        angular_samples: n,
        triangles: tris.len(),
    };
    (tris, stats)
}

/// Loft a thin open-top wall (bottom annulus + inner/outer walls).
pub fn loft_wall(envelope: &Envelope, wall_mm: f32) -> (Vec<Triangle>, MeshStats) {
    loft_hollow(envelope, wall_mm)
}

/// Open-top hollow vessel with approximate wall thickness `wall_mm`.
pub fn loft_hollow(envelope: &Envelope, wall_mm: f32) -> (Vec<Triangle>, MeshStats) {
    if envelope.contours.is_empty() {
        return (Vec::new(), empty_stats());
    }
    let (n, cx, cy, outer) = rings(envelope);
    let thickness = wall_mm.max(0.2);
    let mut tris = Vec::new();

    let inner: Vec<Vec<[f32; 3]>> = envelope
        .contours
        .iter()
        .map(|c| {
            (0..n)
                .map(|i| {
                    let r = (c.radii[i] - thickness).max(0.05);
                    let theta = std::f32::consts::TAU * (i as f32) / (n as f32);
                    [cx + r * theta.cos(), cy + r * theta.sin(), c.z]
                })
                .collect()
        })
        .collect();

    // Bottom annulus, normal −Z.
    for i in 0..n {
        let j = (i + 1) % n;
        tris.push(make_triangle_auto(outer[0][i], inner[0][i], inner[0][j]));
        tris.push(make_triangle_auto(outer[0][i], inner[0][j], outer[0][j]));
    }

    append_wall(&mut tris, &outer, n, true);
    append_wall(&mut tris, &inner, n, false);

    let stats = MeshStats {
        layers: envelope.contours.len(),
        angular_samples: n,
        triangles: tris.len(),
    };
    (tris, stats)
}

/// Solid with bottom only (open top) — also fine for spiral vase.
pub fn loft_solid_open_top(envelope: &Envelope) -> (Vec<Triangle>, MeshStats) {
    if envelope.contours.is_empty() {
        return (Vec::new(), empty_stats());
    }
    let (n, cx, cy, outer) = rings(envelope);
    let mut tris = Vec::new();

    let center_bottom = [cx, cy, envelope.contours[0].z];
    for i in 0..n {
        let j = (i + 1) % n;
        tris.push(make_triangle_auto(center_bottom, outer[0][j], outer[0][i]));
    }
    append_wall(&mut tris, &outer, n, true);

    let stats = MeshStats {
        layers: envelope.contours.len(),
        angular_samples: n,
        triangles: tris.len(),
    };
    (tris, stats)
}
