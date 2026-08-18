use std::fs::File;
use std::io::{BufReader, BufWriter};
use std::path::Path;

use stl_io::{Normal, Triangle, Vertex};

/// Triangle soup in millimeters.
#[derive(Debug, Clone)]
pub struct TriMesh {
    pub triangles: Vec<Triangle>,
}

impl TriMesh {
    pub fn from_triangles(triangles: Vec<Triangle>) -> Self {
        Self { triangles }
    }

    pub fn is_empty(&self) -> bool {
        self.triangles.is_empty()
    }

    pub fn triangle_count(&self) -> usize {
        self.triangles.len()
    }
}

/// Read a binary or ASCII STL from `path`.
pub fn read_stl(path: &Path) -> std::io::Result<TriMesh> {
    let file = File::open(path)?;
    let mut reader = BufReader::new(file);
    let mut stl_reader = stl_io::create_stl_reader(&mut reader)?;
    let mut triangles = Vec::new();
    for tri in stl_reader.as_mut() {
        triangles.push(tri?);
    }
    Ok(TriMesh { triangles })
}

/// Write a binary STL to `path`.
pub fn write_stl(path: &Path, mesh: &TriMesh) -> std::io::Result<()> {
    let file = File::create(path)?;
    let mut writer = BufWriter::new(file);
    stl_io::write_stl(&mut writer, mesh.triangles.iter())?;
    Ok(())
}

/// Build a triangle with an explicit normal (caller-supplied orientation).
pub fn make_triangle(a: [f32; 3], b: [f32; 3], c: [f32; 3], n: [f32; 3]) -> Triangle {
    Triangle {
        normal: Normal::new(n),
        vertices: [Vertex::new(a), Vertex::new(b), Vertex::new(c)],
    }
}

/// Build a triangle and derive a geometric normal from the winding.
pub fn make_triangle_auto(a: [f32; 3], b: [f32; 3], c: [f32; 3]) -> Triangle {
    let ab = [b[0] - a[0], b[1] - a[1], b[2] - a[2]];
    let ac = [c[0] - a[0], c[1] - a[1], c[2] - a[2]];
    let mut n = [
        ab[1] * ac[2] - ab[2] * ac[1],
        ab[2] * ac[0] - ab[0] * ac[2],
        ab[0] * ac[1] - ab[1] * ac[0],
    ];
    let len = (n[0] * n[0] + n[1] * n[1] + n[2] * n[2]).sqrt();
    if len > 1e-12 {
        n[0] /= len;
        n[1] /= len;
        n[2] /= len;
    } else {
        n = [0.0, 0.0, 1.0];
    }
    make_triangle(a, b, c, n)
}
