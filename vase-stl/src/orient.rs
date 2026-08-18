use stl_io::Triangle;

/// Axis treated as the print "up" direction before conversion.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum UpAxis {
    X,
    Y,
    Z,
}

impl UpAxis {
    pub fn as_str(self) -> &'static str {
        match self {
            UpAxis::X => "x",
            UpAxis::Y => "y",
            UpAxis::Z => "z",
        }
    }
}

/// Axis-aligned bounding box of a triangle mesh.
#[derive(Debug, Clone, Copy)]
pub struct BoundingBox {
    pub min: [f32; 3],
    pub max: [f32; 3],
}

impl BoundingBox {
    pub fn from_triangles(triangles: &[Triangle]) -> Option<Self> {
        let mut iter = triangles.iter();
        let first = iter.next()?;
        let mut min = first.vertices[0].0;
        let mut max = first.vertices[0].0;
        for tri in triangles {
            for v in &tri.vertices {
                for i in 0..3 {
                    min[i] = min[i].min(v.0[i]);
                    max[i] = max[i].max(v.0[i]);
                }
            }
        }
        Some(Self { min, max })
    }

    pub fn size(&self) -> [f32; 3] {
        [
            self.max[0] - self.min[0],
            self.max[1] - self.min[1],
            self.max[2] - self.min[2],
        ]
    }

    pub fn center(&self) -> [f32; 3] {
        [
            0.5 * (self.min[0] + self.max[0]),
            0.5 * (self.min[1] + self.max[1]),
            0.5 * (self.min[2] + self.max[2]),
        ]
    }

    pub fn extent_along(&self, axis: UpAxis) -> f32 {
        let s = self.size();
        match axis {
            UpAxis::X => s[0],
            UpAxis::Y => s[1],
            UpAxis::Z => s[2],
        }
    }
}

/// Pick the longest AABB edge as the print axis (vases are usually tall).
pub fn choose_up_axis(bbox: &BoundingBox) -> UpAxis {
    let s = bbox.size();
    if s[0] >= s[1] && s[0] >= s[2] {
        UpAxis::X
    } else if s[1] >= s[0] && s[1] >= s[2] {
        UpAxis::Y
    } else {
        UpAxis::Z
    }
}

/// Remap vertices so `up` becomes +Z. Returns transformed triangles.
pub fn reorient_to_z_up(triangles: &[Triangle], up: UpAxis) -> Vec<Triangle> {
    triangles
        .iter()
        .map(|tri| {
            let mut out = *tri;
            for v in &mut out.vertices {
                v.0 = map_point(v.0, up);
            }
            out.normal.0 = map_point(out.normal.0, up);
            out
        })
        .collect()
}

fn map_point(p: [f32; 3], up: UpAxis) -> [f32; 3] {
    match up {
        UpAxis::Z => p,
        // X-up → (y, z, x)
        UpAxis::X => [p[1], p[2], p[0]],
        // Y-up → (z, x, y)
        UpAxis::Y => [p[2], p[0], p[1]],
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use stl_io::{Normal, Triangle, Vertex};

    fn tri(a: [f32; 3], b: [f32; 3], c: [f32; 3]) -> Triangle {
        Triangle {
            normal: Normal::new([0.0, 0.0, 1.0]),
            vertices: [Vertex::new(a), Vertex::new(b), Vertex::new(c)],
        }
    }

    #[test]
    fn chooses_longest_axis() {
        let bbox = BoundingBox {
            min: [0.0, 0.0, 0.0],
            max: [10.0, 3.0, 4.0],
        };
        assert_eq!(choose_up_axis(&bbox), UpAxis::X);
    }

    #[test]
    fn reorient_x_up_puts_height_on_z() {
        let t = tri([0.0, 0.0, 0.0], [5.0, 0.0, 0.0], [0.0, 1.0, 0.0]);
        let out = reorient_to_z_up(&[t], UpAxis::X);
        let zs: Vec<f32> = out[0].vertices.iter().map(|v| v.0[2]).collect();
        assert!(zs.contains(&0.0));
        assert!(zs.contains(&5.0));
    }
}
