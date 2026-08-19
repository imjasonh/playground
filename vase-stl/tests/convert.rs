use std::f32::consts::TAU;
use std::path::PathBuf;

use stl_io::{Normal, Triangle, Vertex};
use tempfile::tempdir;
use vase_stl::{
    convert, read_stl, write_3mf, write_stl, ConvertOptions, ShellMode, TriMesh, UpAxis,
};

fn tri(a: [f32; 3], b: [f32; 3], c: [f32; 3]) -> Triangle {
    Triangle {
        normal: Normal::new([0.0, 0.0, 1.0]),
        vertices: [Vertex::new(a), Vertex::new(b), Vertex::new(c)],
    }
}

/// Axis-aligned box from `min` to `max` as 12 triangles.
fn box_mesh(min: [f32; 3], max: [f32; 3]) -> TriMesh {
    let (x0, y0, z0) = (min[0], min[1], min[2]);
    let (x1, y1, z1) = (max[0], max[1], max[2]);
    let faces = [
        ([x0, y0, z0], [x1, y0, z0], [x1, y1, z0]),
        ([x0, y0, z0], [x1, y1, z0], [x0, y1, z0]),
        ([x0, y0, z1], [x0, y1, z1], [x1, y1, z1]),
        ([x0, y0, z1], [x1, y1, z1], [x1, y0, z1]),
        ([x0, y0, z0], [x0, y0, z1], [x1, y0, z1]),
        ([x0, y0, z0], [x1, y0, z1], [x1, y0, z0]),
        ([x0, y1, z0], [x1, y1, z0], [x1, y1, z1]),
        ([x0, y1, z0], [x1, y1, z1], [x0, y1, z1]),
        ([x0, y0, z0], [x0, y1, z0], [x0, y1, z1]),
        ([x0, y0, z0], [x0, y1, z1], [x0, y0, z1]),
        ([x1, y0, z0], [x1, y0, z1], [x1, y1, z1]),
        ([x1, y0, z0], [x1, y1, z1], [x1, y1, z0]),
    ];
    TriMesh::from_triangles(faces.into_iter().map(|(a, b, c)| tri(a, b, c)).collect())
}

/// Coarse UV sphere centered at origin.
fn sphere_mesh(radius: f32, slices: usize, stacks: usize) -> TriMesh {
    let mut tris = Vec::new();
    let mut verts = Vec::new();
    for i in 0..=stacks {
        let v = i as f32 / stacks as f32;
        let phi = std::f32::consts::PI * v;
        for j in 0..slices {
            let u = j as f32 / slices as f32;
            let theta = TAU * u;
            verts.push([
                radius * phi.sin() * theta.cos(),
                radius * phi.sin() * theta.sin(),
                radius * phi.cos(),
            ]);
        }
    }
    for i in 0..stacks {
        for j in 0..slices {
            let j2 = (j + 1) % slices;
            let a = i * slices + j;
            let b = i * slices + j2;
            let c = (i + 1) * slices + j2;
            let d = (i + 1) * slices + j;
            if i > 0 {
                tris.push(tri(verts[a], verts[b], verts[c]));
                tris.push(tri(verts[a], verts[c], verts[d]));
            } else {
                tris.push(tri(verts[a], verts[b], verts[c]));
            }
        }
    }
    TriMesh::from_triangles(tris)
}

#[test]
fn converts_box_to_solid_vase() {
    let input = box_mesh([0.0, 0.0, 0.0], [20.0, 20.0, 40.0]);
    let opts = ConvertOptions {
        layer_height: 1.0,
        angular_samples: 32,
        smooth_vertical: 0.0,
        couple_weight: 0.0,
        couple_gap_mm: 5.0, // box faces are vertical; generous budget for test
        line_width_mm: 5.0,
        loft_subdivide: 1,
        band_subsamples: 1,
        up_axis: Some(UpAxis::Z),
        ..ConvertOptions::default()
    };
    let out = convert(&input, &opts).expect("convert");
    assert!(out.stats.layers >= 40);
    assert!(out.stats.triangles > 100);
    assert_eq!(out.up_axis, UpAxis::Z);
    let size = out.bbox_after.size();
    assert!((size[2] - 40.0).abs() < 1.5, "height {}", size[2]);
    assert!(size[0] > 15.0 && size[0] < 30.0, "width {}", size[0]);
}

#[test]
fn auto_orients_tall_x_box() {
    // Tall along X → should become Z-up.
    let input = box_mesh([0.0, 0.0, 0.0], [50.0, 10.0, 10.0]);
    let opts = ConvertOptions {
        layer_height: 1.0,
        angular_samples: 24,
        couple_gap_mm: 5.0,
        line_width_mm: 5.0,
        loft_subdivide: 1,
        ..ConvertOptions::default()
    };
    let out = convert(&input, &opts).expect("convert");
    assert_eq!(out.up_axis, UpAxis::X);
    let size = out.bbox_after.size();
    assert!(size[2] > 45.0, "expected tall output, got {size:?}");
}

#[test]
fn hollow_shell_has_more_triangles_than_solid() {
    let input = box_mesh([-5.0, -5.0, 0.0], [5.0, 5.0, 20.0]);
    let base = ConvertOptions {
        layer_height: 1.0,
        angular_samples: 24,
        up_axis: Some(UpAxis::Z),
        couple_gap_mm: 5.0,
        line_width_mm: 5.0,
        loft_subdivide: 1,
        ..ConvertOptions::default()
    };
    let solid = convert(&input, &base).unwrap();
    let mut hollow_opts = base.clone();
    hollow_opts.shell = ShellMode::hollow(1.0);
    let hollow = convert(&input, &hollow_opts).unwrap();
    assert!(hollow.stats.triangles > solid.stats.triangles);
}

#[test]
fn roundtrip_write_read_stl() {
    let input = sphere_mesh(10.0, 16, 12);
    let dir = tempdir().unwrap();
    let path: PathBuf = dir.path().join("sphere.stl");
    write_stl(&path, &input).unwrap();
    let loaded = read_stl(&path).unwrap();
    assert_eq!(loaded.triangle_count(), input.triangle_count());

    let opts = ConvertOptions {
        layer_height: 0.5,
        angular_samples: 48,
        up_axis: Some(UpAxis::Z),
        couple_gap_mm: 5.0,
        line_width_mm: 5.0,
        loft_subdivide: 1,
        ..ConvertOptions::default()
    };
    let out = convert(&loaded, &opts).unwrap();
    let out_path = dir.path().join("vase.stl");
    write_stl(&out_path, &out.mesh).unwrap();
    let again = read_stl(&out_path).unwrap();
    assert_eq!(again.triangle_count(), out.mesh.triangle_count());
    assert!(again.triangle_count() > 0);
}

#[test]
fn target_height_scales_output() {
    let input = box_mesh([0.0, 0.0, 0.0], [10.0, 10.0, 20.0]);
    let opts = ConvertOptions {
        layer_height: 1.0,
        angular_samples: 24,
        up_axis: Some(UpAxis::Z),
        target_height_mm: Some(100.0),
        couple_gap_mm: 5.0,
        line_width_mm: 5.0,
        loft_subdivide: 1,
        ..ConvertOptions::default()
    };
    let out = convert(&input, &opts).expect("convert");
    let h = out.bbox_after.size()[2];
    assert!((h - 100.0).abs() < 2.0, "height {h}");
}

#[test]
fn rejects_empty_mesh() {
    let err = convert(&TriMesh::from_triangles(vec![]), &ConvertOptions::default());
    assert!(err.is_err());
}

#[test]
fn writes_valid_3mf_zip() {
    let input = box_mesh([-5.0, -5.0, 0.0], [5.0, 5.0, 20.0]);
    let opts = ConvertOptions {
        layer_height: 1.0,
        angular_samples: 24,
        couple_gap_mm: 5.0,
        line_width_mm: 5.0,
        loft_subdivide: 1,
        up_axis: Some(UpAxis::Z),
        ..ConvertOptions::default()
    };
    let out = convert(&input, &opts).unwrap();
    let dir = tempdir().unwrap();
    let path = dir.path().join("vase.3mf");
    write_3mf(&path, &out.mesh, "test-vase").unwrap();
    let data = std::fs::read(&path).unwrap();
    assert!(data.starts_with(b"PK"));
    assert!(out.validation.ok);
    assert!(out.bbox_after.min[2].abs() < 1e-4);
    // Bambu Studio needs PrusaSlicer marker + intact ZIP EOCD.
    {
        use std::io::Read;
        let mut z = zip::ZipArchive::new(std::io::Cursor::new(&data)).unwrap();
        let mut model = String::new();
        z.by_name("3D/3dmodel.model")
            .unwrap()
            .read_to_string(&mut model)
            .unwrap();
        assert!(
            model.contains("PrusaSlicer"),
            "Application metadata must mention PrusaSlicer for Bambu"
        );
        assert!(model.contains("<vertex "), "missing vertices");
        assert!(model.contains("<triangle "), "missing triangles");
        assert!(z.by_name("_rels/.rels").is_ok(), "missing relationships");
    }
}
