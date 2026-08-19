use std::fs::File;
use std::io::{BufWriter, Write};
use std::path::Path;

use zip::write::SimpleFileOptions;
use zip::ZipWriter;

use crate::stl::TriMesh;

/// Write a triangle mesh as a minimal, standards-compatible 3MF (ZIP+XML).
///
/// Units are millimeters. The mesh should already sit on z=0 (bed).
pub fn write_3mf(path: &Path, mesh: &TriMesh, object_name: &str) -> std::io::Result<()> {
    let file = File::create(path)?;
    let mut zip = ZipWriter::new(BufWriter::new(file));
    let opts = SimpleFileOptions::default().compression_method(zip::CompressionMethod::Deflated);

    zip.start_file("[Content_Types].xml", opts)?;
    zip.write_all(
        br#"<?xml version="1.0" encoding="UTF-8"?>
<Types xmlns="http://schemas.openxmlformats.org/package/2006/content-types">
  <Default Extension="rels" ContentType="application/vnd.openxmlformats-package.relationships+xml"/>
  <Default Extension="model" ContentType="application/vnd.ms-package.3dmanufacturing-3dmodel+xml"/>
</Types>
"#,
    )?;

    zip.start_file("_rels/.rels", opts)?;
    zip.write_all(
        br#"<?xml version="1.0" encoding="UTF-8"?>
<Relationships xmlns="http://schemas.openxmlformats.org/package/2006/relationships">
  <Relationship Target="/3D/3dmodel.model" Id="rel0" Type="http://schemas.microsoft.com/3dmanufacturing/2013/01/3dmodel"/>
</Relationships>
"#,
    )?;

    // Build vertex dictionary + triangle indices.
    let mut verts: Vec<[f32; 3]> = Vec::new();
    let mut index_of = std::collections::HashMap::<[u32; 3], u32>::new();
    let mut tris: Vec<[u32; 3]> = Vec::new();

    let key = |p: [f32; 3]| -> [u32; 3] { [p[0].to_bits(), p[1].to_bits(), p[2].to_bits()] };

    for tri in &mesh.triangles {
        let mut idx = [0u32; 3];
        for (k, v) in tri.vertices.iter().enumerate() {
            let p = v.0;
            let kk = key(p);
            idx[k] = if let Some(&i) = index_of.get(&kk) {
                i
            } else {
                let i = verts.len() as u32;
                index_of.insert(kk, i);
                verts.push(p);
                i
            };
        }
        tris.push(idx);
    }

    zip.start_file("3D/3dmodel.model", opts)?;
    let name = esc(object_name);
    write!(
        zip,
        "<?xml version=\"1.0\" encoding=\"UTF-8\"?>\n\
<model unit=\"millimeter\" xml:lang=\"en-US\" xmlns=\"http://schemas.microsoft.com/3dmanufacturing/core/2015/02\">\n\
  <metadata name=\"Application\">vase-stl</metadata>\n\
  <metadata name=\"Title\">{name}</metadata>\n\
  <resources>\n\
    <object id=\"1\" name=\"{name}\" type=\"model\">\n\
      <mesh>\n\
        <vertices>\n"
    )?;
    for v in &verts {
        writeln!(
            zip,
            "          <vertex x=\"{:.5}\" y=\"{:.5}\" z=\"{:.5}\" />",
            v[0], v[1], v[2]
        )?;
    }
    writeln!(zip, "        </vertices>\n        <triangles>")?;
    for t in &tris {
        writeln!(
            zip,
            "          <triangle v1=\"{}\" v2=\"{}\" v3=\"{}\" />",
            t[0], t[1], t[2]
        )?;
    }
    write!(
        zip,
        "        </triangles>\n      </mesh>\n    </object>\n  </resources>\n  <build>\n    <item objectid=\"1\" />\n  </build>\n</model>\n"
    )?;

    zip.finish()?;
    Ok(())
}

fn esc(s: &str) -> String {
    s.replace('&', "&amp;")
        .replace('<', "&lt;")
        .replace('>', "&gt;")
        .replace('"', "&quot;")
}
