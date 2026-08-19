use std::fs::File;
use std::io::{BufWriter, Write};
use std::path::Path;

use zip::write::SimpleFileOptions;
use zip::ZipWriter;

use crate::stl::TriMesh;

/// Write a triangle mesh as a Bambu/Prusa-compatible 3MF (ZIP + XML).
///
/// Bambu Studio routes non-Prusa `.3mf` files through its project importer.
/// We therefore:
/// - keep the OPC layout Bambu itself emits (`Target="/3D/3dmodel.model"`,
///   `Id="rel-1"`),
/// - stamp `Application` with a PrusaSlicer-compatible token so Studio's
///   geometry-only `load_3mf` path is used (same as a Prusa export),
/// - flush the underlying writer so the ZIP central directory is complete.
///
/// Units are millimeters. Prefer a modest triangle count — vase mode does not
/// need multi-million-triangle loft densification.
pub fn write_3mf(path: &Path, mesh: &TriMesh, object_name: &str) -> std::io::Result<()> {
    let file = File::create(path)?;
    let mut zip = ZipWriter::new(BufWriter::new(file));
    let opts = SimpleFileOptions::default()
        .compression_method(zip::CompressionMethod::Deflated)
        .unix_permissions(0o644);

    zip.start_file("[Content_Types].xml", opts)?;
    zip.write_all(
        br#"<?xml version="1.0" encoding="UTF-8"?>
<Types xmlns="http://schemas.openxmlformats.org/package/2006/content-types">
 <Default Extension="rels" ContentType="application/vnd.openxmlformats-package.relationships+xml"/>
 <Default Extension="model" ContentType="application/vnd.ms-package.3dmanufacturing-3dmodel+xml"/>
</Types>
"#,
    )?;

    // Match Bambu Studio / Cura relationship naming (Target with leading slash).
    zip.start_file("_rels/.rels", opts)?;
    zip.write_all(
        br#"<?xml version="1.0" encoding="UTF-8"?>
<Relationships xmlns="http://schemas.openxmlformats.org/package/2006/relationships">
 <Relationship Target="/3D/3dmodel.model" Id="rel-1" Type="http://schemas.microsoft.com/3dmanufacturing/2013/01/3dmodel"/>
</Relationships>
"#,
    )?;

    // Deduplicate vertices by bit-pattern so indices stay stable.
    let mut verts: Vec<[f32; 3]> = Vec::new();
    let mut index_of = std::collections::HashMap::<[u32; 3], u32>::new();
    let mut tris: Vec<[u32; 3]> = Vec::new();

    let key = |p: [f32; 3]| -> [u32; 3] { [p[0].to_bits(), p[1].to_bits(), p[2].to_bits()] };

    for tri in &mesh.triangles {
        let mut idx = [0u32; 3];
        for (k, v) in tri.vertices.iter().enumerate() {
            let p = v.0;
            // Skip non-finite vertices — they crash slicer XML parsers.
            if !p[0].is_finite() || !p[1].is_finite() || !p[2].is_finite() {
                continue;
            }
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
        if idx[0] == idx[1] || idx[1] == idx[2] || idx[0] == idx[2] {
            continue; // degenerate
        }
        tris.push(idx);
    }

    if verts.is_empty() || tris.is_empty() {
        return Err(std::io::Error::new(
            std::io::ErrorKind::InvalidData,
            "mesh has no finite triangles to write as 3MF",
        ));
    }

    zip.start_file("3D/3dmodel.model", opts)?;
    let name = esc(object_name);
    // "PrusaSlicer" in Application makes Bambu Studio use its geometry-only
    // importer (load_3mf) instead of the project importer (load_bbs_3mf),
    // which rejects many third-party geometry packages.
    write!(
        zip,
        "<?xml version=\"1.0\" encoding=\"UTF-8\"?>\n\
<model unit=\"millimeter\" xml:lang=\"en-US\" xmlns=\"http://schemas.microsoft.com/3dmanufacturing/core/2015/02\">\n\
 <metadata name=\"Application\">PrusaSlicer compatible (vase-stl)</metadata>\n\
 <metadata name=\"Title\">{name}</metadata>\n\
 <resources>\n\
  <object id=\"1\" name=\"{name}\" type=\"model\">\n\
   <mesh>\n\
    <vertices>\n"
    )?;
    for v in &verts {
        // Compact floats (no trailing zeros) keep the XML small for Bambu.
        writeln!(
            zip,
            "     <vertex x=\"{}\" y=\"{}\" z=\"{}\"/>",
            trim_f32(v[0]),
            trim_f32(v[1]),
            trim_f32(v[2])
        )?;
    }
    writeln!(zip, "    </vertices>\n    <triangles>")?;
    for t in &tris {
        writeln!(
            zip,
            "     <triangle v1=\"{}\" v2=\"{}\" v3=\"{}\"/>",
            t[0], t[1], t[2]
        )?;
    }
    write!(
        zip,
        "    </triangles>\n   </mesh>\n  </object>\n </resources>\n <build>\n  <item objectid=\"1\"/>\n </build>\n</model>\n"
    )?;

    // Critical: finish the ZIP *and* flush the BufWriter so the EOCD is on disk.
    let mut buf = zip.finish()?;
    buf.flush()?;
    Ok(())
}

fn trim_f32(v: f32) -> String {
    // Enough precision for FDM (~0.001 mm) without bloating the XML.
    let s = format!("{v:.4}");
    if !s.contains('.') {
        return s;
    }
    let s = s.trim_end_matches('0').trim_end_matches('.').to_string();
    if s.is_empty() || s == "-" {
        "0".into()
    } else {
        s
    }
}

fn esc(s: &str) -> String {
    s.replace('&', "&amp;")
        .replace('<', "&lt;")
        .replace('>', "&gt;")
        .replace('"', "&quot;")
}
