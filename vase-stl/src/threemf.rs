use std::fs::File;
use std::io::{BufWriter, Write};
use std::path::Path;

use zip::write::SimpleFileOptions;
use zip::CompressionMethod;
use zip::ZipWriter;

use crate::stl::TriMesh;

/// Write a triangle mesh as a 3MF that Bambu Studio can import as geometry.
///
/// Bambu Studio's File→Open treats lowercase `.3mf` as a *project*. A bare
/// geometry package often ends as "The file does not contain any geometry
/// data." We therefore emit a minimal Bambu-shaped project:
/// - mesh object + build item with `printable="1"`
/// - `Metadata/model_settings.config` describing the part
/// - `Application` = `BambuStudio-…` so the bbs importer recognizes it
/// - flushed ZIP central directory
pub fn write_3mf(path: &Path, mesh: &TriMesh, object_name: &str) -> std::io::Result<()> {
    let file = File::create(path)?;
    let mut zip = ZipWriter::new(BufWriter::new(file));
    let opts = SimpleFileOptions::default()
        .compression_method(CompressionMethod::Deflated)
        .unix_permissions(0o644);

    zip.start_file("[Content_Types].xml", opts)?;
    zip.write_all(
        br#"<?xml version="1.0" encoding="UTF-8"?>
<Types xmlns="http://schemas.openxmlformats.org/package/2006/content-types">
 <Default Extension="rels" ContentType="application/vnd.openxmlformats-package.relationships+xml"/>
 <Default Extension="model" ContentType="application/vnd.ms-package.3dmanufacturing-3dmodel+xml"/>
 <Default Extension="config" ContentType="application/octet-stream"/>
 <Override PartName="/3D/3dmodel.model" ContentType="application/vnd.ms-package.3dmanufacturing-3dmodel+xml"/>
</Types>
"#,
    )?;

    zip.start_file("_rels/.rels", opts)?;
    zip.write_all(
        br#"<?xml version="1.0" encoding="UTF-8"?>
<Relationships xmlns="http://schemas.openxmlformats.org/package/2006/relationships">
 <Relationship Target="/3D/3dmodel.model" Id="rel-1" Type="http://schemas.microsoft.com/3dmanufacturing/2013/01/3dmodel"/>
 <Relationship Target="/Metadata/model_settings.config" Id="rel-2" Type="http://schemas.bambulab.com/package/2021/model-settings"/>
</Relationships>
"#,
    )?;

    let (verts, tris) = dedup_mesh(mesh)?;
    let name = esc(object_name);

    zip.start_file("3D/3dmodel.model", opts)?;
    write!(
        zip,
        "<?xml version=\"1.0\" encoding=\"UTF-8\"?>\n\
<model unit=\"millimeter\" xml:lang=\"en-US\" \
xmlns=\"http://schemas.microsoft.com/3dmanufacturing/core/2015/02\" \
xmlns:BambuStudio=\"http://schemas.bambulab.com/package/2021\">\n\
 <metadata name=\"Application\">BambuStudio-01.10.01.50</metadata>\n\
 <metadata name=\"BambuStudio:3mfVersion\">1</metadata>\n\
 <metadata name=\"Title\">{name}</metadata>\n\
 <resources>\n\
  <object id=\"1\" name=\"{name}\" type=\"model\">\n\
   <mesh>\n\
    <vertices>\n"
    )?;
    for v in &verts {
        writeln!(
            zip,
            "     <vertex x=\"{}\" y=\"{}\" z=\"{}\" />",
            trim_f32(v[0]),
            trim_f32(v[1]),
            trim_f32(v[2])
        )?;
    }
    writeln!(zip, "    </vertices>\n    <triangles>")?;
    for t in &tris {
        writeln!(
            zip,
            "     <triangle v1=\"{}\" v2=\"{}\" v3=\"{}\" />",
            t[0], t[1], t[2]
        )?;
    }
    write!(
        zip,
        "    </triangles>\n   </mesh>\n  </object>\n </resources>\n\
 <build>\n  <item objectid=\"1\" printable=\"1\" \
transform=\"1 0 0 0 0 1 0 0 0 0 1 0\" />\n </build>\n</model>\n"
    )?;

    // Minimal model_settings so Bambu's project importer keeps the part.
    zip.start_file("Metadata/model_settings.config", opts)?;
    write!(
        zip,
        "<?xml version=\"1.0\" encoding=\"UTF-8\"?>\n\
<config>\n\
  <object id=\"1\">\n\
    <metadata key=\"name\" value=\"{name}\"/>\n\
    <part id=\"1\" subtype=\"normal_part\">\n\
      <metadata key=\"name\" value=\"{name}\"/>\n\
      <metadata key=\"matrix\" value=\"1 0 0 0 0 1 0 0 0 0 1 0 0 0 0 1\"/>\n\
    </part>\n\
  </object>\n\
</config>\n"
    )?;

    let mut buf = zip.finish()?;
    buf.flush()?;
    Ok(())
}

type MeshBuffers = (Vec<[f32; 3]>, Vec<[u32; 3]>);

fn dedup_mesh(mesh: &TriMesh) -> std::io::Result<MeshBuffers> {
    let mut verts: Vec<[f32; 3]> = Vec::new();
    let mut index_of = std::collections::HashMap::<[u32; 3], u32>::new();
    let mut tris: Vec<[u32; 3]> = Vec::new();
    let key = |p: [f32; 3]| -> [u32; 3] { [p[0].to_bits(), p[1].to_bits(), p[2].to_bits()] };

    for tri in &mesh.triangles {
        let mut idx = [0u32; 3];
        let mut ok = true;
        for (k, v) in tri.vertices.iter().enumerate() {
            let p = v.0;
            if !p[0].is_finite() || !p[1].is_finite() || !p[2].is_finite() {
                ok = false;
                break;
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
        if !ok || idx[0] == idx[1] || idx[1] == idx[2] || idx[0] == idx[2] {
            continue;
        }
        tris.push(idx);
    }

    if verts.is_empty() || tris.is_empty() {
        return Err(std::io::Error::new(
            std::io::ErrorKind::InvalidData,
            "mesh has no finite triangles to write as 3MF",
        ));
    }
    Ok((verts, tris))
}

fn trim_f32(v: f32) -> String {
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
