//! Bambu Studio project (.3mf) export.
//!
//! Packages a triangle mesh plus print settings the way Bambu Studio's own
//! project files do: a standard 3MF payload (`3D/3dmodel.model`) plus a full
//! flattened settings dump (`Metadata/project_settings.config`) assembled
//! from printer + filament + process presets, with model-specific overrides
//! recorded in `different_settings_to_system` so the UI shows them as
//! modifications of the system presets.
//!
//! Presets come either from the official Bambu Studio profile library on disk
//! ([`BambuPresets::from_profiles_dir`]) or from the embedded flattened dump
//! for the A1 Mini + Generic PLA ([`BambuPresets::embedded_a1mini_pla`]) —
//! the latter needs no filesystem, so it also works from wasm.

use std::collections::BTreeMap;
use std::io::Write as _;
use std::path::Path;

use serde_json::{json, Map, Value};
use stl_io::Triangle;

/// Version stamp Bambu Studio checks for compatibility. Older Studio releases
/// warn but still open the file.
pub const APP_VERSION: &str = "01.10.02.76";

/// Flattened printer/process/filament presets ready for a project dump.
#[derive(Debug, Clone)]
pub struct BambuPresets {
    pub printer: String,
    pub process: String,
    pub filament: String,
    /// Full flattened key/value settings (printer ← filament ← process).
    pub settings: Map<String, Value>,
}

/// Export knobs for one project file.
#[derive(Debug, Clone)]
pub struct ExportOptions {
    /// Process-level overrides, recorded as modifications of the presets.
    pub overrides: BTreeMap<String, String>,
    pub bed_type: String,
    /// Bed edge length (mm); the model is centered on it.
    pub bed_size_mm: f32,
    pub object_name: String,
}

impl Default for ExportOptions {
    fn default() -> Self {
        Self {
            overrides: BTreeMap::new(),
            bed_type: "Textured PEI Plate".into(),
            bed_size_mm: 180.0,
            object_name: "life-stl".into(),
        }
    }
}

/// Overrides used for gusset-mode Life prints (see `docs/printing-a1mini.md`).
pub fn gusset_print_overrides() -> BTreeMap<String, String> {
    [
        ("enable_support", "0"),
        ("wall_loops", "3"),
        ("sparse_infill_density", "15%"),
        ("bridge_speed", "30"),
        ("brim_type", "no_brim"),
    ]
    .into_iter()
    .map(|(k, v)| (k.to_string(), v.to_string()))
    .collect()
}

impl BambuPresets {
    /// Flattened A1 Mini 0.4 nozzle + 0.20mm Standard + Generic PLA presets,
    /// embedded at build time from the official profile library.
    pub fn embedded_a1mini_pla() -> Self {
        let asset: Value = serde_json::from_str(include_str!("bambu_profile_a1mini_pla.json"))
            .expect("embedded profile asset is valid JSON");
        Self {
            printer: asset["printer"].as_str().unwrap().to_string(),
            process: asset["process"].as_str().unwrap().to_string(),
            filament: asset["filament"].as_str().unwrap().to_string(),
            settings: asset["settings"].as_object().unwrap().clone(),
        }
    }

    /// Flatten named presets from a Bambu Studio `resources/profiles/BBL`
    /// directory (with `machine/`, `process/`, and `filament/` subdirs).
    pub fn from_profiles_dir(
        dir: &Path,
        printer: &str,
        process: &str,
        filament: &str,
    ) -> Result<Self, String> {
        let by_name = load_profile_tree(dir)?;
        let mut settings = Map::new();
        for name in [printer, filament, process] {
            for (k, v) in flatten(&by_name, name)? {
                settings.insert(k, v);
            }
        }
        Ok(Self {
            printer: printer.to_string(),
            process: process.to_string(),
            filament: filament.to_string(),
            settings,
        })
    }
}

/// Keys that describe a preset rather than configure the printer.
const META_KEYS: [&str; 11] = [
    "type",
    "name",
    "inherits",
    "from",
    "setting_id",
    "instantiation",
    "description",
    "filament_id",
    "info_file",
    "renamed_from",
    "upward_compatible_machine",
];

fn load_profile_tree(dir: &Path) -> Result<BTreeMap<String, Map<String, Value>>, String> {
    let mut by_name = BTreeMap::new();
    for sub in ["machine", "process", "filament"] {
        let sub_dir = dir.join(sub);
        let entries = std::fs::read_dir(&sub_dir)
            .map_err(|e| format!("cannot read {}: {e}", sub_dir.display()))?;
        for entry in entries.flatten() {
            let path = entry.path();
            if path.extension().and_then(|e| e.to_str()) != Some("json") {
                continue;
            }
            let Ok(text) = std::fs::read_to_string(&path) else {
                continue;
            };
            let Ok(Value::Object(obj)) = serde_json::from_str::<Value>(&text) else {
                continue;
            };
            if let Some(name) = obj.get("name").and_then(Value::as_str) {
                by_name.insert(name.to_string(), obj);
            }
        }
    }
    Ok(by_name)
}

/// Resolve an `inherits` chain; child values override parents.
fn flatten(
    by_name: &BTreeMap<String, Map<String, Value>>,
    name: &str,
) -> Result<Map<String, Value>, String> {
    let mut chain = Vec::new();
    let mut cur = Some(name.to_string());
    let mut seen = std::collections::BTreeSet::new();
    while let Some(n) = cur {
        if !seen.insert(n.clone()) {
            return Err(format!("inheritance loop at {n:?}"));
        }
        let node = by_name
            .get(&n)
            .ok_or_else(|| format!("profile not found: {n:?}"))?;
        cur = node
            .get("inherits")
            .and_then(Value::as_str)
            .map(String::from);
        chain.push(node);
    }
    let mut merged = Map::new();
    for node in chain.iter().rev() {
        for (k, v) in node.iter() {
            if !META_KEYS.contains(&k.as_str()) {
                merged.insert(k.clone(), v.clone());
            }
        }
    }
    Ok(merged)
}

/// Parse a binary STL into triangles.
pub fn read_binary_stl(bytes: &[u8]) -> Result<Vec<Triangle>, String> {
    use stl_io::{Normal, Vertex};
    if bytes.len() < 84 {
        return Err("not a binary STL: shorter than 84-byte header".into());
    }
    let count = u32::from_le_bytes(bytes[80..84].try_into().unwrap()) as usize;
    if bytes.len() < 84 + count * 50 {
        return Err(format!(
            "binary STL truncated: header says {count} triangles"
        ));
    }
    let f = |off: usize| f32::from_le_bytes(bytes[off..off + 4].try_into().unwrap());
    let mut tris = Vec::with_capacity(count);
    for i in 0..count {
        let off = 84 + i * 50;
        let v = |j: usize| {
            let o = off + 12 + j * 12;
            [f(o), f(o + 4), f(o + 8)]
        };
        tris.push(Triangle {
            normal: Normal::new([f(off), f(off + 4), f(off + 8)]),
            vertices: [Vertex::new(v(0)), Vertex::new(v(1)), Vertex::new(v(2))],
        });
    }
    Ok(tris)
}

/// Deduplicated mesh (indexed vertices) for the 3MF payload.
struct IndexedMesh {
    vertices: Vec<[f32; 3]>,
    triangles: Vec<[usize; 3]>,
}

fn index_mesh(tris: &[Triangle]) -> IndexedMesh {
    let mut index: std::collections::HashMap<[i64; 3], usize> = std::collections::HashMap::new();
    let mut vertices = Vec::new();
    let mut triangles = Vec::with_capacity(tris.len());
    let quant = |c: f32| (c as f64 * 10_000.0).round() as i64;
    for t in tris {
        let mut ids = [0usize; 3];
        for (slot, v) in ids.iter_mut().zip(t.vertices.iter()) {
            let p = [v[0], v[1], v[2]];
            let key = [quant(p[0]), quant(p[1]), quant(p[2])];
            *slot = *index.entry(key).or_insert_with(|| {
                vertices.push(p);
                vertices.len() - 1
            });
        }
        triangles.push(ids);
    }
    IndexedMesh {
        vertices,
        triangles,
    }
}

fn model_xml(mesh: &IndexedMesh, bed_size_mm: f32) -> String {
    let (mut min, mut max) = ([f32::MAX; 3], [f32::MIN; 3]);
    for v in &mesh.vertices {
        for a in 0..3 {
            min[a] = min[a].min(v[a]);
            max[a] = max[a].max(v[a]);
        }
    }
    let tx = bed_size_mm / 2.0 - (min[0] + max[0]) / 2.0;
    let ty = bed_size_mm / 2.0 - (min[1] + max[1]) / 2.0;
    let tz = -min[2];

    let mut out = String::with_capacity(mesh.vertices.len() * 48);
    out.push_str(r#"<?xml version="1.0" encoding="UTF-8"?>"#);
    out.push('\n');
    out.push_str(concat!(
        r#"<model unit="millimeter" xml:lang="en-US" "#,
        r#"xmlns="http://schemas.microsoft.com/3dmanufacturing/core/2015/02" "#,
        r#"xmlns:BambuStudio="http://schemas.bambulab.com/package/2021">"#,
    ));
    out.push('\n');
    out.push_str(&format!(
        "<metadata name=\"Application\">BambuStudio-{APP_VERSION}</metadata>\n"
    ));
    out.push_str("<metadata name=\"BambuStudio:3mfVersion\">1</metadata>\n");
    out.push_str("<resources>\n<object id=\"1\" type=\"model\">\n<mesh>\n<vertices>\n");
    for v in &mesh.vertices {
        out.push_str(&format!(
            "<vertex x=\"{}\" y=\"{}\" z=\"{}\"/>\n",
            v[0], v[1], v[2]
        ));
    }
    out.push_str("</vertices>\n<triangles>\n");
    for t in &mesh.triangles {
        out.push_str(&format!(
            "<triangle v1=\"{}\" v2=\"{}\" v3=\"{}\"/>\n",
            t[0], t[1], t[2]
        ));
    }
    out.push_str("</triangles>\n</mesh>\n</object>\n</resources>\n<build>\n");
    out.push_str(&format!(
        "<item objectid=\"1\" transform=\"1 0 0 0 1 0 0 0 1 {tx:.3} {ty:.3} {tz:.3}\" printable=\"1\"/>\n"
    ));
    out.push_str("</build>\n</model>\n");
    out
}

fn model_settings_xml(name: &str) -> String {
    let name = name
        .replace('&', "&amp;")
        .replace('<', "&lt;")
        .replace('>', "&gt;")
        .replace('"', "&quot;");
    format!(
        r#"<?xml version="1.0" encoding="UTF-8"?>
<config>
  <object id="1">
    <metadata key="name" value="{name}"/>
    <metadata key="extruder" value="1"/>
    <part id="1" subtype="normal_part">
      <metadata key="name" value="{name}"/>
    </part>
  </object>
  <plate>
    <metadata key="plater_id" value="1"/>
    <metadata key="plater_name" value=""/>
    <metadata key="locked" value="false"/>
    <model_instance>
      <metadata key="object_id" value="1"/>
      <metadata key="instance_id" value="0"/>
      <metadata key="identify_id" value="1"/>
    </model_instance>
  </plate>
</config>
"#
    )
}

const CONTENT_TYPES: &str = r#"<?xml version="1.0" encoding="UTF-8"?>
<Types xmlns="http://schemas.openxmlformats.org/package/2006/content-types">
 <Default Extension="rels" ContentType="application/vnd.openxmlformats-package.relationships+xml"/>
 <Default Extension="model" ContentType="application/vnd.ms-package.3dmanufacturing-3dmodel+xml"/>
</Types>
"#;

const RELS: &str = r#"<?xml version="1.0" encoding="UTF-8"?>
<Relationships xmlns="http://schemas.openxmlformats.org/package/2006/relationships">
 <Relationship Target="/3D/3dmodel.model" Id="rel-1" Type="http://schemas.microsoft.com/3dmanufacturing/2013/01/3dmodel"/>
</Relationships>
"#;

fn project_settings_json(presets: &BambuPresets, opts: &ExportOptions) -> String {
    let mut config = presets.settings.clone();
    for (k, v) in &opts.overrides {
        config.insert(k.clone(), Value::String(v.clone()));
    }
    let override_list = opts.overrides.keys().cloned().collect::<Vec<_>>().join(";");
    config.insert("name".into(), json!("project_settings"));
    config.insert("from".into(), json!("project"));
    config.insert("version".into(), json!(APP_VERSION));
    config.insert("is_custom_defined".into(), json!("0"));
    config.insert("curr_bed_type".into(), json!(opts.bed_type));
    config.insert("print_settings_id".into(), json!(presets.process));
    config.insert("printer_settings_id".into(), json!(presets.printer));
    config.insert("filament_settings_id".into(), json!([presets.filament]));
    config.insert(
        "inherits_group".into(),
        json!([presets.process, presets.filament, presets.printer]),
    );
    config.insert(
        "different_settings_to_system".into(),
        json!([override_list, "", ""]),
    );
    serde_json::to_string_pretty(&Value::Object(config)).expect("settings serialize")
}

/// Build the full project .3mf in memory.
pub fn project_3mf_bytes(
    triangles: &[Triangle],
    presets: &BambuPresets,
    opts: &ExportOptions,
) -> Result<Vec<u8>, String> {
    if triangles.is_empty() {
        return Err("cannot export an empty mesh".into());
    }
    let mesh = index_mesh(triangles);

    let mut zip = zip::ZipWriter::new(std::io::Cursor::new(Vec::new()));
    let deflate = zip::write::SimpleFileOptions::default()
        .compression_method(zip::CompressionMethod::Deflated);
    let mut put = |path: &str, body: &str| -> Result<(), String> {
        zip.start_file(path, deflate)
            .map_err(|e| format!("zip {path}: {e}"))?;
        zip.write_all(body.as_bytes())
            .map_err(|e| format!("zip {path}: {e}"))
    };
    put("[Content_Types].xml", CONTENT_TYPES)?;
    put("_rels/.rels", RELS)?;
    put("3D/3dmodel.model", &model_xml(&mesh, opts.bed_size_mm))?;
    put(
        "Metadata/model_settings.config",
        &model_settings_xml(&opts.object_name),
    )?;
    put(
        "Metadata/project_settings.config",
        &project_settings_json(presets, opts),
    )?;
    let cursor = zip.finish().map_err(|e| format!("zip finish: {e}"))?;
    Ok(cursor.into_inner())
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::config::{Config, Pattern, SupportMode};
    use crate::{build_model, write_stl_model};
    use std::io::Read;

    fn small_model() -> crate::Model {
        build_model(&Config {
            width: 10,
            height: 10,
            depth: 12,
            pattern: Pattern::Glider,
            mode: SupportMode::Gusset,
            cell_mm: 4.0,
            ..Config::default()
        })
    }

    #[test]
    fn embedded_presets_have_a1mini_geometry() {
        let p = BambuPresets::embedded_a1mini_pla();
        assert_eq!(p.printer, "Bambu Lab A1 mini 0.4 nozzle");
        assert_eq!(p.process, "0.20mm Standard @BBL A1M");
        assert_eq!(p.filament, "Generic PLA @BBL A1M");
        assert_eq!(p.settings["printable_height"], json!("180"));
        assert_eq!(p.settings["nozzle_diameter"], json!(["0.4"]));
        assert!(p.settings.len() > 300, "expected full flattened dump");
    }

    #[test]
    fn flatten_resolves_inheritance_chains() {
        let dir = tempfile::tempdir().unwrap();
        for sub in ["machine", "process", "filament"] {
            std::fs::create_dir(dir.path().join(sub)).unwrap();
        }
        std::fs::write(
            dir.path().join("process/base.json"),
            r#"{"name":"base","layer_height":"0.2","wall_loops":"2"}"#,
        )
        .unwrap();
        std::fs::write(
            dir.path().join("process/child.json"),
            r#"{"name":"child","inherits":"base","wall_loops":"4"}"#,
        )
        .unwrap();
        std::fs::write(
            dir.path().join("machine/m.json"),
            r#"{"name":"m","printable_height":"180"}"#,
        )
        .unwrap();
        std::fs::write(
            dir.path().join("filament/f.json"),
            r#"{"name":"f","nozzle_temperature":["220"]}"#,
        )
        .unwrap();

        let p = BambuPresets::from_profiles_dir(dir.path(), "m", "child", "f").unwrap();
        assert_eq!(p.settings["layer_height"], json!("0.2"), "inherited");
        assert_eq!(p.settings["wall_loops"], json!("4"), "child override wins");
        assert_eq!(p.settings["printable_height"], json!("180"));
        assert_eq!(p.settings["nozzle_temperature"], json!(["220"]));
    }

    #[test]
    fn binary_stl_roundtrip_preserves_triangles() {
        let model = small_model();
        let dir = tempfile::tempdir().unwrap();
        let path = dir.path().join("m.stl");
        write_stl_model(&model, &path).unwrap();
        let tris = read_binary_stl(&std::fs::read(&path).unwrap()).unwrap();
        assert_eq!(tris.len(), model.triangles.len());
    }

    #[test]
    fn project_3mf_contains_settings_and_centered_mesh() {
        let model = small_model();
        let presets = BambuPresets::embedded_a1mini_pla();
        let opts = ExportOptions {
            overrides: gusset_print_overrides(),
            object_name: "test-object".into(),
            ..ExportOptions::default()
        };
        let bytes = project_3mf_bytes(&model.triangles, &presets, &opts).unwrap();

        let mut zip = zip::ZipArchive::new(std::io::Cursor::new(bytes)).unwrap();
        let names: Vec<String> = (0..zip.len())
            .map(|i| zip.by_index(i).unwrap().name().to_string())
            .collect();
        for expected in [
            "[Content_Types].xml",
            "_rels/.rels",
            "3D/3dmodel.model",
            "Metadata/model_settings.config",
            "Metadata/project_settings.config",
        ] {
            assert!(names.iter().any(|n| n == expected), "missing {expected}");
        }

        let mut settings = String::new();
        zip.by_name("Metadata/project_settings.config")
            .unwrap()
            .read_to_string(&mut settings)
            .unwrap();
        let cfg: Value = serde_json::from_str(&settings).unwrap();
        assert_eq!(cfg["enable_support"], json!("0"));
        assert_eq!(cfg["wall_loops"], json!("3"));
        assert_eq!(
            cfg["printer_settings_id"],
            json!("Bambu Lab A1 mini 0.4 nozzle")
        );
        assert_eq!(
            cfg["different_settings_to_system"][0],
            json!("bridge_speed;brim_type;enable_support;sparse_infill_density;wall_loops")
        );

        let mut xml = String::new();
        zip.by_name("3D/3dmodel.model")
            .unwrap()
            .read_to_string(&mut xml)
            .unwrap();
        assert!(xml.contains("BambuStudio-01.10.02.76"));
        assert!(xml.contains("<vertex "));
        assert!(xml.contains("printable=\"1\""));
        // The glider model spans 40 mm; centered on 180 the transform is +70-ish.
        assert!(xml.contains("transform=\"1 0 0 0 1 0 0 0 1 "));
    }

    #[test]
    fn empty_mesh_is_rejected() {
        let presets = BambuPresets::embedded_a1mini_pla();
        assert!(project_3mf_bytes(&[], &presets, &ExportOptions::default()).is_err());
    }
}
