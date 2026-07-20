//! Conway's Game of Life → printable STL (Z = time).
//!
//! Live cells at generation `g` become voxels at height `z = base_layers + g`.
//! Default [`SupportMode::Breakaway`] adds slim pillar/tree supports under
//! overhanging Life cells. Supports are meant to snap off, leaving a single
//! standing Life|Base piece when there are no Life orphans.

pub mod config;
pub mod life;
pub mod mesh;
pub mod metrics;
pub mod physics;
pub mod search;
pub mod seed;
pub mod support;
pub mod volume;

pub use config::{
    Config, PhysicsParams, SupportMode, SupportParams, SupportStyle, DEFAULT_CELL_MM, MIN_CELL_MM,
};
pub use metrics::PrintabilityReport;
pub use physics::SupportPhysicsReport;
pub use volume::{CellKind, Volume};

use std::fs::File;
use std::io::{BufWriter, Write};
use std::path::Path;

use stl_io::Triangle;

use crate::mesh::triangles_from_volume;
use crate::metrics::{analyze, analyze_with_supports};
use crate::seed::initial_grid;
use crate::support::{base_top_mm, build_supports, collect_tips};

/// Built model ready to write as STL.
#[derive(Debug, Clone)]
pub struct Model {
    pub volume: Volume,
    pub triangles: Vec<Triangle>,
    pub report: PrintabilityReport,
    pub support_tips: usize,
    pub support_physics: SupportPhysicsReport,
}

/// Simulate Life onto a volume with a base plate (no supports).
pub fn build_life_volume(config: &Config) -> Volume {
    let mut grid = initial_grid(config);
    let mut volume = Volume::new(config.width, config.height, config.total_z());

    for z in 0..config.base_layers {
        for y in 0..config.height {
            for x in 0..config.width {
                volume.set(x, y, z, CellKind::Base);
            }
        }
    }

    let life_z0 = config.base_layers;
    for z in 0..config.depth {
        for y in 0..config.height {
            for x in 0..config.width {
                if grid.is_alive(x, y) {
                    volume.set(x, y, life_z0 + z, CellKind::Life);
                }
            }
        }
        if z + 1 < config.depth {
            grid = grid.step();
        }
    }

    volume
}

/// Build the Life|Base voxel volume (no support geometry).
pub fn build_volume(config: &Config) -> Volume {
    build_life_volume(config)
}

/// Build the full printable model (Life mesh + optional breakaway supports).
pub fn build_model(config: &Config) -> Model {
    let volume = build_life_volume(config);

    match config.mode {
        SupportMode::Raw => {
            let report = analyze(&volume, config.cell_mm);
            Model {
                triangles: triangles_from_volume(&volume, config.cell_mm),
                volume,
                report,
                support_tips: 0,
                support_physics: SupportPhysicsReport::default(),
            }
        }
        SupportMode::Breakaway => {
            let tips = collect_tips(&volume, config.cell_mm, config.support.tip_offset_mm);
            let support_tips = tips.len();
            let mut triangles = triangles_from_volume(&volume, config.cell_mm);
            let base_z = base_top_mm(&volume, config.cell_mm);
            let (support_tris, support_physics) =
                build_supports(&volume, &tips, config.cell_mm, base_z, &config.support);
            triangles.extend(support_tris);
            let mut report = analyze_with_supports(&volume, config.cell_mm, support_tips);
            report.support_physics = Some(support_physics.clone());
            Model {
                volume,
                triangles,
                report,
                support_tips,
                support_physics,
            }
        }
    }
}

/// Write a binary STL for an already-built model.
pub fn write_stl_model(model: &Model, path: &Path) -> std::io::Result<()> {
    let file = File::create(path)?;
    let mut writer = BufWriter::new(file);
    stl_io::write_stl(&mut writer, model.triangles.iter())?;
    writer.flush()?;
    Ok(())
}

/// Generate the model and write a binary STL to `path`.
pub fn generate_stl(config: &Config, path: &Path) -> std::io::Result<PrintabilityReport> {
    let model = build_model(config);
    write_stl_model(&model, path)?;
    Ok(model.report)
}

/// Format a human-readable printability report.
pub fn format_report(config: &Config, report: &PrintabilityReport) -> String {
    let mut out = String::new();
    let (sx, sy, sz) = config.size_mm();
    out.push_str(&format!(
        "life-stl  {}×{}×{} cells  ({:.1}×{:.1}×{:.1} mm)  seed={}  mode={:?}  cell={}mm\n",
        config.width,
        config.height,
        config.total_z(),
        sx,
        sy,
        sz,
        config.seed,
        config.mode,
        config.cell_mm
    ));
    if config.mode == SupportMode::Breakaway {
        out.push_str(&format!(
            "breakaway supports: style={:?}  shaft={}mm  tip={}mm  cluster={}mm  tips={}\n",
            config.support.style,
            config.support.radius_mm,
            config.support.tip_radius_mm,
            config.support.cluster_mm,
            report.breakaway_support_tips
        ));
        if let Some(phys) = &report.support_physics {
            let sf = if phys.worst_member_sf.is_finite() {
                format!("{:.2}", phys.worst_member_sf)
            } else {
                "n/a".into()
            };
            out.push_str(&format!(
                "support physics: auto={}  trunks={}  splits={}  load={:.3}N  \
                 worst_SF={}  max_trunk_r={:.2}mm  tip_snap≈{:.3}N  {}\n",
                config.support.physics.auto_size,
                phys.trunk_count,
                phys.clusters_split,
                phys.total_support_load_n,
                sf,
                phys.max_trunk_radius_mm,
                phys.tip_snap_force_n,
                if phys.ok {
                    "structurally OK"
                } else {
                    "OVERLOADED"
                }
            ));
        }
    }
    out.push_str(&format!(
        "generations (above {}-cell base): {}\n",
        config.base_layers, config.depth
    ));
    out.push_str(&format!(
        "voxels: life={}  base={}  total_solid={}\n",
        report.life_voxels, report.base_voxels, report.solid_voxels
    ));
    out.push_str(&format!(
        "Life print overhang (empty cell directly below): {} voxels, {:.1} mm² ({:.1}% of solid)\n",
        report.strict_floating_voxels, report.strict_floating_area_mm2, report.strict_floating_pct
    ));
    out.push_str(&format!(
        "Life orphans after support removal: {} ({:.1}% of life)\n",
        report.orphan_life_voxels, report.orphan_life_pct
    ));
    if report.life_self_supporting() {
        out.push_str(
            "Life self-supporting: yes — snap off breakaway supports → one standing piece\n",
        );
    } else if report.life_voxels == 0 {
        out.push_str("Life self-supporting: n/a (no live cells)\n");
    } else {
        out.push_str(
            "Life self-supporting: NO — support removal would leave disconnected Life pieces\n",
        );
    }
    out
}

/// Explain why a model fails the single-piece-after-removal check.
pub fn format_unprintable_reason(config: &Config, report: &PrintabilityReport) -> String {
    if report.life_voxels == 0 {
        return format!(
            "unprintable as a Life sculpture: seed {} produced no live cells across {} generations",
            config.seed, config.depth
        );
    }
    format!(
        "cannot produce a single standing piece after support removal: seed {} leaves {} Life voxel(s) \
         ({:.1}% of Life) face-disconnected from the bed through Life|Base only. Breakaway supports \
         can hold them while printing, but removing supports would leave multiple pieces.",
        config.seed, report.orphan_life_voxels, report.orphan_life_pct
    )
}
