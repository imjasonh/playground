//! Conway's Game of Life → printable STL (Z = time).
//!
//! Live cells at generation `g` become voxels at height `z = base_layers + g`.
//! Life births are always Moore-adjacent to the previous generation, but often
//! rest only on an edge/corner. Default [`SupportMode::Scaffold`] drops
//! vertical columns so every solid has face-on-face support from below.
//!
//! Scaffold is **fused filament**, not breakaway. A model is only considered
//! Life-self-supporting when every Life voxel is face-connected to the bed
//! through Life|Base alone (see [`metrics::PrintabilityReport::life_self_supporting`]).

pub mod config;
pub mod life;
pub mod mesh;
pub mod metrics;
pub mod scaffold;
pub mod search;
pub mod seed;
pub mod volume;

pub use config::{Config, SupportMode, DEFAULT_CELL_MM, MIN_CELL_MM};
pub use metrics::PrintabilityReport;
pub use volume::{CellKind, Volume};

use std::fs::File;
use std::io::{BufWriter, Write};
use std::path::Path;

use crate::mesh::triangles_from_volume;
use crate::metrics::analyze;
use crate::scaffold::apply_scaffolding;
use crate::seed::initial_grid;

/// Simulate Life onto a volume with a base plate (no scaffold).
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

/// Build the voxel volume for `config` (simulate Life, then optionally scaffold).
pub fn build_volume(config: &Config) -> Volume {
    let mut volume = build_life_volume(config);
    match config.mode {
        SupportMode::Raw => {}
        SupportMode::Scaffold => apply_scaffolding(&mut volume, config.base_layers),
    }
    volume
}

/// Write a binary STL for an already-built volume.
pub fn write_stl_volume(
    volume: &Volume,
    cell_mm: f32,
    path: &Path,
) -> std::io::Result<PrintabilityReport> {
    let report = analyze(volume, cell_mm);
    let triangles = triangles_from_volume(volume, cell_mm);
    let file = File::create(path)?;
    let mut writer = BufWriter::new(file);
    stl_io::write_stl(&mut writer, triangles.iter())?;
    writer.flush()?;
    Ok(report)
}

/// Generate the model and write a binary STL to `path`.
pub fn generate_stl(config: &Config, path: &Path) -> std::io::Result<PrintabilityReport> {
    let volume = build_volume(config);
    write_stl_volume(&volume, config.cell_mm, path)
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
    out.push_str(&format!(
        "generations (above {}-cell base): {}\n",
        config.base_layers, config.depth
    ));
    out.push_str(&format!(
        "voxels: life={}  scaffold={}  base={}  total_solid={}\n",
        report.life_voxels, report.scaffold_voxels, report.base_voxels, report.solid_voxels
    ));
    out.push_str(&format!(
        "print overhang (empty cell directly below): {} voxels, {:.1} mm² ({:.1}% of solid)\n",
        report.strict_floating_voxels, report.strict_floating_area_mm2, report.strict_floating_pct
    ));
    out.push_str(&format!(
        "Life orphans if scaffold removed (face-disconnected from bed): {} ({:.1}% of life)\n",
        report.orphan_life_voxels, report.orphan_life_pct
    ));
    if report.life_self_supporting() {
        out.push_str("Life self-supporting: yes (fused scaffold is not load-bearing for Life)\n");
    } else if report.life_voxels == 0 {
        out.push_str("Life self-supporting: n/a (no live cells)\n");
    } else {
        out.push_str(
            "Life self-supporting: NO — removing scaffold would leave disconnected Life pieces\n",
        );
    }
    out.push_str(&format!(
        "Moore-unsupported (no 3×3 support below): {} voxels, {:.1} mm²\n",
        report.moore_unsupported_voxels, report.moore_unsupported_area_mm2
    ));
    out
}

/// Explain why a model fails the removable-scaffold / self-support check.
pub fn format_unprintable_reason(config: &Config, report: &PrintabilityReport) -> String {
    if report.life_voxels == 0 {
        return format!(
            "unprintable as a Life sculpture: seed {} produced no live cells across {} generations",
            config.seed, config.depth
        );
    }
    format!(
        "unprintable without permanent scaffold: seed {} leaves {} Life voxel(s) \
         ({:.1}% of Life, ≈ {:.1} mm² footprint) face-disconnected from the bed \
         through Life|Base only. Scaffold columns can hold them while printing, \
         but they are fused filament — not breakaway — so removing scaffold would \
         leave floating/disconnected pieces.",
        config.seed,
        report.orphan_life_voxels,
        report.orphan_life_pct,
        report.orphan_life_voxels as f64 * f64::from(config.cell_mm) * f64::from(config.cell_mm)
    )
}
