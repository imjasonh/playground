//! Conway's Game of Life → printable STL (Z = time).
//!
//! Live cells at generation `g` become voxels at height `z = base_layers + g`.
//! Life births are always Moore-adjacent to the previous generation, but often
//! rest only on an edge/corner. Default [`SupportMode::Scaffold`] drops
//! vertical columns so every solid has face-on-face support from below.

pub mod config;
pub mod life;
pub mod mesh;
pub mod metrics;
pub mod scaffold;
pub mod seed;
pub mod volume;

pub use config::{Config, SupportMode};
pub use metrics::PrintabilityReport;
pub use volume::{CellKind, Volume};

use std::fs::File;
use std::io::{BufWriter, Write};
use std::path::Path;

use crate::mesh::triangles_from_volume;
use crate::metrics::analyze;
use crate::scaffold::apply_scaffolding;
use crate::seed::initial_grid;

/// Build the voxel volume for `config` (simulate Life, then optionally scaffold).
pub fn build_volume(config: &Config) -> Volume {
    let mut grid = initial_grid(config);
    let mut volume = Volume::new(config.width, config.height, config.total_z());

    // Solid base plate for bed adhesion.
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

    match config.mode {
        SupportMode::Raw => {}
        SupportMode::Scaffold => apply_scaffolding(&mut volume, config.base_layers),
    }

    volume
}

/// Generate the model and write a binary STL to `path`.
pub fn generate_stl(config: &Config, path: &Path) -> std::io::Result<PrintabilityReport> {
    let volume = build_volume(config);
    let report = analyze(&volume, config.cell_mm);
    let triangles = triangles_from_volume(&volume, config.cell_mm);
    let file = File::create(path)?;
    let mut writer = BufWriter::new(file);
    stl_io::write_stl(&mut writer, triangles.iter())?;
    writer.flush()?;
    Ok(report)
}

/// Format a human-readable printability report.
pub fn format_report(config: &Config, report: &PrintabilityReport) -> String {
    let mut out = String::new();
    out.push_str(&format!(
        "life-stl  {}×{}×{}  seed={}  mode={:?}  cell={}mm\n",
        config.width, config.height, config.depth, config.seed, config.mode, config.cell_mm
    ));
    out.push_str(&format!(
        "voxels: life={}  scaffold={}  base={}  total_solid={}\n",
        report.life_voxels, report.scaffold_voxels, report.base_voxels, report.solid_voxels
    ));
    out.push_str(&format!(
        "unsupported overhang (empty cell directly below): {} voxels, {:.1} mm² ({:.1}% of solid)\n",
        report.strict_floating_voxels,
        report.strict_floating_area_mm2,
        report.strict_floating_pct
    ));
    out.push_str(&format!(
        "Moore-unsupported (no 3×3 support below): {} voxels, {:.1} mm² — always 0 for pure Life stacks\n",
        report.moore_unsupported_voxels, report.moore_unsupported_area_mm2
    ));
    out.push_str(&format!(
        "life cells with overhang: {} ({:.1}% of life)\n",
        report.unsupported_life_voxels, report.unsupported_life_pct
    ));
    out
}
