//! Conway's Game of Life → printable STL (Z = time).
//!
//! Live cells at generation `g` become voxels at height `z = base_layers + g`.
//!
//! Three support strategies ([`SupportMode`]):
//!
//! - **Gusset** (default): self-supporting by construction. B3/S23 guarantees
//!   every birth has three live Moore parents one layer below (the FDM 45°
//!   rule), so small diagonal braces from each birth to its parents make the
//!   whole stack one printable piece with nothing to remove. See [`gusset`].
//! - **Breakaway**: slim removable pillar/tree supports under overhanging
//!   cells; gated on post-print cleanup feasibility. See [`support`] and
//!   [`removal`].
//! - **Raw**: Life voxels only; printable only for stacks with no overhangs
//!   (e.g. still-life gardens).
//!
//! Independent of supports, the **complexity gate** ([`complexity`]) rejects
//! evolutions that go quiescent before the top layer — a pattern that settles
//! partway up extrudes a boring static tower above the interesting part.

pub mod complexity;
pub mod config;
pub mod gusset;
pub mod life;
pub mod mesh;
pub mod metrics;
pub mod physics;
pub mod removal;
pub mod search;
pub mod seed;
pub mod support;
pub mod volume;

pub use complexity::ComplexityReport;
pub use config::{
    ComplexityParams, Config, PhysicsParams, RemovalParams, SupportMode, SupportParams,
    SupportStyle, DEFAULT_CELL_MM, MIN_CELL_MM,
};
pub use metrics::PrintabilityReport;
pub use physics::SupportPhysicsReport;
pub use removal::SupportRemovabilityReport;
pub use volume::{CellKind, Volume};

use std::fs::File;
use std::io::{BufWriter, Write};
use std::path::Path;

use stl_io::Triangle;

use crate::complexity::analyze_complexity;
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
    /// Causality braces emitted in gusset mode (0 otherwise).
    pub gusset_braces: usize,
    pub support_physics: SupportPhysicsReport,
    pub support_removability: SupportRemovabilityReport,
    pub complexity: ComplexityReport,
}

/// Simulate Life onto a volume with a base plate (no supports).
///
/// By default the base plate shrink-wraps to the bounding box of the model's
/// XY projection plus [`Config::base_margin`] cells: connected (a rectangle),
/// under every column of the model, and therefore under its center of mass —
/// stable on a table without paying for a full-board slab. `Config::full_base`
/// restores the full-board plate (always used in breakaway mode, whose
/// supports may land on the bed anywhere).
pub fn build_life_volume(config: &Config) -> Volume {
    let mut grids: Vec<crate::life::Grid> = Vec::with_capacity(config.depth);
    let mut grid = initial_grid(config);
    for z in 0..config.depth {
        grids.push(grid.clone());
        if z + 1 < config.depth {
            grid = grid.step();
        }
    }

    let (bx0, by0, bx1, by1) = base_footprint(config, &grids);
    let mut volume = Volume::new(config.width, config.height, config.total_z());

    for z in 0..config.base_layers {
        for y in by0..=by1 {
            for x in bx0..=bx1 {
                volume.set(x, y, z, CellKind::Base);
            }
        }
    }

    let life_z0 = config.base_layers;
    for (z, g) in grids.iter().enumerate() {
        for y in 0..config.height {
            for x in 0..config.width {
                if g.is_alive(x, y) {
                    volume.set(x, y, life_z0 + z, CellKind::Life);
                }
            }
        }
    }

    volume
}

/// Inclusive base-plate cell bounds: full board, or the model's XY-projection
/// bounding box expanded by `base_margin` (full board when there is no life).
fn base_footprint(config: &Config, grids: &[crate::life::Grid]) -> (usize, usize, usize, usize) {
    let full = (0, 0, config.width - 1, config.height - 1);
    if config.full_base {
        return full;
    }
    let mut min_x = usize::MAX;
    let mut min_y = usize::MAX;
    let mut max_x = 0usize;
    let mut max_y = 0usize;
    let mut any = false;
    for g in grids {
        for y in 0..config.height {
            for x in 0..config.width {
                if g.is_alive(x, y) {
                    any = true;
                    min_x = min_x.min(x);
                    min_y = min_y.min(y);
                    max_x = max_x.max(x);
                    max_y = max_y.max(y);
                }
            }
        }
    }
    if !any {
        return full;
    }
    let m = config.base_margin;
    (
        min_x.saturating_sub(m),
        min_y.saturating_sub(m),
        (max_x + m).min(config.width - 1),
        (max_y + m).min(config.height - 1),
    )
}

/// Build the Life|Base voxel volume (no support geometry).
pub fn build_volume(config: &Config) -> Volume {
    build_life_volume(config)
}

/// Build the full printable model (Life mesh + optional breakaway supports).
pub fn build_model(config: &Config) -> Model {
    let volume = build_life_volume(config);
    let complexity = analyze_complexity(config);

    match config.mode {
        SupportMode::Raw => {
            let mut report = analyze(&volume, config.cell_mm);
            report.complexity = Some(complexity.clone());
            Model {
                triangles: triangles_from_volume(&volume, config.cell_mm),
                volume,
                report,
                support_tips: 0,
                gusset_braces: 0,
                support_physics: SupportPhysicsReport::default(),
                support_removability: SupportRemovabilityReport::default(),
                complexity,
            }
        }
        SupportMode::Gusset => {
            let braces = gusset::collect_braces(&volume);
            let mut triangles = triangles_from_volume(&volume, config.cell_mm);
            triangles.extend(gusset::brace_triangles(
                &braces,
                config.cell_mm,
                config.support.gusset_width_mm,
            ));
            let mut report = analyze(&volume, config.cell_mm);
            // Braces physically connect births to parents: orphan connectivity
            // follows Life causality, not just face adjacency.
            let causal_orphans = gusset::count_orphan_life_causal(&volume);
            report.orphan_life_voxels = causal_orphans;
            report.orphan_life_pct =
                100.0 * causal_orphans as f64 / report.life_voxels.max(1) as f64;
            report.gusset_braces = braces.len();
            report.complexity = Some(complexity.clone());
            Model {
                volume,
                triangles,
                report,
                support_tips: 0,
                gusset_braces: braces.len(),
                support_physics: SupportPhysicsReport::default(),
                support_removability: SupportRemovabilityReport::default(),
                complexity,
            }
        }
        SupportMode::Breakaway => {
            let tips = collect_tips(&volume, config.cell_mm, config.support.tip_offset_mm);
            let support_tips = tips.len();
            let mut triangles = triangles_from_volume(&volume, config.cell_mm);
            let base_z = base_top_mm(&volume, config.cell_mm);
            let (support_tris, support_physics, support_removability) =
                build_supports(&volume, &tips, config.cell_mm, base_z, &config.support);
            triangles.extend(support_tris);
            let mut report = analyze_with_supports(&volume, config.cell_mm, support_tips);
            report.support_physics = Some(support_physics.clone());
            report.support_removability = Some(support_removability.clone());
            report.complexity = Some(complexity.clone());
            Model {
                volume,
                triangles,
                report,
                support_tips,
                gusset_braces: 0,
                support_physics,
                support_removability,
                complexity,
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
    if config.mode == SupportMode::Gusset {
        out.push_str(&format!(
            "self-supporting gussets: braces={}  width={}mm — every birth leans on its 3 \
             parents (45° rule); no supports to remove\n",
            report.gusset_braces, config.support.gusset_width_mm
        ));
    }
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
        if let Some(rem) = &report.support_removability {
            out.push_str(&format!(
                "support removal: score={:.0}/100  rest_on_model={}  trapped_trunks={}  \
                 inaccessible_tips={}  {}\n",
                rem.score,
                rem.rest_on_model_count,
                rem.trapped_trunk_count,
                rem.inaccessible_tip_count,
                if rem.ok {
                    "cleanup OK"
                } else {
                    "HARD TO REMOVE"
                }
            ));
            for reason in &rem.reasons {
                out.push_str(&format!("  - {reason}\n"));
            }
        }
    }
    if let Some(cx) = &report.complexity {
        let period = if cx.period == 0 {
            "none".into()
        } else {
            format!("{}", cx.period)
        };
        out.push_str(&format!(
            "complexity: quiescent_gen={}  period={}  unique_states={}  need≥{}  {}\n",
            cx.quiescent_generation,
            period,
            cx.unique_states,
            cx.required_active_generations,
            if cx.ok {
                "interesting OK"
            } else {
                "TOO BORING"
            }
        ));
        for reason in &cx.reasons {
            out.push_str(&format!("  - {reason}\n"));
        }
    }
    out.push_str(&format!(
        "generations (above {}-cell base): {}\n",
        config.base_layers, config.depth
    ));
    let (bw, bh) = report.base_extent_cells;
    out.push_str(&format!(
        "base plate: {}×{} cells ({:.0}×{:.0} mm) — {}\n",
        bw,
        bh,
        bw as f32 * config.cell_mm,
        bh as f32 * config.cell_mm,
        if config.full_base {
            "full board"
        } else {
            "shrink-wrapped to model footprint"
        }
    ));
    out.push_str(&format!(
        "voxels: life={}  base={}  total_solid={}\n",
        report.life_voxels, report.base_voxels, report.solid_voxels
    ));
    out.push_str(&format!(
        "Life print overhang (empty cell directly below): {} voxels, {:.1} mm² ({:.1}% of solid)\n",
        report.strict_floating_voxels, report.strict_floating_area_mm2, report.strict_floating_pct
    ));
    if config.mode == SupportMode::Gusset {
        out.push_str(&format!(
            "Life orphans (causal connectivity): {} ({:.1}% of life)\n",
            report.orphan_life_voxels, report.orphan_life_pct
        ));
    } else {
        out.push_str(&format!(
            "Life orphans after support removal: {} ({:.1}% of life)\n",
            report.orphan_life_voxels, report.orphan_life_pct
        ));
    }
    if report.life_self_supporting() {
        out.push_str(match config.mode {
            SupportMode::Gusset => {
                "Life self-supporting: yes — causality braces make one standing piece\n"
            }
            _ => "Life self-supporting: yes — snap off breakaway supports → one standing piece\n",
        });
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

/// Explain why supports fail the practical-cleanup gate.
pub fn format_hard_removal_reason(config: &Config, report: &PrintabilityReport) -> String {
    let Some(rem) = &report.support_removability else {
        return format!(
            "seed {}: support removability was not analyzed",
            config.seed
        );
    };
    let mut msg = format!(
        "supports are not reasonably removable (score {:.0}/100, need ≥ {:.0}): seed {}",
        rem.score, config.support.removal.min_score, config.seed
    );
    for reason in &rem.reasons {
        msg.push_str("\n  - ");
        msg.push_str(reason);
    }
    msg
}

/// Explain why a Life run fails the interestingness gate.
pub fn format_boring_reason(config: &Config, report: &PrintabilityReport) -> String {
    let Some(cx) = &report.complexity else {
        return format!("seed {}: complexity was not analyzed", config.seed);
    };
    let mut msg = format!(
        "evolution is too boring (quiescent at generation {}, need ≥ {}): seed {}",
        cx.quiescent_generation, cx.required_active_generations, config.seed
    );
    for reason in &cx.reasons {
        msg.push_str("\n  - ");
        msg.push_str(reason);
    }
    msg
}
