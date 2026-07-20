//! Browser bindings (wasm-bindgen) for the life-lab app.
//!
//! The JS shim stays thin: it sends a generation-0 grid (row-major bytes,
//! nonzero = alive) and receives voxel/brace geometry as typed arrays for a
//! three.js `InstancedMesh`, plus gate verdicts for UI feedback. Exports
//! return complete file bytes (binary STL, Bambu Studio project .3mf) for
//! Blob downloads — no server involved.

use wasm_bindgen::prelude::*;

use crate::bambu;
use crate::config::{Config, Pattern, SupportMode};
use crate::gusset;
use crate::life::Grid;
use crate::volume::CellKind;
use crate::{build_model_from_windows, stl_bytes, windows_from_seed, Model};

fn grid_from_cells(cells: &[u8], width: usize, height: usize) -> Result<Grid, JsError> {
    if width == 0 || height == 0 {
        return Err(JsError::new("width and height must be > 0"));
    }
    if cells.len() != width * height {
        return Err(JsError::new(&format!(
            "cells length {} != width*height {}",
            cells.len(),
            width * height
        )));
    }
    let mut grid = Grid::new(width, height);
    for y in 0..height {
        for x in 0..width {
            if cells[y * width + x] != 0 {
                grid.set(x, y, true);
            }
        }
    }
    Ok(grid)
}

fn config_for(width: usize, height: usize, depth: usize, cell_mm: f32) -> Config {
    Config {
        width,
        height,
        depth,
        cell_mm,
        // Pattern is irrelevant for user-drawn seeds; Soup keeps the
        // complexity gate non-exempt.
        pattern: Pattern::Soup,
        mode: SupportMode::Gusset,
        ..Config::default()
    }
}

fn model_from_cells(
    cells: &[u8],
    width: u32,
    height: u32,
    depth: u32,
    cell_mm: f32,
) -> Result<(Model, Config), JsError> {
    let (w, h, d) = (width as usize, height as usize, depth as usize);
    if d == 0 {
        return Err(JsError::new("depth must be > 0"));
    }
    if !(crate::MIN_CELL_MM..=50.0).contains(&cell_mm) {
        return Err(JsError::new(&format!(
            "cell size must be between {} and 50 mm",
            crate::MIN_CELL_MM
        )));
    }
    let seed = grid_from_cells(cells, w, h)?;
    let config = config_for(w, h, d, cell_mm);
    let windows = windows_from_seed(&seed, d);
    Ok((build_model_from_windows(&windows, &config), config))
}

/// Simulation result for the viewer: geometry as flat typed arrays + stats.
#[wasm_bindgen]
pub struct SimResult {
    voxels: Vec<u32>,
    braces: Vec<f32>,
    base: Vec<u32>,
    life_voxels: u32,
    brace_count: u32,
    quiescent_generation: u32,
    period: u32,
    required_active: u32,
    interesting: bool,
    one_piece: bool,
}

#[wasm_bindgen]
impl SimResult {
    /// Life voxels as (x, y, z) triples in volume cells (z includes the base
    /// layer, so generation g sits at z = g + 1).
    #[wasm_bindgen(getter)]
    pub fn voxels(&self) -> Vec<u32> {
        self.voxels.clone()
    }

    /// Braces as (x1,y1,z1, x2,y2,z2) cell-space segment endpoints
    /// (child center → parent center).
    #[wasm_bindgen(getter)]
    pub fn braces(&self) -> Vec<f32> {
        self.braces.clone()
    }

    /// Base plate as (x0, y0, x1, y1, layers), inclusive cell bounds.
    #[wasm_bindgen(getter)]
    pub fn base(&self) -> Vec<u32> {
        self.base.clone()
    }

    #[wasm_bindgen(getter)]
    pub fn life_voxels(&self) -> u32 {
        self.life_voxels
    }

    #[wasm_bindgen(getter)]
    pub fn brace_count(&self) -> u32 {
        self.brace_count
    }

    /// First generation of the boring attractor (== depth if never settles).
    #[wasm_bindgen(getter)]
    pub fn quiescent_generation(&self) -> u32 {
        self.quiescent_generation
    }

    /// Attractor period once settled (0 = never settles within the stack).
    #[wasm_bindgen(getter)]
    pub fn period(&self) -> u32 {
        self.period
    }

    #[wasm_bindgen(getter)]
    pub fn required_active(&self) -> u32 {
        self.required_active
    }

    /// True when the pattern stays active for the whole printed height.
    #[wasm_bindgen(getter)]
    pub fn interesting(&self) -> bool {
        self.interesting
    }

    /// True when the print is one causally connected piece.
    #[wasm_bindgen(getter)]
    pub fn one_piece(&self) -> bool {
        self.one_piece
    }
}

/// Simulate a user-drawn generation 0 and return viewer geometry + verdicts.
#[wasm_bindgen]
pub fn simulate(cells: &[u8], width: u32, height: u32, depth: u32) -> Result<SimResult, JsError> {
    let (model, _config) = model_from_cells(cells, width, height, depth, 4.0)?;
    let volume = &model.volume;

    let mut voxels = Vec::new();
    let mut base_min = (u32::MAX, u32::MAX);
    let mut base_max = (0u32, 0u32);
    let mut base_layers = 0u32;
    for z in 0..volume.depth {
        for y in 0..volume.height {
            for x in 0..volume.width {
                match volume.get(x, y, z) {
                    CellKind::Life => {
                        voxels.extend_from_slice(&[x as u32, y as u32, z as u32]);
                    }
                    CellKind::Base => {
                        base_min.0 = base_min.0.min(x as u32);
                        base_min.1 = base_min.1.min(y as u32);
                        base_max.0 = base_max.0.max(x as u32);
                        base_max.1 = base_max.1.max(y as u32);
                        base_layers = base_layers.max(z as u32 + 1);
                    }
                    CellKind::Empty => {}
                }
            }
        }
    }
    let base = if base_layers > 0 {
        vec![base_min.0, base_min.1, base_max.0, base_max.1, base_layers]
    } else {
        Vec::new()
    };

    let mut braces = Vec::new();
    for b in gusset::collect_braces(volume) {
        let (cx, cy, cz) = b.child;
        let (px, py, pz) = b.parent;
        braces.extend_from_slice(&[
            cx as f32 + 0.5,
            cy as f32 + 0.5,
            cz as f32 + 0.5,
            px as f32 + 0.5,
            py as f32 + 0.5,
            pz as f32 + 0.5,
        ]);
    }

    let cx = &model.complexity;
    Ok(SimResult {
        life_voxels: (voxels.len() / 3) as u32,
        brace_count: (braces.len() / 6) as u32,
        voxels,
        braces,
        base,
        quiescent_generation: cx.quiescent_generation as u32,
        period: cx.period as u32,
        required_active: cx.required_active_generations as u32,
        interesting: cx.ok,
        one_piece: model.report.life_self_supporting(),
    })
}

/// Binary STL bytes for a user-drawn generation 0 (gusset mode).
#[wasm_bindgen]
pub fn export_stl(
    cells: &[u8],
    width: u32,
    height: u32,
    depth: u32,
    cell_mm: f32,
) -> Result<Vec<u8>, JsError> {
    let (model, _) = model_from_cells(cells, width, height, depth, cell_mm)?;
    Ok(stl_bytes(&model))
}

/// Bambu Studio project .3mf bytes (embedded A1 Mini + Generic PLA presets
/// with the gusset-print overrides).
#[wasm_bindgen]
pub fn export_3mf(
    cells: &[u8],
    width: u32,
    height: u32,
    depth: u32,
    cell_mm: f32,
    name: &str,
) -> Result<Vec<u8>, JsError> {
    let (model, _) = model_from_cells(cells, width, height, depth, cell_mm)?;
    let presets = bambu::BambuPresets::embedded_a1mini_pla();
    let opts = bambu::ExportOptions {
        overrides: bambu::gusset_print_overrides(),
        object_name: if name.is_empty() {
            "life-lab".into()
        } else {
            name.into()
        },
        ..bambu::ExportOptions::default()
    };
    bambu::project_3mf_bytes(&model.triangles, &presets, &opts).map_err(|e| JsError::new(&e))
}

/// Generation-0 cells (row-major, 1 = alive) for a named pattern — the same
/// catalog as the CLI (`soup`, `glider`, `acorn`, `rpento`, `pi`, …).
#[wasm_bindgen]
pub fn pattern_cells(
    name: &str,
    width: u32,
    height: u32,
    seed: u32,
    density: f32,
) -> Result<Vec<u8>, JsError> {
    let pattern = Pattern::parse_name(name)
        .ok_or_else(|| JsError::new(&format!("unknown pattern {name:?}")))?;
    let (w, h) = (width as usize, height as usize);
    if w == 0 || h == 0 {
        return Err(JsError::new("width and height must be > 0"));
    }
    let config = Config {
        width: w,
        height: h,
        pattern,
        seed: seed as u64,
        density: density.clamp(0.0, 1.0) as f64,
        ..Config::default()
    };
    let grid = crate::seed::initial_grid(&config);
    let mut cells = vec![0u8; w * h];
    for y in 0..h {
        for x in 0..w {
            if grid.is_alive(x, y) {
                cells[y * w + x] = 1;
            }
        }
    }
    Ok(cells)
}
