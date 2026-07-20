use clap::ValueEnum;

/// How aggressively to make the stack FDM-printable.
#[derive(Debug, Clone, Copy, PartialEq, Eq, ValueEnum)]
pub enum SupportMode {
    /// Exact Life voxels only (plus base plate). Births often overhang on
    /// edge/corner contacts only — printable with care, but support-prone.
    Raw,
    /// Add vertical scaffold columns so every solid has face-on-face support
    /// from the cell directly below. Default; drives overhang area to zero.
    Scaffold,
}

impl std::fmt::Display for SupportMode {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self {
            SupportMode::Raw => write!(f, "raw"),
            SupportMode::Scaffold => write!(f, "scaffold"),
        }
    }
}

/// Named starting patterns (or random).
#[derive(Debug, Clone, Copy, PartialEq, Eq, ValueEnum)]
pub enum Pattern {
    /// Bernoulli random field at `--density`, keyed by `--seed`.
    Random,
    /// Classic glider (needs at least 5×5).
    Glider,
    /// R-pentomino methuselah.
    Rpento,
    /// Blinker oscillator.
    Blinker,
    /// Lightweight spaceship.
    Lwss,
}

/// Generation parameters.
#[derive(Debug, Clone)]
pub struct Config {
    pub width: usize,
    pub height: usize,
    /// Number of Life generations stacked on Z (not counting the base plate).
    pub depth: usize,
    pub seed: u64,
    pub density: f64,
    pub pattern: Pattern,
    pub cell_mm: f32,
    pub base_layers: usize,
    pub mode: SupportMode,
}

impl Default for Config {
    fn default() -> Self {
        Self {
            width: 24,
            height: 24,
            depth: 48,
            seed: 1,
            density: 0.35,
            pattern: Pattern::Random,
            cell_mm: 2.0,
            base_layers: 1,
            mode: SupportMode::Scaffold,
        }
    }
}

impl Config {
    /// Total voxel height including the base plate.
    pub fn total_z(&self) -> usize {
        self.base_layers + self.depth
    }

    /// Physical size in millimeters: (x, y, z).
    pub fn size_mm(&self) -> (f32, f32, f32) {
        (
            self.width as f32 * self.cell_mm,
            self.height as f32 * self.cell_mm,
            self.total_z() as f32 * self.cell_mm,
        )
    }

    /// Convert a physical length in mm to a cell count for the given cell size.
    /// Rounds to the nearest whole cell; errors if the result would be zero.
    pub fn cells_from_mm(mm: f32, cell_mm: f32) -> Result<usize, String> {
        if !(mm.is_finite() && mm > 0.0) {
            return Err(format!("physical size must be > 0 mm, got {mm}"));
        }
        if !(cell_mm.is_finite() && cell_mm > 0.0) {
            return Err(format!("cell size must be > 0 mm, got {cell_mm}"));
        }
        let n = (mm / cell_mm).round();
        if n < 1.0 {
            return Err(format!(
                "size {mm} mm with cell {cell_mm} mm rounds to 0 cells; use a larger size or smaller --cell"
            ));
        }
        // Guard absurd grids (e.g. --cell 0.001).
        if n > 10_000.0 {
            return Err(format!(
                "size {mm} mm with cell {cell_mm} mm is {n} cells; refusing > 10000"
            ));
        }
        Ok(n as usize)
    }
}
