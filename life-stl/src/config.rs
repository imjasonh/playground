/// Default voxel edge length (mm). Sized for reliable FDM with a 0.4 mm
/// nozzle (~10× nozzle width) — e.g. Bambu A1 / A1 Mini stock nozzles.
pub const DEFAULT_CELL_MM: f32 = 4.0;

/// Minimum allowed voxel edge length (mm). Below this, single-voxel walls are
/// thinner than ~5× a 0.4 mm nozzle and tend to under-extrude or snap.
pub const MIN_CELL_MM: f32 = 2.0;

/// How supports are generated for FDM printability.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
#[cfg_attr(feature = "cli", derive(clap::ValueEnum))]
pub enum SupportMode {
    /// Exact Life voxels only (plus base plate). No generated supports.
    Raw,
    /// Slim breakaway pillars/trees. Removable after printing; the
    /// remaining Life|Base mesh must be one piece (see orphan check).
    #[cfg_attr(feature = "cli", value(alias = "supports"))]
    Breakaway,
    /// Self-supporting by construction (default): every birth leans on its
    /// three B3 parents via small diagonal gussets. Nothing to remove; the
    /// whole stack is one piece through Life causality.
    #[cfg_attr(feature = "cli", value(alias = "brace"))]
    Gusset,
}

impl std::fmt::Display for SupportMode {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self {
            SupportMode::Raw => write!(f, "raw"),
            SupportMode::Breakaway => write!(f, "breakaway"),
            SupportMode::Gusset => write!(f, "gusset"),
        }
    }
}

/// Geometry style for [`SupportMode::Breakaway`].
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
#[cfg_attr(feature = "cli", derive(clap::ValueEnum))]
pub enum SupportStyle {
    /// One vertical tapered pillar per overhang tip.
    Pillar,
    /// Cluster nearby tips onto a shared trunk with diagonal branches (Cura-style).
    Tree,
}

impl std::fmt::Display for SupportStyle {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self {
            SupportStyle::Pillar => write!(f, "pillar"),
            SupportStyle::Tree => write!(f, "tree"),
        }
    }
}

/// Material / structural knobs for the simplified support physics model.
#[derive(Debug, Clone, Copy, PartialEq)]
pub struct PhysicsParams {
    /// Filament density (g/cm³). PLA ≈ 1.24.
    pub filament_density_g_cm3: f32,
    /// Working allowable stress (MPa / N/mm²). Conservative PLA ≈ 15–20.
    pub allow_stress_mpa: f32,
    /// Young's modulus (MPa) for buckling. PLA ≈ 3000.
    pub youngs_modulus_mpa: f32,
    /// Multiplier on dead weight for print dynamics (nozzle / cooling).
    pub safety_factor: f32,
    /// When true, split overloaded trunks and thicken shafts from the model.
    pub auto_size: bool,
    /// Max tips merged onto one trunk before forcing a split.
    pub max_tips_per_trunk: u32,
    /// Floor for auto-sized branch/trunk radius (mm).
    pub min_shaft_radius_mm: f32,
    /// Cap for auto-sized trunk radius (mm).
    pub max_trunk_radius_mm: f32,
}

impl Default for PhysicsParams {
    fn default() -> Self {
        Self {
            filament_density_g_cm3: 1.24,
            allow_stress_mpa: 18.0,
            youngs_modulus_mpa: 3000.0,
            safety_factor: 3.0,
            auto_size: true,
            max_tips_per_trunk: 6,
            min_shaft_radius_mm: 0.55,
            max_trunk_radius_mm: 2.4,
        }
    }
}

/// Post-print support cleanup gates (used by seed search / CLI exit codes).
#[derive(Debug, Clone, Copy, PartialEq)]
pub struct RemovalParams {
    /// Minimum removability score (0–100) to accept.
    pub min_score: f32,
    /// When true, unlimited rest-on-model landings are allowed.
    pub allow_rest_on_model: bool,
    /// Max rest-on-model landings before the gate hard-fails. Rest-on-model
    /// branches get a needle taper at **both** ends, so a few are practical
    /// to snap off; many still make miserable cleanup.
    pub max_rest_on_model: usize,
    /// Max fraction of tip contacts that may sit in enclosed pockets.
    pub max_inaccessible_tip_fraction: f32,
    /// Max tip contacts per XY cell footprint before density penalty / fail.
    pub max_tip_density: f32,
}

impl Default for RemovalParams {
    fn default() -> Self {
        Self {
            min_score: 70.0,
            allow_rest_on_model: false,
            max_rest_on_model: 2,
            max_inaccessible_tip_fraction: 0.08,
            // Tips are stacked in Z; a 16×16 soup with ~200 tips ≈ 0.8 / cell.
            max_tip_density: 1.25,
        }
    }
}

/// Evolution interestingness gates (used by seed search / CLI exit codes).
///
/// Rejects runs that become a still life or short-period oscillator before
/// enough generations have elapsed — otherwise most of the Z stack is a
/// boring extruded tower. `Pattern::Random` (still-life gardens) is exempt.
#[derive(Debug, Clone, Copy, PartialEq)]
pub struct ComplexityParams {
    /// Absolute floor: quiescence must not begin before this generation.
    pub min_active_generations: usize,
    /// Also require quiescence ≥ ceil(depth × fraction).
    pub min_active_fraction: f32,
    /// Periods ≤ this count as “boring quiescent” (1 = still life, 2 = blinker).
    pub max_boring_period: usize,
}

impl Default for ComplexityParams {
    fn default() -> Self {
        Self {
            min_active_generations: 8,
            // Print-worthy shapes stay active the whole way up: anything that
            // settles partway leaves a boring extruded tower above it.
            min_active_fraction: 1.0,
            max_boring_period: 2,
        }
    }
}

/// Tunable breakaway-support geometry (millimeters).
#[derive(Debug, Clone, Copy, PartialEq)]
pub struct SupportParams {
    pub style: SupportStyle,
    /// Nominal shaft / branch radius (mm). Auto-size may thicken above this.
    pub radius_mm: f32,
    /// Tip radius at model contact (mm). `0` = true needle point for breakaway.
    pub tip_radius_mm: f32,
    /// Length of the tip taper (mm).
    pub tip_height_mm: f32,
    /// Nominal trunk radius for tree style (mm). Auto-size may thicken.
    pub trunk_radius_mm: f32,
    /// Cluster tips whose XY distance is ≤ this into one trunk (mm).
    pub cluster_mm: f32,
    /// Horizontal offset of the tip from the cell center toward +X/+Y (mm),
    /// so the contact sits near a cell edge for cleaner breakaway.
    pub tip_offset_mm: f32,
    /// Cylinder tessellation segments (≥ 3).
    pub segments: u32,
    /// XY clearance from Life voxel footprints (mm). `0` → radius + 0.4 mm.
    /// Inspired by Cura/Bambu tree-support collision areas.
    pub clearance_mm: f32,
    /// Max branch lean from vertical (degrees). Limits how far a route may
    /// move in XY per cell-layer while descending around obstacles.
    pub max_branch_angle_deg: f32,
    /// Structural model inputs (density, strength, auto-sizing).
    pub physics: PhysicsParams,
    /// Post-print support removal feasibility gates.
    pub removal: RemovalParams,
    /// Gusset strut width (mm) for [`SupportMode::Gusset`].
    pub gusset_width_mm: f32,
}

impl Default for SupportParams {
    fn default() -> Self {
        Self {
            style: SupportStyle::Tree,
            // ~1.5× a 0.4 mm nozzle — printable tube, still snappable.
            radius_mm: 0.6,
            // Needle contact for easy snap-off (0 = true point).
            tip_radius_mm: 0.12,
            tip_height_mm: 2.0,
            trunk_radius_mm: 1.1,
            // Smaller clusters + physics splits keep trunks from overloading.
            cluster_mm: 14.0,
            tip_offset_mm: 0.0,
            segments: 8,
            // Prefer an explicit margin so thin shafts still clear Life faces.
            clearance_mm: 1.0,
            max_branch_angle_deg: 40.0,
            physics: PhysicsParams::default(),
            removal: RemovalParams::default(),
            // ~4.5 perimeters of a 0.4 mm nozzle; sturdy but unobtrusive.
            gusset_width_mm: 1.8,
        }
    }
}

/// Named starting patterns (or random).
///
/// In gusset mode any pattern prints as one piece; the notes below about Life
/// orphans apply to breakaway/raw modes, where connectivity is face-only.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
#[cfg_attr(feature = "cli", derive(clap::ValueEnum))]
pub enum Pattern {
    /// Seeded still-life garden (blocks, tubs, beehives, boats). Stable
    /// forever, so it is exempt from the complexity gate. Default.
    Random,
    /// Classic Bernoulli soup at `--density`. Chaotic; in breakaway mode it
    /// often leaves orphans that cannot form one piece after support removal.
    Soup,
    /// Classic glider (needs at least 5×5). Climbs the stack diagonally.
    Glider,
    /// R-pentomino methuselah (5 cells, centered; ~1103 generations unbounded).
    Rpento,
    /// Blinker oscillator (period 2 — always fails the complexity gate).
    Blinker,
    /// Lightweight spaceship.
    Lwss,
    /// Acorn methuselah (7 cells, centered; ~5206 generations unbounded).
    Acorn,
    /// Pi-heptomino methuselah (7 cells, centered; symmetric bloom).
    Pi,
    /// B-heptomino methuselah (7 cells, centered).
    Bheptomino,
    /// Thunderbird methuselah (6 cells, centered; symmetric).
    Thunderbird,
    /// Bunnies methuselah (9 cells, centered; ~17332 generations unbounded).
    Bunnies,
    /// Rabbits methuselah (9 cells, centered; ~17331 generations unbounded).
    Rabbits,
    /// Diehard (7 cells, centered; vanishes at ~130 generations unbounded).
    Diehard,
}

impl Pattern {
    /// Parse a pattern by its CLI name (clap-independent, for wasm callers).
    pub fn parse_name(name: &str) -> Option<Self> {
        Some(match name.to_ascii_lowercase().as_str() {
            "random" | "garden" => Pattern::Random,
            "soup" => Pattern::Soup,
            "glider" => Pattern::Glider,
            "rpento" | "r-pentomino" => Pattern::Rpento,
            "blinker" => Pattern::Blinker,
            "lwss" => Pattern::Lwss,
            "acorn" => Pattern::Acorn,
            "pi" => Pattern::Pi,
            "bheptomino" | "b-heptomino" => Pattern::Bheptomino,
            "thunderbird" => Pattern::Thunderbird,
            "bunnies" => Pattern::Bunnies,
            "rabbits" => Pattern::Rabbits,
            "diehard" => Pattern::Diehard,
            _ => return None,
        })
    }
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
    /// Base plate covers the whole board instead of shrink-wrapping to the
    /// model's XY projection. Breakaway mode requires this (supports may land
    /// on the bed anywhere).
    pub full_base: bool,
    /// Margin (cells) around the model's XY projection for a shrink-wrapped
    /// base plate. Ignored when `full_base` is set.
    pub base_margin: usize,
    pub mode: SupportMode,
    pub support: SupportParams,
    /// Evolution interestingness gates (soups / named patterns).
    pub complexity: ComplexityParams,
}

impl Default for Config {
    fn default() -> Self {
        Self {
            width: 24,
            height: 24,
            depth: 48,
            seed: 1,
            density: 0.25,
            pattern: Pattern::Random,
            cell_mm: DEFAULT_CELL_MM,
            base_layers: 1,
            full_base: false,
            base_margin: 2,
            mode: SupportMode::Gusset,
            support: SupportParams::default(),
            complexity: ComplexityParams::default(),
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
        if n > 10_000.0 {
            return Err(format!(
                "size {mm} mm with cell {cell_mm} mm is {n} cells; refusing > 10000"
            ));
        }
        Ok(n as usize)
    }
}
