#[cfg(test)]
mod tests;

use std::collections::{HashMap, HashSet};

use crate::errors::{Diagnostic, ErrorCode, Label, Level};
use crate::lexer::Span;
use crate::parser::ast::*;

/// A room's metatile grid is 16×15, giving 240 cells. The compiler
/// expands each cell into a 2×2 CHR-tile block, covering a full
/// 32×30 nametable (256×240 px, matching the NES visible area).
pub const ROOM_GRID_WIDTH: usize = 16;
pub const ROOM_GRID_HEIGHT: usize = 15;
pub const ROOM_CELL_COUNT: usize = ROOM_GRID_WIDTH * ROOM_GRID_HEIGHT;

/// Symbol information stored in the scope.
#[derive(Debug, Clone)]
pub struct Symbol {
    pub name: String,
    pub sym_type: NesType,
    pub is_const: bool,
    pub span: Span,
}

/// Memory assignment for a variable.
#[derive(Debug, Clone)]
pub struct VarAllocation {
    pub name: String,
    pub address: u16,
    pub size: u16,
}

/// Result of semantic analysis.
pub struct AnalysisResult {
    pub symbols: HashMap<String, Symbol>,
    pub var_allocations: Vec<VarAllocation>,
    pub diagnostics: Vec<Diagnostic>,
    pub call_graph: HashMap<String, Vec<String>>,
    pub max_depths: HashMap<String, u32>,
    /// For each state-local variable name, the state it belongs to.
    /// Consumed by the memory-map printer to group overlaid slots by
    /// their owning state. Empty for programs without state-locals.
    pub state_local_owners: HashMap<String, String>,
    /// True when the program declared at least one `save { var ... }`
    /// variable. Drives the iNES header byte-6 bit-1 (battery flag)
    /// so emulators and cartridge boards know to persist the
    /// `$6000-$7FFF` SRAM region across power cycles.
    pub has_battery_saves: bool,
}

/// Default call stack depth limit for the NES runtime.
const DEFAULT_STACK_DEPTH: u32 = 8;

/// Upper bound (exclusive) for user-variable zero-page allocation.
/// Addresses `$80-$FF` are reserved for IR codegen temp slots, so user
/// globals must fit into `$10-$7F`.
const ZP_USER_CAP: u8 = 0x80;

/// Exclusive upper bound of usable RAM. The NES has 2 KB of internal
/// RAM at `$0000-$07FF`; the allocator uses up through `$07FF`.
const RAM_END: u16 = 0x0800;

/// W0107 threshold: a `fast` variable with fewer than this many
/// observed accesses is flagged as wasting a zero-page slot. Writes
/// and reads both count; the initializer of a `VarDecl` counts as a
/// write. Three is a reasonable cutoff — anything below that barely
/// justifies holding a scarce slot that codegen could use for a
/// hotter variable.
const W0107_MIN_ACCESSES: u32 = 3;

/// Analyze a parsed program for semantic errors.
pub fn analyze(program: &Program) -> AnalysisResult {
    // Pre-collect declared and builtin-matchable sfx/music names so
    // the statement walker can check `play` / `start_music` targets.
    let mut sfx_names = HashSet::new();
    for decl in &program.sfx {
        sfx_names.insert(decl.name.clone());
    }
    let mut music_names = HashSet::new();
    for decl in &program.music {
        music_names.insert(decl.name.clone());
    }
    let mut palette_names = HashSet::new();
    for decl in &program.palettes {
        palette_names.insert(decl.name.clone());
    }
    let mut background_names = HashSet::new();
    for decl in &program.backgrounds {
        background_names.insert(decl.name.clone());
    }
    let mut room_names = HashSet::new();
    for decl in &program.rooms {
        room_names.insert(decl.name.clone());
    }
    // Programs that use palette or background declarations need 7
    // bytes of zero page for the vblank-safe update handshake
    // (`$11` flags + 2 × 3 pointer slots). Bump the user zero-page
    // start past that region so var allocation doesn't collide with
    // the runtime slots.
    //
    // Programs that nest user functions inside a `bank Foo { ... }`
    // block additionally need to reserve `$10` for `ZP_BANK_CURRENT`,
    // the slot that `__bank_select` writes the requested bank index
    // into at every cross-bank call. Without this bump, the bank's
    // first user variable lands on top of the same slot that
    // `__bank_select` clobbers, producing nonsense at runtime. The
    // bump only fires when the program actually has banked
    // functions; programs that declare empty bank slots (the
    // existing mmc1_banked / uxrom_banked / mmc3_per_state_split
    // examples) keep the legacy layout because their fixed-bank
    // user code never invokes `__bank_select`.
    let needs_ppu_update_slots = !program.palettes.is_empty() || !program.backgrounds.is_empty();
    // Rooms reserve two additional ZP bytes at `$18-$19` for the
    // `paint_room` → `collides_at` room-pointer handoff, on top of
    // whatever PPU-update slots are already reserved. Programs that
    // use palettes/backgrounds AND rooms pay both bumps; programs
    // with just rooms pay only the room bump (the PPU-update slot
    // region is a prefix of the same block so rooms imply PPU
    // updates via `paint_room`).
    let needs_room_slots = !program.rooms.is_empty();
    let needs_bank_current_slot = program.functions.iter().any(|f| f.bank.is_some());
    let next_zp_addr = if needs_room_slots {
        0x1A
    } else if needs_ppu_update_slots {
        0x18
    } else if needs_bank_current_slot {
        0x11
    } else {
        0x10
    };
    // Detect VRAM-buffer intrinsic usage by scanning the AST. When
    // present, the buffer reserves `$0400-$04FF` and we have to
    // start the user-RAM bump pointer past that region — otherwise
    // user globals and the buffer would alias. Programs that don't
    // use the buffer keep the legacy `$0300` start.
    let uses_vram_buf = program_uses_vram_buf(program);
    let initial_ram_addr: u16 = if uses_vram_buf { 0x0500 } else { 0x0300 };
    let mut analyzer = Analyzer {
        symbols: HashMap::new(),
        var_allocations: Vec::new(),
        diagnostics: Vec::new(),
        next_sram_addr: 0x6000,
        sfx_names,
        music_names,
        palette_names,
        background_names,
        room_names,
        next_ram_addr: initial_ram_addr,
        next_zp_addr,
        call_graph: HashMap::new(),
        max_depths: HashMap::new(),
        stack_depth_limit: DEFAULT_STACK_DEPTH,
        in_loop: false,
        used_vars: HashSet::new(),
        var_access_counts: HashMap::new(),
        function_signatures: HashMap::new(),
        function_return_types: HashMap::new(),
        current_return_type: None,
        in_function_body: false,
        current_scope_prefix: None,
        struct_layouts: HashMap::new(),
    };
    analyzer.analyze_program(program);

    let mut state_local_owners = HashMap::new();
    for state in &program.states {
        for var in &state.locals {
            state_local_owners.insert(var.name.clone(), state.name.clone());
        }
    }

    let has_battery_saves = !program.saves.is_empty();
    AnalysisResult {
        symbols: analyzer.symbols,
        var_allocations: analyzer.var_allocations,
        diagnostics: analyzer.diagnostics,
        call_graph: analyzer.call_graph,
        max_depths: analyzer.max_depths,
        state_local_owners,
        has_battery_saves,
    }
}

struct Analyzer {
    symbols: HashMap<String, Symbol>,
    var_allocations: Vec<VarAllocation>,
    diagnostics: Vec<Diagnostic>,
    /// Set of sfx names declared in the program (user-provided
    /// `sfx Name { ... }` blocks). Used to validate `play Name`
    /// targets. If a name isn't in here and isn't a known builtin,
    /// the analyzer emits E0505.
    sfx_names: HashSet<String>,
    /// Set of music names declared in the program.
    music_names: HashSet<String>,
    /// Set of palette names declared in the program. Used to
    /// validate `set_palette Name` targets.
    palette_names: HashSet<String>,
    /// Set of background names declared in the program. Used to
    /// validate `load_background Name` targets.
    background_names: HashSet<String>,
    /// Set of room names declared in the program. Used to validate
    /// `paint_room Name` targets.
    room_names: HashSet<String>,
    next_ram_addr: u16,
    next_zp_addr: u8,
    /// Bump-pointer for save-block (`save { var ... }`) variables.
    /// Initialised to `$6000` (the iNES SRAM window) and capped at
    /// `$8000`. Save vars never share the main-RAM allocator so
    /// they don't collide with normal globals or interfere with
    /// the analyzer's RAM-overflow check.
    next_sram_addr: u16,
    call_graph: HashMap<String, Vec<String>>,
    max_depths: HashMap<String, u32>,
    stack_depth_limit: u32,
    in_loop: bool,
    /// Names of variables that have been read somewhere in the program.
    /// Used for the W0103 unused-variable warning.
    used_vars: HashSet<String>,
    /// Count of observed references (reads + writes) for each
    /// variable. Used for the W0107 fast-variable-underuse warning
    /// to detect `fast var` declarations that hog a zero-page slot
    /// without justifying it.
    var_access_counts: HashMap<String, u32>,
    /// Function name to parameter types (in order). Used to validate
    /// call arity and argument types.
    function_signatures: HashMap<String, Vec<NesType>>,
    /// Function name to declared return type. `None` here means the
    /// function has no declared return type (i.e. "void"); functions
    /// with a declared return type appear with `Some(ty)`. Used by
    /// W0106 to detect implicit-drop of a return value.
    function_return_types: HashMap<String, Option<NesType>>,
    /// Return type of the function currently being analyzed, or None
    /// when the function has no declared return type. Only meaningful
    /// when `in_function_body` is true.
    current_return_type: Option<NesType>,
    /// True while analyzing a function body (as opposed to a state
    /// handler's `on_enter` / `on_exit` / `on_frame` block). Used to
    /// distinguish "void function" from "state handler" when checking
    /// `return value` statements.
    in_function_body: bool,
    /// Current local scope prefix used to qualify function-body
    /// `var` declarations. `None` at the top level and during
    /// state-level declaration registration; set to `Some("foo")`
    /// while analyzing the body of `fun foo`, and to
    /// `Some("Title::frame")` (etc.) while analyzing a state
    /// handler body. When it is `Some(prefix)`, `register_var`
    /// stores the declaration under a qualified key
    /// `"__local__{prefix}__{name}"`, and `resolve_*` helpers
    /// below fall back through the qualified key first and the
    /// bare key second so identifier reads inside a body resolve
    /// to the locally-scoped entry when one exists.
    ///
    /// This is how functions and handlers get their own local
    /// namespaces without requiring a full nested-scope stack.
    /// Top-level globals, consts, state-level vars, function
    /// names, and enum variants still live at the bare name in
    /// `self.symbols`.
    current_scope_prefix: Option<String>,
    /// Struct name to layout. Each field has an offset in bytes from
    /// the base address of the struct.
    struct_layouts: HashMap<String, StructLayout>,
}

/// Layout info for a struct type.
#[derive(Debug, Clone)]
pub struct StructLayout {
    pub size: u16,
    pub fields: Vec<(String, NesType, u16)>, // (name, type, offset)
}

impl Analyzer {
    fn analyze_program(&mut self, program: &Program) {
        // Register struct layouts first so later declarations can
        // reference them (for variable sizing, etc.).
        for s in &program.structs {
            self.register_struct(s);
        }

        // Register constants
        for c in &program.constants {
            self.register_const(c);
        }

        // Register enum variants as constants with values 0, 1, 2, ...
        for e in &program.enums {
            self.register_enum(e);
        }

        // Register and allocate globals
        for var in &program.globals {
            self.register_var(var);
        }

        // Register save-block variables. These get addresses from
        // the SRAM-only allocator at `$6000+` and never enter the
        // main-RAM bump pointer. The codegen treats them as
        // ordinary globals at absolute addresses; the only place
        // they're special is the iNES header (battery bit) and
        // the linker reads `analysis.has_battery_saves` for that.
        for var in &program.saves {
            self.register_save_var(var);
        }

        // Validate palette and background declarations. Palettes
        // must be ≤ 32 bytes (PPU palette RAM is $3F00-$3F1F) and
        // each byte must fit in 6 bits (NES master palette is
        // `$00-$3F`). Backgrounds must fit in a single 32×30
        // nametable: ≤ 960 tile bytes, ≤ 64 attribute bytes.
        // Duplicate names are caught via the shared symbol table.
        let mut seen_palettes = HashSet::new();
        for palette in &program.palettes {
            if !seen_palettes.insert(palette.name.clone()) {
                self.diagnostics.push(Diagnostic::error(
                    ErrorCode::E0501,
                    format!("duplicate palette '{}'", palette.name),
                    palette.span,
                ));
            }
            if palette.colors.len() > 32 {
                self.diagnostics.push(Diagnostic::error(
                    ErrorCode::E0201,
                    format!(
                        "palette '{}' has {} colors; maximum is 32",
                        palette.name,
                        palette.colors.len()
                    ),
                    palette.span,
                ));
            }
            for (i, c) in palette.colors.iter().enumerate() {
                if *c > 0x3F {
                    self.diagnostics.push(Diagnostic::error(
                        ErrorCode::E0201,
                        format!(
                            "palette '{}' color {i} is ${c:02X}; NES master palette indices are $00-$3F",
                            palette.name,
                        ),
                        palette.span,
                    ));
                }
            }
            // W0105: the NES mirrors $3F10/$3F14/$3F18/$3F1C onto
            // $3F00/$3F04/$3F08/$3F0C, so the "first byte" of every
            // sub-palette at indices 0, 4, 8, 12, 16, 20, 24, 28 is
            // really a single shared universal background colour.
            // Writing a 32-byte blob sequentially with inconsistent
            // values at those offsets silently overwrites $3F00 with
            // whatever the last sprite sub-palette's first byte is —
            // a classic "my screen is suddenly black" bug. The
            // grouped-form palette parser auto-fixes this via its
            // `universal:` field, so only the flat-form `colors:`
            // path can trip this warning in practice.
            let universals: Vec<u8> = [0, 4, 8, 12, 16, 20, 24, 28]
                .into_iter()
                .filter_map(|i| palette.colors.get(i).copied())
                .collect();
            if universals.len() >= 2 {
                let first = universals[0];
                if universals.iter().any(|&b| b != first) {
                    self.diagnostics.push(
                        Diagnostic::warning(
                            ErrorCode::W0105,
                            format!(
                                "palette '{}' has inconsistent universal-background bytes across \
                                 its sub-palettes",
                                palette.name,
                            ),
                            palette.span,
                        )
                        .with_note(
                            "the NES PPU mirrors $3F10/$3F14/$3F18/$3F1C onto \
                             $3F00/$3F04/$3F08/$3F0C, so a 32-byte sequential \
                             palette write overwrites the background universal \
                             colour with sub-palette sp3's first byte",
                        )
                        .with_help(
                            "set every sub-palette's first byte (indices 0, 4, 8, 12, \
                             16, 20, 24, 28) to the same universal colour, or switch \
                             to the grouped form (`universal:` + `bg0..sp3`) which \
                             fixes the mirror automatically",
                        ),
                    );
                }
            }
        }
        let mut seen_backgrounds = HashSet::new();
        for bg in &program.backgrounds {
            if !seen_backgrounds.insert(bg.name.clone()) {
                self.diagnostics.push(Diagnostic::error(
                    ErrorCode::E0501,
                    format!("duplicate background '{}'", bg.name),
                    bg.span,
                ));
            }
            if bg.tiles.len() > 960 {
                self.diagnostics.push(Diagnostic::error(
                    ErrorCode::E0201,
                    format!(
                        "background '{}' has {} tile bytes; maximum is 960 (32×30)",
                        bg.name,
                        bg.tiles.len()
                    ),
                    bg.span,
                ));
            }
            if bg.attributes.len() > 64 {
                self.diagnostics.push(Diagnostic::error(
                    ErrorCode::E0201,
                    format!(
                        "background '{}' has {} attribute bytes; maximum is 64 (8×8)",
                        bg.name,
                        bg.attributes.len()
                    ),
                    bg.span,
                ));
            }
        }

        // Validate sfx declarations' channel-specific constraints.
        // Triangle has no volume register so `volume:` is treated as
        // a per-frame hold flag (nonzero = sustain, zero = release);
        // duty bits are also meaningless for triangle and noise.
        // Pulse 2 is rejected outright on sfx declarations because
        // the pulse-2 channel is owned by the music driver.
        for decl in &program.sfx {
            match decl.channel {
                Channel::Pulse1 => {}
                Channel::Pulse2 => {
                    self.diagnostics.push(Diagnostic::error(
                        ErrorCode::E0201,
                        format!(
                            "sfx '{}' targets pulse2, which is reserved for the music driver",
                            decl.name
                        ),
                        decl.span,
                    ));
                }
                Channel::Triangle => {
                    // Parser default `duty` is 2, so only flag
                    // explicit non-default values. This keeps the
                    // common `channel: triangle, pitch: N, volume: [..]`
                    // form warning-free.
                    if decl.duty != 2 {
                        self.diagnostics.push(Diagnostic::warning(
                            ErrorCode::W0107,
                            format!(
                                "sfx '{}' targets triangle; 'duty' has no effect on this channel",
                                decl.name
                            ),
                            decl.span,
                        ));
                    }
                }
                Channel::Noise => {
                    if decl.duty != 2 {
                        self.diagnostics.push(Diagnostic::warning(
                            ErrorCode::W0107,
                            format!(
                                "sfx '{}' targets noise; 'duty' has no effect on this channel",
                                decl.name
                            ),
                            decl.span,
                        ));
                    }
                    // Noise pitch is a 4-bit period-table index plus
                    // an optional "mode" bit in position 7. Any other
                    // bits set is a user mistake.
                    for p in &decl.pitch {
                        if *p & !0x8F != 0 {
                            self.diagnostics.push(Diagnostic::error(
                                ErrorCode::E0201,
                                format!(
                                    "sfx '{}' noise pitch {:#04x} has bits outside the valid range (low 4 bits index + optional bit 7 mode)",
                                    decl.name, p
                                ),
                                decl.span,
                            ));
                            break;
                        }
                    }
                }
            }
        }

        // Validate metasprite declarations: the parallel offset
        // arrays must all be the same length, the named sprite
        // must exist, and the metasprite name must be unique
        // (against other metasprites and against sprites — both
        // share the same `draw` lookup namespace).
        //
        // We also enforce a more restrictive rule for the v1
        // metasprite lowering: every sprite that PRECEDES a
        // metasprite-targeted sprite in declaration order must use
        // an inline `pixels:` body. The IR lowering at
        // `ir/lowering.rs::lower_program` walks the sprite list to
        // compute base tile indices for the metasprite's `frame:`
        // resolution, but it can't read external `@chr(...)` /
        // `@binary(...)` files at lowering time and falls back to
        // a single-tile assumption — that would silently misalign
        // the metasprite's frame indices. Reject those programs at
        // analysis time so users get a clear error instead of a
        // visual glitch at runtime.
        let mut seen_metasprites = HashSet::new();
        let sprite_names: HashSet<String> =
            program.sprites.iter().map(|s| s.name.clone()).collect();
        for ms in &program.metasprites {
            if !seen_metasprites.insert(ms.name.clone()) {
                self.diagnostics.push(Diagnostic::error(
                    ErrorCode::E0501,
                    format!("duplicate metasprite '{}'", ms.name),
                    ms.span,
                ));
            }
            if sprite_names.contains(&ms.name) {
                self.diagnostics.push(Diagnostic::error(
                    ErrorCode::E0501,
                    format!(
                        "metasprite '{}' shadows a sprite with the same name; pick a unique identifier",
                        ms.name
                    ),
                    ms.span,
                ));
            }
            if sprite_names.contains(&ms.sprite_name) {
                // Check that every sprite up to *and including*
                // the target uses an inline pixels source. Any
                // earlier non-inline sprite would shift the base
                // tile of the target by an unknown amount; the
                // target itself also has to be inline so the
                // lowering knows how many tiles to consume for it.
                for sprite in &program.sprites {
                    let is_inline = matches!(
                        sprite.chr_source,
                        crate::parser::ast::AssetSource::Inline(_)
                    );
                    if !is_inline {
                        self.diagnostics.push(Diagnostic::error(
                            ErrorCode::E0201,
                            format!(
                                "metasprite '{}' depends on sprite '{}' which uses an external `@chr` or `@binary` source; \
                                 the v1 metasprite lowering can't compute base tile indices for non-inline sprites — \
                                 inline the pixel art with a `pixels:` block, or remove the metasprite",
                                ms.name, sprite.name
                            ),
                            ms.span,
                        ));
                        break;
                    }
                    if sprite.name == ms.sprite_name {
                        break;
                    }
                }
            } else {
                self.diagnostics.push(Diagnostic::error(
                    ErrorCode::E0201,
                    format!(
                        "metasprite '{}' references unknown sprite '{}'",
                        ms.name, ms.sprite_name
                    ),
                    ms.span,
                ));
            }
            if ms.dx.len() != ms.dy.len() || ms.dx.len() != ms.frame.len() {
                self.diagnostics.push(Diagnostic::error(
                    ErrorCode::E0201,
                    format!(
                        "metasprite '{}' has mismatched array lengths: \
                         dx={}, dy={}, frame={} — all three must be equal",
                        ms.name,
                        ms.dx.len(),
                        ms.dy.len(),
                        ms.frame.len()
                    ),
                    ms.span,
                ));
            }
            if ms.dx.is_empty() {
                self.diagnostics.push(Diagnostic::error(
                    ErrorCode::E0201,
                    format!(
                        "metasprite '{}' is empty — declare at least one tile",
                        ms.name
                    ),
                    ms.span,
                ));
            }
        }

        // Validate metatileset declarations: each tile array must
        // have exactly 4 entries (TL/TR/BL/BR), entry IDs must
        // match their position in the array, names are unique
        // across metatilesets, and the count is capped at 256 so
        // a metatile ID still fits in a u8. The compile-time
        // expansion in `IrCodeGen::generate` reads from these
        // tables, so anything that gets past the analyzer here
        // produces a corrupt nametable rather than a panic.
        let mut seen_metatilesets: HashSet<String> = HashSet::new();
        for mts in &program.metatilesets {
            if !seen_metatilesets.insert(mts.name.clone()) {
                self.diagnostics.push(Diagnostic::error(
                    ErrorCode::E0501,
                    format!("duplicate metatileset '{}'", mts.name),
                    mts.span,
                ));
            }
            if mts.metatiles.is_empty() {
                self.diagnostics.push(Diagnostic::error(
                    ErrorCode::E0201,
                    format!(
                        "metatileset '{}' is empty — declare at least one metatile",
                        mts.name
                    ),
                    mts.span,
                ));
            }
            if mts.metatiles.len() > 256 {
                self.diagnostics.push(Diagnostic::error(
                    ErrorCode::E0201,
                    format!(
                        "metatileset '{}' has {} metatiles; the limit is 256 (one byte of ID space)",
                        mts.name,
                        mts.metatiles.len()
                    ),
                    mts.span,
                ));
            }
            for (i, mt) in mts.metatiles.iter().enumerate() {
                if usize::from(mt.id) != i {
                    self.diagnostics.push(Diagnostic::error(
                        ErrorCode::E0201,
                        format!(
                            "metatile entry #{i} in metatileset '{}' has id={}; entries \
                             must be declared in ascending order with consecutive IDs starting \
                             at 0",
                            mts.name, mt.id
                        ),
                        mt.span,
                    ));
                }
            }
        }

        // Validate room declarations: must reference a known
        // metatileset, the layout must be exactly 240 entries
        // (16 wide × 15 tall — covers a 32×30 nametable when
        // expanded to 2×2 tiles), and every layout byte must be
        // a valid metatile ID for the referenced set.
        let mts_by_name: std::collections::HashMap<&str, &MetatilesetDecl> = program
            .metatilesets
            .iter()
            .map(|m| (m.name.as_str(), m))
            .collect();
        let mut seen_rooms: HashSet<String> = HashSet::new();
        for room in &program.rooms {
            if !seen_rooms.insert(room.name.clone()) {
                self.diagnostics.push(Diagnostic::error(
                    ErrorCode::E0501,
                    format!("duplicate room '{}'", room.name),
                    room.span,
                ));
            }
            if room.layout.len() != ROOM_CELL_COUNT {
                self.diagnostics.push(Diagnostic::error(
                    ErrorCode::E0201,
                    format!(
                        "room '{}' layout has {} entries; expected exactly {ROOM_CELL_COUNT} \
                         (a {ROOM_GRID_WIDTH}×{ROOM_GRID_HEIGHT} grid of metatile IDs)",
                        room.name,
                        room.layout.len()
                    ),
                    room.span,
                ));
            }
            match mts_by_name.get(room.metatileset.as_str()) {
                None => {
                    self.diagnostics.push(Diagnostic::error(
                        ErrorCode::E0201,
                        format!(
                            "room '{}' references unknown metatileset '{}'",
                            room.name, room.metatileset
                        ),
                        room.span,
                    ));
                }
                Some(mts) => {
                    let max_id = mts.metatiles.len().saturating_sub(1);
                    for (i, &b) in room.layout.iter().enumerate() {
                        if usize::from(b) > max_id {
                            self.diagnostics.push(Diagnostic::error(
                                ErrorCode::E0201,
                                format!(
                                    "room '{}' layout cell {i} = {b} is out of range for \
                                     metatileset '{}' (valid IDs are 0..={max_id})",
                                    room.name, room.metatileset
                                ),
                                room.span,
                            ));
                            break;
                        }
                    }
                }
            }
        }

        // Register functions as symbols
        for fun in &program.functions {
            self.register_fun(fun);
        }

        // Register state-local variables with automatic memory
        // overlaying. At runtime only one state is active at a time
        // (a single `ZP_CURRENT_STATE` byte picks the handler), so
        // every state's locals are mutually exclusive with every
        // other state's — their RAM footprints can share the same
        // addresses. The allocator snapshots both cursors after the
        // globals have been laid out, then rewinds to that snapshot
        // before each state's locals and tracks the running max.
        // The overall cursor advances to the max at the end, so
        // anything allocated after the state-locals (function
        // parameters, function bodies' locals) picks up past every
        // state's overlay window.
        //
        // Each state's on_enter handler re-initializes the locals
        // from their declared initializers — the IR lowering moves
        // those stores into the handler's prologue so a freshly
        // entered state doesn't read another state's leftover
        // bytes. State-locals whose name collides with a global or
        // another state's local are still rejected via E0501 at
        // `register_var` because the symbol table is keyed by the
        // bare name.
        let overlay_zp_base = self.next_zp_addr;
        let overlay_ram_base = self.next_ram_addr;
        let mut max_zp = overlay_zp_base;
        let mut max_ram = overlay_ram_base;
        for state in &program.states {
            self.next_zp_addr = overlay_zp_base;
            self.next_ram_addr = overlay_ram_base;
            for var in &state.locals {
                // Array initializers on state-locals aren't lowered
                // yet — the IR would need to emit a runtime memcpy
                // from a ROM blob into the allocated RAM region on
                // each on_enter, and today the lowerer just
                // `continue`s past the decl. Refuse the program rather
                // than silently dropping the initializer (PR-#31-shaped
                // bug). See docs/future-work.md for the plan.
                if let Some(Expr::ArrayLiteral(_, _)) = &var.init {
                    self.diagnostics.push(Diagnostic::error(
                        ErrorCode::E0601,
                        format!(
                            "state-local variable '{}' has an array \
                             initializer; this isn't lowered yet. Move \
                             the array to a program-level `var` or \
                             assign the elements inside `on_enter`.",
                            var.name
                        ),
                        var.span,
                    ));
                }
                self.register_var(var);
            }
            if self.next_zp_addr > max_zp {
                max_zp = self.next_zp_addr;
            }
            if self.next_ram_addr > max_ram {
                max_ram = self.next_ram_addr;
            }
        }
        self.next_zp_addr = max_zp;
        self.next_ram_addr = max_ram;

        // Validate state references
        let state_names: Vec<&str> = program.states.iter().map(|s| s.name.as_str()).collect();

        // Check start state exists
        if !state_names.contains(&program.start_state.as_str()) {
            self.diagnostics.push(Diagnostic::error(
                ErrorCode::E0404,
                format!("start state '{}' is not defined", program.start_state),
                program.span,
            ));
        }

        // Type-check all state bodies. Each handler body is its
        // own local scope: a `var i` inside `Title::on frame`
        // does not collide with a `var i` inside `Playing::on
        // frame`. State-level `var`s (declared at `state Foo { var x
        // }`) stay in the global scope so every handler in the
        // state can read and write them across frames.
        for state in &program.states {
            if let Some(block) = &state.on_enter {
                self.current_scope_prefix = Some(format!("{}__enter", state.name));
                self.check_block(block, &state_names);
                self.current_scope_prefix = None;
            }
            if let Some(block) = &state.on_exit {
                self.current_scope_prefix = Some(format!("{}__exit", state.name));
                self.check_block(block, &state_names);
                self.current_scope_prefix = None;
            }
            if let Some(block) = &state.on_frame {
                self.current_scope_prefix = Some(format!("{}__frame", state.name));
                self.check_block(block, &state_names);
                self.current_scope_prefix = None;
            }
            // `on scanline(N)` is only valid with mappers that have a
            // scanline-counting IRQ source (currently only MMC3). Keep
            // this as a hard error — without MMC3 the codegen emits
            // the handler functions but the IRQ dispatcher is never
            // wired up, so the handlers silently never run.
            if !state.on_scanline.is_empty() && program.game.mapper != Mapper::MMC3 {
                self.diagnostics.push(Diagnostic::error(
                    ErrorCode::E0603,
                    "`on scanline` requires the MMC3 mapper",
                    state.span,
                ));
            }
            for (line, block) in &state.on_scanline {
                self.current_scope_prefix = Some(format!("{}__scanline_{}", state.name, line));
                self.check_block(block, &state_names);
                self.current_scope_prefix = None;
            }
        }

        // Type-check function bodies. Each function body gets its
        // own local scope by setting `current_scope_prefix` to
        // the function's name. Parameters are registered as
        // function-local symbols under the prefixed key so two
        // different functions can both declare a parameter named
        // `x` without the analyzer's duplicate-declaration check
        // firing. Each parameter also gets its own dedicated RAM
        // slot allocated via `allocate_ram` — the codegen emits a
        // prologue that copies the transport slots `$04-$07`
        // into these RAM slots at function entry, so the param
        // values survive any nested calls the function body
        // makes. Parameters are pre-marked as "used" so we do
        // not emit W0103 for unused function arguments.
        for fun in &program.functions {
            self.current_scope_prefix = Some(fun.name.clone());
            for param in &fun.params {
                let key = self.scoped_name(&param.name);
                let size = match param.param_type {
                    NesType::U8 | NesType::I8 | NesType::Bool => 1,
                    NesType::U16 | NesType::I16 => 2,
                    // Struct/array parameters are not supported
                    // in v0.1; the parser already rejects them,
                    // so defaulting to 1 byte here is just a
                    // fallback to keep the analyzer from
                    // crashing on malformed ASTs.
                    _ => 1,
                };
                if let Some(address) = self.allocate_ram(size, fun.span) {
                    self.symbols.insert(
                        key.clone(),
                        Symbol {
                            name: key.clone(),
                            sym_type: param.param_type.clone(),
                            is_const: false,
                            span: fun.span,
                        },
                    );
                    self.var_allocations.push(VarAllocation {
                        name: key.clone(),
                        address,
                        size,
                    });
                    self.used_vars.insert(key);
                }
            }
            self.current_return_type.clone_from(&fun.return_type);
            self.in_function_body = true;
            self.check_block(&fun.body, &state_names);
            self.current_return_type = None;
            self.in_function_body = false;
            self.current_scope_prefix = None;
        }

        // Build call graph
        self.build_call_graph(program);

        // Detect recursion
        let recursive_fns = detect_recursion(&self.call_graph);
        for name in &recursive_fns {
            self.diagnostics.push(Diagnostic::error(
                ErrorCode::E0402,
                format!("recursion detected in function '{name}'"),
                program.span,
            ));
        }

        // Compute max call depths from entry points (state handlers)
        self.compute_max_depths(program);

        // Check for unused variables (W0103). Variables whose names
        // start with '_' are exempt by convention. Both globals and
        // state-local variables are checked.
        for var in &program.globals {
            self.check_unused_var(var);
        }
        for state in &program.states {
            for var in &state.locals {
                self.check_unused_var(var);
            }
        }

        // Check for under-used `fast` variables (W0107). A `fast`
        // declaration reserves one of the NES's scarce zero-page
        // slots, so it should see frequent traffic; below the
        // threshold the author is spending a precious slot on a
        // cold variable. Globals and state-locals both count.
        for var in &program.globals {
            self.check_fast_var_usage(var);
        }
        for state in &program.states {
            for var in &state.locals {
                self.check_fast_var_usage(var);
            }
        }

        // Check for unreachable states (W0104).
        self.check_unreachable_states(program);

        // Check for literal-coord sprite draws that would
        // overflow the NES's 8-sprites-per-scanline hardware
        // limit (W0109). Only on_frame handlers are checked —
        // on_enter and on_exit fire once per transition and are
        // much less likely to exceed the budget. Only draws
        // with `IntLiteral` (x, y) pairs are counted; dynamic
        // coordinates are skipped because the static analysis
        // can't know where the sprite will land at runtime.
        self.check_sprite_scanline_budget(program);

        // Check every `inline fun` declaration against the
        // IR lowerer's inline-eligibility rules. Functions
        // whose body shape isn't splicable compile as regular
        // out-of-line calls — which is correct, but silent:
        // users who mark a helper `inline` to avoid call
        // overhead might not realize the hint was declined.
        // W0110 makes the fallback visible.
        self.check_inline_declinability(program);
    }

    /// Qualify `name` under the current scope prefix. If no prefix
    /// is active (top-level analysis, state-level declaration) the
    /// name is returned unchanged. Inside a function body the
    /// result is `"__local__{prefix}__{name}"` — the same key the
    /// IR lowerer and codegen use when walking a function's locals.
    fn scoped_name(&self, name: &str) -> String {
        match &self.current_scope_prefix {
            Some(prefix) => format!("__local__{prefix}__{name}"),
            None => name.to_string(),
        }
    }

    /// Resolve a user-written identifier to the matching symbol
    /// table key. Tries the current scope's qualified key first
    /// (so function-local vars shadow same-named globals) and
    /// falls back to the bare key for globals, consts, enum
    /// variants, state-locals, and function names.
    fn resolve_key(&self, name: &str) -> String {
        if let Some(prefix) = &self.current_scope_prefix {
            let qualified = format!("__local__{prefix}__{name}");
            if self.symbols.contains_key(&qualified) {
                return qualified;
            }
        }
        name.to_string()
    }

    /// Look up a user-written identifier in the symbol table,
    /// preferring the current scope's qualified entry (if any)
    /// and falling back to the bare global entry.
    fn resolve_symbol(&self, name: &str) -> Option<&Symbol> {
        if let Some(prefix) = &self.current_scope_prefix {
            let qualified = format!("__local__{prefix}__{name}");
            if let Some(sym) = self.symbols.get(&qualified) {
                return Some(sym);
            }
        }
        self.symbols.get(name)
    }

    /// True if a symbol exists for `name` in the current scope or
    /// in the global scope.
    fn symbol_exists(&self, name: &str) -> bool {
        self.resolve_symbol(name).is_some()
    }

    /// Mark a variable name as having been read somewhere in the program.
    /// Also bumps the W0107 access counter. Resolves the name through
    /// the current scope so the right (qualified-or-bare) key is
    /// recorded.
    fn mark_var_used(&mut self, name: &str) {
        let key = self.resolve_key(name);
        self.used_vars.insert(key.clone());
        *self.var_access_counts.entry(key).or_insert(0) += 1;
    }

    /// Increment the observed access count for `name`. Called for
    /// both reads (via [`Analyzer::mark_var_used`]) and writes (at
    /// `Statement::Assign` handling). Used for W0107.
    fn bump_var_access(&mut self, name: &str) {
        let key = self.resolve_key(name);
        *self.var_access_counts.entry(key).or_insert(0) += 1;
    }

    /// Emit W0107 if `var` is declared `fast` but sees fewer than
    /// [`W0107_MIN_ACCESSES`] observed reads + writes across the
    /// whole program. Variables that are already unused (W0103
    /// fires) are skipped to avoid double-reporting; leading-`_`
    /// names are also exempt by the same convention that W0103 uses.
    /// Array-typed `fast` variables are skipped because they never
    /// end up in zero page anyway (allocation kicks them to main
    /// RAM), so the slot argument doesn't apply.
    fn check_fast_var_usage(&mut self, var: &VarDecl) {
        if var.placement != Placement::Fast {
            return;
        }
        if var.name.starts_with('_') {
            return;
        }
        if !self.used_vars.contains(&var.name) {
            return;
        }
        if matches!(var.var_type, NesType::Array(_, _)) {
            return;
        }
        let count = self.var_access_counts.get(&var.name).copied().unwrap_or(0);
        if count < W0107_MIN_ACCESSES {
            self.diagnostics.push(
                Diagnostic::warning(
                    ErrorCode::W0107,
                    format!(
                        "`fast` variable '{}' is accessed {count} time{plural}; \
                         it wastes a zero-page slot",
                        var.name,
                        plural = if count == 1 { "" } else { "s" },
                    ),
                    var.span,
                )
                .with_help(
                    "drop the `fast` qualifier so the variable lives in main \
                     RAM and the zero-page slot can go to a hotter variable",
                ),
            );
        }
    }

    /// Emit W0103 if `var` is never read anywhere. Variables named
    /// with a leading `_` are exempt by convention.
    fn check_unused_var(&mut self, var: &VarDecl) {
        if var.name.starts_with('_') {
            return;
        }
        if self.used_vars.contains(&var.name) {
            return;
        }
        self.diagnostics.push(Diagnostic {
            level: Level::Warning,
            code: ErrorCode::W0103,
            message: format!("unused variable '{}'", var.name),
            span: var.span,
            labels: Vec::<Label>::new(),
            help: Some("prefix with '_' to silence this warning, or remove the declaration".into()),
            note: None,
        });
    }

    /// Recursively walk an expression tree and mark every identifier that
    /// appears as an `Expr::Ident` (or as an `Expr::ArrayIndex` base) as
    /// "read". Used by the W0103 unused-variable analysis. Also emits
    /// E0502 for any identifier that is not defined in the symbol table.
    fn walk_expr_reads(&mut self, expr: &Expr) {
        match expr {
            Expr::Ident(name, span) => {
                if self.symbol_exists(name) {
                    self.mark_var_used(name);
                } else {
                    self.emit_undefined_var(name, *span);
                }
            }
            Expr::ArrayIndex(name, idx, span) => {
                // Array base is a read; index may contain more reads.
                if self.symbol_exists(name) {
                    self.mark_var_used(name);
                } else {
                    self.emit_undefined_var(name, *span);
                }
                self.walk_expr_reads(idx);
            }
            Expr::FieldAccess(name, field, span) => {
                // Resolve the struct variable through the scope
                // stack and verify the field exists. Mark both the
                // base and the synthetic `name.field` entry used.
                let base_key = self.resolve_key(name);
                let full_name = format!("{base_key}.{field}");
                if self.symbols.contains_key(&full_name) {
                    self.mark_var_used(name);
                    self.used_vars.insert(full_name);
                } else if !self.symbols.contains_key(&base_key) {
                    self.emit_undefined_var(name, *span);
                } else {
                    self.diagnostics.push(Diagnostic::error(
                        ErrorCode::E0201,
                        format!("'{name}' has no field '{field}'"),
                        *span,
                    ));
                }
            }
            Expr::BinaryOp(lhs, op, rhs, span) => {
                // W0101: warn about multiply/divide/modulo with a non-
                // constant operand. These lower to calls into the
                // software multiply/divide routines, which are far more
                // expensive than the simple inline opcodes used for
                // add/sub. A literal like `x * 2` can be strength-
                // reduced to a shift and is therefore cheap.
                if matches!(op, BinOp::Mul | BinOp::Div | BinOp::Mod)
                    && !is_small_constant(lhs)
                    && !is_small_constant(rhs)
                {
                    let op_name = match op {
                        BinOp::Mul => "multiply",
                        BinOp::Div => "divide",
                        BinOp::Mod => "modulo",
                        _ => unreachable!(),
                    };
                    self.diagnostics.push(
                        Diagnostic::warning(
                            ErrorCode::W0101,
                            format!("{op_name} with two non-constant operands is expensive"),
                            *span,
                        )
                        .with_help(
                            "consider precomputing or using a power-of-2 constant for strength reduction",
                        ),
                    );
                }
                self.walk_expr_reads(lhs);
                self.walk_expr_reads(rhs);
            }
            Expr::UnaryOp(_, inner, _) | Expr::Cast(inner, _, _) => {
                self.walk_expr_reads(inner);
            }
            Expr::Call(name, args, span) => {
                // If the function is known, validate its call signature.
                // Undefined-function errors are surfaced elsewhere (for
                // Statement::Call) and via the call-graph pass.
                if is_intrinsic(name) {
                    // Intrinsics can appear in expression position too
                    // (e.g. `var x = rand8()`). Validate arity here so
                    // typos and bad-arity calls don't slip past. Also
                    // reject the void-only intrinsics (`poke`,
                    // `seed_rand`, `set_palette_brightness`) at
                    // expression position so a typo like
                    // `var x = seed_rand(42)` fails at compile time
                    // instead of panicking the linker with an
                    // unresolved label.
                    self.check_intrinsic_args(name, args, *span);
                    if is_void_intrinsic(name) {
                        self.diagnostics.push(Diagnostic::error(
                            ErrorCode::E0203,
                            format!("`{name}` does not return a value; it can only be used as a statement"),
                            *span,
                        ));
                    }
                } else if self.function_signatures.contains_key(name) {
                    self.check_call_signature(name, args, *span);
                }
                for arg in args {
                    self.walk_expr_reads(arg);
                }
            }
            Expr::ArrayLiteral(elems, _) => {
                for e in elems {
                    self.walk_expr_reads(e);
                }
            }
            Expr::StructLiteral(name, fields, span) => {
                // Validate that the struct type exists and that each
                // named field is actually declared. Missing or extra
                // fields are an error; duplicate fields are silently
                // ignored (last-writer-wins).
                if let Some(layout) = self.struct_layouts.get(name).cloned() {
                    for (fname, fexpr) in fields {
                        if let Some((_, field_type, _)) =
                            layout.fields.iter().find(|(n, _, _)| n == fname)
                        {
                            self.walk_expr_reads(fexpr);
                            self.check_expr_type(fexpr, field_type);
                        } else {
                            self.diagnostics.push(Diagnostic::error(
                                ErrorCode::E0201,
                                format!("struct '{name}' has no field '{fname}'"),
                                *span,
                            ));
                        }
                    }
                } else {
                    self.diagnostics.push(Diagnostic::error(
                        ErrorCode::E0201,
                        format!("unknown struct type '{name}'"),
                        *span,
                    ));
                }
            }
            Expr::DebugCall(method, args, span) => {
                // Only the no-argument query methods are recognised
                // today. Anything else is an error so a typo gets
                // caught at compile time rather than silently
                // returning zero. Argument expressions are walked
                // for completeness even though no current method
                // accepts any.
                match method.as_str() {
                    "frame_overrun_count"
                    | "frame_overran"
                    | "sprite_overflow_count"
                    | "sprite_overflow" => {
                        if !args.is_empty() {
                            self.diagnostics.push(Diagnostic::error(
                                ErrorCode::E0203,
                                format!("`debug.{method}` takes no arguments, got {}", args.len()),
                                *span,
                            ));
                        }
                    }
                    _ => {
                        self.diagnostics.push(Diagnostic::error(
                            ErrorCode::E0201,
                            format!(
                                "unknown debug method '{method}' (expected 'frame_overrun_count', \
                                 'frame_overran', 'sprite_overflow_count', or 'sprite_overflow')"
                            ),
                            *span,
                        ));
                    }
                }
                for arg in args {
                    self.walk_expr_reads(arg);
                }
            }
            Expr::IntLiteral(_, _) | Expr::BoolLiteral(_, _) | Expr::ButtonRead(_, _, _) => {}
            Expr::ButtonEdge(_, button, _, span) => {
                // Same validation as ButtonRead: the button name
                // must be recognised. `crate::ir::lowering::button_mask`
                // returns 0 for unknown names which would silently
                // compile to "always false"; reject here so typos
                // surface at compile time.
                if !is_known_button(button) {
                    self.diagnostics.push(Diagnostic::error(
                        ErrorCode::E0201,
                        format!("unknown button '{button}'"),
                        *span,
                    ));
                }
            }
        }
    }

    /// Suggest a similarly-named symbol for undefined-variable errors.
    /// Uses a simple heuristic: same first character and similar length.
    fn suggest_var_name(&self, unknown: &str) -> Option<String> {
        let first = unknown.chars().next()?;
        self.symbols
            .keys()
            .filter(|name| {
                name.starts_with(first)
                    && name.len().abs_diff(unknown.len()) <= 2
                    && name.as_str() != unknown
            })
            .min_by_key(|name| name.len().abs_diff(unknown.len()))
            .cloned()
    }

    /// Emit E0502 for an undefined variable reference, with a "did you mean"
    /// suggestion if a similar symbol exists.
    fn emit_undefined_var(&mut self, name: &str, span: Span) {
        let mut diag = Diagnostic::error(
            ErrorCode::E0502,
            format!("undefined variable '{name}'"),
            span,
        );
        if let Some(suggestion) = self.suggest_var_name(name) {
            diag = diag.with_help(format!("did you mean '{suggestion}'?"));
        }
        self.diagnostics.push(diag);
    }

    /// Reachability analysis for states. Performs a BFS from the start state
    /// through every transition in state handlers and emits W0104 for any
    /// state that is never reached.
    fn check_unreachable_states(&mut self, program: &Program) {
        let mut reachable: HashSet<String> = HashSet::new();
        let mut queue: Vec<String> = vec![program.start_state.clone()];

        while let Some(state_name) = queue.pop() {
            if !reachable.insert(state_name.clone()) {
                continue;
            }
            if let Some(state) = program.states.iter().find(|s| s.name == state_name) {
                collect_transitions_from_state(state, &mut queue);
            }
        }

        for state in &program.states {
            if !reachable.contains(&state.name) {
                self.diagnostics.push(Diagnostic {
                    level: Level::Warning,
                    code: ErrorCode::W0104,
                    message: format!("state '{}' is unreachable from start state", state.name),
                    span: state.span,
                    labels: Vec::<Label>::new(),
                    help: Some(
                        "add a 'transition' to this state from a reachable state, or remove it"
                            .into(),
                    ),
                    note: None,
                });
            }
        }
    }

    /// Static check for the NES's 8-sprites-per-scanline hardware
    /// limit (W0109). Walks every state's `on_frame` handler,
    /// collects literal-coordinate `draw` statements (and expands
    /// metasprites via their per-tile `dx`/`dy` offsets), then
    /// iterates scanlines 0..240 and emits W0109 for any state
    /// where more than 8 sprites overlap a single scanline.
    ///
    /// Draws with non-literal `x` or `y` are skipped — static
    /// analysis can't know where those sprites land at runtime.
    /// Draws inside nested `if`/`while`/`for`/`loop` blocks are
    /// counted as if they always fire; this over-counts programs
    /// that stagger draws across mutually exclusive branches, but
    /// it matches the worst case the hardware sees. Only `on_frame`
    /// is checked — `on_enter`/`on_exit` run once per transition
    /// and aren't on the hot sprite path.
    fn check_sprite_scanline_budget(&mut self, program: &Program) {
        // Build a name -> MetaspriteDecl lookup so draws that target
        // a metasprite can expand to one slot per tile offset.
        let metasprites: HashMap<&str, &MetaspriteDecl> = program
            .metasprites
            .iter()
            .map(|ms| (ms.name.as_str(), ms))
            .collect();

        for state in &program.states {
            let Some(block) = &state.on_frame else {
                continue;
            };

            // Collect (y, x, span) tuples for every literal-coord
            // draw in the handler, recursing through nested control
            // flow and expanding metasprites.
            let mut draws: Vec<(u8, u8, Span)> = Vec::new();
            collect_literal_draws(block, &metasprites, &mut draws);

            // Fast path: if there aren't even 9 literal draws total
            // the overlap check can never trip.
            if draws.len() <= 8 {
                continue;
            }

            // For each scanline, count how many 8×8 sprites cover
            // it. Sprites at y=Y cover scanlines Y..Y+8 (NES OAM
            // stores the y one line early, but for the overlap
            // budget the 8-pixel span is what matters).
            let mut worst_count: usize = 0;
            let mut worst_scanline: u16 = 0;
            for scanline in 0u16..240 {
                let mut count = 0usize;
                for (y, _, _) in &draws {
                    let top = u16::from(*y);
                    if top <= scanline && scanline < top + 8 {
                        count += 1;
                    }
                }
                if count > worst_count {
                    worst_count = count;
                    worst_scanline = scanline;
                }
            }

            if worst_count <= 8 {
                continue;
            }

            // Build a diagnostic pointing at the state with labels
            // on each offending draw. Cap the labels at 9 so the
            // message doesn't become a wall of text for pathological
            // programs.
            let mut diag = Diagnostic::warning(
                ErrorCode::W0109,
                format!(
                    "state '{}' draws {} literal-coordinate sprites overlapping scanline {}; \
                     the NES renders at most 8 sprites per scanline",
                    state.name, worst_count, worst_scanline
                ),
                state.span,
            )
            .with_help(
                "stagger draws vertically by at least 8 pixels, reduce the number of \
                 on-screen sprites, or split the draws across `on_scanline` handlers",
            )
            .with_note(
                "the 9th and later sprites on a scanline are dropped by the PPU, \
                 causing flicker or invisible objects on real hardware",
            );

            let mut labeled: usize = 0;
            let mut seen_spans: HashSet<(u16, u32, u32)> = HashSet::new();
            for (y, _, span) in &draws {
                let top = u16::from(*y);
                if top <= worst_scanline && worst_scanline < top + 8 {
                    // Deduplicate identical spans (metasprite
                    // expansion produces one tuple per tile but all
                    // share the original draw-site span).
                    let key = (span.file_id, span.start, span.end);
                    if !seen_spans.insert(key) {
                        continue;
                    }
                    diag = diag.with_label(*span, "draws here");
                    labeled += 1;
                    if labeled >= 9 {
                        break;
                    }
                }
            }

            self.diagnostics.push(diag);
        }
    }

    /// Walk every `inline fun` declaration and check whether the
    /// IR lowerer will actually inline its body. Functions that
    /// won't inline (conditional returns, loops, transitions,
    /// empty void bodies, etc.) compile as regular out-of-line
    /// calls — correct but silent. W0110 surfaces the fallback
    /// at the declaration site with help text pointing at the
    /// two body shapes the inliner does accept.
    ///
    /// Defers to [`crate::ir::lowering::can_inline_fun`] so the
    /// two sides (warning + actual capture) can never drift.
    fn check_inline_declinability(&mut self, program: &Program) {
        for fun in &program.functions {
            if !fun.is_inline {
                continue;
            }
            if crate::ir::can_inline_fun(fun.return_type.as_ref(), &fun.body) {
                continue;
            }
            self.diagnostics.push(
                Diagnostic::warning(
                    ErrorCode::W0110,
                    format!(
                        "`inline fun {}` cannot be inlined; falling back to a regular call",
                        fun.name
                    ),
                    fun.span,
                )
                .with_help(
                    "the inliner accepts two body shapes: a single `return <expr>` (for \
                     functions with a return type) or a sequence of plain statements with no \
                     control flow (for void functions). Rewrite the body to fit one of those, \
                     or remove the `inline` keyword if the JSR overhead is acceptable",
                )
                .with_note(
                    "rejected body shapes include conditional early returns, if/while/for/loop \
                     blocks, transitions, breaks, continues, and nested function definitions",
                ),
            );
        }
    }

    fn register_const(&mut self, c: &ConstDecl) {
        if self.symbols.contains_key(&c.name) {
            self.diagnostics.push(Diagnostic::error(
                ErrorCode::E0501,
                format!("duplicate declaration of '{}'", c.name),
                c.span,
            ));
            return;
        }
        self.symbols.insert(
            c.name.clone(),
            Symbol {
                name: c.name.clone(),
                sym_type: c.const_type.clone(),
                is_const: true,
                span: c.span,
            },
        );
    }

    /// Register a struct declaration. Computes each field's byte
    /// offset from the base address (fields are laid out contiguously
    /// in declaration order with no padding), and records the total
    /// size. Field types may be `u8`, `i8`, `bool`, `u16`, an array
    /// of any of those, or another previously-declared struct.
    /// Nested struct fields require the inner struct to have been
    /// declared earlier in the program (we don't topologically sort).
    fn register_struct(&mut self, s: &StructDecl) {
        if self.struct_layouts.contains_key(&s.name) {
            self.diagnostics.push(Diagnostic::error(
                ErrorCode::E0501,
                format!("duplicate struct declaration of '{}'", s.name),
                s.span,
            ));
            return;
        }
        // Snapshot the existing per-struct sizes so the size
        // helper can resolve nested struct field sizes without
        // borrowing `self` mutably.
        let struct_sizes: HashMap<String, u16> = self
            .struct_layouts
            .iter()
            .map(|(n, l)| (n.clone(), l.size))
            .collect();
        let mut fields = Vec::new();
        let mut offset: u16 = 0;
        for field in &s.fields {
            // Compute the size for this field. Primitives are 1 or
            // 2 bytes; arrays multiply element size by length;
            // nested structs look up the previously-registered
            // size. A nested struct that hasn't been declared yet
            // is an error — the user must put inner structs
            // before the outer ones.
            let size = match &field.field_type {
                NesType::U8 | NesType::I8 | NesType::Bool => 1,
                NesType::U16 | NesType::I16 => 2,
                NesType::Array(elem, count) => {
                    // Reject arrays of structs for now — the
                    // synthetic-variable model used by the
                    // analyzer flattens scalars into one symbol
                    // per leaf, but an array-of-structs would
                    // need either per-element flattening or a
                    // proper indexed-struct codegen path.
                    if let NesType::Struct(_) = elem.as_ref() {
                        self.diagnostics.push(Diagnostic::error(
                            ErrorCode::E0201,
                            format!(
                                "struct field '{}' is an array of structs, which is not yet supported",
                                field.name
                            ),
                            field.span,
                        ));
                        continue;
                    }
                    let elem_size = type_size_with(elem, &struct_sizes);
                    elem_size * *count
                }
                NesType::Struct(sname) => {
                    let Some(inner) = struct_sizes.get(sname).copied() else {
                        self.diagnostics.push(Diagnostic::error(
                            ErrorCode::E0201,
                            format!(
                                "struct '{}' field '{}' references unknown struct type '{sname}'; declare '{sname}' before '{}'",
                                s.name, field.name, s.name
                            ),
                            field.span,
                        ));
                        continue;
                    };
                    inner
                }
            };
            fields.push((field.name.clone(), field.field_type.clone(), offset));
            offset += size;
        }
        self.struct_layouts.insert(
            s.name.clone(),
            StructLayout {
                size: offset,
                fields,
            },
        );
    }

    /// Register each variant of an enum declaration as a `u8` constant
    /// with a value equal to its declaration order. Variant names must
    /// be globally unique; a duplicate name emits E0501.
    fn register_enum(&mut self, e: &EnumDecl) {
        if self.symbols.contains_key(&e.name) {
            self.diagnostics.push(Diagnostic::error(
                ErrorCode::E0501,
                format!("duplicate declaration of '{}'", e.name),
                e.span,
            ));
            // Don't return — still register the variants.
        }
        for (variant_name, variant_span) in &e.variants {
            if self.symbols.contains_key(variant_name) {
                self.diagnostics.push(Diagnostic::error(
                    ErrorCode::E0501,
                    format!("duplicate declaration of '{variant_name}'"),
                    *variant_span,
                ));
                continue;
            }
            self.symbols.insert(
                variant_name.clone(),
                Symbol {
                    name: variant_name.clone(),
                    sym_type: NesType::U8,
                    is_const: true,
                    span: *variant_span,
                },
            );
        }
    }

    /// Recursively walk a struct layout and synthesize one symbol +
    /// allocation per leaf field, plus a Struct-typed symbol for
    /// each nested-struct intermediate so dotted-name lookups for
    /// `outer.inner` (without the trailing leaf) still resolve.
    ///
    /// For example, given `var p: Player` where `Player { pos:
    /// Point, hp: u8, inv: u8[4] }` and `Point { x: u8, y: u8 }`,
    /// this produces:
    ///
    /// - `p.pos`        — Symbol(Struct("Point"))
    /// - `p.pos.x`      — Symbol(U8) + allocation
    /// - `p.pos.y`      — Symbol(U8) + allocation
    /// - `p.hp`         — Symbol(U8) + allocation
    /// - `p.inv`        — Symbol(Array(U8, 4)) + allocation
    fn flatten_struct_fields(
        &mut self,
        base_name: &str,
        base_addr: u16,
        layout: &StructLayout,
        var_span: Span,
    ) {
        // Snapshot the per-struct sizes once at the top of the
        // recursion so deep struct trees don't rebuild the same
        // map at every leaf — `type_size_with` is the only
        // consumer and it just needs the size lookup.
        let struct_sizes: HashMap<String, u16> = self
            .struct_layouts
            .iter()
            .map(|(n, l)| (n.clone(), l.size))
            .collect();
        for (field_name, field_type, offset) in &layout.fields {
            let full_name = format!("{base_name}.{field_name}");
            let field_addr = base_addr + offset;
            match field_type {
                NesType::Struct(sname) => {
                    // Register the intermediate as a Struct
                    // symbol so a `name.field` walk finds it
                    // even when only the leaves carry storage.
                    self.symbols.insert(
                        full_name.clone(),
                        Symbol {
                            name: full_name.clone(),
                            sym_type: field_type.clone(),
                            is_const: false,
                            span: var_span,
                        },
                    );
                    let nested = self.struct_layouts[sname].clone();
                    self.flatten_struct_fields(&full_name, field_addr, &nested, var_span);
                }
                _ => {
                    // u8 / i8 / u16 / bool / array — leaf field.
                    // The leaf's allocation size mirrors the
                    // top-level rule used by `register_var`.
                    self.symbols.insert(
                        full_name.clone(),
                        Symbol {
                            name: full_name.clone(),
                            sym_type: field_type.clone(),
                            is_const: false,
                            span: var_span,
                        },
                    );
                    let field_size = type_size_with(field_type, &struct_sizes);
                    self.var_allocations.push(VarAllocation {
                        name: full_name,
                        address: field_addr,
                        size: field_size,
                    });
                }
            }
        }
    }

    fn register_var(&mut self, var: &VarDecl) {
        // Scope-qualified storage key. At the top level this is
        // the bare `var.name`; inside a function or handler body
        // it is `"__local__{prefix}__{name}"` so two different
        // functions can each declare a local `var i` without
        // colliding on the flat symbol table.
        let key = self.scoped_name(&var.name);

        // Duplicate check runs against the qualified key so
        // shadowing a global with a function-local var is fine
        // (the local key is distinct). Two locals with the same
        // name inside the same scope still collide and report
        // E0501 correctly.
        if self.symbols.contains_key(&key) {
            self.diagnostics.push(Diagnostic::error(
                ErrorCode::E0501,
                format!("duplicate declaration of '{}'", var.name),
                var.span,
            ));
            return;
        }

        // Validate struct type exists before sizing.
        if let NesType::Struct(sname) = &var.var_type {
            if !self.struct_layouts.contains_key(sname) {
                self.diagnostics.push(Diagnostic::error(
                    ErrorCode::E0201,
                    format!("unknown struct type '{sname}'"),
                    var.span,
                ));
                return;
            }
        }

        let struct_sizes: HashMap<String, u16> = self
            .struct_layouts
            .iter()
            .map(|(n, l)| (n.clone(), l.size))
            .collect();
        let size = type_size_with(&var.var_type, &struct_sizes);

        // Warn on arrays whose byte size exceeds 256: the codegen
        // lowers `arr[i]` to `LDA base,X` (or `ZeroPageX`), and the
        // 6502's X register is 8 bits, so elements whose byte
        // offset is >= 256 are unreachable. For a `u8` array the
        // safe max count is 256; for a `u16` array it's 128
        // (since the codegen doesn't scale the index by element
        // width — see the note in `emit_bounds_check`). This
        // diagnostic replaces the previous silent-skip in the
        // debug-mode bounds checker.
        if let NesType::Array(_, _) = &var.var_type {
            if size > 256 {
                self.diagnostics.push(
                    Diagnostic::warning(
                        ErrorCode::W0108,
                        format!(
                            "array '{}' has byte size {size}, but the 6502's 8-bit X index can only reach the first 256 bytes — elements past that are unreachable",
                            var.name
                        ),
                        var.span,
                    )
                    .with_help(
                        "shrink the array, split it across multiple smaller arrays, or use separate fields for each element".to_string(),
                    ),
                );
            }
        }

        let Some(address) = self.allocate_ram_with_placement(size, var.placement, var.span) else {
            // Allocation failed (E0301 already emitted) — still add the
            // symbol so that later references don't cascade into E0502,
            // but don't record a var_allocations entry.
            self.symbols.insert(
                key.clone(),
                Symbol {
                    name: key,
                    sym_type: var.var_type.clone(),
                    is_const: false,
                    span: var.span,
                },
            );
            return;
        };

        // For struct-typed variables, synthesize per-field entries
        // in the symbol table and var_allocations. This lets the
        // rest of the compiler treat `pos.x` and `pos.y` as
        // ordinary variables at known addresses, without special-
        // casing struct layout. Nested structs recurse — a
        // `Player { pos: Point, ... }` variable produces both
        // `p.pos` (typed `Struct("Point")`) and `p.pos.x`,
        // `p.pos.y` leaves. Array fields produce a single
        // synthetic with the array type so the existing
        // `Expr::ArrayIndex` lowering picks them up.
        //
        // Struct fields use the qualified key as the base so
        // function-local struct instances don't collide with
        // same-named globals. `flatten_struct_fields` builds
        // `"{key}.{field}"` paths, which inherits the scope
        // prefix automatically.
        if let NesType::Struct(sname) = &var.var_type {
            let layout = self.struct_layouts[sname].clone();
            self.flatten_struct_fields(&key, address, &layout, var.span);
            // Also register the struct variable itself (as a symbol
            // only — it doesn't have a single VarAllocation entry).
            self.symbols.insert(
                key.clone(),
                Symbol {
                    name: key,
                    sym_type: var.var_type.clone(),
                    is_const: false,
                    span: var.span,
                },
            );
            return;
        }

        self.symbols.insert(
            key.clone(),
            Symbol {
                name: key.clone(),
                sym_type: var.var_type.clone(),
                is_const: false,
                span: var.span,
            },
        );

        self.var_allocations.push(VarAllocation {
            name: key,
            address,
            size,
        });
    }

    /// Register a `save { var ... }` declaration. Save vars are
    /// allocated from a separate bump pointer over the iNES SRAM
    /// window (`$6000-$7FFF`), get a `VarAllocation` entry just
    /// like a normal global, and live in the main symbol table so
    /// user code reads/writes them with the usual `=` / load
    /// syntax. The only thing special is their address range —
    /// the codegen emits absolute-mode loads/stores automatically
    /// because the address exceeds the zero-page boundary.
    ///
    /// Struct types in save blocks are accepted but not
    /// flattened into per-field SRAM slots yet — the analyzer
    /// emits an error if a save block declares a struct, since
    /// the field-flattening path uses the main-RAM allocator and
    /// would land struct fields back in `$0300+`. Scalars,
    /// scalar arrays, and `u16`/`i16` are the supported set for
    /// this first pass.
    fn register_save_var(&mut self, var: &VarDecl) {
        let key = self.scoped_name(&var.name);
        if self.symbols.contains_key(&key) {
            self.diagnostics.push(Diagnostic::error(
                ErrorCode::E0501,
                format!("duplicate declaration of '{}'", var.name),
                var.span,
            ));
            return;
        }
        // Save vars in SRAM are persisted across power cycles, so an
        // initializer would either silently never run (current
        // behaviour: globals init at reset, but save vars don't pass
        // through that path) or actively clobber the player's saved
        // data on every boot. Neither is what the user wants. Warn
        // and tell them about the magic-byte sentinel pattern.
        if var.init.is_some() {
            self.diagnostics.push(
                Diagnostic::warning(
                    ErrorCode::W0111,
                    format!(
                        "initializer on save-block field `{}` is ignored — \
                         SRAM is preserved across power cycles",
                        var.name
                    ),
                    var.span,
                )
                .with_help(
                    "first-power-on defaults need an explicit magic-byte sentinel: \
                     check a known signature on boot, and only write defaults if it's missing",
                ),
            );
        }
        if matches!(var.var_type, NesType::Struct(_)) {
            self.diagnostics.push(
                Diagnostic::error(
                    ErrorCode::E0201,
                    "struct types are not supported inside `save { }` blocks yet",
                    var.span,
                )
                .with_help("use scalar fields (u8, i8, u16, i16, bool) or scalar arrays"),
            );
            return;
        }
        let struct_sizes: HashMap<String, u16> = self
            .struct_layouts
            .iter()
            .map(|(n, l)| (n.clone(), l.size))
            .collect();
        let size = type_size_with(&var.var_type, &struct_sizes);
        let Some(end) = self.next_sram_addr.checked_add(size) else {
            self.diagnostics.push(Diagnostic::error(
                ErrorCode::E0301,
                "save block exceeds the 8 KB SRAM window ($6000-$7FFF)",
                var.span,
            ));
            return;
        };
        if end > 0x8000 {
            self.diagnostics.push(Diagnostic::error(
                ErrorCode::E0301,
                "save block exceeds the 8 KB SRAM window ($6000-$7FFF)",
                var.span,
            ));
            return;
        }
        let address = self.next_sram_addr;
        self.next_sram_addr = end;
        // Mark the save-mode flag so the linker knows to flip
        // the iNES battery bit. Stored on `var_allocations` via
        // the address range itself — addresses ≥ `$6000` are SRAM
        // by construction, so the analyzer needs no extra side
        // table beyond the existing allocation list.
        self.symbols.insert(
            key.clone(),
            Symbol {
                name: key.clone(),
                sym_type: var.var_type.clone(),
                is_const: false,
                span: var.span,
            },
        );
        self.var_allocations.push(VarAllocation {
            name: key,
            address,
            size,
        });
    }

    fn register_fun(&mut self, fun: &FunDecl) {
        if self.symbols.contains_key(&fun.name) {
            self.diagnostics.push(Diagnostic::error(
                ErrorCode::E0501,
                format!("duplicate declaration of '{}'", fun.name),
                fun.span,
            ));
            return;
        }
        // The v0.1 calling convention passes parameters via four
        // Parameters are passed through zero-page transport slots
        // for *leaf* functions only; non-leaf functions use a
        // direct-write calling convention where the caller stages
        // each argument straight into the callee's analyzer-
        // allocated parameter RAM slot, bypassing the transport
        // slots entirely. That lifts the per-function parameter cap
        // from 4 (the number of ZP transport slots at $04-$07) to 8
        // for non-leaves. Leaves still cap at 4 because their bodies
        // read `$04-$07` directly and there's nowhere to put extras.
        //
        // The analyzer can't know which functions will be leaves
        // without running the leaf-analysis that only exists in the
        // codegen, so we apply the looser 8-param cap here and let
        // the codegen's `function_is_leaf` check demote any
        // 5-to-8-param function to non-leaf automatically. The net
        // user-visible rule: 1–4 params works everywhere; 5–8 params
        // works but forbids the leaf fast path.
        if fun.params.len() > 8 {
            self.diagnostics.push(
                Diagnostic::error(
                    ErrorCode::E0506,
                    format!(
                        "function '{}' has {} parameters; the maximum is 8",
                        fun.name,
                        fun.params.len()
                    ),
                    fun.span,
                )
                .with_help(
                    "pass related data through a struct global, or split the function into two"
                        .to_string(),
                ),
            );
            return;
        }
        let sym_type = fun.return_type.clone().unwrap_or(NesType::U8);
        self.symbols.insert(
            fun.name.clone(),
            Symbol {
                name: fun.name.clone(),
                sym_type,
                is_const: false,
                span: fun.span,
            },
        );
        let param_types: Vec<NesType> = fun.params.iter().map(|p| p.param_type.clone()).collect();
        self.function_signatures
            .insert(fun.name.clone(), param_types);
        self.function_return_types
            .insert(fun.name.clone(), fun.return_type.clone());
    }

    /// Attempt to allocate `size` bytes of RAM for a variable declared
    /// at `span`. Returns `None` on overflow, emitting E0301. The
    /// zero-page user region is bounded above by [`ZP_USER_CAP`] to
    /// leave room for IR codegen temp slots starting at $80.
    fn allocate_ram(&mut self, size: u16, span: Span) -> Option<u16> {
        self.allocate_ram_with_placement(size, Placement::Auto, span)
    }

    fn allocate_ram_with_placement(
        &mut self,
        size: u16,
        placement: Placement,
        span: Span,
    ) -> Option<u16> {
        // Zero-page u8 allocation — bounded by ZP_USER_CAP to avoid
        // colliding with the IR temp region at $80+. `slow` forces
        // main RAM so users can deliberately keep a u8 out of ZP
        // (e.g. a cold variable they don't want wasting a ZP slot);
        // without this branch the `slow` keyword parsed but had no
        // observable effect, which is the same silent-drop shape
        // that bit PR #31.
        if size == 1 && self.next_zp_addr < ZP_USER_CAP && placement != Placement::Slow {
            let addr = u16::from(self.next_zp_addr);
            self.next_zp_addr = self.next_zp_addr.wrapping_add(1);
            return Some(addr);
        }

        // Larger / remaining allocations go into the main RAM region
        // after the OAM buffer.
        let end = self.next_ram_addr.checked_add(size)?;
        if end > RAM_END {
            self.diagnostics.push(
                Diagnostic::error(
                    ErrorCode::E0301,
                    "out of RAM: too many variables declared",
                    span,
                )
                .with_help(
                    "the NES only has 2 KB of RAM ($0000-$07FF); consider removing some globals",
                ),
            );
            return None;
        }
        let addr = self.next_ram_addr;
        self.next_ram_addr = end;
        Some(addr)
    }

    fn build_call_graph(&mut self, program: &Program) {
        // Record calls from each function body
        for fun in &program.functions {
            let callees = collect_calls(&fun.body);
            self.call_graph.insert(fun.name.clone(), callees);
        }

        // Record calls from each state handler
        for state in &program.states {
            if let Some(block) = &state.on_enter {
                let key = format!("{}::enter", state.name);
                let callees = collect_calls(block);
                self.call_graph.insert(key, callees);
            }
            if let Some(block) = &state.on_exit {
                let key = format!("{}::exit", state.name);
                let callees = collect_calls(block);
                self.call_graph.insert(key, callees);
            }
            if let Some(block) = &state.on_frame {
                let key = format!("{}::frame", state.name);
                let callees = collect_calls(block);
                self.call_graph.insert(key, callees);
            }
        }
    }

    fn compute_max_depths(&mut self, program: &Program) {
        let mut cache = HashMap::new();

        // Entry points are state handlers
        for state in &program.states {
            let handler_keys: Vec<String> = [
                state
                    .on_enter
                    .as_ref()
                    .map(|_| format!("{}::enter", state.name)),
                state
                    .on_exit
                    .as_ref()
                    .map(|_| format!("{}::exit", state.name)),
                state
                    .on_frame
                    .as_ref()
                    .map(|_| format!("{}::frame", state.name)),
            ]
            .into_iter()
            .flatten()
            .collect();

            for key in handler_keys {
                let mut visited = HashSet::new();
                let depth = compute_depth(&key, &self.call_graph, &mut visited, &mut cache);
                self.max_depths.insert(key.clone(), depth);

                if depth > self.stack_depth_limit {
                    self.diagnostics.push(Diagnostic::error(
                        ErrorCode::E0401,
                        format!(
                            "call depth {depth} in handler '{key}' exceeds stack limit {}",
                            self.stack_depth_limit
                        ),
                        program.span,
                    ));
                }
            }
        }
    }

    fn check_block(&mut self, block: &Block, state_names: &[&str]) {
        let mut terminated_by: Option<Span> = None;
        let mut warned_dead_code = false;
        for stmt in &block.statements {
            if let Some(term_span) = terminated_by {
                if !warned_dead_code {
                    self.diagnostics.push(
                        Diagnostic::warning(
                            ErrorCode::W0104,
                            "unreachable code after return / break / transition",
                            stmt.span(),
                        )
                        .with_label(term_span, "execution stops here"),
                    );
                    warned_dead_code = true;
                }
            }
            self.check_statement(stmt, state_names);
            if stmt_is_terminator(stmt) && terminated_by.is_none() {
                terminated_by = Some(stmt.span());
            }
        }
    }

    fn check_statement(&mut self, stmt: &Statement, state_names: &[&str]) {
        match stmt {
            Statement::VarDecl(var) => {
                self.register_var(var);
                if let Some(init) = &var.init {
                    self.walk_expr_reads(init);
                    self.check_expr_type(init, &var.var_type);
                    // The initializer is a write to the variable;
                    // count it toward W0107's access tally without
                    // marking the variable "read" (W0103 still wants
                    // to fire on a declared-but-unread var).
                    self.bump_var_access(&var.name);
                }
            }
            Statement::Assign(lvalue, _, expr, span) => {
                // Check if trying to assign to a constant. Lookups
                // go through `resolve_symbol` so a function-local
                // shadowing a global const/var is handled correctly.
                match lvalue {
                    LValue::Var(name) => {
                        if let Some(sym) = self.resolve_symbol(name) {
                            if sym.is_const {
                                self.diagnostics.push(Diagnostic::error(
                                    ErrorCode::E0203,
                                    format!("cannot assign to constant '{name}'"),
                                    *span,
                                ));
                            }
                            // A plain scalar write doesn't count as a
                            // read for W0103 (an unused variable might
                            // only be written to, never read), but it
                            // is still an access of the variable's
                            // storage for W0107's "is this `fast`
                            // slot worth it?" check.
                            self.bump_var_access(name);
                        } else {
                            // Assigning to an undeclared name is an
                            // error — the lowering would otherwise
                            // silently synthesize a VarId for it.
                            self.emit_undefined_var(name, *span);
                        }
                    }
                    LValue::ArrayIndex(name, idx) => {
                        if let Some(sym) = self.resolve_symbol(name) {
                            if sym.is_const {
                                self.diagnostics.push(Diagnostic::error(
                                    ErrorCode::E0203,
                                    format!("cannot assign to constant '{name}'"),
                                    *span,
                                ));
                            }
                        } else {
                            self.emit_undefined_var(name, *span);
                        }
                        // Indexing an array counts as a read of the array,
                        // and the index expression itself may contain reads.
                        self.mark_var_used(name);
                        self.walk_expr_reads(idx);
                    }
                    LValue::Field(name, field) => {
                        // Struct instances are stored under the
                        // scope-qualified key (see register_var);
                        // the per-field synthetic keys inherit that
                        // prefix via `flatten_struct_fields`. Build
                        // the field path off whichever key actually
                        // exists — scoped first, bare second.
                        let base_key = self.resolve_key(name);
                        let full_name = format!("{base_key}.{field}");
                        if self.symbols.contains_key(&full_name) {
                            // Assigning to a field is a mutation; don't
                            // mark the struct variable as "read" just
                            // because we wrote to one of its fields.
                            self.used_vars.insert(full_name);
                        } else if self.symbols.contains_key(&base_key) {
                            self.diagnostics.push(Diagnostic::error(
                                ErrorCode::E0201,
                                format!("'{name}' has no field '{field}'"),
                                *span,
                            ));
                        } else {
                            self.emit_undefined_var(name, *span);
                        }
                    }
                }
                self.walk_expr_reads(expr);
                let ltype = self.lvalue_type(lvalue, *span);
                if let Some(lt) = ltype {
                    self.check_expr_type(expr, &lt);
                }
            }
            Statement::If(cond, then_block, else_ifs, else_block, _) => {
                self.walk_expr_reads(cond);
                self.check_expr_type(cond, &NesType::Bool);
                self.check_block(then_block, state_names);
                for (cond, block) in else_ifs {
                    self.walk_expr_reads(cond);
                    self.check_expr_type(cond, &NesType::Bool);
                    self.check_block(block, state_names);
                }
                if let Some(block) = else_block {
                    self.check_block(block, state_names);
                }
            }
            Statement::While(cond, body, span) => {
                self.walk_expr_reads(cond);
                self.check_expr_type(cond, &NesType::Bool);
                let was_in_loop = self.in_loop;
                self.in_loop = true;
                self.check_block(body, state_names);
                self.in_loop = was_in_loop;
                // W0102: a `while true { ... }` (or the rarely-written
                // `while 1 { ... }`) that never breaks, returns,
                // transitions, or waits for a frame is an infinite
                // spin — same hazard as the bare `loop { ... }` below.
                if is_always_true(cond) && !block_can_exit_or_yield(body) {
                    self.diagnostics.push(
                        Diagnostic::warning(
                            ErrorCode::W0102,
                            "infinite loop with no break, return, transition, or wait_frame",
                            *span,
                        )
                        .with_help(
                            "add `wait_frame`, `break`, `return`, or `transition` somewhere in the body",
                        ),
                    );
                }
            }
            Statement::For {
                var,
                start,
                end,
                body,
                span,
            } => {
                // Evaluate start/end (both u8) for reads and type
                // checking, then register the loop variable as a u8
                // for the duration of the body.
                self.walk_expr_reads(start);
                self.walk_expr_reads(end);
                self.check_expr_type(start, &NesType::U8);
                self.check_expr_type(end, &NesType::U8);
                // Register the loop variable under the current
                // scope's qualified key so two `for i in 0..n`
                // loops in different functions get their own
                // per-function RAM slot.
                let loop_key = self.scoped_name(var);
                let was_shadowed = self.symbols.remove(&loop_key);
                self.symbols.insert(
                    loop_key.clone(),
                    Symbol {
                        name: loop_key.clone(),
                        sym_type: NesType::U8,
                        is_const: false,
                        span: *span,
                    },
                );
                // Synthesize a VarAllocation for the loop variable
                // so IR lowering / codegen can treat it like any
                // other u8 local.
                let loop_var_addr = self.allocate_ram(1, *span).unwrap_or(0x10);
                self.var_allocations.push(VarAllocation {
                    name: loop_key.clone(),
                    address: loop_var_addr,
                    size: 1,
                });
                // Loop variable is always "used" in the header.
                self.used_vars.insert(loop_key.clone());
                let was_in_loop = self.in_loop;
                self.in_loop = true;
                self.check_block(body, state_names);
                self.in_loop = was_in_loop;
                self.symbols.remove(&loop_key);
                if let Some(old) = was_shadowed {
                    self.symbols.insert(loop_key, old);
                }
            }
            Statement::Loop(body, span) => {
                let was_in_loop = self.in_loop;
                self.in_loop = true;
                self.check_block(body, state_names);
                self.in_loop = was_in_loop;
                // W0102: loop body must contain a break, return,
                // transition, or wait_frame — otherwise the NES spins
                // forever inside the loop and vblank never gets handled.
                if !block_can_exit_or_yield(body) {
                    self.diagnostics.push(Diagnostic::warning(
                        ErrorCode::W0102,
                        "infinite loop with no break, return, transition, or wait_frame",
                        *span,
                    ).with_help("add `wait_frame`, `break`, `return`, or `transition` somewhere in the body"));
                }
            }
            Statement::Transition(name, span) => {
                if !state_names.contains(&name.as_str()) {
                    self.diagnostics.push(Diagnostic::error(
                        ErrorCode::E0404,
                        format!("transition to undefined state '{name}'"),
                        *span,
                    ));
                }
            }
            Statement::Draw(draw) => {
                self.walk_expr_reads(&draw.x);
                self.walk_expr_reads(&draw.y);
                self.check_expr_type(&draw.x, &NesType::U8);
                self.check_expr_type(&draw.y, &NesType::U8);
                if let Some(frame) = &draw.frame {
                    self.walk_expr_reads(frame);
                    self.check_expr_type(frame, &NesType::U8);
                }
            }
            Statement::Return(Some(expr), span) => {
                self.walk_expr_reads(expr);
                if let Some(ret_ty) = self.current_return_type.clone() {
                    // Function with declared return type — check the value.
                    self.check_expr_type(expr, &ret_ty);
                } else if self.in_function_body {
                    // Function with no declared return type ("void"),
                    // but the return statement has a value.
                    self.diagnostics.push(Diagnostic::error(
                        ErrorCode::E0203,
                        "return value in function with no declared return type",
                        *span,
                    ));
                }
                // State handlers (`in_function_body == false`) accept
                // `return value` silently — the value is simply discarded.
            }
            Statement::Call(name, args, span) => {
                if is_intrinsic(name) {
                    self.check_intrinsic_args(name, args, *span);
                } else if self.symbols.contains_key(name) {
                    self.check_call_signature(name, args, *span);
                    // W0106: a call at statement position whose
                    // callee has a declared return type silently
                    // drops the value. Flag it so the author at
                    // least acknowledges the discard.
                    if matches!(self.function_return_types.get(name), Some(Some(_))) {
                        self.diagnostics.push(
                            Diagnostic::warning(
                                ErrorCode::W0106,
                                format!("return value of '{name}' is discarded"),
                                *span,
                            )
                            .with_help(
                                "bind the result to a variable (e.g. `var _result: u8 = f()`), \
                                 or remove the return type from the function if the value isn't useful",
                            ),
                        );
                    }
                } else {
                    self.diagnostics.push(Diagnostic::error(
                        ErrorCode::E0503,
                        format!("undefined function '{name}'"),
                        *span,
                    ));
                }
                for arg in args {
                    self.walk_expr_reads(arg);
                }
            }
            Statement::Scroll(x, y, _) => {
                self.walk_expr_reads(x);
                self.walk_expr_reads(y);
                self.check_expr_type(x, &NesType::U8);
                self.check_expr_type(y, &NesType::U8);
            }
            Statement::Break(span) => {
                if !self.in_loop {
                    self.diagnostics.push(Diagnostic::error(
                        ErrorCode::E0203,
                        "break outside of loop",
                        *span,
                    ));
                }
            }
            Statement::Continue(span) => {
                if !self.in_loop {
                    self.diagnostics.push(Diagnostic::error(
                        ErrorCode::E0203,
                        "continue outside of loop",
                        *span,
                    ));
                }
            }
            Statement::Return(None, span) => {
                // Bare `return` in a function with a declared return
                // type is an error — the caller expects a value.
                if self.in_function_body && self.current_return_type.is_some() {
                    self.diagnostics.push(Diagnostic::error(
                        ErrorCode::E0203,
                        "missing return value in function with declared return type",
                        *span,
                    ));
                }
            }
            Statement::WaitFrame(_) => {}
            Statement::CycleSprites(_) => {}
            Statement::SetPalette(name, span) => {
                if !self.palette_names.contains(name) {
                    self.diagnostics.push(Diagnostic::error(
                        ErrorCode::E0502,
                        format!("unknown palette '{name}'"),
                        *span,
                    ));
                }
            }
            Statement::LoadBackground(name, span) => {
                if !self.background_names.contains(name) {
                    self.diagnostics.push(Diagnostic::error(
                        ErrorCode::E0502,
                        format!("unknown background '{name}'"),
                        *span,
                    ));
                }
            }
            Statement::PaintRoom(name, span) => {
                if !self.room_names.contains(name) {
                    self.diagnostics.push(Diagnostic::error(
                        ErrorCode::E0502,
                        format!("unknown room '{name}'"),
                        *span,
                    ));
                }
            }
            Statement::DebugLog(args, _) => {
                for arg in args {
                    self.walk_expr_reads(arg);
                }
            }
            Statement::DebugAssert(cond, _) => {
                self.walk_expr_reads(cond);
                self.check_expr_type(cond, &NesType::Bool);
            }
            Statement::InlineAsm(_, _) | Statement::RawAsm(_, _) => {
                // Inline assembly is treated as an opaque block. The
                // codegen parses and validates the body; analysis has
                // nothing to check.
            }
            Statement::Play(name, span) => {
                // `play Name` is valid if the name refers to a
                // declared sfx block or to a builtin effect. Anything
                // else is an E0505 — the runtime driver needs a
                // known blob to point at, and silently accepting
                // bad names would hide typos.
                if !self.sfx_names.contains(name) && !crate::assets::is_builtin_sfx(name) {
                    self.diagnostics.push(
                        Diagnostic::error(ErrorCode::E0505, format!("unknown sfx '{name}'"), *span)
                            .with_help(
                                "declare one with `sfx Name { pitch: [..], volume: [..] }`, \
                         or use a builtin: coin, jump, hit, click, cancel, shoot, step",
                            ),
                    );
                }
            }
            Statement::StartMusic(name, span) => {
                if !self.music_names.contains(name) && !crate::assets::is_builtin_music(name) {
                    self.diagnostics.push(
                        Diagnostic::error(
                            ErrorCode::E0505,
                            format!("unknown music track '{name}'"),
                            *span,
                        )
                        .with_help(
                            "declare one with `music Name { notes: [..] }`, \
                         or use a builtin: theme, battle, victory, gameover",
                        ),
                    );
                }
            }
            Statement::StopMusic(_) => {
                // No arguments, nothing to validate.
            }
        }
    }

    fn lvalue_type(&self, lvalue: &LValue, _span: Span) -> Option<NesType> {
        match lvalue {
            LValue::Var(name) => self.resolve_symbol(name).map(|s| s.sym_type.clone()),
            LValue::ArrayIndex(name, _) => {
                self.resolve_symbol(name)
                    .and_then(|sym| match &sym.sym_type {
                        NesType::Array(elem, _) => Some(elem.as_ref().clone()),
                        _ => None,
                    })
            }
            LValue::Field(name, field) => {
                let base_key = self.resolve_key(name);
                let full_name = format!("{base_key}.{field}");
                self.symbols.get(&full_name).map(|s| s.sym_type.clone())
            }
        }
    }

    /// Check that a call site matches the function's declared signature:
    /// argument count matches the parameter count, and each argument's
    /// inferred type is compatible with the declared parameter type.
    fn check_call_signature(&mut self, name: &str, args: &[Expr], span: Span) {
        let Some(params) = self.function_signatures.get(name).cloned() else {
            return;
        };
        if params.len() != args.len() {
            self.diagnostics.push(Diagnostic::error(
                ErrorCode::E0203,
                format!(
                    "wrong number of arguments to '{name}': expected {}, got {}",
                    params.len(),
                    args.len()
                ),
                span,
            ));
            return;
        }
        for (param_ty, arg) in params.iter().zip(args.iter()) {
            self.check_expr_type(arg, param_ty);
        }
    }

    fn check_expr_type(&mut self, expr: &Expr, expected: &NesType) {
        let actual = self.infer_type(expr);
        if let Some(actual) = actual {
            // Allow numeric comparisons to produce bool
            if *expected == NesType::Bool && actual == NesType::Bool {
                return;
            }
            // For M1: be lenient about integer types in conditions
            // button reads produce bool
            if *expected == NesType::Bool {
                match expr {
                    Expr::ButtonRead(..)
                    | Expr::ButtonEdge(..)
                    | Expr::BinaryOp(
                        _,
                        BinOp::Eq
                        | BinOp::NotEq
                        | BinOp::Lt
                        | BinOp::Gt
                        | BinOp::LtEq
                        | BinOp::GtEq,
                        _,
                        _,
                    )
                    | Expr::UnaryOp(UnaryOp::Not, _, _)
                    | Expr::BinaryOp(_, BinOp::And | BinOp::Or, _, _) => return,
                    _ => {}
                }
            }
            if actual != *expected {
                // Allow implicit u8/i8/u16 in assignments for M1 simplicity
                if is_integer_type(&actual) && is_integer_type(expected) {
                    return;
                }
                self.diagnostics.push(
                    Diagnostic::error(
                        ErrorCode::E0201,
                        format!("type mismatch: expected {expected}, found {actual}"),
                        expr.span(),
                    )
                    .with_help(format!("use 'as {expected}' for explicit conversion")),
                );
            }
        }
    }

    fn infer_type(&self, expr: &Expr) -> Option<NesType> {
        match expr {
            Expr::IntLiteral(v, _) => {
                if *v <= 255 {
                    Some(NesType::U8)
                } else {
                    Some(NesType::U16)
                }
            }
            Expr::BoolLiteral(_, _) => Some(NesType::Bool),
            Expr::Ident(name, _) => self.resolve_symbol(name).map(|s| s.sym_type.clone()),
            Expr::ButtonRead(_, _, _) | Expr::ButtonEdge(_, _, _, _) => Some(NesType::Bool),
            Expr::BinaryOp(_, op, _, _) => match op {
                BinOp::Eq
                | BinOp::NotEq
                | BinOp::Lt
                | BinOp::Gt
                | BinOp::LtEq
                | BinOp::GtEq
                | BinOp::And
                | BinOp::Or => Some(NesType::Bool),
                _ => Some(NesType::U8), // Simplified for M1
            },
            Expr::UnaryOp(UnaryOp::Not, _, _) => Some(NesType::Bool),
            Expr::UnaryOp(_, _, _) => Some(NesType::U8),
            Expr::Call(name, _, _) => match name.as_str() {
                // PRNG intrinsics: rand8 returns u8, rand16 returns u16.
                "rand8" => Some(NesType::U8),
                "rand16" => Some(NesType::U16),
                "collides_at" => Some(NesType::Bool),
                _ => Some(NesType::U8), // Simplified for M1
            },
            Expr::ArrayIndex(name, _, _) => {
                self.resolve_symbol(name).and_then(|s| match &s.sym_type {
                    NesType::Array(elem, _) => Some(elem.as_ref().clone()),
                    _ => None,
                })
            }
            Expr::FieldAccess(name, field, _) => {
                let base_key = self.resolve_key(name);
                let full_name = format!("{base_key}.{field}");
                self.symbols.get(&full_name).map(|s| s.sym_type.clone())
            }
            Expr::ArrayLiteral(_, _) => Some(NesType::U8), // element type inferred from context
            Expr::Cast(_, target, _) => Some(target.clone()),
            Expr::StructLiteral(name, _, _) => Some(NesType::Struct(name.clone())),
            // Both `debug.frame_overrun_count()` and
            // `debug.frame_overran()` return a single byte, so they
            // type-check as u8 even though the latter is conceptually
            // a flag (0 / 1). Treating it as u8 lets it work in
            // `debug.assert(!debug.frame_overran())` where the
            // analyzer's bool-leniency rule for `!` already kicks in.
            Expr::DebugCall(_, _, _) => Some(NesType::U8),
        }
    }
}

/// Collect every state name mentioned in a transition statement inside the
/// given state's handlers and append them to `queue`. Used by the W0104
/// unreachable-state check.
fn collect_transitions_from_state(state: &StateDecl, queue: &mut Vec<String>) {
    if let Some(block) = &state.on_enter {
        collect_transitions_block(block, queue);
    }
    if let Some(block) = &state.on_exit {
        collect_transitions_block(block, queue);
    }
    if let Some(block) = &state.on_frame {
        collect_transitions_block(block, queue);
    }
    for (_, block) in &state.on_scanline {
        collect_transitions_block(block, queue);
    }
}

fn collect_transitions_block(block: &Block, queue: &mut Vec<String>) {
    for stmt in &block.statements {
        collect_transitions_stmt(stmt, queue);
    }
}

fn collect_transitions_stmt(stmt: &Statement, queue: &mut Vec<String>) {
    match stmt {
        Statement::Transition(name, _) => queue.push(name.clone()),
        Statement::If(_, then_b, elifs, else_b, _) => {
            collect_transitions_block(then_b, queue);
            for (_, b) in elifs {
                collect_transitions_block(b, queue);
            }
            if let Some(b) = else_b {
                collect_transitions_block(b, queue);
            }
        }
        Statement::While(_, body, _) | Statement::Loop(body, _) => {
            collect_transitions_block(body, queue);
        }
        Statement::For { body, .. } => {
            collect_transitions_block(body, queue);
        }
        _ => {}
    }
}

/// Walk a block and collect `(y, x, span)` tuples for every literal
/// -coordinate draw it contains. Metasprite draws expand to one
/// tuple per tile using the metasprite's `dx`/`dy` offsets; plain
/// sprites contribute exactly one tuple at the literal `(x, y)`.
/// Draws with a non-literal coordinate are skipped — static
/// analysis can't know where they land.
///
/// Recurses through `if`/`while`/`for`/`loop` bodies and counts
/// every branch as if it always fires. This conservatively
/// over-counts programs that stagger draws across mutually
/// exclusive branches, but it matches the worst case the PPU can
/// see on any given frame.
fn collect_literal_draws(
    block: &Block,
    metasprites: &HashMap<&str, &MetaspriteDecl>,
    out: &mut Vec<(u8, u8, Span)>,
) {
    for stmt in &block.statements {
        collect_literal_draws_stmt(stmt, metasprites, out);
    }
}

fn collect_literal_draws_stmt(
    stmt: &Statement,
    metasprites: &HashMap<&str, &MetaspriteDecl>,
    out: &mut Vec<(u8, u8, Span)>,
) {
    match stmt {
        Statement::Draw(draw) => {
            let (Expr::IntLiteral(x, _), Expr::IntLiteral(y, _)) = (&draw.x, &draw.y) else {
                return;
            };
            // Literals that don't fit in u8 would already be caught
            // by the type checker; bail out here rather than risk
            // double-reporting.
            if *x > 255 || *y > 255 {
                return;
            }
            let base_x = *x as u8;
            let base_y = *y as u8;
            if let Some(ms) = metasprites.get(draw.sprite_name.as_str()) {
                // Metasprite: one slot per tile. Share the original
                // draw-site span so the diagnostic labels point at
                // user-authored source, not invented offsets.
                for i in 0..ms.dx.len() {
                    let tile_x = base_x.wrapping_add(ms.dx[i]);
                    let tile_y = base_y.wrapping_add(ms.dy[i]);
                    out.push((tile_y, tile_x, draw.span));
                }
            } else {
                out.push((base_y, base_x, draw.span));
            }
        }
        Statement::If(_, then_b, elifs, else_b, _) => {
            collect_literal_draws(then_b, metasprites, out);
            for (_, b) in elifs {
                collect_literal_draws(b, metasprites, out);
            }
            if let Some(b) = else_b {
                collect_literal_draws(b, metasprites, out);
            }
        }
        Statement::While(_, body, _) | Statement::Loop(body, _) => {
            collect_literal_draws(body, metasprites, out);
        }
        Statement::For { body, .. } => {
            collect_literal_draws(body, metasprites, out);
        }
        _ => {}
    }
}

/// Collect all function/call names from a block.
fn collect_calls(block: &Block) -> Vec<String> {
    let mut calls = Vec::new();
    for stmt in &block.statements {
        collect_calls_stmt(stmt, &mut calls);
    }
    calls
}

fn collect_calls_stmt(stmt: &Statement, calls: &mut Vec<String>) {
    match stmt {
        Statement::Call(name, args, _) => {
            calls.push(name.clone());
            for arg in args {
                collect_calls_expr(arg, calls);
            }
        }
        Statement::If(cond, then_b, elifs, else_b, _) => {
            collect_calls_expr(cond, calls);
            collect_calls_block(then_b, calls);
            for (c, b) in elifs {
                collect_calls_expr(c, calls);
                collect_calls_block(b, calls);
            }
            if let Some(b) = else_b {
                collect_calls_block(b, calls);
            }
        }
        Statement::While(cond, body, _) => {
            collect_calls_expr(cond, calls);
            collect_calls_block(body, calls);
        }
        Statement::Loop(body, _) => {
            collect_calls_block(body, calls);
        }
        Statement::For {
            start, end, body, ..
        } => {
            collect_calls_expr(start, calls);
            collect_calls_expr(end, calls);
            collect_calls_block(body, calls);
        }
        Statement::Assign(_, _, expr, _) => {
            collect_calls_expr(expr, calls);
        }
        Statement::VarDecl(var) => {
            if let Some(init) = &var.init {
                collect_calls_expr(init, calls);
            }
        }
        Statement::Return(Some(expr), _) => {
            collect_calls_expr(expr, calls);
        }
        Statement::Draw(draw) => {
            collect_calls_expr(&draw.x, calls);
            collect_calls_expr(&draw.y, calls);
            if let Some(f) = &draw.frame {
                collect_calls_expr(f, calls);
            }
        }
        Statement::Scroll(x, y, _) => {
            collect_calls_expr(x, calls);
            collect_calls_expr(y, calls);
        }
        Statement::DebugLog(args, _) => {
            for arg in args {
                collect_calls_expr(arg, calls);
            }
        }
        Statement::DebugAssert(cond, _) => {
            collect_calls_expr(cond, calls);
        }
        Statement::Return(None, _)
        | Statement::Transition(_, _)
        | Statement::WaitFrame(_)
        | Statement::CycleSprites(_)
        | Statement::Break(_)
        | Statement::Continue(_)
        | Statement::InlineAsm(_, _)
        | Statement::RawAsm(_, _)
        | Statement::Play(_, _)
        | Statement::StartMusic(_, _)
        | Statement::StopMusic(_)
        | Statement::SetPalette(_, _)
        | Statement::LoadBackground(_, _)
        | Statement::PaintRoom(_, _) => {}
    }
}

fn collect_calls_block(block: &Block, calls: &mut Vec<String>) {
    for stmt in &block.statements {
        collect_calls_stmt(stmt, calls);
    }
}

/// True if the program references any of the VRAM-buffer
/// intrinsics anywhere user code can reach. Used at analyzer
/// init time to bump the user-RAM bump pointer past the buffer
/// region (`$0400-$04FF`) so user globals don't alias the
/// runtime's ring. Walks both function bodies and state handlers.
fn program_uses_vram_buf(program: &Program) -> bool {
    fn block_uses(block: &Block) -> bool {
        let mut calls = Vec::new();
        collect_calls_block(block, &mut calls);
        calls
            .iter()
            .any(|c| matches!(c.as_str(), "nt_set" | "nt_attr" | "nt_fill_h"))
    }
    for fun in &program.functions {
        if block_uses(&fun.body) {
            return true;
        }
    }
    for state in &program.states {
        for b in [&state.on_enter, &state.on_exit, &state.on_frame]
            .into_iter()
            .flatten()
        {
            if block_uses(b) {
                return true;
            }
        }
        for (_, b) in &state.on_scanline {
            if block_uses(b) {
                return true;
            }
        }
    }
    false
}

/// Return true if the given block contains any statement that can
/// either exit the enclosing loop (`break`, `return`, `transition`)
/// or yield control back to the frame loop (`wait_frame`).
///
/// This is used by the W0102 check to decide whether an otherwise-
/// unbounded `loop { }` is actually an infinite spin. We recurse into
/// nested control-flow blocks so that a `break` inside a conditional
/// body still counts as "can exit".
/// True if the expression is a small integer literal — used to avoid
/// emitting W0101 for multiply/divide where at least one operand can be
/// handled by strength reduction (e.g. `x * 2`, `x / 4`).
fn is_small_constant(expr: &Expr) -> bool {
    matches!(expr, Expr::IntLiteral(_, _))
}

/// True if `name` is a built-in intrinsic function recognized by the
/// compiler. Intrinsics don't need a declaration and may have
/// special codegen (e.g. \`poke\` / \`peek\` write to raw addresses).
fn is_intrinsic(name: &str) -> bool {
    matches!(
        name,
        "poke"
            | "peek"
            | "rand8"
            | "rand16"
            | "seed_rand"
            | "set_palette_brightness"
            | "fade_out"
            | "fade_in"
            | "sprite_0_split"
            | "nt_set"
            | "nt_attr"
            | "nt_fill_h"
            | "collides_at"
    )
}

/// True if `name` is an intrinsic that does not produce a usable
/// return value. These are valid only at statement position;
/// using them as an expression is a type error caught by the
/// analyzer so the codegen / linker never sees a stray
/// `Expr::Call` for one of them.
fn is_void_intrinsic(name: &str) -> bool {
    matches!(
        name,
        "poke"
            | "seed_rand"
            | "set_palette_brightness"
            | "fade_out"
            | "fade_in"
            | "sprite_0_split"
            | "nt_set"
            | "nt_attr"
            | "nt_fill_h"
    )
}

/// True if `name` is one of the NES controller's eight buttons.
/// Mirrors the `button_mask` table in `ir::lowering`.
fn is_known_button(name: &str) -> bool {
    matches!(
        name,
        "a" | "b" | "select" | "start" | "up" | "down" | "left" | "right"
    )
}

impl Analyzer {
    /// Validate the arguments to a built-in intrinsic. Emits
    /// diagnostics for mismatched arity or non-constant addresses.
    fn check_intrinsic_args(&mut self, name: &str, args: &[Expr], span: Span) {
        match name {
            "poke" if args.len() != 2 => {
                self.diagnostics.push(Diagnostic::error(
                    ErrorCode::E0203,
                    format!(
                        "`poke` takes exactly 2 arguments (addr, value), got {}",
                        args.len()
                    ),
                    span,
                ));
            }
            "peek" if args.len() != 1 => {
                self.diagnostics.push(Diagnostic::error(
                    ErrorCode::E0203,
                    format!("`peek` takes exactly 1 argument (addr), got {}", args.len()),
                    span,
                ));
            }
            "rand8" | "rand16" if !args.is_empty() => {
                self.diagnostics.push(Diagnostic::error(
                    ErrorCode::E0203,
                    format!("`{name}` takes no arguments, got {}", args.len()),
                    span,
                ));
            }
            "seed_rand" if args.len() != 1 => {
                self.diagnostics.push(Diagnostic::error(
                    ErrorCode::E0203,
                    format!(
                        "`seed_rand` takes exactly 1 argument (seed: u16), got {}",
                        args.len()
                    ),
                    span,
                ));
            }
            "set_palette_brightness" if args.len() != 1 => {
                self.diagnostics.push(Diagnostic::error(
                    ErrorCode::E0203,
                    format!(
                        "`set_palette_brightness` takes exactly 1 argument (level: u8 0..8), got {}",
                        args.len()
                    ),
                    span,
                ));
            }
            "fade_out" | "fade_in" if args.len() != 1 => {
                self.diagnostics.push(Diagnostic::error(
                    ErrorCode::E0203,
                    format!(
                        "`{name}` takes exactly 1 argument (step_frames: u8), got {}",
                        args.len()
                    ),
                    span,
                ));
            }
            "sprite_0_split" if args.len() != 2 => {
                self.diagnostics.push(Diagnostic::error(
                    ErrorCode::E0203,
                    format!(
                        "`sprite_0_split` takes exactly 2 arguments (scroll_x: u8, scroll_y: u8), got {}",
                        args.len()
                    ),
                    span,
                ));
            }
            "nt_set" | "nt_attr" if args.len() != 3 => {
                self.diagnostics.push(Diagnostic::error(
                    ErrorCode::E0203,
                    format!(
                        "`{name}` takes exactly 3 arguments (x: u8, y: u8, value: u8), got {}",
                        args.len()
                    ),
                    span,
                ));
            }
            "nt_fill_h" if args.len() != 4 => {
                self.diagnostics.push(Diagnostic::error(
                    ErrorCode::E0203,
                    format!(
                        "`nt_fill_h` takes exactly 4 arguments (x: u8, y: u8, len: u8, tile: u8), got {}",
                        args.len()
                    ),
                    span,
                ));
            }
            "collides_at" if args.len() != 2 => {
                self.diagnostics.push(Diagnostic::error(
                    ErrorCode::E0203,
                    format!(
                        "`collides_at` takes exactly 2 arguments (x: u8, y: u8), got {}",
                        args.len()
                    ),
                    span,
                ));
            }
            _ => {}
        }
    }
}

/// True if this statement unconditionally ends block execution —
/// subsequent statements in the same block cannot be reached.
fn stmt_is_terminator(stmt: &Statement) -> bool {
    matches!(
        stmt,
        Statement::Return(_, _)
            | Statement::Break(_)
            | Statement::Continue(_)
            | Statement::Transition(_, _)
    )
}

fn block_can_exit_or_yield(block: &Block) -> bool {
    block.statements.iter().any(stmt_can_exit_or_yield)
}

/// True if `expr` is an always-true constant condition — i.e. the
/// literal `true`, or a non-zero integer literal. Used by W0102 so
/// `while true { ... }` gets the same treatment as bare `loop`.
fn is_always_true(expr: &Expr) -> bool {
    match expr {
        Expr::BoolLiteral(true, _) => true,
        Expr::IntLiteral(v, _) => *v != 0,
        _ => false,
    }
}

fn stmt_can_exit_or_yield(stmt: &Statement) -> bool {
    match stmt {
        Statement::Break(_)
        | Statement::Return(_, _)
        | Statement::Transition(_, _)
        | Statement::WaitFrame(_) => true,
        Statement::If(_, then_b, elifs, else_b, _) => {
            block_can_exit_or_yield(then_b)
                || elifs.iter().any(|(_, b)| block_can_exit_or_yield(b))
                || else_b.as_ref().is_some_and(block_can_exit_or_yield)
        }
        Statement::While(_, body, _) | Statement::Loop(body, _) => {
            // A nested loop with a wait_frame inside still yields
            // control, so check its body recursively.
            block_can_exit_or_yield(body)
        }
        Statement::For { body, .. } => block_can_exit_or_yield(body),
        _ => false,
    }
}

fn collect_calls_expr(expr: &Expr, calls: &mut Vec<String>) {
    match expr {
        Expr::Call(name, args, _) => {
            calls.push(name.clone());
            for arg in args {
                collect_calls_expr(arg, calls);
            }
        }
        Expr::BinaryOp(lhs, _, rhs, _) => {
            collect_calls_expr(lhs, calls);
            collect_calls_expr(rhs, calls);
        }
        Expr::UnaryOp(_, inner, _) => {
            collect_calls_expr(inner, calls);
        }
        Expr::ArrayIndex(_, idx, _) => {
            collect_calls_expr(idx, calls);
        }
        Expr::ArrayLiteral(elems, _) => {
            for e in elems {
                collect_calls_expr(e, calls);
            }
        }
        Expr::StructLiteral(_, fields, _) => {
            for (_, e) in fields {
                collect_calls_expr(e, calls);
            }
        }
        Expr::Cast(inner, _, _) => {
            collect_calls_expr(inner, calls);
        }
        Expr::DebugCall(_, args, _) => {
            // Debug calls aren't user-defined functions, so we
            // don't add them to the call graph — but their
            // argument expressions may still mention real calls
            // we should track.
            for arg in args {
                collect_calls_expr(arg, calls);
            }
        }
        Expr::IntLiteral(_, _)
        | Expr::BoolLiteral(_, _)
        | Expr::Ident(_, _)
        | Expr::FieldAccess(_, _, _)
        | Expr::ButtonRead(_, _, _)
        | Expr::ButtonEdge(_, _, _, _) => {}
    }
}

/// Detect cycles in the call graph using DFS. Returns the names of all
/// functions that participate in a cycle (direct or mutual recursion).
fn detect_recursion(graph: &HashMap<String, Vec<String>>) -> Vec<String> {
    let mut recursive = Vec::new();
    let mut visited = HashSet::new();
    let mut on_stack = HashSet::new();

    for node in graph.keys() {
        if !visited.contains(node) {
            detect_recursion_dfs(node, graph, &mut visited, &mut on_stack, &mut recursive);
        }
    }

    recursive.sort();
    recursive.dedup();
    recursive
}

fn detect_recursion_dfs(
    node: &str,
    graph: &HashMap<String, Vec<String>>,
    visited: &mut HashSet<String>,
    on_stack: &mut HashSet<String>,
    recursive: &mut Vec<String>,
) {
    visited.insert(node.to_string());
    on_stack.insert(node.to_string());

    if let Some(callees) = graph.get(node) {
        for callee in callees {
            if on_stack.contains(callee) {
                // Found a cycle — mark the callee (the one we recursed back to)
                recursive.push(callee.clone());
            } else if !visited.contains(callee) {
                detect_recursion_dfs(callee, graph, visited, on_stack, recursive);
            }
        }
    }

    on_stack.remove(node);
}

/// Compute the maximum call depth starting from a given node in the call graph.
/// Returns `None` if a cycle is encountered (handled separately by recursion detection).
fn compute_depth(
    node: &str,
    graph: &HashMap<String, Vec<String>>,
    visited: &mut HashSet<String>,
    cache: &mut HashMap<String, u32>,
) -> u32 {
    if let Some(&depth) = cache.get(node) {
        return depth;
    }
    if visited.contains(node) {
        // Cycle — return 0 to avoid infinite recursion; the cycle itself
        // is flagged by detect_recursion.
        return 0;
    }
    visited.insert(node.to_string());
    let mut max_child: u32 = 0;
    if let Some(callees) = graph.get(node) {
        for callee in callees {
            let child = compute_depth(callee, graph, visited, cache);
            max_child = max_child.max(child);
        }
    }
    visited.remove(node);
    let depth = if graph.get(node).is_none_or(Vec::is_empty) {
        0
    } else {
        1 + max_child
    };
    cache.insert(node.to_string(), depth);
    depth
}

/// Compute the byte size of a type. Struct types are looked up in
/// `struct_sizes`; if absent, returns 0 (the analyzer will have
/// reported an error already).
fn type_size_with(t: &NesType, struct_sizes: &HashMap<String, u16>) -> u16 {
    match t {
        NesType::U8 | NesType::I8 | NesType::Bool => 1,
        NesType::U16 | NesType::I16 => 2,
        NesType::Array(elem, count) => type_size_with(elem, struct_sizes) * count,
        NesType::Struct(name) => struct_sizes.get(name).copied().unwrap_or(0),
    }
}

fn is_integer_type(t: &NesType) -> bool {
    matches!(t, NesType::U8 | NesType::I8 | NesType::U16 | NesType::I16)
}
