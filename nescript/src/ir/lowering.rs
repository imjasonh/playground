use std::collections::{HashMap, HashSet};

use super::*;
use crate::analyzer::AnalysisResult;
use crate::parser::ast::*;

/// Marker prefix the lowering prepends to the body of a `raw asm`
/// block, telling the codegen to skip `{var}` substitution. Uses
/// NUL characters so no normal source text can spoof it.
pub const RAW_ASM_PREFIX: &str = "\0RAW\0";

/// Lower a parsed & analyzed program into IR.
pub fn lower(program: &Program, analysis: &AnalysisResult) -> IrProgram {
    let mut ctx = LoweringContext::new(analysis);
    ctx.lower_program(program);
    ctx.finish()
}

struct LoweringContext {
    functions: Vec<IrFunction>,
    globals: Vec<IrGlobal>,
    rom_data: Vec<IrRomBlock>,
    var_map: HashMap<String, VarId>,
    const_values: HashMap<String, u16>,
    /// Type of each named variable (resolved from the analyzer's
    /// symbol table). Used to decide between 8-bit and 16-bit IR
    /// ops for identifier reads/writes and binary operations.
    var_types: HashMap<String, NesType>,
    /// Current local scope prefix — mirrors the analyzer's field
    /// of the same name. While lowering a function or handler
    /// body this is `Some("<func_name>")` (or `Some("State__frame")`,
    /// etc), and `get_or_create_var` prepends
    /// `"__local__{prefix}__"` to any bare identifier lookup so
    /// function-local vars resolve to the scoped entry the
    /// analyzer registered for them. `None` outside of any body.
    current_scope_prefix: Option<String>,
    /// Captured inline function bodies. Populated by
    /// `capture_inline_bodies` before any lowering runs. Each
    /// entry is keyed by function name and holds the parameter
    /// list plus the shape of the body (see [`InlineBody`]).
    /// Call sites targeting a name in this map expand inline:
    /// each argument is lowered to a temp, the temps are
    /// registered as substitutions for the parameter names,
    /// and the body is lowered into the caller's current block
    /// in place of a `Call` op. See `try_inline_call_expr` /
    /// `try_inline_call_stmt` below; the feature was added on
    /// the War bug-cleanup branch (see `git log`).
    inline_bodies: HashMap<String, CapturedInline>,
    /// Substitution stack for nested inline expansions. The top
    /// frame is the active substitution map — `Expr::Ident(name)`
    /// lookups check it first and, if the name is present, use
    /// the stored IR temp directly without emitting any load op.
    /// Nested inlines push a fresh frame on entry and pop it on
    /// exit so an inline body calling another inline sees the
    /// inner function's parameter substitutions, not its
    /// caller's.
    inline_subs_stack: Vec<HashMap<String, IrTemp>>,
    /// Parallel to `inline_subs_stack`: maps each parameter
    /// name to the constant value the call site passed for it,
    /// when that arg was a compile-time constant. Used by the
    /// `Statement::InlineAsm` lowering path so that `{param}`
    /// inside an `inline fun` body can be substituted with
    /// `#$<value>` at expansion time. Without this, the codegen's
    /// `substitute_asm_vars` would resolve `{param}` against the
    /// caller's analyzer scope and never find a match — `LDX
    /// {dst}` would land in the asm parser as a literal token
    /// and fail to assemble.
    inline_const_args_stack: Vec<HashMap<String, u8>>,
    next_var_id: u32,
    next_temp: u32,
    next_block: u32,
    // Current function being built
    current_blocks: Vec<IrBasicBlock>,
    current_ops: Vec<IrOp>,
    current_label: String,
    current_locals: Vec<IrLocal>,
    // Loop context for break/continue
    loop_stack: Vec<LoopContext>,
    // State metadata captured from the AST
    state_names: Vec<String>,
    start_state: String,
    /// Map from a byte temp (used as the "low byte" of a wide
    /// value) to the matching high byte temp. Temps not in the
    /// map are plain 8-bit byte temps. Populated by
    /// `lower_expr_wide` when it produces a u16 result; consumed
    /// by binary-op, compare, and assignment lowering when they
    /// need to decide between `Add`/`Add16`, etc.
    wide_hi: HashMap<IrTemp, IrTemp>,
    /// Temps whose source value is a signed integer (`i8` / `i16`).
    /// Populated by the `LoadVar` / cast / negate / sign-extended-
    /// literal paths and propagated through arithmetic in
    /// `lower_binop`. Consumed at compare time to pick between
    /// `Signedness::Unsigned` and `Signedness::Signed`, and by
    /// `widen()` to decide whether the synthesized high byte should
    /// be `LoadImm 0` (zero-extension) or [`IrOp::SignExtend`]
    /// (sign-extension). Tracking the signedness on the temp itself —
    /// rather than re-deriving it from the AST at every consumer —
    /// keeps the consumer code matched to the existing `is_wide` /
    /// `widen` shape, and means a temp can carry a different
    /// signedness than its source variable when the user inserts an
    /// explicit `as` cast.
    signed_temps: HashSet<IrTemp>,
    /// Captured metasprite declarations keyed by name. When a
    /// `Statement::Draw` names a metasprite (rather than a flat
    /// sprite), the lowering expands it inline into one
    /// [`IrOp::DrawSprite`] per tile, with x/y offsets folded into
    /// the per-tile coordinates and the metasprite's `frame:`
    /// entry used as the literal frame index. Storing the lookup
    /// here keeps the per-statement lowering simple and avoids
    /// having to thread the program through every helper.
    metasprites: HashMap<String, MetaspriteInfo>,
    /// When true (driven by `game { sprite_flicker: true }`), the
    /// lowerer injects an `IrOp::CycleSprites` op at the top of
    /// every `on frame` handler, giving the runtime the same
    /// rotating-OAM effect as an explicit `cycle_sprites` call
    /// without requiring user code to opt in at every site.
    auto_sprite_flicker: bool,
}

/// A captured `inline fun` body that the lowerer can splice in
/// at each call site. Two flavours are recognised:
///
/// - **Expression**: the function body is exactly
///   `{ return <expr> }`. The return expression can be lowered
///   into either a statement context (result discarded) or an
///   expression context (result used).
/// - **Void**: the function has no return type and its body is
///   a sequence of plain statements (no `return`, no loops, no
///   conditionals). The statements can only be spliced into
///   statement contexts. This is the shape of helpers like
///   `set_phase(p) { phase = p; phase_timer = 0 }`.
///
/// Anything more exotic (early returns inside `if`, loops,
/// nested blocks, recursive inlines, etc.) is not captured and
/// compiles as a regular `JSR` call, with no warning since
/// declining to inline is always a correct fallback.
#[derive(Debug, Clone)]
enum InlineBody {
    Expression(Expr),
    Void(Vec<Statement>),
}

/// Captured inline function metadata: parameter list plus the
/// shape of the body. See `InlineBody` and
/// `LoweringContext::inline_bodies`.
#[derive(Debug, Clone)]
struct CapturedInline {
    params: Vec<Param>,
    body: InlineBody,
}

#[derive(Debug, Clone)]
struct MetaspriteInfo {
    sprite_name: String,
    dx: Vec<u8>,
    dy: Vec<u8>,
    frame: Vec<u8>,
}

struct LoopContext {
    continue_label: String,
    break_label: String,
}

impl LoweringContext {
    fn new(analysis: &AnalysisResult) -> Self {
        let mut var_map = HashMap::new();
        let mut next_var_id = 0u32;

        // Pre-register all allocated variables
        for alloc in &analysis.var_allocations {
            var_map.insert(alloc.name.clone(), VarId(next_var_id));
            next_var_id += 1;
        }

        // Capture the type of each named variable from the
        // analyzer's symbol table. This lets the lowering decide
        // whether an identifier read should expand to a Byte or
        // Word value — which in turn controls whether binary ops
        // emit 8-bit or 16-bit IR.
        let mut var_types = HashMap::new();
        for (name, sym) in &analysis.symbols {
            var_types.insert(name.clone(), sym.sym_type.clone());
        }

        Self {
            functions: Vec::new(),
            globals: Vec::new(),
            rom_data: Vec::new(),
            var_map,
            const_values: HashMap::new(),
            var_types,
            current_scope_prefix: None,
            inline_bodies: HashMap::new(),
            inline_subs_stack: Vec::new(),
            inline_const_args_stack: Vec::new(),
            next_var_id,
            next_temp: 0,
            next_block: 0,
            current_blocks: Vec::new(),
            current_ops: Vec::new(),
            current_label: String::new(),
            current_locals: Vec::new(),
            loop_stack: Vec::new(),
            state_names: Vec::new(),
            start_state: String::new(),
            wide_hi: HashMap::new(),
            signed_temps: HashSet::new(),
            metasprites: HashMap::new(),
            auto_sprite_flicker: false,
        }
    }

    fn fresh_temp(&mut self) -> IrTemp {
        let t = IrTemp(self.next_temp);
        self.next_temp += 1;
        t
    }

    fn fresh_label(&mut self, prefix: &str) -> String {
        self.next_block += 1;
        format!("{prefix}_{}", self.next_block)
    }

    /// Resolve a user-written identifier to the scoped key used by
    /// the symbol table. Mirrors `Analyzer::resolve_key`: tries the
    /// current function/handler's qualified key first, falls back
    /// to the bare key for globals / consts / enum variants /
    /// state-level vars / function names.
    fn scoped_key(&self, name: &str) -> String {
        if let Some(prefix) = &self.current_scope_prefix {
            let qualified = format!("__local__{prefix}__{name}");
            if self.var_map.contains_key(&qualified) || self.var_types.contains_key(&qualified) {
                return qualified;
            }
        }
        name.to_string()
    }

    fn get_or_create_var(&mut self, name: &str) -> VarId {
        let key = self.scoped_key(name);
        if let Some(&id) = self.var_map.get(&key) {
            return id;
        }
        let id = VarId(self.next_var_id);
        self.next_var_id += 1;
        self.var_map.insert(key, id);
        id
    }

    /// Walk the program and capture every `inline fun` whose
    /// body matches one of the shapes the lowerer can splice
    /// in at call sites. Two shapes are recognised:
    ///
    /// 1. **Single-return-expression**: the function has a
    ///    declared return type and its body is exactly
    ///    `{ return <expr> }`. Lowered as `InlineBody::Expression`
    ///    — usable in both expression and statement contexts.
    /// 2. **Void multi-statement**: the function has no return
    ///    type and its body is a sequence of plain statements
    ///    (assigns, calls, draws — no control flow, no
    ///    `return`). Lowered as `InlineBody::Void` — usable
    ///    only in statement contexts.
    ///
    /// Anything else (conditional early returns, loops,
    /// block-nested `if`s, etc.) is silently declined and the
    /// function compiles as a regular `JSR` call. Users who
    /// want their `inline fun` inlined can check the
    /// `--asm-dump` output; declining is always correct.
    fn capture_inline_bodies(&mut self, program: &Program) {
        for fun in &program.functions {
            if !fun.is_inline {
                continue;
            }
            // Defer to the shared `can_inline_fun` helper so the
            // analyzer's W0110 check and this capture pass agree
            // on exactly which bodies are splicable — any drift
            // between the two would either swallow real bugs
            // (lower inlines a body the analyzer thinks it
            // wouldn't) or emit false-positive warnings (analyzer
            // warns on something the lowerer actually inlines).
            if !can_inline_fun(fun.return_type.as_ref(), &fun.body) {
                continue;
            }
            // Single-return-expression shape.
            if fun.return_type.is_some() && fun.body.statements.len() == 1 {
                if let Statement::Return(Some(expr), _) = &fun.body.statements[0] {
                    self.inline_bodies.insert(
                        fun.name.clone(),
                        CapturedInline {
                            params: fun.params.clone(),
                            body: InlineBody::Expression(expr.clone()),
                        },
                    );
                    continue;
                }
            }
            // Void multi-statement shape: no return type, every
            // body statement is splicable. The helper already
            // checked both conditions so we just clone.
            self.inline_bodies.insert(
                fun.name.clone(),
                CapturedInline {
                    params: fun.params.clone(),
                    body: InlineBody::Void(fun.body.statements.clone()),
                },
            );
        }
    }

    /// Inline a call to `name` in expression context and
    /// return the result temp. Returns `None` if the target
    /// isn't in `inline_bodies` or is a void-body inline that
    /// can't produce a value.
    fn try_inline_call_expr(&mut self, name: &str, args: &[Expr]) -> Option<IrTemp> {
        let captured = self.inline_bodies.get(name).cloned()?;
        let InlineBody::Expression(return_expr) = &captured.body else {
            return None;
        };
        if captured.params.len() != args.len() {
            return None;
        }
        let arg_temps: Vec<IrTemp> = args.iter().map(|a| self.lower_expr(a)).collect();
        let mut frame = HashMap::new();
        for (param, temp) in captured.params.iter().zip(arg_temps.iter()) {
            frame.insert(param.name.clone(), *temp);
        }
        self.inline_subs_stack.push(frame);
        let result = self.lower_expr(return_expr);
        self.inline_subs_stack.pop();
        Some(result)
    }

    /// Inline a call to `name` in statement context. Returns
    /// `true` on success (i.e. the body was spliced into
    /// `current_ops`), `false` if the target isn't in
    /// `inline_bodies`.
    ///
    /// A single-return-expression inline used in statement
    /// context lowers the return expression and discards the
    /// result — the side effects of argument evaluation still
    /// happen, which is what a regular `Statement::Call` would
    /// do.
    fn try_inline_call_stmt(&mut self, name: &str, args: &[Expr]) -> bool {
        let Some(captured) = self.inline_bodies.get(name).cloned() else {
            return false;
        };
        if captured.params.len() != args.len() {
            return false;
        }
        // If the body contains an `asm { ... }` block, we can
        // only safely inline when *every* argument is a compile-
        // time constant. The asm body's `{param}` references get
        // pre-substituted with `#$<value>` immediates at the
        // expansion site (see `Statement::InlineAsm` lowering),
        // and there's no way to do that for a runtime value.
        // Fall back to a regular Call op for the runtime case;
        // the caller will JSR the out-of-line definition that
        // preserves the standard parameter-passing convention.
        if body_has_inline_asm(&captured.body) {
            let all_const = args.iter().all(|a| self.eval_const(a).is_some());
            if !all_const {
                return false;
            }
        }
        let arg_temps: Vec<IrTemp> = args.iter().map(|a| self.lower_expr(a)).collect();
        let mut frame = HashMap::new();
        let mut const_frame: HashMap<String, u8> = HashMap::new();
        for ((param, arg), temp) in captured
            .params
            .iter()
            .zip(args.iter())
            .zip(arg_temps.iter())
        {
            frame.insert(param.name.clone(), *temp);
            if let Some(v) = self.eval_const(arg) {
                const_frame.insert(param.name.clone(), v as u8);
            }
        }
        self.inline_subs_stack.push(frame);
        self.inline_const_args_stack.push(const_frame);
        match &captured.body {
            InlineBody::Expression(expr) => {
                // Evaluate the expression for its side effects;
                // discard the result temp.
                let _ = self.lower_expr(expr);
            }
            InlineBody::Void(stmts) => {
                for stmt in stmts {
                    self.lower_statement(stmt);
                }
            }
        }
        self.inline_subs_stack.pop();
        self.inline_const_args_stack.pop();
        true
    }

    /// Look up `name` in the active inline substitution frame,
    /// if any. Returns the IR temp previously computed for that
    /// parameter (during `try_inline_call_*`'s argument
    /// lowering). The top of the stack wins so nested inlines
    /// see their own frame.
    fn lookup_inline_sub(&self, name: &str) -> Option<IrTemp> {
        self.inline_subs_stack.last()?.get(name).copied()
    }

    /// Recursively expand a struct-literal global initializer into
    /// per-leaf-field `IrGlobal` entries. Handles three field-value
    /// shapes:
    ///
    /// - Scalar constant expressions (e.g. `x: 5`) → emit one
    ///   `IrGlobal` whose `init_value` is the folded constant.
    /// - Nested struct literals (e.g. `pos: Vec2 { x: 1, y: 2 }`)
    ///   → recurse with `base_name = "outer.pos"`, expanding the
    ///   inner literal's fields under the dotted path.
    /// - Array literals (e.g. `inv: [1, 2, 3, 4]`) → emit one
    ///   `IrGlobal` whose `init_array` carries the per-byte values.
    ///
    /// Each leaf global's size is derived from the analyzer's
    /// recorded field type so `u16` fields still claim two bytes.
    fn expand_struct_literal_init(&mut self, base_name: &str, fields: &[(String, Expr)]) {
        for (fname, fexpr) in fields {
            let full = format!("{base_name}.{fname}");
            let fvid = self.get_or_create_var(&full);
            let field_type = self.var_types.get(&full).cloned();
            match fexpr {
                Expr::StructLiteral(_, inner_fields, _) => {
                    // Register the intermediate symbol with size 0 —
                    // its byte-allocation lives in the leaves, but
                    // the IR codegen still needs a global record so
                    // that name lookups don't fail.
                    self.globals.push(IrGlobal {
                        var_id: fvid,
                        name: full.clone(),
                        size: 0,
                        init_value: None,
                        init_array: Vec::new(),
                    });
                    self.expand_struct_literal_init(&full, inner_fields);
                }
                Expr::ArrayLiteral(elems, _) => {
                    let init_array: Vec<u8> = elems
                        .iter()
                        .filter_map(|e| self.eval_const(e).map(|v| v as u8))
                        .collect();
                    let size = type_size(field_type.as_ref().unwrap_or(&NesType::U8));
                    self.globals.push(IrGlobal {
                        var_id: fvid,
                        name: full,
                        size,
                        init_value: None,
                        init_array,
                    });
                }
                _ => {
                    let fval = self.eval_const(fexpr);
                    let size = match field_type {
                        Some(NesType::U16 | NesType::I16) => 2,
                        _ => 1,
                    };
                    self.globals.push(IrGlobal {
                        var_id: fvid,
                        name: full,
                        size,
                        init_value: fval,
                        init_array: Vec::new(),
                    });
                }
            }
        }
    }

    /// Try to evaluate an expression at compile time, using the
    /// already-registered constants as operands. Returns `None` if
    /// the expression references something that isn't known at this
    /// point (e.g. a runtime variable) or contains an operator we
    /// don't constant-fold. The result is a u16 to keep the same
    /// range as the AST integer literal type.
    fn eval_const(&self, expr: &Expr) -> Option<u16> {
        match expr {
            Expr::IntLiteral(v, _) => Some(*v),
            Expr::BoolLiteral(b, _) => Some(u16::from(*b)),
            Expr::Ident(name, _) => {
                // Inside an `inline fun` expansion, parameter
                // names resolve to whatever the call site
                // passed. If the arg was a compile-time constant
                // it's stashed in `inline_const_args_stack`'s
                // top frame — return that so a nested inline
                // call like `rotr1_wk(dst)` can recognise its
                // own arg as constant and inline in turn.
                if let Some(frame) = self.inline_const_args_stack.last() {
                    if let Some(&v) = frame.get(name) {
                        return Some(u16::from(v));
                    }
                }
                self.const_values.get(name).copied()
            }
            Expr::BinaryOp(lhs, op, rhs, _) => {
                let l = self.eval_const(lhs)?;
                let r = self.eval_const(rhs)?;
                match op {
                    BinOp::Add => Some(l.wrapping_add(r)),
                    BinOp::Sub => Some(l.wrapping_sub(r)),
                    BinOp::Mul => Some(l.wrapping_mul(r)),
                    BinOp::Div if r != 0 => Some(l / r),
                    BinOp::Mod if r != 0 => Some(l % r),
                    BinOp::BitwiseAnd => Some(l & r),
                    BinOp::BitwiseOr => Some(l | r),
                    BinOp::BitwiseXor => Some(l ^ r),
                    BinOp::ShiftLeft => Some(l.wrapping_shl(u32::from(r))),
                    BinOp::ShiftRight => Some(l.wrapping_shr(u32::from(r))),
                    BinOp::Eq => Some(u16::from(l == r)),
                    BinOp::NotEq => Some(u16::from(l != r)),
                    BinOp::Lt => Some(u16::from(l < r)),
                    BinOp::Gt => Some(u16::from(l > r)),
                    BinOp::LtEq => Some(u16::from(l <= r)),
                    BinOp::GtEq => Some(u16::from(l >= r)),
                    _ => None,
                }
            }
            Expr::UnaryOp(op, inner, _) => {
                let v = self.eval_const(inner)?;
                match op {
                    UnaryOp::Negate => Some(v.wrapping_neg()),
                    UnaryOp::BitNot => Some(!v),
                    UnaryOp::Not => Some(u16::from(v == 0)),
                }
            }
            Expr::Cast(inner, _, _) => self.eval_const(inner),
            _ => None,
        }
    }

    fn emit(&mut self, op: IrOp) {
        self.current_ops.push(op);
    }

    fn start_block(&mut self, label: &str) {
        self.current_label = label.to_string();
        self.current_ops = Vec::new();
    }

    fn end_block(&mut self, terminator: IrTerminator) {
        self.current_blocks.push(IrBasicBlock {
            label: self.current_label.clone(),
            ops: std::mem::take(&mut self.current_ops),
            terminator,
        });
    }

    fn finish(self) -> IrProgram {
        IrProgram {
            functions: self.functions,
            globals: self.globals,
            rom_data: self.rom_data,
            states: self.state_names,
            start_state: self.start_state,
            var_map: self.var_map,
        }
    }

    fn lower_program(&mut self, program: &Program) {
        // Capture state metadata before lowering
        self.state_names = program.states.iter().map(|s| s.name.clone()).collect();
        program.start_state.clone_into(&mut self.start_state);
        // Pick up the `sprite_flicker` game attribute so each
        // on-frame handler's prologue can inject a CycleSprites
        // op without threading the flag through per-handler calls.
        self.auto_sprite_flicker = program.game.sprite_flicker;

        // Capture metasprite declarations so the per-statement
        // Draw lowering can expand `draw Hero` into one
        // DrawSprite op per tile. The `frame:` array in a
        // metasprite is interpreted *relative to the underlying
        // sprite's base tile* — i.e. `frame: [0, 1, 2, 3]` on a
        // 16×16 sprite means "the four tiles this sprite owns".
        // Since the IR codegen's DrawSprite op takes an *absolute*
        // tile index whenever `frame` is set, we need to resolve
        // the per-sprite base tile here and rewrite the array
        // before storing it.
        //
        // Tile assignment mirrors `assets::resolve_sprites`: tile
        // index 0 is reserved for the runtime's default smiley,
        // user sprites start at 1, and each sprite consumes
        // `chr_bytes.len() / 16` tiles (rounded up). Sprites with
        // an external `@chr(...)` / `@binary(...)` source whose
        // bytes aren't available at parse time fall back to a
        // single-tile assumption — that's a regression for those
        // exotic sources but keeps the in-tree examples working.
        let mut sprite_base: HashMap<String, u8> = HashMap::new();
        let mut next_tile: u8 = 1;
        for sprite in &program.sprites {
            sprite_base.insert(sprite.name.clone(), next_tile);
            let tile_count = match &sprite.chr_source {
                crate::parser::ast::AssetSource::Inline(bytes) => {
                    (bytes.len().div_ceil(16)).max(1) as u8
                }
                _ => 1,
            };
            next_tile = next_tile.saturating_add(tile_count);
        }
        for ms in &program.metasprites {
            let base = sprite_base.get(&ms.sprite_name).copied().unwrap_or(0);
            let resolved_frames: Vec<u8> =
                ms.frame.iter().map(|&f| base.saturating_add(f)).collect();
            self.metasprites.insert(
                ms.name.clone(),
                MetaspriteInfo {
                    sprite_name: ms.sprite_name.clone(),
                    dx: ms.dx.clone(),
                    dy: ms.dy.clone(),
                    frame: resolved_frames,
                },
            );
        }

        // Register enum variants first so constants that reference
        // them (e.g. `const FIRST: u8 = VariantA`) can resolve.
        for e in &program.enums {
            for (i, (variant, _)) in e.variants.iter().enumerate() {
                self.const_values.insert(variant.clone(), i as u16);
            }
        }

        // Register constants with constant-evaluation. Each const
        // may reference earlier constants.
        for c in &program.constants {
            if let Some(v) = self.eval_const(&c.value) {
                self.const_values.insert(c.name.clone(), v);
            }
        }

        // Lower globals. Initializers can be any constant expression.
        // Struct-literal initializers are expanded into per-field
        // globals so each field gets its own `init_value`; the parent
        // struct itself is still registered (size=0) so any later IR
        // op referencing it by name still resolves. Array-literal
        // initializers are lowered into `init_array` on the parent
        // global — the IR codegen's startup loop emits one LDA/STA
        // per byte into the global's base address. Nested struct
        // literals (`Player { pos: Vec2 { x: 1, y: 2 }, ... }`)
        // and array-literal field values (`Hero { inv: [1,2,3,4] }`)
        // are expanded recursively below.
        for var in &program.globals {
            let var_id = self.get_or_create_var(&var.name);
            let init = var.init.as_ref().and_then(|e| self.eval_const(e));
            let init_array = match &var.init {
                Some(Expr::ArrayLiteral(elems, _)) => elems
                    .iter()
                    .filter_map(|e| self.eval_const(e).map(|v| v as u8))
                    .collect(),
                _ => Vec::new(),
            };
            self.globals.push(IrGlobal {
                var_id,
                name: var.name.clone(),
                size: type_size(&var.var_type),
                init_value: init,
                init_array,
            });
            if let Some(Expr::StructLiteral(_, fields, _)) = &var.init {
                self.expand_struct_literal_init(&var.name, fields);
            }
        }

        // Capture `inline fun` bodies that qualify for real
        // inlining. A function qualifies when it's marked
        // `inline`, has a declared return type, and its body
        // consists of exactly one `Statement::Return(Some(expr))`.
        // Call sites targeting one of these functions will be
        // expanded in-place in `lower_expr` / `lower_statement`
        // instead of emitting a `Call` op — the caller's body
        // gets the return expression spliced in with the
        // function's parameters substituted for argument temps.
        //
        // Functions marked `inline` but with more complex bodies
        // (multi-statement, void, loops, conditionals) compile
        // as regular calls with a W0109 "inline declined"
        // warning emitted by the analyzer. This catches users
        // who write `inline fun` expecting the keyword to be
        // enforced.
        self.capture_inline_bodies(program);

        // Register state-local variables as IR globals so the codegen
        // resolves their addresses through the same `ir.globals`
        // pathway it uses for program globals — the analyzer records
        // them under their bare names in `var_allocations`, which
        // `IrCodeGen::new` then matches against each global's
        // `name` field. Without this, a `LoadVar`/`StoreVar` on a
        // state-local variable resolved its `VarId` to no address
        // and the codegen silently emitted nothing — the root
        // cause of the "state-local variables don't actually work"
        // bug that this change ships with the overlay feature.
        //
        // `init_value` / `init_array` are intentionally left blank:
        // state-locals are re-initialized in each state's on_enter
        // handler below, not at program reset. The analyzer's
        // overlay allocation means one state's initial bytes would
        // stomp on another state's if we emitted them at reset.
        for state in &program.states {
            for var in &state.locals {
                let var_id = self.get_or_create_var(&var.name);
                self.globals.push(IrGlobal {
                    var_id,
                    name: var.name.clone(),
                    size: type_size(&var.var_type),
                    init_value: None,
                    init_array: Vec::new(),
                });
            }
        }

        // Lower user functions
        for fun in &program.functions {
            self.lower_function(fun);
        }

        // Lower state handlers
        for state in &program.states {
            self.lower_state(state, state.name == program.start_state);
        }
    }

    fn lower_function(&mut self, fun: &FunDecl) {
        self.next_temp = 0;
        // Clear the wide-temp tracking map. `wide_hi` records "this
        // low temp has its high byte at this other temp" entries
        // produced by `make_wide`; without clearing it, the entries
        // from previous functions leak into the next function and
        // get matched against fresh temp IDs (since next_temp resets
        // to 0). That manifests as `is_wide(t)` spuriously returning
        // true and, worse, `widen(t)` returning a stale `hi` temp ID
        // that collides with a later `fresh_temp()` allocation —
        // producing 16-bit IR ops where the destination temp is
        // *also* one of the source temps (the `wide_hi` leak bug
        // fixed on the War cleanup branch; see `git log` for the
        // full reproduction).
        self.wide_hi.clear();
        self.signed_temps.clear();
        self.current_blocks = Vec::new();
        self.current_locals = Vec::new();
        // Enter the function's local scope so all bare identifier
        // lookups inside the body resolve against the analyzer's
        // `__local__{function_name}__{name}` entries.
        self.current_scope_prefix = Some(fun.name.clone());

        // Register parameters as locals. They're looked up via
        // their bare name (which `get_or_create_var` now qualifies
        // via `scoped_key`), so two different functions can each
        // have a parameter named `x` without the VarIds colliding.
        for param in &fun.params {
            let var_id = self.get_or_create_var(&param.name);
            self.current_locals.push(IrLocal {
                var_id,
                name: param.name.clone(),
                size: type_size(&param.param_type),
            });
            // Register the param type under the scoped key so
            // `lower_expr` can decide 8-bit vs 16-bit loads.
            let key = format!("__local__{}__{}", fun.name, param.name);
            self.var_types.insert(key, param.param_type.clone());
        }

        let entry = self.fresh_label(&format!("fn_{}_entry", fun.name));
        self.start_block(&entry);
        self.lower_block(&fun.body);

        // Ensure the function ends with a return
        if self.current_ops.is_empty()
            || !matches!(
                self.current_blocks.last().map(|b| &b.terminator),
                Some(IrTerminator::Return(_))
            )
        {
            self.end_block(IrTerminator::Return(None));
        }

        self.functions.push(IrFunction {
            name: fun.name.clone(),
            blocks: std::mem::take(&mut self.current_blocks),
            locals: std::mem::take(&mut self.current_locals),
            param_count: fun.params.len(),
            has_return: fun.return_type.is_some(),
            bank: fun.bank.clone(),
            source_span: fun.span,
        });
        self.current_scope_prefix = None;
    }

    fn lower_state(&mut self, state: &StateDecl, _is_start: bool) {
        // Lower each event handler as a separate function. Each
        // handler uses a distinct scope prefix so a `var i` in
        // `Title::on frame` and one in `Playing::on frame` get
        // different VarIds.

        // State-local variables with initializers need their values
        // re-established every time the state is entered, because
        // the analyzer overlays state-locals across mutually
        // exclusive states and another state's writes can clobber
        // the bytes in between. If the state already has an
        // on_enter handler, `lower_handler` prepends the
        // initializer stores; if not, synthesize an empty one here
        // so the dispatch path still calls into the prelude.
        let needs_synthetic_enter =
            state.on_enter.is_none() && state.locals.iter().any(|v| v.init.is_some());
        let synthetic_enter = Block {
            statements: Vec::new(),
            span: state.span,
        };
        let on_enter_block: Option<&Block> = state.on_enter.as_ref().or(if needs_synthetic_enter {
            Some(&synthetic_enter)
        } else {
            None
        });
        if let Some(on_enter) = on_enter_block {
            self.lower_handler(
                &format!("{}_enter", state.name),
                &format!("{}__enter", state.name),
                on_enter,
                state,
            );
        }

        if let Some(on_exit) = &state.on_exit {
            self.lower_handler(
                &format!("{}_exit", state.name),
                &format!("{}__exit", state.name),
                on_exit,
                state,
            );
        }

        if let Some(on_frame) = &state.on_frame {
            self.lower_handler(
                &format!("{}_frame", state.name),
                &format!("{}__frame", state.name),
                on_frame,
                state,
            );
        }

        // Lower each scanline handler as a function named
        // `{state}_scanline_{N}`. The IR codegen will generate the MMC3
        // IRQ dispatch wrapper separately.
        for (line, block) in &state.on_scanline {
            let name = format!("{}_scanline_{line}", state.name);
            let scope = format!("{}__scanline_{line}", state.name);
            self.lower_handler(&name, &scope, block, state);
        }
    }

    fn lower_handler(&mut self, name: &str, scope_prefix: &str, block: &Block, state: &StateDecl) {
        self.next_temp = 0;
        // Same per-function reset as `lower_function`. See the
        // commentary there for why this is critical — without it,
        // state-handler bodies pick up wide temp pairs left over
        // from the previous function and emit
        // catastrophically wrong 16-bit IR ops.
        self.wide_hi.clear();
        self.signed_temps.clear();
        self.current_blocks = Vec::new();
        self.current_scope_prefix = Some(scope_prefix.to_string());
        // Seed `current_locals` with the state's declared locals so any
        // `VarDecl` inside the handler body — tracked by
        // `lower_statement` via `current_locals` — is appended alongside
        // them. Without this, handler-local variables (e.g. a `var i`
        // inside a `while`) would get orphaned: their `VarId` would be
        // created by `get_or_create_var`, but the `IrFunction`'s
        // `locals` list (which the IR codegen uses to allocate RAM
        // addresses) would never see them. The result would be a
        // silent `LoadVar`/`StoreVar` emit-nothing bug that leaves the
        // temp slots uninitialized at runtime.
        //
        // State-level locals (declared at `state Foo { var i: u8 }`
        // outside any handler) live in the GLOBAL scope so every
        // handler in the state can read/write them across frames.
        // `get_or_create_var` would try the scoped key first —
        // which isn't registered for state-locals — then fall back
        // to the bare key, which IS registered.
        self.current_locals = Vec::new();
        for var in &state.locals {
            let var_id = self.get_or_create_var(&var.name);
            self.current_locals.push(IrLocal {
                var_id,
                name: var.name.clone(),
                size: type_size(&var.var_type),
            });
        }

        let entry = self.fresh_label(&format!("{name}_entry"));
        self.start_block(&entry);

        // on_enter handlers carry the state-local initializer
        // prologue: every `var x: u8 = expr` declared at
        // `state Foo { ... }` level gets a store emitted at the
        // top of on_enter so the state's locals are reset every
        // time the state is entered. This is what makes the
        // analyzer's overlay allocation safe — another state
        // having written into these bytes no longer matters,
        // because we unconditionally re-initialize them here.
        // User code inside the on_enter body then runs on top.
        // Locals without an initializer are left at whatever
        // bytes the previous state wrote; the programmer can
        // explicitly assign them if they want a fresh value.
        if name.ends_with("_enter") {
            for var in &state.locals {
                let Some(init) = &var.init else { continue };
                let var_id = self.get_or_create_var(&var.name);
                if let Expr::ArrayLiteral(_, _) = init {
                    // Array initializers for state-locals aren't
                    // supported yet — a runtime memcpy loop from a
                    // ROM blob would be the natural lowering.
                    // Programs that try this should get a diagnostic
                    // from the analyzer; for now, silently skip.
                    continue;
                }
                if let Expr::StructLiteral(_, fields, _) = init {
                    for (fname, fexpr) in fields {
                        let full = format!("{}.{fname}", var.name);
                        let fvid = self.get_or_create_var(&full);
                        let val = self.lower_expr(fexpr);
                        self.emit(IrOp::StoreVar(fvid, val));
                    }
                    continue;
                }
                let val = self.lower_expr(init);
                self.emit(IrOp::StoreVar(var_id, val));
                // u16-typed state-locals also need the high byte
                // of the initializer stored at base+1. Mirror the
                // `VarDecl` lowering in `lower_statement` so wide
                // inits round-trip cleanly.
                if matches!(var.var_type, NesType::U16 | NesType::I16) {
                    let (_, hi) = self.widen(val);
                    self.emit(IrOp::StoreVarHi(var_id, hi));
                }
            }
        }

        // When `game { sprite_flicker: true }` is set, implicitly
        // call `cycle_sprites` at the top of every `on frame`
        // handler. Detected via the handler name suffix —
        // `{state}_frame` — so `on_enter` / `on_exit` / scanline
        // handlers don't pay the extra ~10 bytes. The existing
        // `IrOp::CycleSprites` lowering emits the `__sprite_cycle_used`
        // marker on its first hit, which is all the linker needs to
        // switch the NMI over to the rotating-OAM variant.
        if self.auto_sprite_flicker && name.ends_with("_frame") {
            self.emit(IrOp::CycleSprites);
        }

        self.lower_block(block);
        self.end_block(IrTerminator::Return(None));

        self.functions.push(IrFunction {
            name: name.to_string(),
            blocks: std::mem::take(&mut self.current_blocks),
            locals: std::mem::take(&mut self.current_locals),
            param_count: 0,
            has_return: false,
            // State handlers always live in the fixed bank — the
            // analyzer rejects state-handler nesting inside `bank`
            // blocks because the NMI dispatcher and reset path JSR
            // into them directly without going through a trampoline.
            bank: None,
            source_span: state.span,
        });
        self.current_scope_prefix = None;
    }

    fn lower_block(&mut self, block: &Block) {
        for stmt in &block.statements {
            self.lower_statement(stmt);
        }
    }

    fn lower_statement(&mut self, stmt: &Statement) {
        // Emit a source-location marker before every statement we
        // lower. The codegen turns these into label-definition
        // pseudo-ops (`__src_<file>_<byte>_<line>_<col>`), which
        // the linker then reports back to the CLI so it can emit a
        // source map. Release builds don't need the map, but we
        // still leave the markers in — they lower to zero bytes in
        // codegen, so there's no ROM cost.
        self.emit(IrOp::SourceLoc(stmt.span()));
        match stmt {
            Statement::VarDecl(var) => {
                let var_id = self.get_or_create_var(&var.name);
                // Track every local declared inside the current
                // function so the IR codegen can allocate backing
                // storage (e.g. RAM) for it.
                if !self.current_locals.iter().any(|l| l.var_id == var_id) {
                    self.current_locals.push(IrLocal {
                        var_id,
                        name: var.name.clone(),
                        size: type_size(&var.var_type),
                    });
                }
                // Seed the var_types map for local declarations so
                // subsequent references lower with the right width.
                self.var_types
                    .insert(var.name.clone(), var.var_type.clone());
                if let Some(init) = &var.init {
                    // Struct literal initializers expand to per-field
                    // stores on the synthetic field variables.
                    if let Expr::StructLiteral(_, fields, _) = init {
                        for (fname, fexpr) in fields {
                            let full = format!("{}.{fname}", var.name);
                            let fvid = self.get_or_create_var(&full);
                            let val = self.lower_expr(fexpr);
                            self.emit(IrOp::StoreVar(fvid, val));
                        }
                    } else {
                        let val = self.lower_expr(init);
                        self.emit(IrOp::StoreVar(var_id, val));
                        // u16 / i16 var: write the high byte too,
                        // zero-extending narrow initializers. For
                        // `i16` negative literals, the IR lowering
                        // of integer literals already packs both
                        // bytes via the IntLiteral path, so `widen`
                        // produces the correct sign/zero-extension
                        // — narrow-to-wide stores here still do the
                        // right thing for both signednesses.
                        if matches!(var.var_type, NesType::U16 | NesType::I16) {
                            let (_, hi) = self.widen(val);
                            self.emit(IrOp::StoreVarHi(var_id, hi));
                        }
                    }
                }
            }
            Statement::Assign(lvalue, op, expr, _) => {
                self.lower_assign(lvalue, *op, expr);
            }
            Statement::If(cond, then_block, else_ifs, else_block, _) => {
                self.lower_if(cond, then_block, else_ifs, else_block.as_ref());
            }
            Statement::While(cond, body, _) => {
                self.lower_while(cond, body);
            }
            Statement::Loop(body, _) => {
                self.lower_loop(body);
            }
            Statement::For {
                var,
                start,
                end,
                body,
                ..
            } => {
                // Desugar `for var in start..end { body }` into:
                //     var = start
                //     while var < end { body; var = var + 1 }
                let var_id = self.get_or_create_var(var);
                // The loop variable is implicitly declared by the
                // `for` statement — track it as a local so the IR
                // codegen allocates backing storage. Without this
                // the `StoreVar`/`LoadVar` ops for the counter are
                // silently dropped by `IrCodeGen` (`var_addrs`
                // has no entry), making the counter permanently 0
                // and turning the loop into an infinite one. Same
                // class of bug as handler-local `var` decls before
                // the earlier fix.
                if !self.current_locals.iter().any(|l| l.var_id == var_id) {
                    self.current_locals.push(IrLocal {
                        var_id,
                        name: var.clone(),
                        size: 1,
                    });
                }
                let start_temp = self.lower_expr(start);
                self.emit(IrOp::StoreVar(var_id, start_temp));
                // Precompute the end value once outside the loop
                // header so subsequent iterations don't recompute it.
                // (For a literal, the optimizer collapses this.)
                self.lower_for_body(var_id, end, body);
            }
            Statement::Break(_) => {
                if let Some(ctx) = self.loop_stack.last() {
                    let label = ctx.break_label.clone();
                    self.end_block(IrTerminator::Jump(label.clone()));
                    let cont = self.fresh_label("after_break");
                    self.start_block(&cont);
                }
            }
            Statement::Continue(_) => {
                if let Some(ctx) = self.loop_stack.last() {
                    let label = ctx.continue_label.clone();
                    self.end_block(IrTerminator::Jump(label.clone()));
                    let cont = self.fresh_label("after_continue");
                    self.start_block(&cont);
                }
            }
            Statement::Return(value, _) => {
                let temp = value.as_ref().map(|e| self.lower_expr(e));
                self.end_block(IrTerminator::Return(temp));
                let cont = self.fresh_label("after_return");
                self.start_block(&cont);
            }
            Statement::Draw(draw) => {
                if let Some(meta) = self.metasprites.get(&draw.sprite_name).cloned() {
                    // Metasprite expansion: for each tile in the
                    // declaration, emit one DrawSprite with x/y
                    // offset by (dx[i], dy[i]) and frame = frame[i].
                    // The IR codegen sees N independent draws so
                    // the runtime OAM-cursor path picks them up
                    // exactly like a hand-written sequence of
                    // `draw` statements.
                    //
                    // The user's `frame:` argument is ignored when
                    // drawing a metasprite — the per-tile frame
                    // index comes from the declaration. The
                    // analyzer doesn't currently flag this; future
                    // work could warn on it.
                    let base_x = self.lower_expr(&draw.x);
                    let base_y = self.lower_expr(&draw.y);
                    for ((dx_off, dy_off), tile) in meta.dx.iter().zip(&meta.dy).zip(&meta.frame) {
                        let off_x = self.fresh_temp();
                        self.emit(IrOp::LoadImm(off_x, *dx_off));
                        let x_sum = self.fresh_temp();
                        self.emit(IrOp::Add(x_sum, base_x, off_x));

                        let off_y = self.fresh_temp();
                        self.emit(IrOp::LoadImm(off_y, *dy_off));
                        let y_sum = self.fresh_temp();
                        self.emit(IrOp::Add(y_sum, base_y, off_y));

                        let tile_imm = self.fresh_temp();
                        self.emit(IrOp::LoadImm(tile_imm, *tile));

                        self.emit(IrOp::DrawSprite {
                            sprite_name: meta.sprite_name.clone(),
                            x: x_sum,
                            y: y_sum,
                            frame: Some(tile_imm),
                        });
                    }
                    return;
                }
                let x = self.lower_expr(&draw.x);
                let y = self.lower_expr(&draw.y);
                let frame = draw.frame.as_ref().map(|e| self.lower_expr(e));
                self.emit(IrOp::DrawSprite {
                    sprite_name: draw.sprite_name.clone(),
                    x,
                    y,
                    frame,
                });
            }
            Statement::Transition(name, _) => {
                self.emit(IrOp::Transition(name.clone()));
            }
            Statement::WaitFrame(_) => {
                self.emit(IrOp::WaitFrame);
            }
            Statement::CycleSprites(_) => {
                self.emit(IrOp::CycleSprites);
            }
            Statement::Call(name, args, _) => {
                match name.as_str() {
                    // Built-in `poke(addr, value)` — write a byte to
                    // a compile-time-constant address.
                    "poke" if args.len() == 2 => {
                        if let Some(addr) = self.eval_const(&args[0]) {
                            let val = self.lower_expr(&args[1]);
                            self.emit(IrOp::Poke(addr, val));
                        }
                    }
                    // `seed_rand(x)` — install `x` as the new PRNG
                    // state. `x` is widened to u16 so a narrow seed
                    // still lands in both bytes of the state.
                    "seed_rand" if args.len() == 1 => {
                        let seed = self.lower_expr(&args[0]);
                        let (lo, hi) = self.widen(seed);
                        self.emit(IrOp::SeedRand(lo, hi));
                    }
                    // `set_palette_brightness(level)` — translate a
                    // 0..8 level into $2001 mask bits.
                    "set_palette_brightness" if args.len() == 1 => {
                        let level = self.lower_expr(&args[0]);
                        self.emit(IrOp::SetPaletteBrightness(level));
                    }
                    // `fade_out(step_frames)` / `fade_in(step_frames)` —
                    // blocking fades that walk brightness 4 → 0 and
                    // 0 → 4 respectively, calling
                    // `__set_palette_brightness` per step with
                    // `step_frames` frames of wait between steps.
                    "fade_out" if args.len() == 1 => {
                        let n = self.lower_expr(&args[0]);
                        self.emit(IrOp::FadeOut(n));
                    }
                    "fade_in" if args.len() == 1 => {
                        let n = self.lower_expr(&args[0]);
                        self.emit(IrOp::FadeIn(n));
                    }
                    // `sprite_0_split(scroll_x, scroll_y)` — busy-wait
                    // for the PPU's sprite-0 hit flag, then write
                    // the new scroll values to `$2005`. Works on
                    // any mapper (NROM/UxROM/MMC1 included), unlike
                    // `on_scanline(N)` which requires MMC3's IRQ.
                    "sprite_0_split" if args.len() == 2 => {
                        let x = self.lower_expr(&args[0]);
                        let y = self.lower_expr(&args[1]);
                        self.emit(IrOp::Sprite0Split {
                            scroll_x: x,
                            scroll_y: y,
                        });
                    }
                    // VRAM update buffer intrinsics. Each call appends
                    // one entry to the runtime ring at $0400 that the
                    // NMI handler drains during vblank.
                    "nt_set" if args.len() == 3 => {
                        let x = self.lower_expr(&args[0]);
                        let y = self.lower_expr(&args[1]);
                        let tile = self.lower_expr(&args[2]);
                        self.emit(IrOp::NtSet { x, y, tile });
                    }
                    "nt_attr" if args.len() == 3 => {
                        let x = self.lower_expr(&args[0]);
                        let y = self.lower_expr(&args[1]);
                        let value = self.lower_expr(&args[2]);
                        self.emit(IrOp::NtAttr { x, y, value });
                    }
                    "nt_fill_h" if args.len() == 4 => {
                        let x = self.lower_expr(&args[0]);
                        let y = self.lower_expr(&args[1]);
                        let len = self.lower_expr(&args[2]);
                        let tile = self.lower_expr(&args[3]);
                        self.emit(IrOp::NtFillH { x, y, len, tile });
                    }
                    // `rand8()` / `rand16()` at statement position —
                    // valid because they have side effects (advancing
                    // the PRNG state). The returned value is discarded
                    // by routing through a fresh temp that nothing
                    // reads; the JSR still runs so the state advances.
                    "rand8" if args.is_empty() => {
                        let t = self.fresh_temp();
                        self.emit(IrOp::Rand8(t));
                    }
                    "rand16" if args.is_empty() => {
                        let lo = self.fresh_temp();
                        let hi = self.fresh_temp();
                        self.emit(IrOp::Rand16(lo, hi));
                    }
                    _ => {
                        // Inline expansion at statement context
                        // splices either the return expression
                        // (discarding its result) or the body
                        // statements directly into `current_ops`.
                        if self.try_inline_call_stmt(name, args) {
                            return;
                        }
                        let arg_temps: Vec<_> = args.iter().map(|a| self.lower_expr(a)).collect();
                        self.emit(IrOp::Call(None, name.clone(), arg_temps));
                    }
                }
            }
            Statement::Scroll(x_expr, y_expr, _) => {
                let x = self.lower_expr(x_expr);
                let y = self.lower_expr(y_expr);
                self.emit(IrOp::Scroll(x, y));
            }
            Statement::SetPalette(name, _) => {
                self.emit(IrOp::SetPalette(name.clone()));
            }
            Statement::LoadBackground(name, _) => {
                self.emit(IrOp::LoadBackground(name.clone()));
            }
            Statement::PaintRoom(name, _) => {
                self.emit(IrOp::PaintRoom(name.clone()));
            }
            Statement::DebugLog(args, _) => {
                let temps: Vec<_> = args.iter().map(|a| self.lower_expr(a)).collect();
                self.emit(IrOp::DebugLog(temps));
            }
            Statement::DebugAssert(cond, _) => {
                let t = self.lower_expr(cond);
                self.emit(IrOp::DebugAssert(t));
            }
            Statement::InlineAsm(body, _) => {
                // When we're expanding an `inline fun` body, the
                // analyzer's per-function scope no longer matches
                // the caller's, so the codegen's
                // `substitute_asm_vars` would fail to resolve
                // `{param}` references. Pre-substitute every
                // parameter that the inline frame knows the
                // constant value of, replacing `{name}` with
                // `#$<value>` so the inlined asm parses as an
                // immediate-mode operand.
                let final_body = if let Some(consts) = self.inline_const_args_stack.last() {
                    if consts.is_empty() {
                        body.clone()
                    } else {
                        substitute_inline_const_params(body, consts)
                    }
                } else {
                    body.clone()
                };
                self.emit(IrOp::InlineAsm(final_body));
            }
            Statement::RawAsm(body, _) => {
                // Raw asm skips `{var}` substitution. We reuse the
                // same IR op variant but mark the body with a magic
                // prefix the codegen can detect — simpler than
                // adding a separate IrOp.
                self.emit(IrOp::InlineAsm(format!("{RAW_ASM_PREFIX}{body}")));
            }
            Statement::Play(name, _) => {
                self.emit(IrOp::PlaySfx(name.clone()));
            }
            Statement::StartMusic(name, _) => {
                self.emit(IrOp::StartMusic(name.clone()));
            }
            Statement::StopMusic(_) => {
                self.emit(IrOp::StopMusic);
            }
        }
    }

    fn lower_assign(&mut self, lvalue: &LValue, op: AssignOp, expr: &Expr) {
        // Special case: `var = StructLiteral { ... }` expands to
        // per-field stores against the analyzer-synthesized field
        // variables. This avoids needing struct values as IR temps.
        if let (LValue::Var(name), AssignOp::Assign, Expr::StructLiteral(_, fields, _)) =
            (lvalue, op, expr)
        {
            for (fname, fexpr) in fields {
                let full = format!("{name}.{fname}");
                let field_var = self.get_or_create_var(&full);
                let val = self.lower_expr(fexpr);
                self.emit(IrOp::StoreVar(field_var, val));
                // u16 fields need the high byte written too — the
                // `widen` helper yields a zero-extended high temp
                // when the RHS is narrow.
                if matches!(self.var_types.get(&full), Some(NesType::U16 | NesType::I16)) {
                    let (_, val_hi) = self.widen(val);
                    self.emit(IrOp::StoreVarHi(field_var, val_hi));
                }
            }
            return;
        }

        match lvalue {
            LValue::Var(name) => {
                let var_id = self.get_or_create_var(name);
                // Is the destination a u16 variable? Wide vars need
                // both bytes written on every assignment, otherwise
                // the high byte silently stays stale. Both `u16`
                // and `i16` use this wide-store path.
                let dest_is_u16 =
                    matches!(self.var_types.get(name), Some(NesType::U16 | NesType::I16));
                match op {
                    AssignOp::Assign => {
                        let val = self.lower_expr(expr);
                        self.emit(IrOp::StoreVar(var_id, val));
                        if dest_is_u16 {
                            // Narrow value: zero-extend.
                            let (_, val_hi) = self.widen(val);
                            self.emit(IrOp::StoreVarHi(var_id, val_hi));
                        }
                    }
                    _ => {
                        // Load current value. For u16, load both bytes
                        // and register as wide so binary-op lowering
                        // uses the 16-bit path.
                        let current = self.fresh_temp();
                        self.emit(IrOp::LoadVar(current, var_id));
                        if dest_is_u16 {
                            let current_hi = self.fresh_temp();
                            self.emit(IrOp::LoadVarHi(current_hi, var_id));
                            self.make_wide(current, current_hi);
                        }
                        let rhs = self.lower_expr(expr);
                        let result = self.fresh_temp();
                        let wide = dest_is_u16 || self.is_wide(current) || self.is_wide(rhs);
                        if wide && matches!(op, AssignOp::PlusAssign | AssignOp::MinusAssign) {
                            let (a_lo, a_hi) = self.widen(current);
                            let (b_lo, b_hi) = self.widen(rhs);
                            let d_hi = self.fresh_temp();
                            match op {
                                AssignOp::PlusAssign => self.emit(IrOp::Add16 {
                                    d_lo: result,
                                    d_hi,
                                    a_lo,
                                    a_hi,
                                    b_lo,
                                    b_hi,
                                }),
                                AssignOp::MinusAssign => self.emit(IrOp::Sub16 {
                                    d_lo: result,
                                    d_hi,
                                    a_lo,
                                    a_hi,
                                    b_lo,
                                    b_hi,
                                }),
                                _ => unreachable!(),
                            }
                            self.make_wide(result, d_hi);
                            self.emit(IrOp::StoreVar(var_id, result));
                            if dest_is_u16 {
                                self.emit(IrOp::StoreVarHi(var_id, d_hi));
                            }
                        } else {
                            let ir_op = compound_assign_op(op, result, current, rhs, expr, self);
                            self.emit(ir_op);
                            self.emit(IrOp::StoreVar(var_id, result));
                            if dest_is_u16 {
                                // High byte unchanged by 8-bit op; keep
                                // the previously-loaded high byte.
                                let (_, cur_hi) = self.widen(current);
                                self.emit(IrOp::StoreVarHi(var_id, cur_hi));
                            }
                        }
                    }
                }
            }
            LValue::ArrayIndex(name, index) => {
                let var_id = self.get_or_create_var(name);
                let idx = self.lower_expr(index);
                let val = self.lower_expr(expr);
                // For compound assignment on arrays, load first
                if op == AssignOp::Assign {
                    self.emit(IrOp::ArrayStore(var_id, idx, val));
                } else {
                    let current = self.fresh_temp();
                    self.emit(IrOp::ArrayLoad(current, var_id, idx));
                    let result = self.fresh_temp();
                    let ir_op = compound_assign_op(op, result, current, val, expr, self);
                    self.emit(ir_op);
                    self.emit(IrOp::ArrayStore(var_id, idx, result));
                }
            }
            LValue::Field(name, field) => {
                // The analyzer synthesizes a variable named
                // `"struct.field"` for each struct field, so we can
                // treat field assignment as a regular variable
                // assignment to that synthetic name. u16 fields
                // follow the same two-byte path as u16 globals.
                let full_name = format!("{name}.{field}");
                let var_id = self.get_or_create_var(&full_name);
                let dest_is_u16 = matches!(
                    self.var_types.get(&full_name),
                    Some(NesType::U16 | NesType::I16)
                );
                match op {
                    AssignOp::Assign => {
                        let val = self.lower_expr(expr);
                        self.emit(IrOp::StoreVar(var_id, val));
                        if dest_is_u16 {
                            // Narrow value: zero-extend via widen
                            // (which returns the original hi temp if
                            // the value is already wide).
                            let (_, val_hi) = self.widen(val);
                            self.emit(IrOp::StoreVarHi(var_id, val_hi));
                        }
                    }
                    _ => {
                        let current = self.fresh_temp();
                        self.emit(IrOp::LoadVar(current, var_id));
                        if dest_is_u16 {
                            let current_hi = self.fresh_temp();
                            self.emit(IrOp::LoadVarHi(current_hi, var_id));
                            self.make_wide(current, current_hi);
                        }
                        let rhs = self.lower_expr(expr);
                        let result = self.fresh_temp();
                        let wide = dest_is_u16 || self.is_wide(current) || self.is_wide(rhs);
                        if wide && matches!(op, AssignOp::PlusAssign | AssignOp::MinusAssign) {
                            let (a_lo, a_hi) = self.widen(current);
                            let (b_lo, b_hi) = self.widen(rhs);
                            let d_hi = self.fresh_temp();
                            match op {
                                AssignOp::PlusAssign => self.emit(IrOp::Add16 {
                                    d_lo: result,
                                    d_hi,
                                    a_lo,
                                    a_hi,
                                    b_lo,
                                    b_hi,
                                }),
                                AssignOp::MinusAssign => self.emit(IrOp::Sub16 {
                                    d_lo: result,
                                    d_hi,
                                    a_lo,
                                    a_hi,
                                    b_lo,
                                    b_hi,
                                }),
                                _ => unreachable!(),
                            }
                            self.make_wide(result, d_hi);
                            self.emit(IrOp::StoreVar(var_id, result));
                            if dest_is_u16 {
                                self.emit(IrOp::StoreVarHi(var_id, d_hi));
                            }
                        } else {
                            let ir_op = compound_assign_op(op, result, current, rhs, expr, self);
                            self.emit(ir_op);
                            self.emit(IrOp::StoreVar(var_id, result));
                            if dest_is_u16 {
                                // High byte unchanged by 8-bit op;
                                // keep the previously-loaded high
                                // byte.
                                let (_, cur_hi) = self.widen(current);
                                self.emit(IrOp::StoreVarHi(var_id, cur_hi));
                            }
                        }
                    }
                }
            }
        }
    }

    fn lower_if(
        &mut self,
        cond: &Expr,
        then_block: &Block,
        else_ifs: &[(Expr, Block)],
        else_block: Option<&Block>,
    ) {
        let end_label = self.fresh_label("if_end");

        let cond_temp = self.lower_expr(cond);
        let then_label = self.fresh_label("if_then");
        let else_label = if else_ifs.is_empty() && else_block.is_none() {
            end_label.clone()
        } else {
            self.fresh_label("if_else")
        };

        self.end_block(IrTerminator::Branch(
            cond_temp,
            then_label.clone(),
            else_label.clone(),
        ));

        // Then block
        self.start_block(&then_label);
        self.lower_block(then_block);
        self.end_block(IrTerminator::Jump(end_label.clone()));

        // Else-if chains
        let mut current_else = else_label;
        for (i, (elif_cond, elif_block)) in else_ifs.iter().enumerate() {
            self.start_block(&current_else);
            let cond_temp = self.lower_expr(elif_cond);
            let elif_then = self.fresh_label("elif_then");
            let elif_else = if i + 1 < else_ifs.len() || else_block.is_some() {
                self.fresh_label("elif_else")
            } else {
                end_label.clone()
            };
            self.end_block(IrTerminator::Branch(
                cond_temp,
                elif_then.clone(),
                elif_else.clone(),
            ));

            self.start_block(&elif_then);
            self.lower_block(elif_block);
            self.end_block(IrTerminator::Jump(end_label.clone()));

            current_else = elif_else;
        }

        // Else block
        if let Some(block) = else_block {
            self.start_block(&current_else);
            self.lower_block(block);
            self.end_block(IrTerminator::Jump(end_label.clone()));
        }

        self.start_block(&end_label);
    }

    fn lower_while(&mut self, cond: &Expr, body: &Block) {
        let cond_label = self.fresh_label("while_cond");
        let body_label = self.fresh_label("while_body");
        let end_label = self.fresh_label("while_end");

        self.end_block(IrTerminator::Jump(cond_label.clone()));

        // Condition check
        self.start_block(&cond_label);
        let cond_temp = self.lower_expr(cond);
        self.end_block(IrTerminator::Branch(
            cond_temp,
            body_label.clone(),
            end_label.clone(),
        ));

        // Body
        self.loop_stack.push(LoopContext {
            continue_label: cond_label,
            break_label: end_label.clone(),
        });
        self.start_block(&body_label);
        self.lower_block(body);
        let cond_label = &self.loop_stack.last().unwrap().continue_label.clone();
        self.end_block(IrTerminator::Jump(cond_label.clone()));
        self.loop_stack.pop();

        self.start_block(&end_label);
    }

    /// Lower the loop body for a `for var in start..end { body }`.
    /// Assumes `var` has already been initialized to the start
    /// value. Emits the condition `var < end` each iteration and
    /// increments `var` at the continue edge.
    fn lower_for_body(&mut self, var_id: VarId, end: &Expr, body: &Block) {
        let cond_label = self.fresh_label("for_cond");
        let body_label = self.fresh_label("for_body");
        let end_label = self.fresh_label("for_end");

        self.end_block(IrTerminator::Jump(cond_label.clone()));

        // Condition: var < end
        self.start_block(&cond_label);
        let var_temp = self.fresh_temp();
        self.emit(IrOp::LoadVar(var_temp, var_id));
        let end_temp = self.lower_expr(end);
        let cmp_temp = self.fresh_temp();
        // `for` loops drive a u8 counter today (analyzer enforces),
        // so the unsigned compare is always correct.
        self.emit(IrOp::CmpLt(
            cmp_temp,
            var_temp,
            end_temp,
            Signedness::Unsigned,
        ));
        self.end_block(IrTerminator::Branch(
            cmp_temp,
            body_label.clone(),
            end_label.clone(),
        ));

        // Body + increment.
        let step_label = self.fresh_label("for_step");
        self.loop_stack.push(LoopContext {
            continue_label: step_label.clone(),
            break_label: end_label.clone(),
        });
        self.start_block(&body_label);
        self.lower_block(body);
        self.end_block(IrTerminator::Jump(step_label.clone()));
        self.loop_stack.pop();

        // Step: var = var + 1
        self.start_block(&step_label);
        let cur = self.fresh_temp();
        self.emit(IrOp::LoadVar(cur, var_id));
        let one = self.fresh_temp();
        self.emit(IrOp::LoadImm(one, 1));
        let next = self.fresh_temp();
        self.emit(IrOp::Add(next, cur, one));
        self.emit(IrOp::StoreVar(var_id, next));
        self.end_block(IrTerminator::Jump(cond_label));

        self.start_block(&end_label);
    }

    fn lower_loop(&mut self, body: &Block) {
        let body_label = self.fresh_label("loop_body");
        let end_label = self.fresh_label("loop_end");

        self.end_block(IrTerminator::Jump(body_label.clone()));

        self.loop_stack.push(LoopContext {
            continue_label: body_label.clone(),
            break_label: end_label.clone(),
        });
        self.start_block(&body_label);
        self.lower_block(body);
        self.end_block(IrTerminator::Jump(body_label));
        self.loop_stack.pop();

        self.start_block(&end_label);
    }

    /// Mark a temp as the low byte of a wide (u16) value, with the
    /// given high-byte temp. Consumers that care about 16-bit
    /// semantics look up the high byte in `wide_hi`; consumers that
    /// only need a byte ignore the map entirely (implicit truncation).
    fn make_wide(&mut self, lo: IrTemp, hi: IrTemp) {
        self.wide_hi.insert(lo, hi);
    }

    /// True if `t` was produced as the low byte of a wide value.
    fn is_wide(&self, t: IrTemp) -> bool {
        self.wide_hi.contains_key(&t)
    }

    /// Return the high-byte temp for a wide value. If `t` is not
    /// wide, extend it: allocate a fresh temp and emit either
    /// `LoadImm 0` (zero-extend, for unsigned narrow values) or
    /// [`IrOp::SignExtend`] (for signed narrow values). Used before
    /// emitting a 16-bit IR op when one operand is narrow and the
    /// other is wide. The signed path is what makes
    /// `var s8: i8 = -10; var w: i16 = 0; w = s8` round-trip
    /// correctly — without it, the store would land at `$00F6`
    /// (=246) instead of `$FFF6` (=-10).
    fn widen(&mut self, t: IrTemp) -> (IrTemp, IrTemp) {
        if let Some(&hi) = self.wide_hi.get(&t) {
            return (t, hi);
        }
        let hi = self.fresh_temp();
        if self.signed_temps.contains(&t) {
            self.emit(IrOp::SignExtend(hi, t));
            self.signed_temps.insert(hi);
        } else {
            self.emit(IrOp::LoadImm(hi, 0));
        }
        (t, hi)
    }

    /// Mark a temp as carrying a signed value. See `signed_temps` for
    /// the consumer model.
    fn mark_signed(&mut self, t: IrTemp) {
        self.signed_temps.insert(t);
    }

    /// Combined signedness for a binary op: signed if either operand
    /// is signed. Mirrors the way C / Rust promote to the widest
    /// signed type when one side is signed.
    fn binop_signedness(&self, a: IrTemp, b: IrTemp) -> Signedness {
        if self.signed_temps.contains(&a) || self.signed_temps.contains(&b) {
            Signedness::Signed
        } else {
            Signedness::Unsigned
        }
    }

    fn lower_expr(&mut self, expr: &Expr) -> IrTemp {
        match expr {
            Expr::IntLiteral(v, _) => {
                let t = self.fresh_temp();
                self.emit(IrOp::LoadImm(t, *v as u8));
                // For literals that don't fit in a byte, also emit
                // the high byte and register the pair as wide so
                // later assignment to a u16 var stores both halves.
                if *v > 0xFF {
                    let hi = self.fresh_temp();
                    self.emit(IrOp::LoadImm(hi, (*v >> 8) as u8));
                    self.make_wide(t, hi);
                }
                t
            }
            Expr::BoolLiteral(v, _) => {
                let t = self.fresh_temp();
                self.emit(IrOp::LoadImm(t, u8::from(*v)));
                t
            }
            Expr::Ident(name, _) => {
                // When we're inside an inline expansion and this
                // name is a parameter of the function currently
                // being inlined, return the pre-computed argument
                // temp directly instead of emitting a load op.
                // That's how substitution actually happens: the
                // body expression references the parameter, we
                // short-circuit the lookup to the temp the caller
                // already evaluated.
                if let Some(temp) = self.lookup_inline_sub(name) {
                    return temp;
                }
                // Check constants first
                if let Some(&val) = self.const_values.get(name) {
                    let t = self.fresh_temp();
                    self.emit(IrOp::LoadImm(t, val as u8));
                    return t;
                }
                let var_id = self.get_or_create_var(name);
                let t = self.fresh_temp();
                self.emit(IrOp::LoadVar(t, var_id));
                let scoped = self.scoped_key(name);
                let var_ty = self
                    .var_types
                    .get(&scoped)
                    .or_else(|| self.var_types.get(name))
                    .cloned();
                // For u16 / i16 variables, also load the high byte
                // and register the temp pair as wide so downstream
                // ops can emit 16-bit IR when appropriate.
                if matches!(var_ty, Some(NesType::U16 | NesType::I16)) {
                    let hi = self.fresh_temp();
                    self.emit(IrOp::LoadVarHi(hi, var_id));
                    self.make_wide(t, hi);
                    if matches!(var_ty, Some(NesType::I16)) {
                        self.mark_signed(t);
                        self.mark_signed(hi);
                    }
                } else if matches!(var_ty, Some(NesType::I8)) {
                    self.mark_signed(t);
                }
                t
            }
            Expr::ArrayIndex(name, index, _) => {
                let var_id = self.get_or_create_var(name);
                let idx = self.lower_expr(index);
                let t = self.fresh_temp();
                self.emit(IrOp::ArrayLoad(t, var_id, idx));
                let scoped = self.scoped_key(name);
                let elem_ty = match self
                    .var_types
                    .get(&scoped)
                    .or_else(|| self.var_types.get(name))
                {
                    Some(NesType::Array(elem, _)) => Some(elem.as_ref().clone()),
                    _ => None,
                };
                if matches!(elem_ty, Some(NesType::I8 | NesType::I16)) {
                    self.mark_signed(t);
                }
                t
            }
            Expr::FieldAccess(name, field, _) => {
                // Field access lowers to a plain load of the
                // synthetic `"struct.field"` variable produced by the
                // analyzer. u16 fields follow the same two-byte path
                // as u16 globals — load the low byte via `LoadVar`
                // and the high byte via `LoadVarHi`, then register
                // the pair as wide.
                let full_name = format!("{name}.{field}");
                let var_id = self.get_or_create_var(&full_name);
                let t = self.fresh_temp();
                self.emit(IrOp::LoadVar(t, var_id));
                let var_ty = self.var_types.get(&full_name).cloned();
                if matches!(var_ty, Some(NesType::U16 | NesType::I16)) {
                    let hi = self.fresh_temp();
                    self.emit(IrOp::LoadVarHi(hi, var_id));
                    self.make_wide(t, hi);
                    if matches!(var_ty, Some(NesType::I16)) {
                        self.mark_signed(t);
                        self.mark_signed(hi);
                    }
                } else if matches!(var_ty, Some(NesType::I8)) {
                    self.mark_signed(t);
                }
                t
            }
            Expr::BinaryOp(left, op, right, _) => self.lower_binop(left, *op, right),
            Expr::UnaryOp(op, inner, _) => {
                // Constant-fold `-<literal>` into a wide two's-
                // complement literal so a negative source like
                // `-10` assigned to an `i16` stores $FFF6 (sign-
                // extended) rather than the zero-extended $00F6
                // that a byte-level negate + widen would produce.
                // Without this fold, `var vy: i16 = -10` would
                // silently land at $00F6 = 246 in the target.
                if let (UnaryOp::Negate, Expr::IntLiteral(v, _)) = (op, inner.as_ref()) {
                    let negated = (*v).wrapping_neg();
                    let t = self.fresh_temp();
                    self.emit(IrOp::LoadImm(t, negated as u8));
                    if *v != 0 {
                        let hi = self.fresh_temp();
                        self.emit(IrOp::LoadImm(hi, (negated >> 8) as u8));
                        self.make_wide(t, hi);
                        self.mark_signed(t);
                        self.mark_signed(hi);
                    } else {
                        // -0 is still a literal that wants signed
                        // semantics in any compare it participates in.
                        self.mark_signed(t);
                    }
                    return t;
                }
                let val = self.lower_expr(inner);
                let t = self.fresh_temp();
                match op {
                    UnaryOp::Negate => {
                        self.emit(IrOp::Negate(t, val));
                        // Negation is the canonical signed op — its
                        // result is always interpreted as a signed
                        // two's-complement value.
                        self.mark_signed(t);
                    }
                    UnaryOp::Not => {
                        // Logical not: compare with 0
                        let zero = self.fresh_temp();
                        self.emit(IrOp::LoadImm(zero, 0));
                        self.emit(IrOp::CmpEq(t, val, zero));
                    }
                    UnaryOp::BitNot => self.emit(IrOp::Complement(t, val)),
                }
                t
            }
            Expr::Call(name, args, _) => {
                // Built-in `peek(addr)` reads a byte from a fixed
                // absolute address at compile time.
                if name == "peek" && args.len() == 1 {
                    if let Some(addr) = self.eval_const(&args[0]) {
                        let t = self.fresh_temp();
                        self.emit(IrOp::Peek(t, addr));
                        return t;
                    }
                }
                // `rand8()` — draw the next 8 bits from the PRNG.
                if name == "rand8" && args.is_empty() {
                    let t = self.fresh_temp();
                    self.emit(IrOp::Rand8(t));
                    return t;
                }
                // `rand16()` — draw the next 16 bits. Return a
                // wide-marked low temp so callers get u16 semantics.
                if name == "rand16" && args.is_empty() {
                    let lo = self.fresh_temp();
                    let hi = self.fresh_temp();
                    self.emit(IrOp::Rand16(lo, hi));
                    self.make_wide(lo, hi);
                    return lo;
                }
                // `collides_at(x, y)` — a 2-arg bool-returning
                // builtin. Both args are u8 screen coordinates; the
                // result is 0 / 1. Codegen emits a JSR to a shared
                // runtime helper that walks the current room's
                // collision bitmap.
                if name == "collides_at" && args.len() == 2 {
                    let x = self.lower_expr(&args[0]);
                    let y = self.lower_expr(&args[1]);
                    let dest = self.fresh_temp();
                    self.emit(IrOp::CollidesAt { dest, x, y });
                    return dest;
                }
                // `inline fun` bodies captured by
                // `capture_inline_bodies` expand in-place here:
                // no JSR, no parameter transport, no prologue.
                // The return value is whatever temp the body
                // expression lowered to.
                if let Some(t) = self.try_inline_call_expr(name, args) {
                    return t;
                }
                let arg_temps: Vec<_> = args.iter().map(|a| self.lower_expr(a)).collect();
                let t = self.fresh_temp();
                self.emit(IrOp::Call(Some(t), name.clone(), arg_temps));
                t
            }
            Expr::ButtonEdge(player, button, released, _) => {
                let player_index = match player {
                    Some(Player::P2) => 1u8,
                    _ => 0u8,
                };
                let mask = button_mask(button);
                let dest = self.fresh_temp();
                self.emit(IrOp::ReadInputEdge {
                    dest,
                    player: player_index,
                    mask,
                    released: *released,
                });
                dest
            }
            Expr::ButtonRead(player, button, _) => {
                // Button reads: read the input byte, mask with the button bit.
                // Player 1 reads from $01, player 2 reads from $08.
                let player_index = match player {
                    Some(Player::P2) => 1u8,
                    _ => 0u8,
                };
                let input = self.fresh_temp();
                self.emit(IrOp::ReadInput(input, player_index));
                let mask = button_mask(button);
                let mask_temp = self.fresh_temp();
                self.emit(IrOp::LoadImm(mask_temp, mask));
                let t = self.fresh_temp();
                self.emit(IrOp::And(t, input, mask_temp));
                t
            }
            Expr::ArrayLiteral(_, _) => {
                // Array literals are handled during initialization, not as general expressions
                let t = self.fresh_temp();
                self.emit(IrOp::LoadImm(t, 0));
                t
            }
            Expr::StructLiteral(_, _, _) => {
                // Struct literals are only supported as the right
                // hand side of a plain assignment (see lower_assign).
                // Falling through here means the literal was used in
                // an expression context the lowering can't handle;
                // emit zero so the build still produces a ROM.
                let t = self.fresh_temp();
                self.emit(IrOp::LoadImm(t, 0));
                t
            }
            Expr::Cast(inner, target, _) => {
                // Lower the inner expression and re-tag the result's
                // signedness to match the cast target. Casts to `i8`
                // / `i16` mark the temp signed (the user is asserting
                // signed interpretation regardless of the source);
                // casts to `u8` / `u16` strip the signed flag so
                // subsequent compares pick the unsigned path. Width
                // changes are still no-ops at IR level — the codegen
                // only cares about the low byte for narrowing, and
                // widening uses the same `widen()` path as everywhere
                // else.
                let t = self.lower_expr(inner);
                match target {
                    NesType::I8 | NesType::I16 => self.mark_signed(t),
                    NesType::U8 | NesType::U16 => {
                        self.signed_temps.remove(&t);
                    }
                    _ => {}
                }
                t
            }
            Expr::DebugCall(method, _args, _) => {
                // The analyzer already validated the method name and
                // argument count, so we can dispatch on the method
                // name directly. All currently-supported methods
                // map to a Peek of a runtime address: the codegen
                // strips the read out and substitutes a constant
                // zero in release builds, so the builtin disappears
                // from non-debug ROMs.
                let t = self.fresh_temp();
                let addr: u16 = match method.as_str() {
                    "frame_overrun_count" => 0x07FF,
                    "frame_overran" => 0x07FE,
                    "sprite_overflow_count" => 0x07FD,
                    "sprite_overflow" => 0x07FC,
                    // Should be unreachable post-analyzer, but emit
                    // a zero rather than panicking so a parser test
                    // that bypasses the analyzer still produces IR.
                    _ => {
                        self.emit(IrOp::LoadImm(t, 0));
                        return t;
                    }
                };
                self.emit(IrOp::Peek(t, addr));
                t
            }
        }
    }

    fn lower_binop(&mut self, left: &Expr, op: BinOp, right: &Expr) -> IrTemp {
        // Short-circuit for logical operators
        match op {
            BinOp::And => return self.lower_logical_and(left, right),
            BinOp::Or => return self.lower_logical_or(left, right),
            _ => {}
        }

        // Shift operators with a compile-time-constant RHS take a
        // specialized path that bakes the count into the IR op. This
        // also covers the common `x << 1` / `x >> 2` case where the
        // RHS is a literal in the source.
        if matches!(op, BinOp::ShiftLeft | BinOp::ShiftRight) {
            if let Some(count) = self.eval_const(right) {
                let l = self.lower_expr(left);
                let t = self.fresh_temp();
                // Shifting by ≥ 8 zeroes an 8-bit value; clamp so the
                // codegen doesn't emit an absurd number of ASL/LSR.
                let count = count.min(8) as u8;
                let ir_op = if op == BinOp::ShiftLeft {
                    IrOp::ShiftLeft(t, l, count)
                } else {
                    IrOp::ShiftRight(t, l, count)
                };
                self.emit(ir_op);
                return t;
            }
        }

        let l = self.lower_expr(left);
        let r = self.lower_expr(right);
        let wide = self.is_wide(l) || self.is_wide(r);
        let t = self.fresh_temp();

        // 16-bit path: either operand is a wide value. Promote the
        // narrower operand via zero-extension and emit the 16-bit
        // IR op. Only add/sub/cmp are wide-aware today — other
        // bitwise ops and multiply fall through to their 8-bit
        // variants, which truncate to the low byte. (Multi-byte
        // bitwise / multiply could be added later; today they're
        // rare enough in NES code to defer.)
        // Combined signedness: signed iff either operand is signed.
        // For compares the value goes into the IR op's `signed`
        // field; for arithmetic we propagate it onto the result temp
        // so a chain like `cast_i8 + 1 < limit` keeps signed
        // semantics through to the compare.
        let sign = self.binop_signedness(l, r);

        if wide {
            let (a_lo, a_hi) = self.widen(l);
            let (b_lo, b_hi) = self.widen(r);
            match op {
                BinOp::Add => {
                    let d_hi = self.fresh_temp();
                    self.emit(IrOp::Add16 {
                        d_lo: t,
                        d_hi,
                        a_lo,
                        a_hi,
                        b_lo,
                        b_hi,
                    });
                    self.make_wide(t, d_hi);
                    if sign == Signedness::Signed {
                        self.mark_signed(t);
                        self.mark_signed(d_hi);
                    }
                    return t;
                }
                BinOp::Sub => {
                    let d_hi = self.fresh_temp();
                    self.emit(IrOp::Sub16 {
                        d_lo: t,
                        d_hi,
                        a_lo,
                        a_hi,
                        b_lo,
                        b_hi,
                    });
                    self.make_wide(t, d_hi);
                    if sign == Signedness::Signed {
                        self.mark_signed(t);
                        self.mark_signed(d_hi);
                    }
                    return t;
                }
                BinOp::Eq => {
                    self.emit(IrOp::CmpEq16 {
                        dest: t,
                        a_lo,
                        a_hi,
                        b_lo,
                        b_hi,
                    });
                    return t;
                }
                BinOp::NotEq => {
                    self.emit(IrOp::CmpNe16 {
                        dest: t,
                        a_lo,
                        a_hi,
                        b_lo,
                        b_hi,
                    });
                    return t;
                }
                BinOp::Lt => {
                    self.emit(IrOp::CmpLt16 {
                        dest: t,
                        a_lo,
                        a_hi,
                        b_lo,
                        b_hi,
                        signed: sign,
                    });
                    return t;
                }
                BinOp::Gt => {
                    self.emit(IrOp::CmpGt16 {
                        dest: t,
                        a_lo,
                        a_hi,
                        b_lo,
                        b_hi,
                        signed: sign,
                    });
                    return t;
                }
                BinOp::LtEq => {
                    self.emit(IrOp::CmpLtEq16 {
                        dest: t,
                        a_lo,
                        a_hi,
                        b_lo,
                        b_hi,
                        signed: sign,
                    });
                    return t;
                }
                BinOp::GtEq => {
                    self.emit(IrOp::CmpGtEq16 {
                        dest: t,
                        a_lo,
                        a_hi,
                        b_lo,
                        b_hi,
                        signed: sign,
                    });
                    return t;
                }
                // Other operators fall through to the 8-bit path
                // below, truncating the wide operand to its low
                // byte. This is intentional for bitwise/shift ops
                // which are rarely used on u16 values in NES code.
                _ => {}
            }
        }

        match op {
            BinOp::Add => self.emit(IrOp::Add(t, l, r)),
            BinOp::Sub => self.emit(IrOp::Sub(t, l, r)),
            BinOp::Mul => self.emit(IrOp::Mul(t, l, r)),
            BinOp::BitwiseAnd => self.emit(IrOp::And(t, l, r)),
            BinOp::BitwiseOr => self.emit(IrOp::Or(t, l, r)),
            BinOp::BitwiseXor => self.emit(IrOp::Xor(t, l, r)),
            BinOp::Eq => self.emit(IrOp::CmpEq(t, l, r)),
            BinOp::NotEq => self.emit(IrOp::CmpNe(t, l, r)),
            BinOp::Lt => self.emit(IrOp::CmpLt(t, l, r, sign)),
            BinOp::Gt => self.emit(IrOp::CmpGt(t, l, r, sign)),
            BinOp::LtEq => self.emit(IrOp::CmpLtEq(t, l, r, sign)),
            BinOp::GtEq => self.emit(IrOp::CmpGtEq(t, l, r, sign)),
            BinOp::ShiftLeft => self.emit(IrOp::ShiftLeftVar(t, l, r)),
            BinOp::ShiftRight => self.emit(IrOp::ShiftRightVar(t, l, r)),
            BinOp::Div => self.emit(IrOp::Div(t, l, r)),
            BinOp::Mod => self.emit(IrOp::Mod(t, l, r)),
            BinOp::And | BinOp::Or => unreachable!("handled above"),
        }

        if sign == Signedness::Signed
            && matches!(
                op,
                BinOp::Add | BinOp::Sub | BinOp::Mul | BinOp::Div | BinOp::Mod
            )
        {
            self.mark_signed(t);
        }

        t
    }

    /// Emit an IR "move" from `src` to `dest`: `dest = src | 0`.
    /// Used to merge values from different control-flow paths.
    fn emit_move(&mut self, dest: IrTemp, src: IrTemp) {
        let zero = self.fresh_temp();
        self.emit(IrOp::LoadImm(zero, 0));
        self.emit(IrOp::Or(dest, src, zero));
    }

    fn lower_logical_and(&mut self, left: &Expr, right: &Expr) -> IrTemp {
        let result = self.fresh_temp();
        let right_label = self.fresh_label("and_right");
        let end_label = self.fresh_label("and_end");
        let false_label = self.fresh_label("and_false");

        let l = self.lower_expr(left);
        self.end_block(IrTerminator::Branch(
            l,
            right_label.clone(),
            false_label.clone(),
        ));

        // Right side (only evaluated if left is true)
        self.start_block(&right_label);
        let r = self.lower_expr(right);
        self.emit_move(result, r);
        self.end_block(IrTerminator::Jump(end_label.clone()));

        // False path
        self.start_block(&false_label);
        self.emit(IrOp::LoadImm(result, 0));
        self.end_block(IrTerminator::Jump(end_label.clone()));

        // Merge
        self.start_block(&end_label);
        result
    }

    fn lower_logical_or(&mut self, left: &Expr, right: &Expr) -> IrTemp {
        let result = self.fresh_temp();
        let right_label = self.fresh_label("or_right");
        let end_label = self.fresh_label("or_end");
        let true_label = self.fresh_label("or_true");

        let l = self.lower_expr(left);
        self.end_block(IrTerminator::Branch(
            l,
            true_label.clone(),
            right_label.clone(),
        ));

        // True path (left was true)
        self.start_block(&true_label);
        self.emit(IrOp::LoadImm(result, 1));
        self.end_block(IrTerminator::Jump(end_label.clone()));

        // Right side
        self.start_block(&right_label);
        let r = self.lower_expr(right);
        self.emit_move(result, r);
        self.end_block(IrTerminator::Jump(end_label.clone()));

        // Merge
        self.start_block(&end_label);
        result
    }
}

/// True if `stmt` is simple enough for the inliner to splice
/// into a caller without a CFG rewrite. Accepted shapes: plain
/// assignments, statement-context calls, draws, scroll/set
/// palette / load background, `wait_frame`, inline asm, and the
/// `debug.log` / `debug.assert` builtins. Rejected: any shape with
/// control flow (if/while/loop/for/match/return/break/continue
/// /transition) because those would require cloning basic
/// blocks and renumbering labels per call site, which is
/// more than the simple substitution machinery can handle.
fn is_splicable_void_stmt(stmt: &Statement) -> bool {
    matches!(
        stmt,
        Statement::Assign(..)
            | Statement::Call(..)
            | Statement::Draw(..)
            | Statement::Scroll(..)
            | Statement::SetPalette(..)
            | Statement::LoadBackground(..)
            | Statement::PaintRoom(..)
            | Statement::WaitFrame(..)
            | Statement::CycleSprites(..)
            | Statement::Play(..)
            | Statement::StartMusic(..)
            | Statement::StopMusic(..)
            | Statement::InlineAsm(..)
            | Statement::RawAsm(..)
            | Statement::DebugLog(..)
            | Statement::DebugAssert(..)
    )
}

/// True if an `inline fun` with the given return type and body
/// matches one of the shapes [`LoweringContext::capture_inline_bodies`]
/// can splice into a caller. Two shapes are recognised:
///
/// 1. **Single-return expression**: the function has a declared
///    return type and its body is exactly `{ return <expr> }`.
/// 2. **Void multi-statement**: the function has no return type
///    and every body statement passes [`is_splicable_void_stmt`].
///
/// Anything else (conditional early returns, loops, nested
/// control flow, multiple returns, an empty void body) falls back
/// to a regular `JSR` call at every site. The analyzer calls this
/// to emit `W0110` when a declared-inline function won't actually
/// be inlined, and the IR lowerer calls the same logic when it
/// decides which bodies to capture — keeping both sides in sync.
#[must_use]
pub fn can_inline_fun(return_type: Option<&NesType>, body: &Block) -> bool {
    // Single-return expression shape.
    if return_type.is_some()
        && body.statements.len() == 1
        && matches!(body.statements[0], Statement::Return(Some(_), _))
    {
        return true;
    }
    // Void multi-statement shape.
    if return_type.is_none()
        && !body.statements.is_empty()
        && body.statements.iter().all(is_splicable_void_stmt)
    {
        return true;
    }
    false
}

/// True if `body` contains any `Statement::InlineAsm`. Used by the
/// `inline fun` splicer to decide whether all-constant arguments are
/// required (asm `{param}` substitution can only synthesise a
/// `#$<value>` immediate at expansion time, not a runtime address).
///
/// We deliberately don't recurse into nested statements: an inline
/// fun's body is gated by [`is_splicable_void_stmt`], which only
/// admits flat sequences of `Assign`/`Call`/`Draw`/`InlineAsm`/etc.
/// — never `If`/`While`/`Loop`/`For` — so any inline-asm statement
/// that's reachable shows up at the top level. Single-return-
/// expression bodies can't contain asm at all (asm is a statement,
/// not an expression). If `is_splicable_void_stmt` ever loosens to
/// admit nested control flow, this check needs to follow.
fn body_has_inline_asm(body: &InlineBody) -> bool {
    match body {
        InlineBody::Expression(_) => false,
        InlineBody::Void(stmts) => stmts.iter().any(stmt_contains_inline_asm),
    }
}

fn stmt_contains_inline_asm(stmt: &Statement) -> bool {
    matches!(stmt, Statement::InlineAsm(..))
}

/// Replace `{name}` tokens in an inline-asm body with `#$<value>`
/// immediate-mode operands, using the per-frame constant map built
/// by `try_inline_call_stmt`. Names not in the map are left alone
/// so the codegen's `substitute_asm_vars` can still resolve them
/// (e.g. `{wk}` for a global array's address).
///
/// Walks `body` as Unicode chars to preserve any non-ASCII content
/// (typically comments) verbatim. The `{` / `}` braces and the
/// identifier characters inside them are all ASCII, so the
/// byte-level brace search is safe — it can't mis-fire on a UTF-8
/// continuation byte.
fn substitute_inline_const_params(body: &str, consts: &HashMap<String, u8>) -> String {
    let mut out = String::with_capacity(body.len());
    let bytes = body.as_bytes();
    let mut i = 0;
    while i < bytes.len() {
        if bytes[i] == b'{' {
            if let Some(end) = bytes[i + 1..].iter().position(|&b| b == b'}') {
                let name_start = i + 1;
                let name_end = i + 1 + end;
                let name = &body[name_start..name_end];
                let is_ident = !name.is_empty()
                    && name
                        .chars()
                        .next()
                        .is_some_and(|c| c == '_' || c.is_ascii_alphabetic())
                    && name.chars().all(|c| c == '_' || c.is_ascii_alphanumeric());
                if is_ident {
                    if let Some(&val) = consts.get(name) {
                        use std::fmt::Write;
                        let _ = write!(out, "#${val:02X}");
                        i = name_end + 1;
                        continue;
                    }
                }
            }
        }
        // Pass the next char through verbatim, copying all of its
        // UTF-8 bytes in one go so multi-byte characters in
        // comments survive intact.
        let ch_len = utf8_char_len(bytes[i]);
        out.push_str(&body[i..i + ch_len]);
        i += ch_len;
    }
    out
}

/// Length in bytes of the UTF-8 character whose lead byte is
/// `lead`. UTF-8 lead bytes encode the length in the count of
/// leading 1-bits: `0xxx_xxxx` = 1, `110x_xxxx` = 2, `1110_xxxx`
/// = 3, `1111_0xxx` = 4. Continuation bytes (`10xx_xxxx`) shouldn't
/// appear at a char boundary; if one does we return 1 so iteration
/// still makes progress on malformed input.
fn utf8_char_len(lead: u8) -> usize {
    match lead {
        0x00..=0x7F => 1,
        0xC0..=0xDF => 2,
        0xE0..=0xEF => 3,
        0xF0..=0xFF => 4,
        _ => 1,
    }
}

fn type_size(t: &NesType) -> u16 {
    match t {
        NesType::U8 | NesType::I8 | NesType::Bool => 1,
        NesType::U16 | NesType::I16 => 2,
        NesType::Array(elem, count) => type_size(elem) * count,
        // Struct sizes are resolved in the analyzer. IR lowering only
        // sees struct types on `var` declarations, which are skipped
        // below via the analyzer's synthetic field allocations.
        NesType::Struct(_) => 0,
    }
}

fn button_mask(button: &str) -> u8 {
    match button {
        "a" => 0x80,
        "b" => 0x40,
        "select" => 0x20,
        "start" => 0x10,
        "up" => 0x08,
        "down" => 0x04,
        "left" => 0x02,
        "right" => 0x01,
        _ => 0x00,
    }
}

/// Build the IR op for a compound-assignment `lhs OP= rhs`. The
/// `rhs_expr` is consulted for shift counts so `x <<= 3` becomes
/// `ShiftLeft(result, current, 3)` rather than a runtime shift. All
/// other operators just map to their 3-address form over the already-
/// lowered temps.
fn compound_assign_op(
    op: AssignOp,
    result: IrTemp,
    current: IrTemp,
    rhs: IrTemp,
    rhs_expr: &Expr,
    ctx: &LoweringContext,
) -> IrOp {
    match op {
        AssignOp::PlusAssign => IrOp::Add(result, current, rhs),
        AssignOp::MinusAssign => IrOp::Sub(result, current, rhs),
        AssignOp::AmpAssign => IrOp::And(result, current, rhs),
        AssignOp::PipeAssign => IrOp::Or(result, current, rhs),
        AssignOp::CaretAssign => IrOp::Xor(result, current, rhs),
        AssignOp::ShiftLeftAssign => {
            if let Some(n) = ctx.eval_const(rhs_expr) {
                IrOp::ShiftLeft(result, current, n.min(8) as u8)
            } else {
                IrOp::ShiftLeftVar(result, current, rhs)
            }
        }
        AssignOp::ShiftRightAssign => {
            if let Some(n) = ctx.eval_const(rhs_expr) {
                IrOp::ShiftRight(result, current, n.min(8) as u8)
            } else {
                IrOp::ShiftRightVar(result, current, rhs)
            }
        }
        AssignOp::Assign => unreachable!(),
    }
}
