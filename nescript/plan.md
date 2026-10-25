# NEScript Compiler — Engineering Design & Implementation Plan

**Version 0.1 — Draft**

---

## 1. Executive Summary

This document describes the architecture, implementation strategy, and milestone plan for the NEScript compiler: a Rust-based toolchain that compiles NEScript source files into iNES-format NES ROMs. The compiler owns the entire pipeline from source text to playable ROM, with no external assembler or linker dependencies.

The plan is structured around five milestones, each producing a working compiler that generates a playable ROM demonstrating progressively more language features. The first milestone targets a "sprite on screen, moving with the d-pad" demo in approximately 4–6 weeks of focused development.

---

## 2. Architecture Overview

### 2.1 Pipeline

```
                          ┌─────────────────────────────────────────┐
                          │           NEScript Compiler              │
                          │                (nescript)                │
                          │                                         │
  .ne source ────────────►│  Lexer ──► Parser ──► Analyzer ──►      │
  .png assets             │                                         │
  .ftm/.nsf audio         │  IR Lowering ──► Optimizer ──►          │
                          │                                         │
                          │  Codegen ──► Assembler ──► ROM Builder  │
                          │                                         │
                          └──────────┬──────────┬──────────┬────────┘
                                     │          │          │
                                  game.nes   game.dbg   game.map
                                  (ROM)      (symbols)  (memory map)
```

### 2.2 Compilation Phases

| Phase           | Input              | Output                | Key Responsibility                                      |
|-----------------|--------------------|------------------------|----------------------------------------------------------|
| **Lexer**       | Source text         | Token stream           | Tokenization, string/number literal parsing              |
| **Parser**      | Token stream        | AST                    | Syntax validation, tree construction                     |
| **Analyzer**    | AST                 | Annotated AST          | Type checking, call graph, depth limits, scope resolution|
| **IR Lowering** | Annotated AST       | NEScript IR            | Flatten expressions, expand u16 ops, resolve sugar       |
| **Optimizer**   | IR                  | Optimized IR           | Constant folding, dead code, ZP promotion, inlining      |
| **Codegen**     | Optimized IR        | 6502 instruction list  | Register allocation, instruction selection               |
| **Assembler**   | 6502 instructions   | Byte sequences + fixups| Opcode encoding, address resolution                      |
| **ROM Builder** | Bytes + assets      | .nes file              | Bank layout, vectors, iNES header                        |

### 2.3 Design Principles for the Compiler Itself

1. **Single binary, zero dependencies.** The compiler is one Rust binary. No need to install ca65, Python, or Node. Asset conversion (PNG → CHR) is built in.
2. **Fast compilation.** NES games are small. Compilation should be under 1 second for any reasonable project. No incremental compilation needed for v1.
3. **Excellent errors.** Every error message includes the source location, a clear explanation, and a `help:` suggestion where possible. Errors are the primary teaching tool.
4. **Testable at every layer.** Each compiler phase is a pure function (input → output) with no global state, enabling unit testing in isolation.

---

## 3. Rust Project Structure

```
nescript/
├── Cargo.toml
├── Cargo.lock
├── src/
│   ├── main.rs                  // CLI entry point (clap-based)
│   ├── lib.rs                   // Library root — exposes all phases
│   │
│   ├── lexer/
│   │   ├── mod.rs               // Lexer public API
│   │   ├── token.rs             // Token enum and Span type
│   │   └── tests.rs
│   │
│   ├── parser/
│   │   ├── mod.rs               // Recursive descent parser
│   │   ├── ast.rs               // AST node definitions
│   │   └── tests.rs
│   │
│   ├── analyzer/
│   │   ├── mod.rs               // Orchestrates analysis passes
│   │   ├── types.rs             // Type checking
│   │   ├── scope.rs             // Scope/symbol table management
│   │   ├── call_graph.rs        // Call graph + depth analysis
│   │   └── tests.rs
│   │
│   ├── ir/
│   │   ├── mod.rs               // IR type definitions
│   │   ├── lowering.rs          // AST → IR translation
│   │   └── tests.rs
│   │
│   ├── optimizer/
│   │   ├── mod.rs               // Optimization pass runner
│   │   ├── const_fold.rs        // Constant folding
│   │   ├── dead_code.rs         // Dead code elimination
│   │   ├── zp_promote.rs        // Zero-page promotion analysis
│   │   ├── inliner.rs           // Function inlining
│   │   └── tests.rs
│   │
│   ├── codegen/
│   │   ├── mod.rs               // IR → 6502 instruction selection
│   │   ├── regalloc.rs          // A/X/Y register allocation
│   │   ├── patterns.rs          // Instruction patterns (idiom matching)
│   │   └── tests.rs
│   │
│   ├── asm/
│   │   ├── mod.rs               // Assembler public API
│   │   ├── opcodes.rs           // 6502 opcode table (56 instructions × addressing modes)
│   │   ├── encode.rs            // Instruction → bytes
│   │   ├── addressing.rs        // Addressing mode types and resolution
│   │   └── tests.rs
│   │
│   ├── linker/
│   │   ├── mod.rs               // Bank layout and address assignment
│   │   ├── banks.rs             // Bank allocation logic
│   │   ├── fixups.rs            // Address fixup/relocation
│   │   └── tests.rs
│   │
│   ├── rom/
│   │   ├── mod.rs               // iNES ROM builder
│   │   ├── header.rs            // iNES header generation
│   │   ├── vectors.rs           // NMI/RESET/IRQ vector table
│   │   └── tests.rs
│   │
│   ├── assets/
│   │   ├── mod.rs               // Asset pipeline orchestration
│   │   ├── chr.rs               // PNG → CHR tile conversion
│   │   ├── nametable.rs         // PNG → nametable + tile set
│   │   ├── palette.rs           // Color extraction and NES palette mapping
│   │   ├── audio.rs             // FamiTracker/NSF import (stub for v1)
│   │   └── tests.rs
│   │
│   ├── runtime/
│   │   ├── mod.rs               // Built-in runtime code
│   │   ├── init.rs              // NES hardware initialization sequence
│   │   ├── nmi.rs               // NMI handler generation
│   │   ├── input.rs             // Controller read routine
│   │   ├── oam.rs               // OAM DMA setup
│   │   ├── ppu.rs               // PPU helper routines
│   │   └── math.rs              // Software multiply/divide routines
│   │
│   ├── debug/
│   │   ├── mod.rs               // Debug instrumentation
│   │   ├── source_map.rs        // ROM address → source location mapping
│   │   ├── symbols.rs           // Symbol table output (Mesen-compatible)
│   │   └── checks.rs            // Runtime check code generation
│   │
│   ├── reports/
│   │   ├── mod.rs               // Human-readable reports
│   │   ├── memory_map.rs        // Memory map report generator
│   │   └── call_graph.rs        // Call graph report generator
│   │
│   └── errors/
│       ├── mod.rs               // Error types and formatting
│       ├── diagnostic.rs        // Diagnostic struct with spans
│       └── render.rs            // Terminal rendering with color and context
│
├── runtime_asm/
│   ├── init.s                   // Reference 6502 init sequence
│   ├── nmi.s                    // Reference NMI handler
│   └── input.s                  // Reference controller read
│
├── tests/
│   ├── integration/
│   │   ├── hello_sprite.ne      // Minimal test: sprite on screen
│   │   ├── input_test.ne        // Controller input test
│   │   ├── state_machine.ne     // State transition test
│   │   ├── coin_cavern.ne       // Full sample game
│   │   └── expected/            // Expected ROM outputs (golden files)
│   │
│   ├── error_tests/
│   │   ├── recursion.ne         // Should produce E0402
│   │   ├── type_mismatch.ne     // Should produce E0201
│   │   ├── depth_exceeded.ne    // Should produce E0401
│   │   └── zp_overflow.ne       // Should produce E0301
│   │
│   └── asm_tests/
│       ├── opcode_tests.rs      // Verify every 6502 opcode encodes correctly
│       └── addressing_tests.rs  // Verify addressing mode resolution
│
├── examples/
│   ├── hello_world.ne           // Minimal "hello" program
│   ├── coin_cavern.ne           // Full sample game from spec
│   └── assets/                  // Sample PNGs, audio files
│
└── docs/
    ├── language_spec.md         // NEScript language specification
    ├── architecture.md          // This document
    └── nes_reference.md         // NES hardware quick reference for contributors
```

---

## 4. Key Data Structures

### 4.1 Tokens

```rust
#[derive(Debug, Clone, PartialEq)]
pub struct Token {
    pub kind: TokenKind,
    pub span: Span,
}

#[derive(Debug, Clone, Copy, PartialEq)]
pub struct Span {
    pub file_id: u16,       // index into file table
    pub start: u32,         // byte offset in source
    pub end: u32,
}

#[derive(Debug, Clone, PartialEq)]
pub enum TokenKind {
    // Literals
    IntLiteral(u16),
    StringLiteral(String),
    BoolLiteral(bool),

    // Identifiers and keywords
    Ident(String),
    KwGame, KwState, KwOn, KwFun, KwVar, KwConst,
    KwIf, KwElse, KwWhile, KwBreak, KwContinue, KwReturn,
    KwTrue, KwFalse, KwNot, KwAnd, KwOr,
    KwFast, KwSlow, KwInline,
    KwInclude, KwStart, KwTransition,
    KwSprite, KwBackground, KwPalette, KwSfx, KwMusic,
    KwDraw, KwPlay, KwStopMusic, KwStartMusic,
    KwLoadBackground, KwSetPalette, KwScroll,
    KwAsm, KwRaw, KwBank,
    KwLoop, KwWaitFrame,
    KwU8, KwI8, KwU16, KwBool,
    KwDebug, KwAs,

    // Symbols
    LParen, RParen, LBrace, RBrace, LBracket, RBracket,
    Comma, Colon, Semicolon, Arrow,     // ->
    Dot,
    At,                                  // @

    // Operators
    Plus, Minus, Star, Slash, Percent,
    Amp, Pipe, Caret, Tilde,
    ShiftLeft, ShiftRight,
    Eq, NotEq, Lt, Gt, LtEq, GtEq,
    Assign, PlusAssign, MinusAssign,
    AmpAssign, PipeAssign, CaretAssign,
    ShiftLeftAssign, ShiftRightAssign,

    // Special
    Eof,
    AsmBody(String),                     // raw asm content between { }
}
```

### 4.2 AST Nodes

```rust
pub struct Program {
    pub game: GameDecl,
    pub includes: Vec<IncludeDecl>,
    pub globals: Vec<VarDecl>,
    pub constants: Vec<ConstDecl>,
    pub functions: Vec<FunDecl>,
    pub states: Vec<StateDecl>,
    pub sprites: Vec<SpriteDecl>,
    pub backgrounds: Vec<BackgroundDecl>,
    pub palettes: Vec<PaletteDecl>,
    pub sound_effects: Vec<SfxDecl>,
    pub music_tracks: Vec<MusicDecl>,
    pub banks: Vec<BankDecl>,
    pub start_state: String,
    pub span: Span,
}

pub struct GameDecl {
    pub name: String,
    pub mapper: Mapper,
    pub mirroring: Mirroring,
    pub stack_depth: u8,
    pub span: Span,
}

pub struct StateDecl {
    pub name: String,
    pub locals: Vec<VarDecl>,
    pub on_enter: Option<Block>,
    pub on_exit: Option<Block>,
    pub on_frame: Option<Block>,
    pub on_scanline: Vec<(u8, Block)>,
    pub span: Span,
}

pub struct FunDecl {
    pub name: String,
    pub params: Vec<Param>,
    pub return_type: Option<NesType>,
    pub body: Block,
    pub is_inline: bool,
    pub span: Span,
}

pub struct VarDecl {
    pub name: String,
    pub var_type: NesType,
    pub init: Option<Expr>,
    pub placement: Placement,        // Fast, Slow, Auto
    pub span: Span,
}

#[derive(Debug, Clone, PartialEq)]
pub enum NesType {
    U8,
    I8,
    U16,
    Bool,
    Array(Box<NesType>, u16),        // element type, fixed size
}

#[derive(Debug, Clone)]
pub enum Expr {
    IntLiteral(u16, Span),
    BoolLiteral(bool, Span),
    Ident(String, Span),
    ArrayIndex(String, Box<Expr>, Span),
    ArrayLiteral(Vec<Expr>, Span),
    BinaryOp(Box<Expr>, BinOp, Box<Expr>, Span),
    UnaryOp(UnaryOp, Box<Expr>, Span),
    Call(String, Vec<Expr>, Span),
    Cast(Box<Expr>, NesType, Span),
    ButtonRead(Option<Player>, String, Span),  // p1/p2, button name
}

#[derive(Debug, Clone)]
pub enum Statement {
    VarDecl(VarDecl),
    Assign(LValue, AssignOp, Expr, Span),
    If(Expr, Block, Vec<(Expr, Block)>, Option<Block>, Span),
    While(Expr, Block, Span),
    Loop(Block, Span),
    Break(Span),
    Continue(Span),
    Return(Option<Expr>, Span),
    Draw(DrawStmt, Span),
    Play(String, Span),
    StartMusic(String, Span),
    StopMusic(Span),
    Transition(String, Span),
    LoadBackground(String, Span),
    SetPalette(String, Span),
    Scroll(Expr, Expr, Span),
    WaitFrame(Span),
    Call(String, Vec<Expr>, Span),
    Asm(String, Vec<AsmBinding>, Span),     // body, variable bindings
    RawAsm(String, Span),
    DebugLog(Vec<Expr>, Span),
    DebugOverlay(Vec<Expr>, Span),
    DebugAssert(Expr, Option<String>, Span),
}
```

### 4.3 Intermediate Representation

The IR is a flat, register-agnostic representation that maps closely to 6502 operations without committing to specific registers or addresses.

```rust
pub struct IrProgram {
    pub functions: Vec<IrFunction>,
    pub globals: Vec<IrGlobal>,
    pub rom_data: Vec<IrRomBlock>,       // constant data, asset data
}

pub struct IrFunction {
    pub name: String,
    pub blocks: Vec<IrBasicBlock>,
    pub locals: Vec<IrLocal>,
    pub source_span: Span,
}

pub struct IrBasicBlock {
    pub label: String,
    pub ops: Vec<IrOp>,
    pub terminator: IrTerminator,
}

#[derive(Debug, Clone)]
pub enum IrOp {
    // Load/Store
    LoadImm(IrTemp, u8),                    // temp = immediate
    LoadVar(IrTemp, VarId),                 // temp = variable
    StoreVar(VarId, IrTemp),                // variable = temp

    // Arithmetic (8-bit)
    Add(IrTemp, IrTemp, IrTemp),            // dest = a + b
    Sub(IrTemp, IrTemp, IrTemp),
    And(IrTemp, IrTemp, IrTemp),
    Or(IrTemp, IrTemp, IrTemp),
    Xor(IrTemp, IrTemp, IrTemp),
    ShiftLeft(IrTemp, IrTemp, u8),
    ShiftRight(IrTemp, IrTemp, u8),
    Negate(IrTemp, IrTemp),                 // dest = -src (two's complement)
    Complement(IrTemp, IrTemp),             // dest = ~src

    // 16-bit operations (expanded from u16 expressions)
    Add16(IrTemp, IrTemp, IrTemp),          // dest_lo/hi = a_lo/hi + b_lo/hi
    Sub16(IrTemp, IrTemp, IrTemp),
    LoadImm16(IrTemp, u16),
    LoadVar16(IrTemp, VarId),
    StoreVar16(VarId, IrTemp),

    // Comparison (sets a boolean temp)
    CmpEq(IrTemp, IrTemp, IrTemp),
    CmpNe(IrTemp, IrTemp, IrTemp),
    CmpLt(IrTemp, IrTemp, IrTemp),          // signed or unsigned variant
    CmpGt(IrTemp, IrTemp, IrTemp),
    CmpLtU(IrTemp, IrTemp, IrTemp),         // explicitly unsigned
    CmpGtU(IrTemp, IrTemp, IrTemp),

    // Array access
    ArrayLoad(IrTemp, VarId, IrTemp),       // dest = array[index]
    ArrayStore(VarId, IrTemp, IrTemp),      // array[index] = value

    // Function call
    Call(Option<IrTemp>, String, Vec<IrTemp>),  // dest = func(args)

    // Hardware operations
    DrawSprite(SpriteId, IrTemp, IrTemp, IrTemp, IrTemp, IrTemp),
    PlaySfx(SfxId),
    StartMusic(MusicId),
    StopMusic,
    ReadInput,
    WaitFrame,
    SetScroll(IrTemp, IrTemp),
    LoadBackground(BackgroundId),
    SetPalette(PaletteId),

    // Debug (stripped in release)
    DebugLog(Vec<IrTemp>),
    DebugAssert(IrTemp, String),

    // Source mapping
    SourceLoc(Span),
}

#[derive(Debug, Clone)]
pub enum IrTerminator {
    Jump(String),                           // unconditional jump to label
    Branch(IrTemp, String, String),         // if temp then label_t else label_f
    Return(Option<IrTemp>),
    Transition(String),                     // state transition
    Unreachable,
}

// IrTemp is a virtual register — unlimited supply, resolved during codegen
#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash)]
pub struct IrTemp(pub u32);

// VarId uniquely identifies a variable across the program
#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash)]
pub struct VarId(pub u32);
```

### 4.4 6502 Instruction Representation

```rust
#[derive(Debug, Clone)]
pub struct Instruction {
    pub opcode: Opcode,
    pub mode: AddressingMode,
    pub source: Option<Span>,               // link back to NEScript source
}

#[derive(Debug, Clone, Copy, PartialEq)]
pub enum Opcode {
    LDA, LDX, LDY, STA, STX, STY,
    ADC, SBC, AND, ORA, EOR,
    ASL, LSR, ROL, ROR,
    INC, DEC, INX, INY, DEX, DEY,
    CMP, CPX, CPY, BIT,
    JMP, JSR, RTS, RTI,
    BEQ, BNE, BCC, BCS, BMI, BPL, BVC, BVS,
    CLC, SEC, CLI, SEI, CLV, CLD, SED,
    PHA, PLA, PHP, PLP,
    TAX, TAY, TXA, TYA, TSX, TXS,
    NOP, BRK,
}

#[derive(Debug, Clone)]
pub enum AddressingMode {
    Implied,                                // CLC, RTS, etc.
    Accumulator,                            // ASL A
    Immediate(u8),                          // LDA #$FF
    ZeroPage(u8),                           // LDA $10
    ZeroPageX(u8),                          // LDA $10,X
    ZeroPageY(u8),                          // LDX $10,Y
    Absolute(u16),                          // LDA $8000
    AbsoluteX(u16),                         // LDA $8000,X
    AbsoluteY(u16),                         // LDA $8000,Y
    Indirect(u16),                          // JMP ($FFFC)
    IndirectX(u8),                          // LDA ($10,X)
    IndirectY(u8),                          // LDA ($10),Y
    Relative(i8),                           // BEQ +5  (branch offset)

    // Pre-resolution symbolic forms (resolved by linker)
    Label(String),                          // JMP some_label
    LabelRelative(String),                  // BEQ some_label
    SymbolLo(String),                       // LDA #<some_address
    SymbolHi(String),                       // LDA #>some_address
}
```

---

## 5. Phase Details

### 5.1 Lexer

**Implementation:** Hand-written scanner (no parser generator). NEScript's lexical grammar is simple enough that a hand-written lexer is clearer and produces better error messages than a generated one.

**Key behavior:**
- Tracks byte offset, line, and column for every token.
- `asm { ... }` blocks: when the lexer encounters `asm` followed by `{`, it switches to a raw-capture mode that collects everything until the matching `}`, respecting nested braces. The content is emitted as a single `AsmBody` token.
- Numeric literal parsing handles decimal, hex (`0x`), and binary (`0b`) prefixes.
- Unterminated strings and unknown characters produce error tokens with descriptive messages rather than panicking.

**Estimated size:** ~400 lines of Rust.

### 5.2 Parser

**Implementation:** Recursive descent, single-token lookahead. The grammar is LL(1)-friendly by design. No ambiguities requiring backtracking.

**Key decisions:**
- `draw` statements use a keyword-argument syntax that looks like `draw SpriteName frame: expr at: (expr, expr)`. The parser recognizes `draw` as a statement keyword, then consumes named property pairs until it hits a statement-ending token (newline at same indentation, `}`, or another statement keyword). Properties can appear in any order.
- Operator precedence is handled via Pratt parsing (precedence climbing) for expressions.
- Error recovery: on a parse error, the parser skips to the next statement boundary (`;`, `}`, or a keyword that starts a new declaration) and continues. This allows reporting multiple errors per compilation.

**Estimated size:** ~800 lines of Rust.

### 5.3 Semantic Analyzer

This is the most complex phase. It performs multiple passes over the AST:

**Pass 1 — Symbol Resolution:**
Build a symbol table. Resolve all identifier references to their declarations. Detect undefined variables, duplicate declarations, and scope violations.

**Pass 2 — Type Checking:**
Verify that all operations have compatible types. Check assignments, function arguments, return types, and array index types. Insert explicit cast nodes where the programmer wrote `as`. Flag implicit coercion attempts as errors.

**Pass 3 — Call Graph Analysis:**
Build a directed graph of function calls. Detect recursion (cycles in the graph). Compute the maximum call depth for every entry point (each `on frame`, `on enter`, etc.). Compare against `stack_depth` and emit errors if exceeded.

**Pass 4 — State Machine Validation:**
Verify that all `transition` targets name real states. Verify that `start` names a real state. Warn if any state is unreachable from the start state.

**Pass 5 — Memory Planning:**
Compute variable lifetimes. Determine which state-local variables can share RAM addresses. Count zero-page demand vs. supply. Assign preliminary memory locations (finalized during codegen/linking).

**Estimated size:** ~1,200 lines of Rust.

### 5.4 IR Lowering

Translates the annotated AST into the flat IR representation:

- Expressions become sequences of IrOps operating on virtual temps.
- `u16` operations expand into paired `u8` operations with carry propagation.
- `if`/`while`/`loop` become basic blocks with branch terminators.
- `on frame` desugars into a loop + wait_frame.
- `draw` statements become `DrawSprite` ops with evaluated sub-expressions.
- `debug.*` statements are either lowered to debug ops (debug mode) or discarded entirely (release mode).
- `button.X_pressed` expressions expand to `(current & mask) AND NOT (previous & mask)`.

**Estimated size:** ~600 lines of Rust.

### 5.5 Optimizer

Runs a sequence of optimization passes over the IR. Each pass is a function `fn optimize(ir: &mut IrProgram)`.

**Constant Folding:** Evaluate operations on known constants at compile time. `3 + 5` becomes `8`. `score > 255` on a `u8` becomes `false`.

**Dead Code Elimination:** Remove ops whose results are never used. Remove basic blocks that are never jumped to.

**Zero-Page Promotion:** Analyze access frequency across hot paths (frame handlers). Rank variables by access count. Assign the hottest variables to zero-page, respecting the `fast`/`slow` hints as hard constraints. Variables marked `fast` get ZP unconditionally (or error if no room). Variables marked `slow` are excluded. Unmarked variables are auto-promoted by rank.

**Function Inlining:** Inline functions marked `inline` or functions under a size threshold (~8 IR ops) that are called from only 1–2 sites.

**Strength Reduction:** Replace multiply/divide by powers of 2 with shifts. Replace `x * 3` with `x + x + x` (three adds are cheaper than a software multiply on the 6502).

**Estimated size:** ~800 lines of Rust.

### 5.6 Code Generation

Translates IR ops into 6502 instructions. This is the heart of the compiler.

**Register Allocation Strategy:**

The 6502 has three registers: A (accumulator, used for all arithmetic), X and Y (index registers, used for array indexing and loops). There is no general register file.

The codegen uses a simple strategy:
1. A is the primary working register. Most IR temps map to A.
2. X is used for array indexing and loop counters.
3. Y is used as a secondary index register.
4. When all three are in use, spill to a set of compiler-reserved zero-page temporaries ($00–$0F).

This is not a full graph-coloring allocator — the 6502's constraints make that overkill. Instead, the codegen walks each basic block linearly, tracking what's currently in A/X/Y, and emitting loads/stores as needed.

**Pattern Matching:**

Common IR sequences map to idiomatic 6502 code:

```
IR: LoadVar(t0, px), LoadImm(t1, 2), Add(t2, t0, t1), StoreVar(px, t2)
6502:
    LDA px          ; load px into A
    CLC
    ADC #2          ; add immediate 2
    STA px          ; store back
```

The codegen has a pattern table for these common cases, falling back to a generic temp-based approach for complex expressions.

**Comparison and Branching:**

The 6502 has no "compare and branch" — it sets flags with CMP, then branches on flags. The codegen maps:
- `==` → CMP + BEQ
- `!=` → CMP + BNE
- `<` (unsigned) → CMP + BCC
- `>=` (unsigned) → CMP + BCS
- Signed comparisons require additional flag checks (N xor V).

**Estimated size:** ~1,000 lines of Rust.

### 5.7 Assembler

Encodes 6502 instructions into bytes. The 6502 is well-documented and regular.

**Implementation:**
- A lookup table maps (Opcode, AddressingMode) → u8 opcode byte.
- Instructions are 1, 2, or 3 bytes depending on addressing mode.
- Labels are resolved in two passes: first pass collects label addresses, second pass fills in references.
- Branch instructions (BEQ, BNE, etc.) use relative addressing (signed 8-bit offset). If a branch target is out of range (>127 bytes away), the assembler automatically rewrites it as the inverse branch over a JMP (e.g., BEQ +3 / JMP far_target).

**Opcode table dimensions:** 56 unique instructions × ~12 addressing modes = ~150 valid combinations. The full table fits in a static array.

**Estimated size:** ~500 lines of Rust (including the opcode table).

### 5.8 Linker / ROM Builder

Arranges compiled code and data into the final ROM image.

**For NROM (no banking):**
1. Lay out PRG ROM starting at $8000 (32 KB) or $C000 (16 KB).
2. Place the runtime init code at the RESET vector entry.
3. Place the NMI handler.
4. Place all compiled functions and state handlers.
5. Place constant data (lookup tables, palette data, nametable data).
6. Write the interrupt vector table at $FFFA: NMI, RESET, IRQ addresses.
7. Place CHR data (tiles) into the CHR ROM section.
8. Prepend the 16-byte iNES header.
9. Write the .nes file.

**For banked mappers:**
The linker manages multiple PRG banks. The fixed bank contains the runtime, NMI handler, and trampoline stubs. Switchable banks contain state code and associated data. The linker verifies that no single bank exceeds its size limit and that cross-bank references go through trampolines.

**Estimated size:** ~400 lines of Rust.

### 5.9 Runtime Library

The compiler emits a small runtime library embedded in every ROM. This is not a separate file — the codegen emits these routines directly.

**Components:**

| Routine              | Size (est.) | Purpose                                         |
|----------------------|-------------|--------------------------------------------------|
| Hardware init        | ~80 bytes   | Disable IRQ, reset PPU, clear RAM, set stack     |
| NMI handler          | ~60 bytes   | OAM DMA, PPU updates, set vblank flag            |
| Controller read      | ~40 bytes   | Read joypad register, compute pressed/released   |
| OAM buffer clear     | ~20 bytes   | Zero the OAM shadow buffer each frame            |
| State dispatcher     | ~30 bytes   | Jump table for active state's frame handler      |
| Software multiply    | ~50 bytes   | 8×8→16 multiply (included only if used)          |
| Software divide      | ~60 bytes   | 8÷8→8 divide (included only if used)             |
| PPU write helpers     | ~40 bytes   | Palette write, nametable write routines          |
| Debug output (debug) | ~30 bytes   | Write to debug port $4800 (stripped in release)  |

**Total runtime overhead:** ~300–400 bytes in release mode (out of 32,768). This is well within budget.

---

## 6. Asset Pipeline

### 6.1 PNG → CHR Conversion

**Dependencies:** The `image` crate (pure Rust, no system dependencies) for PNG decoding.

**Process:**
1. Load PNG image.
2. Divide into 8×8 pixel grid.
3. For each tile, extract the 4 most-used colors and map to NES palette indices (2-bit depth).
4. Encode each tile as 16 bytes of CHR data (two bitplanes, 8 bytes each).
5. Optionally deduplicate tiles (for nametable conversion).

**Color mapping:** The compiler includes a reference table of all 64 NES colors in RGB. Source image colors are mapped to the nearest NES color by Euclidean distance in RGB space. The compiler warns if a source color is far from any NES color.

### 6.2 PNG → Nametable Conversion

1. Convert the full 256×240 image into 8×8 tiles as above.
2. Deduplicate tiles (NES nametable is 960 tile indices, but CHR ROM holds at most 256 unique tiles per bank).
3. Build the 960-byte nametable (tile indices) and 64-byte attribute table (palette assignments per 16×16 pixel region).
4. Emit tile data to CHR ROM and nametable data to PRG ROM.
5. Error if more than 256 unique tiles are needed (NES hardware limit).

### 6.3 Audio (Deferred)

For v1, audio asset handling is stubbed. The `@sfx()` and `@music()` directives will accept pre-formatted binary data via `@binary()` as a workaround. Full FamiTracker import is a v2 feature.

---

## 7. Error System

### 7.1 Error Architecture

```rust
pub struct Diagnostic {
    pub level: Level,            // Error, Warning, Info
    pub code: ErrorCode,         // E0201, W0101, etc.
    pub message: String,         // primary message
    pub span: Span,              // primary source location
    pub labels: Vec<Label>,      // secondary annotations
    pub help: Option<String>,    // actionable suggestion
    pub note: Option<String>,    // additional context
}

pub enum ErrorCode {
    // E01xx: Lexer errors
    E0101, // unterminated string
    E0102, // invalid character
    E0103, // number literal overflow

    // E02xx: Type errors
    E0201, // type mismatch
    E0202, // invalid cast
    E0203, // invalid operation for type

    // E03xx: Memory errors
    E0301, // zero-page overflow
    E0302, // RAM overflow
    E0303, // ROM overflow (bank too full)

    // E04xx: Control flow errors
    E0401, // call depth exceeded
    E0402, // recursion detected
    E0403, // unreachable state
    E0404, // transition to undefined state

    // E05xx: Declaration errors
    E0501, // duplicate declaration
    E0502, // undefined variable
    E0503, // undefined function
    E0504, // missing start declaration
    E0505, // multiple start declarations

    // W01xx: Warnings
    W0101, // expensive multiply/divide operation
    W0102, // loop without break or wait_frame
    W0103, // unused variable
    W0104, // unreachable code after return/break/transition
}
```

### 7.2 Error Rendering

Errors are rendered to the terminal with ANSI color codes (disabled if not a TTY):

```
error[E0201]: type mismatch
  --> game.ne:42:15
   |
42 |   var x: u8 = -5
   |               ^^ expected u8, found negative integer
   |
   = help: use i8 if you need negative values: var x: i8 = -5

error[E0402]: recursion is not allowed
  --> game.ne:55:5
   |
55 |     flood_fill(x + 1, y)
   |     ^^^^^^^^^^^^^^^^^^^^
   |
   = note: flood_fill calls itself (directly recursive)
   = help: the NES has only 256 bytes of stack; use an iterative
           algorithm instead
```

The renderer uses the `Span` to extract the relevant source line and draw the underline/caret precisely.

---

## 8. Testing Strategy

### 8.1 Unit Tests

Every compiler phase has its own test module. Tests are pure: construct input, call the phase function, assert on output.

```rust
// Example: lexer test
#[test]
fn lex_variable_declaration() {
    let tokens = lex("var x: u8 = 42");
    assert_eq!(tokens[0].kind, TokenKind::KwVar);
    assert_eq!(tokens[1].kind, TokenKind::Ident("x".into()));
    assert_eq!(tokens[2].kind, TokenKind::Colon);
    assert_eq!(tokens[3].kind, TokenKind::KwU8);
    assert_eq!(tokens[4].kind, TokenKind::Assign);
    assert_eq!(tokens[5].kind, TokenKind::IntLiteral(42));
}

// Example: assembler test
#[test]
fn encode_lda_immediate() {
    let bytes = assemble_instruction(Opcode::LDA, AddressingMode::Immediate(0xFF));
    assert_eq!(bytes, vec![0xA9, 0xFF]);
}
```

### 8.2 Integration Tests (Golden File Tests)

Each `.ne` test file in `tests/integration/` has a corresponding expected output. The test harness compiles the source and compares the resulting ROM byte-for-byte against the golden file. If the golden file doesn't exist, the test creates it and marks itself as "needs review."

Additionally, integration tests can run the ROM in an embedded NES CPU emulator (using the `mos6502` crate or a minimal custom implementation) for a fixed number of frames and assert on memory state. For example: "after 10 frames with the right button held, the byte at the player_x address should have increased by 20."

### 8.3 Error Tests

Each `.ne` file in `tests/error_tests/` is expected to fail compilation. The test asserts that the correct error code is produced and the error message contains expected substrings.

### 8.4 Fuzzing

The lexer and parser are fuzz-tested using `cargo-fuzz` to ensure they don't panic on arbitrary input. The compiler should always produce a clean error or a valid ROM — never a crash.

### 8.5 Hardware Validation

Select milestone ROMs are tested on real NES hardware via flash cart (manual process, not automated). This catches emulator-specific behavior that doesn't match real hardware (e.g., PPU timing edge cases).

---

## 9. Dependencies (Rust Crates)

| Crate         | Purpose                                    | Size Impact |
|---------------|---------------------------------------------|-------------|
| `clap`        | CLI argument parsing                        | small       |
| `image`       | PNG loading for asset pipeline              | moderate    |
| `ariadne`     | Beautiful error message rendering           | small       |
| `serde`       | Config/debug symbol serialization           | small       |
| `serde_json`  | Debug symbol output format                  | small       |

Total external dependencies: 5 crates. No native/C dependencies. The compiler builds and runs on Windows, macOS, and Linux without any platform-specific setup.

---

## 10. Milestone Plan

### Milestone 1 — "Hello Sprite" (Weeks 1–6)

**Goal:** Compile a minimal NEScript program that displays a sprite on screen and moves it with the d-pad. The resulting .nes file runs in an emulator.

**Language subset:**
- `game` declaration (NROM only)
- `var` (u8 only, global only)
- `const` (u8 only)
- `on frame` (single state, no state machine)
- `if` / `else`
- Arithmetic: `+`, `-`, `+=`, `-=`
- Comparison: `==`, `!=`, `<`, `>`, `<=`, `>=`
- `button.*` input (held only, no pressed/released)
- `draw` (single sprite, hardcoded CHR data)
- Inline `asm` blocks

**Compiler phases built:**
- Lexer (full)
- Parser (subset)
- Analyzer (basic type checking, no call graph yet)
- Codegen (direct AST → 6502, skip IR for this milestone)
- Assembler (full)
- ROM builder (NROM only)
- Runtime (init, NMI, controller read, OAM DMA)

**Not included:** IR, optimizer, asset pipeline, multi-state, functions, arrays, debug mode.

**Test program:**
```
game "Hello Sprite" {
  mapper: NROM
}

var px: u8 = 128
var py: u8 = 120

on frame {
  if button.right { px += 2 }
  if button.left  { px -= 2 }
  if button.down  { py += 2 }
  if button.up    { py -= 2 }

  draw Smiley at: (px, py)
}

start Main
```

**Deliverables:**
- Compiler binary that produces a working .nes ROM
- ROM runs correctly in FCEUX / Mesen
- 6502 assembler with full opcode test coverage
- Basic error messages for type errors and syntax errors

**Estimated effort:** 4–6 weeks (one developer, focused)

---

### Milestone 2 — "Game Loop" (Weeks 7–12)

**Goal:** Compile a multi-state game with functions, arrays, and the full type system.

**New language features:**
- State machine (`state`, `on enter`, `on exit`, `transition`)
- Functions (`fun`, `return`, parameters)
- Arrays (fixed-size `u8[N]`)
- All primitive types (`i8`, `u16`, `bool`)
- `while`, `loop`, `break`, `continue`
- `button.*_pressed` and `button.*_released`
- `fast` / `slow` hints
- `play` (sound — stubbed with beep)
- Unary minus

**Compiler phases built:**
- Full parser
- Full analyzer (call graph, depth limits, recursion detection, state validation)
- IR lowering
- Basic optimizer (constant folding, dead code)
- Codegen from IR
- Memory map report
- Call graph report

**Test program:** Coin Cavern sample game (simplified — hardcoded tile data, no PNG pipeline).

**Deliverables:**
- Coin Cavern compiles and runs
- State transitions work correctly
- Functions with parameters and return values
- Call depth enforcement with clear error messages
- Memory map and call graph reports

**Estimated effort:** 5–7 weeks

---

### Milestone 3 — "Asset Pipeline" (Weeks 13–18)

**Goal:** PNG images compile directly into CHR/nametable data. Debug mode works.

**New features:**
- `@chr("file.png")` — PNG → CHR conversion
- `@nametable("file.png")` — PNG → nametable + tile dedup
- `@palette("file.png")` — auto palette extraction
- `@binary("file.bin")` — raw include
- `sprite` declarations with asset references
- `background` declarations
- `palette` declarations
- `load_background`, `set_palette`
- `include` directive
- Debug mode: `debug.log`, `debug.assert`, runtime bounds checks
- Source map / debug symbol output
- `--debug` compiler flag

**Compiler additions:**
- Asset pipeline (chr.rs, nametable.rs, palette.rs)
- Debug instrumentation pass
- Source map generator
- Include file resolution

**Deliverables:**
- Full Coin Cavern with real PNG assets compiles and runs
- Debug build with logging visible in Mesen's debug console
- Source maps allow setting breakpoints on NEScript lines in Mesen
- Include works for multi-file projects

**Estimated effort:** 5–6 weeks

---

### Milestone 4 — "Optimization & Polish" (Weeks 19–24)

**Goal:** Compiler produces well-optimized code. Error messages are polished. The developer experience is smooth.

**New features:**
- Zero-page auto-promotion (frequency analysis)
- Function inlining
- Strength reduction (multiply/divide by power-of-2 → shifts)
- `scroll()` command
- `inline` keyword
- `as` type casting
- `debug.overlay`
- Frame overrun detection (debug mode)
- `--asm-dump` flag (view generated assembly)
- Compiler performance profiling / benchmarking

**Compiler additions:**
- Full optimizer suite
- Assembly dump output
- Performance regression tests (compilation speed)
- Fuzz testing for lexer and parser

**Deliverables:**
- Generated code is within 20% of hand-written 6502 for equivalent logic
- Compilation under 500ms for any project
- Full test suite (unit, integration, error, fuzz)
- Polished error messages with help text for all error codes

**Estimated effort:** 5–6 weeks

---

### Milestone 5 — "Bank Switching & Release" (Weeks 25–32)

**Goal:** Support banked mappers (MMC1, UxROM, MMC3). Audio pipeline. v0.1 public release.

**New features:**
- `bank` declarations
- Mapper support: MMC1, UxROM, MMC3
- Cross-bank trampolines (auto-generated)
- `on scanline` (MMC3 IRQ)
- `@music("file.ftm")` — FamiTracker import
- `@sfx("file.nsf")` — sound effect import
- Audio driver integration
- `start_music`, `stop_music` fully functional
- Software multiply/divide (included only when used)
- `nescript check` command (type-check without building)

**Compiler additions:**
- Bank allocator and linker for multi-bank ROMs
- Trampoline generator
- Audio asset parsers
- Music/SFX driver code generation

**Deliverables:**
- A game using MMC1 or MMC3 with multiple banks compiles and runs
- Audio playback works on emulator and real hardware
- Documentation: language spec, getting started guide, examples
- Binary releases for Windows, macOS, Linux
- v0.1 public release

**Estimated effort:** 6–8 weeks

---

## 11. Timeline Summary

| Milestone | Weeks   | Cumulative | Key Deliverable                       |
|-----------|---------|------------|----------------------------------------|
| M1        | 1–6     | 6 weeks    | Sprite on screen, d-pad movement       |
| M2        | 7–12    | 12 weeks   | Multi-state game with functions/arrays  |
| M3        | 13–18   | 18 weeks   | PNG asset pipeline, debug mode          |
| M4        | 19–24   | 24 weeks   | Optimized codegen, polished errors      |
| M5        | 25–32   | 32 weeks   | Bank switching, audio, public release   |

**Total estimated timeline: ~8 months to v0.1 release** (one developer, focused). With two developers, milestones 3 and 4 can partially overlap (asset pipeline and optimizer are independent), reducing the timeline to approximately 6 months.

---

## 12. Risks and Mitigations

| Risk                                              | Impact | Mitigation                                                    |
|---------------------------------------------------|--------|---------------------------------------------------------------|
| 6502 codegen produces subtly wrong code            | High   | Integration tests with CPU emulator validation; test on real hardware at each milestone |
| PPU timing issues (writes outside vblank)          | High   | Runtime enforces vblank-only PPU access; NMI handler design reviewed against known-good implementations |
| Asset pipeline color mapping produces ugly results  | Medium | Allow manual palette override; provide clear warning when colors are approximated |
| Optimizer introduces bugs                          | Medium | Every optimization pass has its own test suite; optimizer can be disabled with `--no-opt` flag |
| FamiTracker format parsing is complex              | Medium | Defer to M5; use binary include as workaround; consider using existing FT export tools |
| Scope creep (too many language features too early)  | Medium | Strict milestone scoping; "reserved for future" list in spec prevents premature implementation |
| Single-developer bus factor                        | Low    | Thorough documentation; clean module boundaries; public repo from M1 |

---

## 13. Open Questions

1. **Inline asm label syntax:** Should labels in `asm {}` blocks use `.label:` (ca65 style) or `label:` (generic)? This affects the assembler's label parser.

2. **Debug port address:** $4800 is the conventional choice for debug output in homebrew NES emulators, but not all emulators support it. Should we support multiple debug output methods?

3. **OAM allocation strategy:** Currently the compiler allocates OAM slots per `draw` call in order. Should we support priority-based allocation or automatic sprite cycling to mitigate the 8-sprites-per-scanline hardware limit?

4. **Error recovery granularity:** How aggressively should the parser recover from errors? More recovery = more errors reported per compile = faster iteration. But poor recovery can produce cascading false errors.

5. **WASM build target:** Should the compiler itself compile to WASM for a future browser-based IDE? This would require avoiding file system access in the core pipeline (using an in-memory VFS instead). Worth considering in the architecture now even if not implemented until post-v1.
