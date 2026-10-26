# Compiler Architecture

An overview of the NEScript compiler internals for contributors and maintainers.

---

## Pipeline

```
Source (.ne) --> Lexer --> Parser --> Analyzer --> IR Lowering --> Optimizer --> Codegen --> Peephole --> Linker --> ROM (.nes)
```

Each phase is a pure function (input to output) with no global state, making every stage independently testable.

### Phase Summary

| Phase           | Input               | Output                 | Responsibility                                       |
|-----------------|----------------------|------------------------|------------------------------------------------------|
| **Lexer**       | Source text           | Token stream           | Tokenization, number/string literal parsing          |
| **Parser**      | Token stream          | AST                    | Syntax validation, tree construction                 |
| **Analyzer**    | AST                   | Annotated AST          | Type checking, scope resolution, call graph analysis |
| **IR Lowering** | Annotated AST         | NEScript IR            | Flatten expressions, expand u16 ops, desugar         |
| **Optimizer**   | IR                    | Optimized IR           | Constant folding, dead code, strength reduction, inlining |
| **Codegen**     | Optimized IR          | 6502 instruction list  | Slot allocation, instruction selection               |
| **Peephole**    | 6502 instructions     | 6502 instructions      | Dead-load elimination, branch folding, INC/DEC fold  |
| **Linker**      | Instructions + assets | .nes file              | Bank layout, vectors, iNES header                    |

---

## Modules

Each module has a `mod.rs` (implementation) and a co-located `tests.rs` with unit tests.

### `lexer/`
`mod.rs`, `token.rs`, `tests.rs`. Tokenizes NEScript source into a stream of typed tokens with source spans. Handles decimal/hex/binary integer literals, string literals, keywords, operators, and the raw-capture mode for `asm { ... }` bodies.

### `parser/`
`mod.rs`, `ast.rs`, `preprocess.rs`, `tests.rs`. Recursive descent parser that converts the token stream into an AST. `ast.rs` defines every AST node type (expressions, statements, declarations). `preprocess.rs` inlines `include "path.ne"` directives before parsing.

### `analyzer/`
`mod.rs`, `tests.rs`. Performs semantic analysis on the AST: type checking, scope and symbol table management, call graph construction with depth analysis, state reachability, unused-variable detection, and dead-code-after-terminator warnings. Emits all user-facing diagnostics beyond lexer/parser syntax errors.

### `ir/`
`mod.rs` (types), `lowering.rs` (AST → IR), `tests.rs`. The IR is a flat, register-agnostic representation built from virtual temps and basic blocks. Lowering flattens nested expressions, expands 16-bit operations, desugars `for` into `while`, resolves constant expressions early, and performs real `inline fun` splicing — functions marked `inline` whose bodies match one of the two splicable shapes (single `return <expr>` or void statement sequence) are captured before lowering begins and substituted at every call site. Bodies that don't match (conditional returns, loops, nested control flow) fall back to regular out-of-line calls and the analyzer emits `W0110` at the declaration.

### `optimizer/`
`mod.rs`, `tests.rs`. Runs passes over the IR in order: strength reduction (mul/div by powers of two, mod by powers of two, ShiftVar → ShiftLeft/Right), constant folding (arithmetic + comparisons + shifts), copy propagation, and dead code elimination. The `inline fun` splicing happens one phase earlier in `ir/lowering.rs` so the optimizer sees already-inlined call sites.

### `codegen/`
`ir_codegen.rs`, `peephole.rs`, `mod.rs`. `ir_codegen.rs` walks the optimized IR and emits 6502 instructions; variables land in allocated addresses and IR temps land in a recycling zero-page slot pool. `peephole.rs` runs after codegen to clean up the temp-heavy output (dead-load elimination, branch folding, INC/DEC fold, copy propagation).

### `asm/`
`mod.rs`, `opcodes.rs`, `inline_parser.rs`, `tests.rs`. The built-in assembler and the inline-asm parser. `opcodes.rs` defines the 6502 opcode table with addressing modes. `inline_parser.rs` parses the body of `asm { ... }` blocks so codegen can splice real instructions in-line.

### `linker/`
`mod.rs`, `debug_symbols.rs`, `tests.rs`. Assigns addresses to code and data segments, resolves label/symbol fixups, lays out banks for banked mappers (MMC1/UxROM/MMC3), and emits the final iNES byte stream via `rom::RomBuilder`. `debug_symbols.rs` owns the three debug-info writers — `render_mlb` (Mesen `.mlb`), `render_source_map` (plain-text ROM→source line map), and `render_dbg` (ca65-compatible `.dbg` debug-info file for Mesen source-level debugging).

### `rom/`
`mod.rs`, `tests.rs`. Builds the final iNES ROM file. Generates the 16-byte iNES header and places the NMI/RESET/IRQ vector table.

### `runtime/`
`mod.rs`, `tests.rs`. Contains built-in runtime code emitted into every ROM: NES hardware init, NMI handler, controller reads, OAM DMA, software multiply/divide, the frame-walking audio driver (`gen_audio_tick`, `gen_period_table`, `gen_data_block`), and the MMC1/UxROM/MMC3 mapper init and bank-switch helpers.

### `assets/`
`mod.rs`, `chr.rs`, `palette.rs`, `resolve.rs`, `audio.rs`, `tests.rs`. The asset pipeline. `chr.rs` converts PNGs to CHR tile data. `palette.rs` maps RGB to NES palette indices. `resolve.rs` resolves `sprite` declarations into tile-indexed CHR blocks. `audio.rs` compiles `sfx`/`music` declarations into ROM-ready envelope and note-stream byte tables, plus the builtin effect/track tables used when programs reference audio names they haven't declared.

### `errors/`
`mod.rs`, `diagnostic.rs`, `render.rs`. Defines the `Diagnostic` struct (error codes, severity, spans, labels, help text). Renders diagnostics with color and source context for terminal output using ariadne.

---

## Testing

### Test Organization

Tests are co-located with each module in `tests.rs` files under `src/`:

```
src/lexer/tests.rs        -- lexer unit tests
src/parser/tests.rs       -- parser unit tests
src/analyzer/tests.rs     -- semantic analysis tests
src/ir/tests.rs           -- IR lowering tests
src/optimizer/tests.rs    -- optimizer tests
src/asm/tests.rs          -- assembler tests
src/linker/tests.rs       -- linker tests
src/rom/tests.rs          -- ROM builder tests
src/runtime/tests.rs      -- runtime code emission tests
src/assets/tests.rs       -- asset pipeline tests
```

End-to-end and error-code tests live in `tests/integration_test.rs`, which compiles representative `.ne` snippets through the full pipeline and asserts on ROM/diagnostic shape. The emulator smoke test (`tests/emulator/run_examples.mjs`) runs every example through `jsnes` and byte-compares the resulting screenshot and audio hash against goldens in `tests/emulator/goldens/`.

### Running Tests

```bash
# Run all tests
cargo test

# Run tests for a specific module
cargo test --lib lexer
cargo test --lib parser
cargo test --lib analyzer

# Run integration tests only
cargo test --test integration_test

# Run a specific test by name
cargo test test_name
```

### Test Strategy

Each compiler phase is a pure function, so unit tests provide isolated input and verify output without side effects. Integration tests compile complete `.ne` programs and either assert on shape (length, presence of specific labels) or byte-compare output against checked-in goldens. Emulator goldens catch regressions that pass type-check but corrupt the final executable image.
