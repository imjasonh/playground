# NEScript Language Specification

**Version 0.1 — Draft**

---

## 1. Overview

NEScript is a statically-typed, compiled programming language designed to produce performant NES (Nintendo Entertainment System) game code. It compiles to 6502 machine code packaged as iNES-format ROM files, playable in emulators or on original hardware via flash cartridges.

NEScript balances approachability for general programmers with the performance control demanded by the NES's constrained hardware: a 1.79 MHz 8-bit CPU, 2 KB of RAM, 256 bytes of stack, and no hardware multiply, divide, or floating point.

### 1.1 Design Principles

1. **Game-aware, not general-purpose.** First-class constructs for sprites, backgrounds, input, sound, and frame-based execution.
2. **Transparent cost model.** Syntax weight reflects runtime cost. Cheap operations look light; expensive operations look heavy.
3. **No hidden allocation.** Every variable has a statically-known address. No heap, no garbage collector, no dynamic dispatch.
4. **Guardrails over footguns.** The compiler prevents common NES pitfalls (stack overflow, missing vblank yield, bank-crossing errors) at compile time.
5. **Progressive disclosure.** Beginners use declarative constructs. Advanced users drop to imperative loops or inline assembly.

### 1.2 Target Hardware

| Resource         | Capacity                          |
|------------------|-----------------------------------|
| CPU              | Ricoh 2A03 (MOS 6502 variant), 1.79 MHz |
| RAM              | 2,048 bytes ($0000–$07FF)         |
| Zero Page        | 256 bytes ($0000–$00FF), fast access |
| Stack            | 256 bytes ($0100–$01FF)           |
| PPU (graphics)   | Separate processor, 2 KB VRAM    |
| OAM (sprites)    | 64 sprites, 256 bytes             |
| PRG ROM          | Game code, 16 KB or 32 KB (NROM) |
| CHR ROM          | Tile graphics, 8 KB (NROM)       |
| Audio            | 5 channels (2 pulse, 1 triangle, 1 noise, 1 DPCM) |

---

## 2. Lexical Structure

### 2.1 Source Encoding

NEScript source files use UTF-8 encoding. Only ASCII characters are permitted in identifiers and keywords. UTF-8 is permitted in string literals and comments.

File extension: `.ne`

### 2.2 Comments

```
// Line comment — extends to end of line

/* Block comment
   may span multiple lines */
```

Block comments do not nest.

### 2.3 Keywords

The following identifiers are reserved:

```
game      state     on        fun       var       const
if        else      while     for       in        match
break     continue  return
true      false     not       and       or
fast      slow      include   start     transition
sprite    background palette   sfx       music
draw      play      stop_music start_music
load_background set_palette
asm       raw       bank
loop      wait_frame
u8        i8        u16       bool
enum      struct
debug     as
```

### 2.4 Identifiers

Identifiers begin with a letter or underscore, followed by letters, digits, or underscores. Case-sensitive.

```
[a-zA-Z_][a-zA-Z0-9_]*
```

Maximum length: 64 characters.

### 2.5 Literals

**Integer literals:**

```
42          // decimal
0xFF        // hexadecimal
0b10110001  // binary
```

All integer literals must fit in `u16` (0–65535). The compiler narrows to the required type at usage.

**Boolean literals:**

```
true
false
```

**String literals** (used only in asset paths and debug statements):

```
"assets/player.png"
```

Escape sequences: `\\`, `\"`, `\n`, `\t`.

**Array literals:**

```
[1, 2, 3, 4, 5]
```

### 2.6 Operators

**Arithmetic:** `+`, `-` (binary and unary), `*`, `/`, `%`

Note: `*`, `/`, and `%` are available but expensive. The compiler emits software routines for multiply and divide. Multiplication or division by powers of two is optimized to shifts. The compiler emits a warning for non-power-of-two multiply and divide to ensure the programmer is aware of the cost.

**Bitwise:** `&`, `|`, `^`, `~`, `<<`, `>>`

**Comparison:** `==`, `!=`, `<`, `>`, `<=`, `>=`

**Logical:** `and`, `or`, `not`

**Assignment:** `=`, `+=`, `-=`, `&=`, `|=`, `^=`, `<<=`, `>>=`

**Precedence (highest to lowest):**

| Level | Operators                     | Associativity |
|-------|-------------------------------|---------------|
| 1     | `()` grouping                 | —             |
| 2     | `-` (unary), `~`, `not`       | right         |
| 3     | `*`, `/`, `%`                 | left          |
| 4     | `+`, `-`                      | left          |
| 5     | `<<`, `>>`                    | left          |
| 6     | `&`                           | left          |
| 7     | `^`                           | left          |
| 8     | `|`                           | left          |
| 9     | `==`, `!=`, `<`, `>`, `<=`, `>=` | left       |
| 10    | `and`                         | left          |
| 11    | `or`                          | left          |
| 12    | `=`, `+=`, `-=`, etc.         | right         |

---

## 3. Type System

### 3.1 Primitive Types

| Type   | Size    | Range             | Description                          |
|--------|---------|-------------------|--------------------------------------|
| `u8`   | 1 byte  | 0 to 255          | Unsigned 8-bit integer               |
| `i8`   | 1 byte  | -128 to 127       | Signed 8-bit integer (two's complement) |
| `u16`  | 2 bytes | 0 to 65,535       | Unsigned 16-bit integer (little-endian) |
| `bool` | 1 byte  | `true` / `false`  | Boolean, stored as 0 or 1            |

### 3.2 Arrays

Arrays are fixed-size, homogeneous, and zero-indexed.

```
var enemies: u8[8]               // 8 bytes in RAM
const table: u8[4] = [10, 20, 30, 40]  // in ROM
```

Array size must be a compile-time constant. Maximum 256 elements (indices must fit in `u8` for efficient 6502 indexed addressing).

Array bounds are checked at compile time where possible. In debug mode, runtime bounds checks are inserted. In release mode, out-of-bounds access is undefined behavior.

### 3.3 Type Coercion

NEScript performs no implicit type coercion. All conversions are explicit:

```
var a: u8 = 200
var b: u16 = a as u16     // zero-extend
var c: i8 = a as i8       // reinterpret bits (debug warning if > 127)
var d: u8 = b as u8       // truncate (debug warning if > 255)
```

### 3.4 Overflow Behavior

Arithmetic overflow wraps silently in release mode, matching 6502 hardware behavior. In debug mode, overflow emits a warning to the debug console but still wraps (the game continues running).

---

## 4. Variables and Memory

### 4.1 Variable Declarations

```
var name: type                    // uninitialized (zeroed at state entry)
var name: type = expression       // initialized
const name: type = expression     // compile-time constant, stored in ROM
```

### 4.2 Memory Placement

The compiler assigns variables to memory regions automatically based on usage analysis. Programmers may provide hints:

```
fast var px: u8       // hint: prefer zero-page ($00–$FF), faster access
slow var high_score: u16  // hint: prefer upper RAM, rarely accessed
var normal: u8        // no hint: compiler decides
```

**Zero-page** ($00–$FF): 256 bytes, faster instructions (2 cycles vs 3–4). The compiler reserves bytes $00–$0F for internal use (frame counter, temp registers, NMI flags). Remaining bytes are allocated to variables by frequency of access.

**RAM** ($0200–$07FF): General variable storage. Address $0200–$02FF is reserved for OAM sprite buffer (DMA'd to PPU each frame).

If zero-page is exhausted and `fast` variables cannot be placed, the compiler emits a **compile error** listing all `fast` declarations and their byte costs.

### 4.3 Scope

**Global variables** are declared at the top level of a file. They persist for the lifetime of the program and occupy RAM permanently.

**State-local variables** are declared inside a `state` block. They are initialized on state entry and their RAM is eligible for reuse by other states. Two states that are never active simultaneously may share the same RAM addresses.

**Function-local variables** are declared inside a `fun` block. They are allocated on the 6502 stack or in compiler-managed temporary RAM. They cease to exist when the function returns.

**Block-local variables** (inside `if`, `while`, etc.) are scoped to their block but share the enclosing function's or state's memory allocation.

### 4.4 Constants

```
const MAX_ENEMIES: u8 = 5
const SPEED: u8 = 3
const SIN_TABLE: u8[8] = [0, 49, 90, 117, 127, 117, 90, 49]
```

Constants are evaluated at compile time and placed in ROM. They may be used in array size declarations and other compile-time contexts.

---

## 5. Functions

### 5.1 Declaration

```
fun name(param1: type, param2: type) -> return_type {
  // body
}

fun name() {
  // no parameters, no return value
}
```

### 5.2 Calling Convention

Parameters are passed via zero-page temporary locations. Return values are placed in the A register (for `u8`, `i8`, `bool`) or a zero-page temporary pair (for `u16`).

The compiler manages the mapping. The programmer does not interact with registers directly (except in `asm` blocks).

### 5.3 Call Depth Limit

The 6502 stack is 256 bytes. Each function call consumes approximately 6 bytes of stack (return address + saved registers). NEScript enforces a maximum static call depth, defaulting to **8**.

```
game "MyGame" {
  stack_depth: 12    // override default
}
```

The compiler builds a complete call graph at compile time. Because recursion is prohibited and function pointers do not exist, the call graph is always fully resolvable. If any path through the call graph exceeds the configured depth, the compiler emits an error showing the deepest call chain.

### 5.4 Recursion

Recursion is a **compile error**. The compiler detects both direct recursion (`a` calls `a`) and indirect recursion (`a` calls `b` calls `a`) via the call graph.

### 5.5 Inlining

The compiler may inline small functions automatically. The programmer may hint:

```
inline fun add_clamped(a: u8, b: u8) -> u8 {
  var result: u16 = (a as u16) + (b as u16)
  if result > 255 { return 255 }
  return result as u8
}
```

`inline` is a hint, not a guarantee. The compiler may decline to inline if the function is too large or called from too many sites.

---

## 6. Control Flow

### 6.1 If / Else

```
if condition {
  // body
} else if other_condition {
  // body
} else {
  // body
}
```

Braces are always required. There is no ternary operator.

### 6.2 While Loop

```
while condition {
  // body
}
```

`break` exits the innermost loop. `continue` skips to the next iteration.

### 6.3 Loop (Infinite)

```
loop {
  // body — must contain break or wait_frame to avoid hanging
}
```

The compiler emits a warning if a `loop` block contains neither `break`, `wait_frame`, nor `transition`.

### 6.4 Wait Frame

```
wait_frame()
```

Yields execution until the next NMI (vertical blank) interrupt. This is how the game synchronizes to the 60 Hz display refresh. Calling `wait_frame()` triggers the OAM DMA transfer and PPU updates before yielding.

---

## 7. Game Structure

### 7.1 Game Declaration

Every NEScript program begins with a game declaration:

```
game "Display Name" {
  mapper:      NROM          // cartridge mapper (see §7.6)
  mirroring:   vertical      // or horizontal
  stack_depth: 8             // max call depth (default 8)
}
```

### 7.2 States

States are the top-level organizational unit of a NEScript game. Exactly one state is active at any time. States declare event handlers and local variables.

```
state StateName {
  var local_var: u8 = 0     // state-local variable

  on enter {
    // runs once when transitioning to this state
  }

  on exit {
    // runs once when transitioning away from this state
  }

  on frame {
    // runs every frame (60 Hz) while this state is active
    // implicit wait_frame() at end
  }

  on scanline(N) {
    // runs at scanline N via IRQ (mapper-dependent)
  }
}
```

**`on frame`** is syntactic sugar for:

```
on enter {
  loop {
    // frame body here
    wait_frame()
  }
}
```

This means `on enter` with an explicit loop and `on frame` are mutually exclusive patterns. A state may have `on enter` (for setup) alongside `on frame`, but `on enter` must not contain an infinite loop if `on frame` is also defined.

### 7.3 State Transitions

```
transition StateName
```

Transitions are immediate. The current state's `on exit` handler runs, then the target state's `on enter` handler runs. Transitions may only target states defined in the current compilation unit or included files.

A transition from within `on frame` exits the frame loop. The remainder of the frame handler does not execute.

### 7.4 Entry Point

```
start StateName
```

Declares which state is entered on power-on / reset. Exactly one `start` declaration must exist per game. The compiler places the RESET vector to point to the startup code, which initializes hardware and enters the start state.

### 7.5 Include

```
include "physics.ne"
include "enemies.ne"
```

Textual inclusion, resolved relative to the including file's directory. Circular includes are a compile error. Include guards are not needed — the compiler tracks included files and skips duplicates.

### 7.6 Mappers

The mapper determines the cartridge hardware and thus the available ROM size and capabilities. Supported mappers:

| Mapper     | PRG ROM      | CHR ROM    | Features                    |
|------------|-------------|------------|------------------------------|
| `NROM`     | 16 or 32 KB | 8 KB       | No banking, simplest        |
| `MMC1`     | Up to 256 KB| Up to 128 KB| Switchable banks           |
| `UxROM`    | Up to 256 KB| 8 KB CHR RAM| PRG banking only          |
| `MMC3`     | Up to 512 KB| Up to 256 KB| Scanline counter, banking  |

Additional mappers may be supported in future versions. Mapper choice affects which features are available (e.g., `on scanline` requires MMC3 or similar).

---

## 8. Banks

For mappers with bank switching, NEScript provides explicit bank declarations:

```
bank 0 {
  // Code and data always resident in memory
  // NMI handler, core engine, shared functions
}

bank 1 {
  state TitleScreen { ... }
  background TitleBG { ... }
}

bank 2 {
  state Playing { ... }
  state Paused { ... }
}
```

**Rules:**

1. Bank 0 (or the fixed bank for the mapper) is always resident. The NMI handler, startup code, and trampoline stubs live here.
2. A `transition` between states in different banks automatically emits a bank-switch and trampoline.
3. Calling a function in another bank emits a cross-bank call via the trampoline in the fixed bank.
4. If a function or state references data in another bank without an explicit cross-bank call, the compiler emits an error.
5. If no `bank` declarations are present, the compiler auto-assigns states and data to banks, keeping each state and its referenced assets together.

---

## 9. Input

The NES has two controller ports. NEScript provides a built-in input model:

```
button.up             // D-pad up held this frame
button.down
button.left
button.right
button.a              // A button held
button.b              // B button held
button.start
button.select

button.a_pressed      // A button just pressed (was not held last frame)
button.a_released     // A button just released (was held last frame)
// _pressed and _released variants exist for all 8 buttons
```

For two-player games:

```
p1.button.a           // player 1
p2.button.right       // player 2
```

If no player prefix is used, `button` refers to player 1.

The compiler auto-generates the controller read routine and previous-frame tracking, consuming 3 bytes of RAM (current, previous, pressed) per controller.

---

## 10. Graphics

### 10.1 Palettes

The NES has 4 background palettes and 4 sprite palettes, each containing 4 colors selected from the NES's 64-color master palette. A `palette` declaration provides all 32 bytes at once:

```
palette my_palette {
    colors: [0x0F, 0x00, 0x10, 0x30,   // bg sub-palette 0
             0x0F, 0x07, 0x17, 0x27,   // bg sub-palette 1
             0x0F, 0x09, 0x19, 0x29,   // bg sub-palette 2
             0x0F, 0x01, 0x11, 0x21,   // bg sub-palette 3
             0x0F, 0x00, 0x10, 0x30,   // sprite sub-palette 0
             0x0F, 0x14, 0x24, 0x34,   // sprite sub-palette 1
             0x0F, 0x1A, 0x2A, 0x3A,   // sprite sub-palette 2
             0x0F, 0x12, 0x22, 0x32]   // sprite sub-palette 3
}

set_palette my_palette          // queued for next vblank
```

The first declared palette is loaded at reset time, before rendering is enabled. Subsequent declarations live in PRG ROM as named blobs and become active via `set_palette`, which queues the write for the next vblank via the NMI handler.

### 10.2 Sprites

```
sprite SpriteName {
  tiles:   @chr("file.png", rows: 1, cols: 4)  // compile-time conversion
  size:    8x8            // or 8x16
  palette: 0              // which sprite sub-palette (0-3)
}
```

Drawing sprites:

```
draw SpriteName
  frame: expression       // which animation frame (index into tiles)
  at: (x_expr, y_expr)   // screen position
  flip_h: bool_expr       // optional, horizontal flip
  flip_v: bool_expr       // optional, vertical flip
  palette: expression     // optional, override palette index
```

The `draw` statement writes to the OAM shadow buffer. The compiler manages OAM slot allocation per frame, up to the NES limit of 64 sprites. If more than 64 sprites are drawn in a single frame, the compiler can optionally emit a warning (debug mode) or rotate priority (future feature).

### 10.3 Backgrounds

```
background TitleScreen {
    tiles:      [0x00, 0x01, 0x02, /* ... up to 960 bytes ... */]
    attributes: [0xFF, 0x55,       /* ... up to 64 bytes  ... */]
}

load_background TitleScreen     // queued for next vblank
```

`tiles` is a 32×30 nametable (up to 960 bytes, in row-major order); `attributes` is the 8×8 attribute table (up to 64 bytes). Shorter lists are zero-padded; omitted `attributes` default to all-zero. The first declared background is loaded at reset time and background rendering is enabled automatically.

### 10.4 Scrolling

```
scroll(x_expr, y_expr)             // set PPU scroll position
```

For split-screen scrolling (status bar + scrolling playfield), use `on scanline` to change the scroll mid-frame (requires MMC3 or similar mapper).

---

## 11. Assets

Asset directives use the `@` prefix and are evaluated at compile time. The compiler converts source assets into NES-native formats and embeds them in ROM.

### 11.1 Graphics Assets

```
@chr("file.png", rows: N, cols: M)
```

Converts a PNG image into CHR tile data. The image is divided into an N×M grid of 8×8 pixel cells (or 8×16 for tall sprites). Each cell becomes one tile. Colors are mapped to the nearest NES palette entry.

```
@nametable("file.png")
```

Converts a full 256×240 PNG into a nametable (tile index map) plus any unique tiles needed. Outputs both tile data and the 960-byte nametable + 64-byte attribute table.

```
@palette("file.png")
```

Extracts the 4 most-used colors from an image and maps them to NES palette values. Convenience for prototyping.

### 11.2 Audio Assets

```
@sfx("file.nsf")           // sound effect (NSF format)
@music("file.ftm")          // FamiTracker module
```

The compiler embeds the audio data and generates the necessary driver code. The audio driver is included automatically if any `sfx` or `music` declarations exist.

### 11.3 Binary Assets

```
@binary("file.bin")
```

Includes raw binary data verbatim. Useful for pre-computed lookup tables or custom data formats.

---

## 12. Sound

### 12.1 Sound Effects

```
sfx SfxName {
  data: @sfx("file.nsf")
}

play SfxName                   // trigger sound effect
```

Sound effects are fire-and-forget. Playing a new effect on the same channel interrupts the previous one.

### 12.2 Music

```
music TrackName {
  data: @music("file.ftm")
}

start_music TrackName          // begin playback, loops
stop_music                     // silence
```

The music driver runs during NMI. Only one track plays at a time.

---

## 13. Inline Assembly

### 13.1 Bound Assembly

```
fun fast_routine(input: u8) -> u8 {
  asm {
    lda {input}           // {var} resolves to the variable's address
    asl a
    asl a
    sta {return}          // {return} is the return value location
  }
}
```

Within `asm` blocks:
- `{variable_name}` is replaced with the variable's resolved memory address.
- `{return}` is the location where the return value should be stored.
- All 6502 instructions and addressing modes are available.
- Labels may be defined with a colon: `loop_start:`.
- Labels inside `asm` blocks are local to that block (no conflicts with other blocks).

### 13.2 Raw Assembly

```
raw asm {
  .org $C000
  ; completely unmanaged — you handle everything
  nop
  rti
}
```

Raw asm blocks bypass all compiler management. They are placed verbatim into the output. Use with extreme caution.

---

## 14. Debug Mode

When compiled with `--debug`, the compiler enables additional runtime instrumentation.

### 14.1 Debug Logging

```
debug.log("Player position: ", px, ", ", py)
debug.log("Coin collected! Score: ", score)
```

In debug mode, `debug.log` writes to the emulator's debug console (using a mapper-specific debug register or a standardized debug output port at $4800). In release mode, all `debug.*` statements are stripped entirely — zero bytes, zero cycles.

### 14.2 Debug Assertions

```
debug.assert(lives > 0, "Lives should never be negative here")
debug.assert(px < 255, "Player out of bounds")
```

In debug mode, a failed assertion halts execution and outputs the message. In release mode, stripped entirely.

### 14.3 Runtime Checks (future)

The following checks are planned for debug mode but are not yet emitted (see `docs/future-work.md`):

- **Array bounds checking**: Indexed access should emit a bounds test before the load/store.
- **Stack depth monitoring**: Each function entry should check remaining stack space.
- **Frame overrun detection**: A timer should check whether the frame handler took longer than one vblank period (~29,780 CPU cycles) and log a warning.

### 14.4 Source Maps (future)

A debug-symbol output (`.dbg` / `.mlb` / `.sym`) relating ROM addresses to NEScript source locations is planned but not yet emitted. See `docs/future-work.md`.

---

## 15. Compiler Outputs

### 15.1 ROM File

The primary output is an `.nes` file in iNES format:

```
Bytes 0–3:    "NES" + $1A (magic number)
Byte 4:       PRG ROM size in 16 KB units
Byte 5:       CHR ROM size in 8 KB units
Byte 6:       Flags 6 (mapper low nybble, mirroring)
Byte 7:       Flags 7 (mapper high nybble)
Bytes 8–15:   Zero padding
[PRG ROM]:    Game code
[CHR ROM]:    Tile graphics
```

### 15.2 Memory Map Report

The compiler outputs a human-readable memory map:

```
=== NEScript Memory Map ===
Zero Page ($00–$FF):
  $00–$0F  [SYSTEM]  reserved (frame counter, temp, NMI flags)
  $10      [FAST]    px (u8) — accessed 12 times in hot path
  $11      [FAST]    py (u8) — accessed 10 times in hot path
  $12      [AUTO]    vx (i8) — promoted to ZP by compiler
  ...
RAM ($0200–$07FF):
  $0200–$02FF  [SYSTEM]  OAM shadow buffer
  $0300        [STATE:Playing]  timer (u8)
  $0300        [STATE:GameOver] timer (u8)  ← shares address!
  $0301        [STATE:Playing]  shake (u8)
  $0301        [STATE:GameOver] blink (bool)  ← shares address!
  ...
ROM Usage: 4,218 / 32,768 bytes (12.8%)
Zero Page: 38 / 240 available bytes (15.8%)
RAM: 112 / 1,280 available bytes (8.7%)
```

### 15.3 Call Graph Report

```
=== Call Graph (max depth: 4 / 8) ===
on_frame [Playing]
  ├── update_player (depth 1)
  │   └── check_collision (depth 2)
  │       └── overlap (depth 3)
  ├── update_coins (depth 1)
  │   └── overlap (depth 2)
  └── draw_player (depth 1)
```

### 15.4 Debug Symbols

When `--debug` is specified, the compiler additionally outputs:

- `game.dbg` — source map (ROM address → source file:line:column)
- `game.sym` — symbol table (variable names → RAM addresses, function names → ROM addresses)

These files follow the cc65/Mesen debug symbol format for compatibility with existing NES debugging tools.

---

## 16. Compiler Flags

```
nescript build game.ne                    # release build
nescript build game.ne --debug            # debug build with runtime checks
nescript build game.ne --output my_game.nes
nescript build game.ne --map              # emit memory map report
nescript build game.ne --call-graph       # emit call graph report
nescript build game.ne --asm-dump         # output intermediate 6502 assembly
nescript check game.ne                    # type-check only, no output
```

---

## 17. Error Messages

NEScript prioritizes clear, actionable error messages aimed at programmers who may not know 6502 internals.

**Type error:**
```
error[E0201]: type mismatch
  --> game.ne:42:15
   |
42 |   var x: u8 = -5
   |               ^^ expected u8, found negative integer
   |
   = help: use i8 if you need negative values: var x: i8 = -5
```

**Call depth exceeded:**
```
error[E0401]: call depth exceeds limit
  --> game.ne:78:5
   |
78 |     deep_function()
   |     ^^^^^^^^^^^^^^^
   |
   = note: this call chain is 9 levels deep (limit is 8):
           on_frame → update → physics → resolve → check → test → compare → eval → deep_function
   = help: increase stack_depth in game declaration, or refactor to reduce nesting
```

**Recursion detected:**
```
error[E0402]: recursion is not allowed
  --> game.ne:55:5
   |
55 |     flood_fill(x + 1, y)
   |     ^^^^^^^^^^^^^^^^^^^^
   |
   = note: flood_fill calls itself (directly recursive)
   = help: the NES has only 256 bytes of stack; use an iterative algorithm instead
```

**Zero-page exhausted:**
```
error[E0301]: zero-page overflow
   |
   = note: 'fast' variables require 42 bytes, but only 240 are available
   = note: fast var enemy_table: u8[32] (32 bytes) at game.ne:15
   = note: fast var particle_x: u8[16] (16 bytes) at game.ne:18
   = help: remove 'fast' from less performance-critical variables
```

**Frame overrun warning (debug runtime):**
```
warning: frame overrun in state 'Playing'
  frame handler took 34,210 cycles (limit: 29,780)
  heaviest call: update_enemies() — 12,400 cycles
```

---

## 18. Reserved for Future Versions

The following features are planned but not included in v0.1:

- **Structs**: `struct Vec2 { x: u8, y: u8 }` — named composite types with known layout.
- **Enums**: `enum Direction { Up, Down, Left, Right }` — mapped to u8 values.
- **Fixed-point arithmetic**: `fixed8.8` type for sub-pixel movement with operator support.
- **Text/HUD system**: First-class font sheet declarations, HUD region definitions, and layout system for score displays, health bars, menus, and dialogue.
- **Metasprites**: Multi-tile sprite definitions with relative positioning.
- **Tilemaps and collision maps**: Declarative level data with built-in tile collision queries.
- **SRAM / battery save**: Persistent storage declarations for save data.
- **Second controller**: While input reading supports two controllers, ergonomic two-player APIs are deferred.
- **NES 2.0 header**: Extended iNES header format for additional metadata.

---

## 19. Grammar (EBNF Summary)

```ebnf
program         = game_decl { include } { top_level_decl } start_decl ;

game_decl       = "game" STRING "{" { game_prop } "}" ;
game_prop       = IDENT ":" ( IDENT | INTEGER ) ;

include         = "include" STRING ;

top_level_decl  = var_decl | const_decl | fun_decl | state_decl
                | sprite_decl | palette_decl | background_decl
                | sfx_decl | music_decl | bank_decl ;

var_decl        = ["fast" | "slow"] "var" IDENT ":" type ["=" expr] ;
const_decl      = "const" IDENT ":" type "=" expr ;

type            = "u8" | "i8" | "u16" | "bool" | type "[" INTEGER "]" ;

fun_decl        = ["inline"] "fun" IDENT "(" [param_list] ")" ["->" type] block ;
param_list      = param { "," param } ;
param           = IDENT ":" type ;

state_decl      = "state" IDENT "{" { state_body } "}" ;
state_body      = var_decl | event_handler ;
event_handler   = "on" event_kind block ;
event_kind      = "enter" | "exit" | "frame" | "scanline" "(" INTEGER ")" ;

sprite_decl     = "sprite" IDENT "{" { sprite_prop } "}" ;
sprite_prop     = IDENT ":" expr ;

palette_decl    = "palette" IDENT "{" "colors" ":" "[" int_list "]" "}" ;
background_decl = "background" IDENT "{" bg_prop { bg_prop } "}" ;
bg_prop         = ("tiles" | "attributes") ":" "[" int_list "]" ;

sfx_decl        = "sfx" IDENT "{" sfx_prop { sfx_prop } "}" ;
sfx_prop        = ("duty" ":" INTEGER | "pitch" ":" "[" int_list "]" | "volume" ":" "[" int_list "]") ;
music_decl      = "music" IDENT "{" music_prop { music_prop } "}" ;
music_prop      = ("duty" ":" INTEGER | "volume" ":" INTEGER | "repeat" ":" BOOL | "notes" ":" "[" int_list "]") ;
int_list        = INTEGER { "," INTEGER } ;

bank_decl       = "bank" INTEGER "{" { top_level_decl } "}" ;

asset_ref       = "@" IDENT "(" STRING { "," IDENT ":" expr } ")" ;

block           = "{" { statement } "}" ;
statement       = var_decl | const_decl | assign_stmt | if_stmt | while_stmt
                | for_stmt | loop_stmt | return_stmt | break_stmt | continue_stmt
                | draw_stmt | play_stmt | transition_stmt | fun_call
                | asm_block | debug_stmt | music_stmt | scroll_stmt
                | load_bg_stmt | set_palette_stmt | wait_frame_stmt ;

if_stmt         = "if" expr block { "else" "if" expr block } [ "else" block ] ;
while_stmt      = "while" expr block ;
for_stmt        = "for" IDENT "in" expr ".." expr block ;
loop_stmt       = "loop" block ;
return_stmt     = "return" [expr] ;
break_stmt      = "break" ;
continue_stmt   = "continue" ;

draw_stmt       = "draw" IDENT { draw_prop } ;
draw_prop       = IDENT ":" expr ;

play_stmt       = "play" IDENT ;
music_stmt      = ("start_music" | "stop_music") [IDENT] ;
transition_stmt = "transition" IDENT ;
scroll_stmt     = "scroll" "(" expr "," expr ")" ;
load_bg_stmt    = "load_background" IDENT ;
set_palette_stmt= "set_palette" IDENT ;
wait_frame_stmt = "wait_frame" "(" ")" ;

debug_stmt      = "debug" "." ( "log" | "assert" ) "(" expr { "," expr } ")" ;

asm_block       = "asm" "{" ASM_BODY "}" ;
                | "raw" "asm" "{" ASM_BODY "}" ;

fun_call        = IDENT "(" [expr { "," expr }] ")" ;

assign_stmt     = lvalue assign_op expr ;
assign_op       = "=" | "+=" | "-=" | "&=" | "|=" | "^=" | "<<=" | ">>=" ;
lvalue          = IDENT | IDENT "[" expr "]" ;

expr            = unary_expr { binary_op unary_expr } ;
unary_expr      = ["-" | "~" | "not"] primary_expr ;
primary_expr    = INTEGER | "true" | "false" | IDENT | IDENT "[" expr "]"
                | fun_call | "(" expr ")" | expr "as" type
                | input_expr ;

input_expr      = ["p1" "." | "p2" "."] "button" "." IDENT ;

binary_op       = "+" | "-" | "*" | "/" | "%" | "&" | "|" | "^"
                | "<<" | ">>" | "==" | "!=" | "<" | ">" | "<=" | ">="
                | "and" | "or" ;

start_decl      = "start" IDENT ;
```

---

## 20. Complete Example

See the companion file `nescript_sample_game.ne` ("Coin Cavern") for a complete game demonstrating states, sprites, input, collision, sound, animation, debug logging, and the asset pipeline.
