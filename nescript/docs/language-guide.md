# NEScript Language Guide

NEScript is a statically-typed, compiled language designed for NES game development. It compiles directly to 6502 machine code packaged as iNES-format ROMs -- no external assembler or tooling required.

This guide covers every language feature with practical examples.

---

## Program Structure

Every NEScript program consists of a game declaration, top-level definitions, and a start declaration.

```
game "My Game" {
    mapper: NROM
    mirroring: vertical
}

const SPEED: u8 = 2

var score: u8 = 0

fun helper() -> u8 {
    return 42
}

state Title {
    on frame {
        draw Logo at: (100, 100)
        if button.start {
            transition Playing
        }
    }
}

state Playing {
    on enter {
        score = 0
    }
    on frame {
        // game logic here
    }
}

start Title
```

### Game Declaration

The `game` block is required and must appear first. It names the game and sets hardware configuration.

```
game "Coin Cavern" {
    mapper: NROM
    mirroring: vertical
}
```

Available properties:

| Property     | Values                           | Default      |
|--------------|----------------------------------|--------------|
| `mapper`     | `NROM`, `MMC1`, `UxROM`, `MMC3`  | required     |
| `mirroring`  | `horizontal`, `vertical`         | `horizontal` |

### Start Declaration

Exactly one `start` declaration must exist. It names the initial state entered on power-on.

```
start Title
```

---

## Types

NEScript has four primitive types and fixed-size arrays.

### Primitive Types

| Type   | Size    | Range           | Description                        |
|--------|---------|-----------------|------------------------------------|
| `u8`   | 1 byte  | 0 to 255        | Unsigned 8-bit integer             |
| `i8`   | 1 byte  | -128 to 127     | Signed 8-bit integer               |
| `u16`  | 2 bytes | 0 to 65535      | Unsigned 16-bit integer            |
| `bool` | 1 byte  | `true` / `false`| Boolean                            |

### Arrays

Arrays are fixed-size, homogeneous, and zero-indexed. The size must be a compile-time constant. Maximum 256 elements.

```
var enemies: u8[8]
const TABLE: u8[4] = [10, 20, 30, 40]
```

### Type Casting

NEScript has no implicit coercion. All conversions use `as`:

```
var a: u8 = 200
var b: u16 = a as u16       // zero-extend: 200
var c: i8 = a as i8         // reinterpret bits
var d: u8 = b as u8         // truncate to low byte
```

---

## Variables

### Variable Declarations

Variables are declared with `var` and must have an explicit type:

```
var x: u8                   // uninitialized (zeroed on state entry)
var y: u8 = 100             // initialized
var pos: u16 = 0x0400       // 16-bit value
var alive: bool = true
var scores: u8[4] = [0, 0, 0, 0]
```

### Constants

Constants are evaluated at compile time and stored in ROM:

```
const MAX_ENEMIES: u8 = 5
const SPEED: u8 = 3
const SIN_TABLE: u8[8] = [0, 49, 90, 117, 127, 117, 90, 49]
```

### Enums

Enums declare a named set of `u8` constants. Each variant is assigned an
index starting at 0 in declaration order:

```
enum Direction { Up, Down, Left, Right }
// Up=0, Down=1, Left=2, Right=3

var player_dir: u8 = Up

on frame {
    if button.left  { player_dir = Left }
    if button.right { player_dir = Right }
    if player_dir == Down { /* ... */ }
}
```

Variant names are global — they are flattened into the top-level symbol
table, so a variant cannot share its name with any other constant,
variable, or function (E0501). An enum cannot have more than 256
variants because each is stored as a `u8`.

### Structs

Structs declare composite types with named fields:

```
struct Vec2 {
    x: u8,
    y: u8,
}

struct Player {
    health: u8,
    lives: u8,
}

var pos: Vec2
var hero: Player

on frame {
    pos.x = 100
    pos.y = 50
    hero.health = 3
    hero.lives = 5
    if button.right { pos.x += 1 }
    draw Hero at: (pos.x, pos.y)
}
```

Fields are laid out contiguously in declaration order. A variable of
struct type allocates enough contiguous bytes to hold all its fields;
each field is accessible via the dot operator.

Struct literals initialize or assign all fields at once:

```
struct Vec2 { x: u8, y: u8 }

// as an initializer
var pos: Vec2 = Vec2 { x: 100, y: 50 }

// as an assignment
on frame {
    pos = Vec2 { x: 0, y: 0 }
    if button.right {
        pos = Vec2 { x: pos.x + 1, y: pos.y }
    }
}
```

Inside `if`, `while`, and `for` conditions the struct literal syntax
is reserved for the following block, so wrap the literal in parens if
you ever need one in a condition:

```
if pos == (Vec2 { x: 0, y: 0 }) { /* ... */ }
```

In v0.1 only primitive field types (`u8`, `i8`, `bool`) are supported —
nested structs, `u16`, and array fields are not yet allowed.

### Memory Placement Hints

The NES has 256 bytes of zero-page RAM with faster access. You can hint where variables should be placed:

```
fast var px: u8             // prefer zero-page (faster instructions)
slow var high_score: u16    // prefer upper RAM (saves zero-page space)
var normal: u8              // compiler decides automatically
```

If zero-page is exhausted and `fast` variables cannot be placed, the compiler emits error `E0301`.

### Scope

| Scope    | Declared In    | Lifetime                                   |
|----------|----------------|---------------------------------------------|
| Global   | Top level      | Entire program, permanent RAM allocation    |
| State    | `state` block  | Active while state is active; RAM reusable  |
| Function | `fun` block    | Duration of function call                   |
| Block    | `if`/`while`   | Enclosing block, shares parent allocation   |

---

## Functions

### Declaration

Functions use `fun`, with optional parameters and return type:

```
fun add(a: u8, b: u8) -> u8 {
    return a + b
}

fun reset_score() {
    score = 0
}
```

### Inline Functions

The `inline` keyword marks a function for inlining at call sites. The IR
lowering pass captures the body up front and substitutes it wherever the
function is called, skipping the normal `JSR` entirely. Two body shapes
are accepted:

**Single-return expression** — a function with a declared return type
whose body is exactly `{ return <expr> }`. The expression is re-lowered
in place of each call, with every parameter name substituted for the
caller's argument temps.

```
inline fun card_rank(card: u8) -> u8 {
    return card >> 4
}
```

**Void multi-statement** — a function with no return type whose body is
a sequence of plain statements (assigns, calls, draws, scroll,
`set_palette`, `load_background`, `wait_frame`, `cycle_sprites`, inline
asm, or the `debug.*` builtins). Nested control flow, `return`,
`break`, `continue`, and `transition` are not allowed.

```
inline fun set_phase(p: u8) {
    phase = p
    phase_timer = 0
    cursor_x = 0
}
```

Functions marked `inline` whose body doesn't match either shape (a
conditional early return, a `while` loop, nested `if`/`else`, etc.)
fall back to a regular out-of-line `JSR` call. The compiler emits a
`W0110` warning at the declaration site so the declined hint is
visible — rewrite the body to fit one of the two shapes, or drop the
`inline` keyword if the call overhead is acceptable.

### Calling Functions

```
var result: u8 = add(10, 20)
reset_score()
```

### Restrictions

- **No recursion.** Both direct and indirect recursion are compile errors (`E0402`).
- **Call depth limit.** The default maximum call depth is 8. Exceeding it produces error `E0401`.
- **Maximum 8 parameters per function.** The calling convention is hybrid: **leaf** functions (no nested `JSR` in their body) receive up to four parameters through fixed zero-page transport slots `$04`-`$07`, while **non-leaf** functions receive up to eight parameters via direct caller writes into per-function RAM spill slots (no transport, no prologue copy). Declaring a function with 9+ parameters produces error `E0506`. Declaring a leaf with 5+ parameters silently promotes it to the non-leaf convention — you pay the direct-write cost rather than the prologue-copy cost, which is still cheaper than the old transport-plus-spill path.

#### Why no recursion?

This is a deliberate design choice, not a bug. NEScript uses a hybrid
direct-write calling convention that lands each function's
parameters and locals at a fixed RAM address the analyzer reserves
at compile time. Recursion would require each activation to have
its own stack frame, which means either:

1. A software stack pointer managed by a prologue/epilogue at every
   call site (costs cycles on a platform that only has 2 KB of RAM
   and a 256-byte hardware stack), or
2. The hardware stack carrying frames directly (the 6502's 256-byte
   `$0100-$01FF` stack overflows fast — a single recursive call
   with any meaningful locals blows it within a handful of levels).

Neither is a good fit for the NES's constraints, and NEScript
already surfaces the tradeoff at compile time via the call-depth
limit (`E0401`) and the parameter cap (`E0506`). The direct-write
convention is what makes those limits enforceable.

If you actually need recursion-shaped logic — flood fill, tree
walking, tile-spread simulations — the idiomatic pattern is an
explicit stack held in a small `u8` array:

```
const MAX_STACK: u8 = 32
var stack: u8[MAX_STACK] = [0; 32]
var top: u8 = 0

fun flood_push(x: u8) {
    stack[top] = x
    top += 1
}

fun flood_pop() -> u8 {
    top -= 1
    return stack[top]
}

fun flood_fill(start: u8) {
    flood_push(start)
    while top > 0 {
        var here: u8 = flood_pop()
        // ...process `here`, push neighbours that need visiting...
    }
}
```

This gives the compiler full visibility into the worst-case stack
depth (`MAX_STACK`), uses flat RAM instead of the hardware stack,
and composes cleanly with the call-graph validator.

---

## States

States are the top-level organizational unit. Exactly one state is active at any time.

### State Declaration

```
state Playing {
    var timer: u8 = 0           // state-local variable

    on enter {
        // runs once when entering this state
        timer = 60
    }

    on exit {
        // runs once when leaving this state
    }

    on frame {
        // runs every frame (60 Hz) while this state is active
        timer -= 1
        draw Player at: (player_x, player_y)
    }
}
```

`on frame` is syntactic sugar for a loop with an implicit `wait_frame()` at the end. A state can have any combination of `on enter`, `on exit`, and `on frame`.

### State-Local Variables and Memory Overlays

Variables declared directly inside a `state` block (outside any handler) are **state-local**. They are visible to every handler in the state (`on enter`, `on frame`, etc.) and persist for as long as that state is active.

Because the NES runtime keeps exactly one state active at a time, the compiler **automatically overlays state-local variables across states**. Two states' locals can share the same RAM bytes without colliding — only the currently active state reads or writes them. This makes the limited 2 KB of NES work RAM go much further on programs with many scenes or game modes.

```
state Title {
    var blink: u8 = 0   // overlays with Playing.timer below
    on enter { blink = 0 }
    on frame { blink = blink + 1 }
}

state Playing {
    var timer: u8 = 0   // same byte as Title.blink — reused
    var lives: u8 = 3
    on enter { timer = 0; lives = 3 }
    on frame { timer = timer + 1 }
}
```

Every time a state is entered, its state-local variables are re-initialized from their declared initializers (`= 0`, `= 3` above) before `on enter` runs. This is what makes the overlay safe: entering Playing re-runs `timer = 0` even if the previous state wrote a different value into the shared byte. `cargo run -- build <file> --memory-map` shows each overlaid address alongside its owning state.

Global `var`s (declared at the top level, outside any state) are never overlaid and keep dedicated RAM slots. Variables declared inside a handler block are handler-local and live only for the handler invocation.

### State Transitions

```
transition GameOver
```

Transitions are immediate. The current state's `on exit` runs, then the target state's `on enter` runs. The remainder of the current frame handler does not execute.

---

## Expressions

### Literals

```
42              // decimal integer
0xFF            // hexadecimal
0b10110001      // binary
1_000           // underscores allowed for readability (if supported)
true            // boolean
false           // boolean
[1, 2, 3]      // array literal
```

All integer literals must fit in `u16` (0-65535). The compiler narrows to the required type at usage.

### Arithmetic Operators

| Operator | Description    | Example      |
|----------|----------------|--------------|
| `+`      | Addition       | `a + b`      |
| `-`      | Subtraction    | `a - b`      |
| `*`      | Multiplication | `a * b`      |
| `/`      | Division       | `a / b`      |
| `%`      | Modulo         | `a % b`      |

`*`, `/`, and `%` are available but expensive on the 6502 (software routines). The compiler optimizes power-of-two operations to shifts and warns on non-power-of-two multiply/divide.

### Bitwise Operators

| Operator | Description    | Example      |
|----------|----------------|--------------|
| `&`      | Bitwise AND    | `a & 0x0F`   |
| `\|`     | Bitwise OR     | `a \| 0x80`  |
| `^`      | Bitwise XOR    | `a ^ mask`   |
| `~`      | Bitwise NOT    | `~a`         |
| `<<`     | Shift left     | `a << 2`     |
| `>>`     | Shift right    | `a >> 1`     |

### Comparison Operators

| Operator | Description       | Example      |
|----------|-------------------|--------------|
| `==`     | Equal             | `a == 0`     |
| `!=`     | Not equal         | `a != b`     |
| `<`      | Less than         | `a < 10`     |
| `>`      | Greater than      | `a > max`    |
| `<=`     | Less or equal     | `a <= 255`   |
| `>=`     | Greater or equal  | `a >= min`   |

### Logical Operators

NEScript uses keyword-based logical operators:

```
if alive and (health > 0) {
    // ...
}
if not paused or force_update {
    // ...
}
```

| Operator | Description   |
|----------|---------------|
| `and`    | Logical AND   |
| `or`     | Logical OR    |
| `not`    | Logical NOT   |

### Operator Precedence

From highest to lowest:

| Level | Operators                          | Associativity |
|-------|------------------------------------|---------------|
| 1     | `()` grouping                      | --            |
| 2     | `-` (unary), `~`, `not`            | right         |
| 3     | `*`, `/`, `%`                      | left          |
| 4     | `+`, `-`                           | left          |
| 5     | `<<`, `>>`                         | left          |
| 6     | `&`                                | left          |
| 7     | `^`                                | left          |
| 8     | `\|`                               | left          |
| 9     | `==`, `!=`, `<`, `>`, `<=`, `>=`   | left          |
| 10    | `and`                              | left          |
| 11    | `or`                               | left          |

### Button Reads

Read controller input as boolean expressions:

```
if button.right {
    player_x += SPEED
}
if button.a {
    jump()
}
```

Available buttons: `up`, `down`, `left`, `right`, `a`, `b`, `start`, `select`.

For two-player games, prefix with the player:

```
if p1.button.a { /* player 1 */ }
if p2.button.right { /* player 2 */ }
```

Without a prefix, `button` refers to player 1.

### Function Calls in Expressions

```
var clamped: u8 = clamp_x(player_x + SPEED)
```

### Array Indexing

```
var val: u8 = table[i]
table[i] = 0
```

### Type Casting

```
var wide: u16 = narrow as u16
```

---

## Statements

### Assignment

```
x = 10
x += 5
x -= 1
x &= 0x0F
x |= 0x80
x ^= mask
```

All assignment operators:

| Operator | Description         |
|----------|---------------------|
| `=`      | Assign              |
| `+=`     | Add and assign      |
| `-=`     | Subtract and assign |
| `&=`     | AND and assign      |
| `\|=`    | OR and assign       |
| `^=`     | XOR and assign      |

Array element assignment:

```
enemies[i] = 0
scores[player] += 10
```

### If / Else If / Else

Braces are always required. No ternary operator.

```
if health == 0 {
    transition GameOver
} else if health < 3 {
    flash_warning()
} else {
    // normal gameplay
}
```

### While Loop

```
var i: u8 = 0
while i < 10 {
    enemies[i] = 0
    i += 1
}
```

### Match Statement

`match` matches a scrutinee against a sequence of patterns and
executes the body of the first matching arm. Each arm's pattern is
compared against the scrutinee with `==`. An underscore arm `_` acts
as the catch-all:

```
enum State { Title, Playing, GameOver }
var state: u8 = Title

on frame {
    match state {
        Title => {
            if button.start { state = Playing }
        }
        Playing => {
            // ... game logic ...
        }
        GameOver => {
            if button.a { state = Title }
        }
        _ => {}
    }
}
```

`match` desugars to an `if` / `else if` chain at parse time, so
patterns can be any expression that produces a value comparable to
the scrutinee.

### For Loop

The `for` loop iterates over a half-open integer range `[start, end)`:

```
for i in 0..8 {
    total += arr[i]
}
```

The loop variable is a `u8` scoped to the loop body. Both bounds can
be any expression that evaluates to `u8` at runtime, including
constants or variables. The range is half-open, so `0..8` iterates
`0, 1, 2, ..., 7` (8 iterations). For a closed range, use `0..9`.

The loop is desugared into a `while` loop with an index variable, so
`break` and `continue` work the same as in any loop body.

### Loop (Infinite)

```
loop {
    wait_frame()
    if button.start {
        break
    }
}
```

The compiler warns if a `loop` contains neither `break`, `wait_frame`, nor `transition`.

### Break and Continue

```
var i: u8 = 0
while i < 20 {
    i += 1
    if enemies[i] == 0 {
        continue            // skip inactive enemies
    }
    if i > 10 {
        break               // stop processing
    }
    update_enemy(i)
}
```

### Return

```
fun abs_diff(a: u8, b: u8) -> u8 {
    if a > b {
        return a - b
    }
    return b - a
}
```

Functions without a return type use `return` with no value (or simply reach the end of the function body).

### Draw

Render a sprite to the screen:

```
draw Player at: (player_x, player_y)
draw Coin at: (COIN_X, COIN_Y) frame: anim_frame
```

The `draw` statement writes to the OAM shadow buffer. The NES supports
up to 64 sprites per frame, and the PPU can only render 8 sprites per
scanline — see the `cycle_sprites` statement below and the
[sprite-per-scanline mitigations](#sprite-per-scanline-mitigations)
section for how to handle scenes that exceed the 8-per-scanline budget.

Syntax: `draw SpriteName at: (x_expr, y_expr) [frame: expr]`

### Transition

Switch to another state immediately:

```
transition GameOver
```

The current state's `on exit` runs, then the target state's `on enter` runs.

### Wait Frame

Yield execution until the next vertical blank (NMI). Synchronizes to the 60 Hz display refresh.

```
wait_frame()
```

This triggers OAM DMA transfer and PPU updates before yielding. Inside `on frame`, a `wait_frame()` is implicit at the end of each frame.

### Cycle Sprites

Rotate the runtime's sprite-cycling offset by one OAM slot (4 bytes),
naturally wrapping at 256 back to 0. When any statement in a program
emits `cycle_sprites`, the linker switches the NMI handler over to a
variant that writes the current offset byte (at `$07EF`) to `$2003`
before triggering the OAM DMA — so each frame's DMA lands in a
different slot of the PPU's OAM buffer.

```
on frame {
    draw Enemy0 at: (e0x, e0y)
    draw Enemy1 at: (e1x, e1y)
    // ...lots of enemies...
    cycle_sprites
    wait_frame
}
```

The practical effect is the classic NES flicker: scenes with more than
8 sprites on a single scanline drop a *different* sprite on each
frame, and the eye reconstructs the missing pixels from frame
persistence. Permanent dropout becomes visible flicker, which reads as
a hardware limit rather than a game bug.

`cycle_sprites` is opt-in by design. Programs that never call it emit
the original fixed-offset NMI path (byte-identical to every
pre-cycling ROM). See
[sprite-per-scanline mitigations](#sprite-per-scanline-mitigations)
for when to use it together with the compile-time `W0109` warning and
the debug-mode `debug.sprite_overflow*()` telemetry.

### Scroll

Set the PPU scroll position:

```
scroll(scroll_x, scroll_y)
```

### Set Palette

```
set_palette NightPalette
```

Queues the named palette for a vblank-safe copy into PPU palette
RAM (`$3F00-$3F1F`). The write is applied by the NMI handler on the
next vblank. See `palette` declarations below.

### Load Background

```
load_background Level1
```

Queues the named background (a full-screen 32×30 nametable + 64-byte
attribute table) for a vblank-safe copy into nametable 0
(`$2000-$23FF`). Applied by the NMI handler at the next vblank. See
`background` declarations below.

### Function Calls as Statements

```
reset_score()
update_physics(player_x, player_y)
```

---

## Assets

### Sprite Declarations

Sprites can be authored in two ways. Pick whichever maps best to how
your art starts out.

**Raw CHR bytes.** Supply 16 bytes of 2-bitplane CHR per tile — the
form every NES toolchain consumes:

```
sprite Player {
    chr: @chr("assets/player.png")
}

sprite Coin {
    chr: @binary("assets/coin.bin")
}

sprite Heart {
    chr: [0x66, 0xFF, 0xFF, 0xFF, 0x7E, 0x3C, 0x18, 0x00,
          0x66, 0xFF, 0xFF, 0xFF, 0x7E, 0x3C, 0x18, 0x00]
}
```

**ASCII pixel art.** One string per 8-pixel row, one character per
pixel. Far easier to hand-author, and the compiler does the 2-bitplane
encoding for you:

```
sprite Arrow {
    pixels: [
        "...##...",
        "...###..",
        "########",
        "########",
        "########",
        "########",
        "...###..",
        "...##..."
    ]
}
```

Characters map to 2-bit palette indices:

| Char(s)     | Index | Meaning                  |
|-------------|-------|--------------------------|
| `.` ` ` `0` | 0     | transparent / background |
| `#` `1`     | 1     | sub-palette colour 1     |
| `%` `2`     | 2     | sub-palette colour 2     |
| `@` `3`     | 3     | sub-palette colour 3     |

Both dimensions must be multiples of 8. Multi-tile sprites (16×8,
8×16, 16×16, …) are split into 8×8 tiles in row-major reading order
so consecutive tile indices match what your eye reads.

### Palette Declarations

Palettes can be authored in two styles. Both produce the same 32-byte
PPU palette blob (background + sprite, in the canonical
`$3F00-$3F1F` layout) — pick whichever reads best.

**Flat form.** The raw 32-byte list, matching how PPU palette RAM is
laid out. Every entry can be a byte literal *or* a named NES colour:

```
palette MainPalette {
    colors: [
        black, dk_blue,  blue,    sky_blue,   // bg sub-palette 0
        black, dk_red,   red,     peach,      // bg sub-palette 1
        black, dk_green, green,   mint,       // bg sub-palette 2
        black, dk_gray,  lt_gray, white,      // bg sub-palette 3
        black, dk_blue,  blue,    sky_blue,   // sp sub-palette 0
        black, dk_red,   red,     peach,      // sp sub-palette 1
        black, dk_green, green,   mint,       // sp sub-palette 2
        black, dk_gray,  lt_gray, white       // sp sub-palette 3
    ]
}
```

**Grouped form.** Declare each sub-palette by name and supply a shared
`universal:` colour. The compiler auto-fills every sub-palette's
first byte with the universal, which fixes the notorious
`$3F10 / $3F14 / $3F18 / $3F1C` mirror trap: when a program writes
all 32 bytes sequentially, the last four "sprite sub-palette 0"
bytes would otherwise overwrite the shared background colour.

```
palette Sunset {
    universal: black
    bg0: [dk_blue,  blue,    sky_blue]
    bg1: [dk_red,   red,     peach]
    bg2: [dk_olive, olive,   cream]
    bg3: [dk_gray,  lt_gray, white]
    sp0: [dk_blue,  blue,    sky_blue]
    sp1: [dk_red,   red,     peach]
    sp2: [dk_green, green,   mint]
    sp3: [dk_gray,  lt_gray, white]
}
```

Each `bgN` / `spN` field takes 3 colours (the universal is
prepended); giving 4 colours instead overrides the universal for
that slot only. Omitted slots default to `[universal, 0, 0, 0]`.

**Named colours.** Friendlier than hex bytes, and the names are the
same ones you'd find on a NES palette poster. Names are
case-insensitive, and `dark_red` / `dk_red` / `dark-red` are all
synonyms.

| Group      | Names                                                           |
|------------|-----------------------------------------------------------------|
| Grayscale  | `black`, `dk_gray`, `gray`, `lt_gray`, `white`, `off_white`     |
| Blues      | `dk_blue`, `blue`, `sky_blue`, `pale_blue`, `indigo`, `royal_blue`, `periwinkle`, `ice_blue` |
| Purples    | `dk_purple`, `purple` (`violet`), `lavender`, `pale_purple`, `dk_magenta`, `magenta`, `pink`, `pale_pink` |
| Pinks      | `maroon`, `rose`, `hot_pink`, `pale_rose`                       |
| Reds       | `dk_red`, `red`, `lt_red`, `peach`                              |
| Oranges    | `brown`, `dk_orange`, `orange`, `tan`                           |
| Yellows    | `dk_olive`, `olive`, `yellow`, `cream`                          |
| Greens     | `dk_green`, `green`, `lime`, `pale_green`, `forest`, `bright_green`, `neon_green`, `mint` |
| Teals      | `dk_teal`, `teal`, `aqua`, `pale_teal`                          |
| Cyans      | `dk_cyan`, `cyan`, `lt_cyan`, `pale_cyan`                       |

`black` maps to `$0F`, the canonical "one true black" slot the
hardware guarantees to render as `(0, 0, 0)` on every TV. If a
colour name you want isn't listed, reach for a hex byte literal —
the palette helper resolves every NES master-palette index `$00-$3F`.

The *first* `palette` declared in a program is loaded into VRAM at
reset time, before rendering is enabled, so the title screen boots
with the right colours on frame 0. Additional declarations sit in
PRG ROM as named data blobs and become active via `set_palette Name`,
which queues the write for the next vblank.

### Background Declarations

Like palettes and sprites, backgrounds can be authored two ways.

**Raw byte form.** A flat `tiles:` list (up to 960 bytes, row-major)
and an optional `attributes:` list (up to 64 bytes). Best if you've
already generated the nametable with an external tool.

```
background TitleScreen {
    tiles: [0x00, 0x01, 0x01, 0x00,  /* ... up to 960 bytes ... */]
    attributes: [0xFF, 0x55,         /* ... up to 64 bytes ... */]
}
```

**Tilemap form.** A `legend { }` block names single characters, a
`map:` list-of-strings paints the nametable one row at a time, and
an optional `palette_map:` grid of digit characters packs the 64-byte
attribute table automatically:

```
background StageOne {
    legend {
        ".": 0       // empty / sky
        "#": 1       // brick
        "X": 2       // coin
    }
    map: [
        "................................",
        "................................",
        "......##........##..............",
        "....##..##....##..##............",
        "..##......##.##.....##..........",
        "##..........###.......##........"
    ]
    palette_map: [
        "0000000000000000",   // 16 cells wide; one entry per 16×16 metatile
        "0000000000000000",
        "0000111111110000",
        "0000111111110000",
        "2222222222222222"
        // ... up to 15 rows total
    ]
}
```

Rules:
- `map:` strings must be ≤ 32 characters; shorter rows are
  right-padded with tile 0. No more than 30 rows.
- Every character in a `map:` string must be defined in the legend
  (otherwise `E0201`).
- `palette_map:` rows are ≤ 16 digit characters (`0`-`3`, plus
  `.` / space as a sub-palette 0 alias). Up to 16 rows are
  accepted: the first 15 cover the visible 240-scanline screen and
  the optional 16th covers the off-screen half of the last
  attribute row (the PPU still reads it). If exactly 15 rows are
  supplied, the parser auto-replicates row 14 into row 15 so the
  visible bottom edge of the screen gets consistent attribute
  bytes. The packer handles the awkward
  `(br<<6)|(bl<<4)|(tr<<2)|tl` attribute-byte layout for you.
- Raw and tilemap forms are mutually exclusive per field
  (`tiles:` vs `map:`, `attributes:` vs `palette_map:`).

The *first* `background` declared is loaded into nametable 0 at
reset time and background rendering is enabled automatically.
Additional backgrounds can be swapped in via `load_background Name`,
which queues the update for the next vblank. Full-nametable updates
do not fit inside a single vblank, so large background swaps may
require the program to disable rendering temporarily.

### Asset Sources

Three ways to provide asset data:

| Source                     | Description                           |
|----------------------------|---------------------------------------|
| `@chr("file.png")`        | Convert PNG to CHR tile data          |
| `@binary("file.bin")`     | Include raw binary data verbatim      |
| Inline `[0x00, 0x7E, ...]`| Hex byte array directly in source     |

---

## Audio

NEScript ships with a full data-driven audio subsystem. Sound effects run on pulse channel 1 and music runs on pulse channel 2, both driven by an NMI-time tick that walks per-track data tables compiled into PRG ROM. Programs that never touch audio pay zero ROM or cycle cost — the driver and its period table are only linked in when user code contains at least one `play`, `start_music`, or `stop_music` statement.

### Statements

```
play SfxName          // trigger a one-shot sound effect
start_music TrackName // begin looping background music
stop_music            // silence the music channel
```

Each statement looks up the name in the program's user declarations first, then falls back to the builtin table. Unknown names are a hard error (E0505).

### SFX Declarations

An `sfx` block is a frame-accurate envelope for pulse 1. The v1
audio driver latches the pulse period *once* on trigger (it never
updates `$4002/$4003` mid-effect), so a scalar pitch is the natural
way to write one. `volume` / `envelope` runs one byte per frame, so
the envelope length controls the effect duration:

```
sfx Pickup {
    duty: 2                                // 0-3, 2 = 50% square (default)
    pitch: 0x50                            // latched period byte
    envelope: [15, 12, 9, 6, 3]            // 0-15, one entry per frame
}
```

Both spellings are interchangeable:

- `pitch: 0x50` — single byte, latched once on trigger.
- `pitch: [0x50, 0x50, ...]` — per-frame array, still accepted for
  backwards compatibility; the analyzer requires its length to
  match `volume`.
- `envelope: [...]` and `volume: [...]` — aliases for the same
  field. Use whichever reads better in context.

Rules:
- `envelope` / `volume` values are 0-15 (4-bit pulse volume).
- `duty` is 0-3 and defaults to 2.
- Maximum 120 frames (2 seconds at 60 fps).

### Music Declarations

A `music` block is a list of `(pitch, duration)` pairs played on
pulse 2. Two authoring styles are available; the parser picks
between them based on whether `tempo:` is set.

**Note-name form** — set `tempo:` to the default frames-per-note and
write each note as a name (C4, Eb4, Fs4, …, rest) with an optional
per-note duration override:

```
music Theme {
    duty: 2                              // 0-3 (default 2)
    volume: 10                           // 0-15 (default 10)
    repeat: true                         // loop when track ends (default true)
    tempo: 20                            // default frames per note
    notes: [
        C4, E4, G4, C5,                  // each note lasts 20 frames
        G4 40,                           // held twice as long
        rest 10,                         // short rest
        E4, C4
    ]
}
```

**Raw-pair form** — leave `tempo:` unset and write a flat list of
`pitch, duration, pitch, duration, ...` integer pairs:

```
music Theme {
    duty: 2
    volume: 10
    notes: [
        37, 20,    // C4 for 20 frames
        41, 20,    // E4
        44, 20,    // G4
        49, 20,    // C5
        0, 10      // rest for 10 frames
    ]
}
```

Note names cover C1..B5 (60 entries in the builtin period table,
middle C at index 37). Accidentals use `s` for sharp and `b` for
flat (e.g. `Cs4` = C#4 = `Db4`) because `#` / `♭` aren't valid
identifier characters. `rest` (or the alias `_`) is pitch 0.

Rules:
- Raw-pair form must contain an even number of entries.
- Pitches are 0 (rest) or 1-60 (period table index).
- Duration must be ≥ 1 frame.
- `tempo` must be ≥ 1 frame (only present in note-name form).
- Maximum 256 notes per track.

### Builtin Names

For programs that want classic game audio without writing data tables, NEScript provides a handful of builtin effects and tracks that can be used directly:

**Builtin SFX**

| Name | Description |
|------|-------------|
| `coin`, `pickup`, `collect` | Ascending high blip |
| `jump`, `hop` | Descending arc |
| `hit`, `damage`, `explode` | Low blast |
| `click`, `select`, `confirm` | Sharp beep |
| `cancel`, `back`, `error` | Low longer tone |
| `shoot`, `laser`, `fire` | Very high pulse |
| `step`, `footstep` | Short low thud |

**Builtin Music**

| Name | Description |
|------|-------------|
| `title`, `theme`, `main` | Major arpeggio (looping) |
| `battle`, `boss` | Driving pulse (looping) |
| `win`, `victory`, `fanfare` | Ascending burst (one-shot) |
| `gameover`, `lose`, `fail` | Descending dirge (looping) |

A user-declared `sfx` or `music` block takes priority over a builtin with the same name, so `sfx coin { ... }` will shadow the default coin effect.

### How It Works

Compile time:

1. The resolver compiles each `sfx` into `(period_lo, period_hi, envelope[])` and each `music` into `(header, (pitch, duration)[])`, appending builtins for any referenced name that isn't user-declared.
2. The IR codegen emits `play Name` as: write trigger bytes to `$4002`/`$4003`, load envelope pointer into `$0C/$0D`, set the sfx counter. `start_music Name` stamps a state byte into `$07`, loads the stream pointer into `$0E/$0F` (and the loop base into `$05/$06`), and primes the duration counter.
3. The linker splices the audio tick, the 60-entry period table, and every compiled sfx/music blob into PRG ROM, all guarded on a `__audio_used` marker label so silent programs never pay the cost.

Runtime (every NMI, if audio is in use):

1. **SFX**: if the counter is nonzero, read one envelope byte through `(ZP_SFX_PTR),Y` and write it to `$4000`. A zero sentinel mutes pulse 1 and stops the tick.
2. **Music**: if active and the note counter hits zero, read the next pitch byte. 0 = rest (mute pulse 2). 1-60 = look up the period in the table and write to `$4006`/`$4007`. `0xFF` = loop back to the base pointer (or mute if `repeat: false`). Then read the duration byte and reload the counter.

Total memory cost: 8 bytes of zero page, ~200 bytes for the driver body, 120 bytes for the period table, plus the data for each user-declared sfx/music.

---

## Mappers

The mapper determines cartridge hardware and available ROM size.

| Mapper  | PRG ROM       | CHR ROM        | Features                         |
|---------|---------------|----------------|----------------------------------|
| `NROM`  | 16 or 32 KB   | 8 KB           | No banking, simplest             |
| `MMC1`  | Up to 256 KB  | Up to 128 KB   | Switchable banks                 |
| `UxROM` | Up to 256 KB  | 8 KB CHR RAM   | PRG banking only                 |
| `MMC3`  | Up to 512 KB  | Up to 256 KB   | Scanline counter, banking        |

### Bank Declarations

For mappers with bank switching:

```
bank MainCode {
    // Always-resident code (NMI handler, core engine)
}

bank Level1 {
    state Level1 { ... }
    background Level1BG { ... }
}
```

Banks can hold `prg` (code/data) or `chr` (graphics) content. Transitions between states in different banks automatically emit bank-switch and trampoline code.

---

## Comments

```
// Line comment -- extends to end of line

/* Block comment
   spans multiple lines */
```

---

## Includes

Split your game across multiple files:

```
include "physics.ne"
include "enemies.ne"
```

Includes are resolved relative to the including file. Circular includes are a compile error. Duplicate includes are skipped automatically.

---

## Debug Mode

Compile with `--debug` to enable runtime instrumentation. All debug features are stripped completely in release builds (zero bytes, zero cycles).

### Debug Logging

```
debug.log("Player position: ", px, ", ", py)
```

### Debug Assertions

```
debug.assert(lives > 0, "Lives should never be negative")
```

### Runtime Checks (Debug Only)

In debug mode, the compiler inserts:
- Array bounds checking on indexed access
- Arithmetic overflow warnings
- Stack depth monitoring at function entry
- Frame overrun detection (bumps a counter at `$07FF` whenever the
  frame handler runs past vblank)
- Sprite-per-scanline overflow detection (bumps a counter at `$07FD`
  whenever the PPU's sprite overflow flag at `$2002` bit 5 was set
  for the just-finished frame)

### Debug Queries

Four builtin expressions let user code inspect the debug counters and
sticky bits. All four return a `u8`, peek a fixed runtime address in
debug builds, and compile to a constant zero in release builds (so
`debug.assert(not debug.frame_overran())` guards disappear entirely
when you ship).

```
var n: u8 = debug.frame_overrun_count()    // cumulative overruns since reset
debug.assert(not debug.frame_overran())    // sticky bit, cleared on next wait_frame

var s: u8 = debug.sprite_overflow_count()  // cumulative PPU sprite overflows
debug.assert(not debug.sprite_overflow())  // sticky bit, cleared on next wait_frame
```

The sprite overflow pair reads the NES hardware flag (`$2002` bit 5),
which has a few well-known quirks but is correct for the overwhelming
majority of cases. Use it together with the compile-time `W0109` static
check and the runtime `cycle_sprites` flicker mitigation — see the
sprite-per-scanline section below.

### Sprite-per-scanline mitigations

The NES PPU can only render 8 sprites per scanline. Anything past the
budget is silently dropped, and because sprites land in the shadow OAM
in draw order, the same sprite gets dropped every frame — a permanent
dropout that reads as a bug rather than a hardware limit. NEScript
ships three layers of mitigation:

1. **Compile time** — the `W0109` warning fires on layouts with more
   than 8 literal-coordinate sprites overlapping any scanline. Catches
   static HUDs, text labels, and title screens.
2. **Runtime** — the `cycle_sprites` keyword statement bumps a
   rotating offset byte at `$07EF`. A cycling variant of the NMI
   handler writes that byte to `$2003` before the OAM DMA, so each
   frame's DMA lands in a different slot of the PPU's OAM buffer.
   Over N frames each of the N overlapping sprites gets dropped
   approximately once, producing visible flicker the eye
   reconstructs from frame persistence — the classic NES idiom
   used by Gradius, Battletoads, and every shmup.
3. **Playtesting** — `debug.sprite_overflow()` /
   `debug.sprite_overflow_count()` expose the PPU hardware flag as
   debug queries so user code can assert the budget holds, or a
   debug overlay can display the running count.

```
on frame {
    // ... draw all your sprites ...
    cycle_sprites   // rotate one slot per frame
    wait_frame
}
```

See `examples/sprite_flicker_demo.ne` for the end-to-end flow.

---

## Hardware Intrinsics

For the common case of reading or writing a single PPU/APU/mapper
register, NEScript provides two built-in intrinsics:

```
poke(0x2006, 0x3F)        // write $3F to PPU address register
poke(0x2006, 0x00)        // (second half of the address)
poke(0x2007, 0x0F)        // write a palette byte to PPU data

var status: u8 = peek(0x2002)  // read PPU status register
```

The address argument to both is a compile-time constant. Zero-page
addresses compile to `STA $XX` / `LDA $XX`; anything larger compiles
to absolute addressing.

## VRAM Update Buffer

The PPU's `$2006` / `$2007` registers can only be written safely
during vblank — writing during active rendering corrupts the
internal address register and garbles every subsequent tile.
`on frame` handlers run partly during vblank and partly during
rendering, so user code can't directly `poke` the PPU.

The VRAM update buffer solves this: user intrinsics **queue** PPU
writes to a 256-byte ring at `$0400-$04FF` during `on frame`, and
the NMI handler **drains** the ring to `$2007` during vblank. User
code never touches `$2006` or `$2007` directly.

Three intrinsics cover the common patterns:

```
nt_set(x, y, tile)              // one tile at nametable cell (x, y)
nt_attr(x, y, value)            // one attribute byte covering the
                                //   4×4-cell metatile at (x, y)
nt_fill_h(x, y, len, tile)      // horizontal run of `len` copies
                                //   of `tile` starting at (x, y)
```

`x` and `y` are nametable cell coordinates (`0..32`, `0..30`) — not
pixel coordinates. The compiler computes the PPU address
(`$2000 + y*32 + x` for nametable, `$23C0 + (y/4)*8 + (x/4)` for
attribute) and emits the buffer-append inline at each call site.

### HUD pattern

Queue an update only when the underlying state changes. That
makes per-frame cost scale with what actually moved, not with HUD
complexity:

```
var score:      u8 = 0
var last_score: u8 = 255   // 255 forces the first-frame paint

on frame {
    // ... gameplay that may or may not bump `score` ...

    if score != last_score {
        last_score = score
        var digit: u8 = score & 0x0F
        nt_set(28, 1, digit)    // one 4-byte buffer entry
    }
}
```

A typical HUD touches two or three cells per change, so the 256-
byte buffer is more than enough for any realistic frame. See
`examples/hud_demo.ne` for a worked example with a bouncing-ball
playfield, a score cell that updates on each wall hit, a 5-cell
lives indicator drawn via `nt_fill_h`, and a one-shot `nt_attr`
call at startup that paints the HUD row in a distinct palette.

### Budget

Per-entry buffer cost:

| Intrinsic      | Buffer bytes       | Drain cycles         |
|----------------|--------------------|----------------------|
| `nt_set`       | 4                  | ~20                  |
| `nt_attr`      | 4                  | ~20                  |
| `nt_fill_h`    | `3 + len`          | `~12 + 8*len`        |

The 256-byte buffer holds ~50 single-tile writes that drain in
~1000 cycles, well inside vblank's ~2273-cycle budget. Programs
that don't call any of the three intrinsics pay zero bytes and
zero cycles — the drain routine isn't linked, the NMI doesn't
JSR it, and the 256-byte buffer region stays available for user
variables.

### Limits

- Only **horizontal** writes (PPU auto-increment 1). Vertical
  writes (column-fill) would need to toggle `$2000` bit 2; that's
  a known follow-up documented in `docs/future-work.md` §G.
- `nt_fill_h` takes a runtime `len`. If `len` overflows the
  remaining space in the buffer (head + 3 + len > 256) the writer
  scribbles into neighbouring RAM. The runtime does not bounds-
  check; a debug-mode overflow trap is a known follow-up.
- The buffer does not coalesce adjacent writes. Calling
  `nt_set(0, 0, 1)` then `nt_set(1, 0, 2)` emits two separate
  entries (8 buffer bytes) even though a single `len=2` entry
  would fit both.

## Inline Assembly

For more elaborate sequences, use `asm { ... }` blocks:

```
fun fast_shift(input: u8) -> u8 {
    var result: u8 = 0
    asm {
        LDA {input}
        ASL A
        ASL A
        STA {result}
    }
    return result
}
```

Inside an `asm` block, `{name}` is replaced with the resolved
zero-page or absolute address of the variable `name`. Labels
defined with `name:` are local to the block.

### Raw Assembly

```
raw asm {
    LDA #$42
    STA $2007
}
```

`raw asm` skips variable substitution — `{name}` is passed through
verbatim. Useful for completely unmanaged snippets that don't
reference NEScript variables.

---

## Error Codes

### Lexer Errors (E01xx)

| Code   | Description                |
|--------|----------------------------|
| E0101  | Unterminated string literal |
| E0102  | Invalid character           |
| E0103  | Number literal overflow     |

### Type Errors (E02xx)

| Code   | Description                |
|--------|----------------------------|
| E0201  | Type mismatch              |
| E0203  | Invalid operation for type |

### Memory Errors (E03xx)

| Code   | Description                |
|--------|----------------------------|
| E0301  | Zero-page overflow         |

### Control Flow Errors (E04xx)

| Code   | Description                |
|--------|----------------------------|
| E0401  | Call depth exceeded        |
| E0402  | Recursion detected         |
| E0404  | Transition to undefined state |

### Declaration Errors (E05xx)

| Code   | Description                |
|--------|----------------------------|
| E0501  | Duplicate declaration      |
| E0502  | Undefined variable         |
| E0503  | Undefined function         |
| E0504  | Missing start declaration  |
| E0505  | Multiple start declarations|
| E0506  | Function has too many parameters (max 8) |

### Warnings (W01xx)

| Code   | Description                              |
|--------|------------------------------------------|
| W0101  | Expensive multiply/divide operation      |
| W0102  | Loop without break or wait_frame         |
| W0103  | Unused variable                          |
| W0104  | Unreachable code (after return/break/transition, or state unreachable from start) |
| W0105  | Palette sub-palette universal mismatch (mirror collision) |
| W0106  | Implicit drop of non-void function return value |
| W0107  | `fast` variable rarely accessed (wastes a zero-page slot) |
| W0108  | Array elements past byte 255 unreachable via 8-bit X index |
| W0109  | More than 8 literal-coordinate sprites overlap one scanline (NES hardware limit — see `cycle_sprites` and `debug.sprite_overflow()` for runtime mitigations) |
| W0110  | `inline fun` body shape cannot be inlined; falling back to a regular `JSR` call (rewrite as a single-return expression or a void statement sequence, or drop the `inline` keyword) |

`nescript build` prints warnings in addition to errors on a successful
compile, so code-quality hints surface during normal development without
needing a separate `nescript check` pass. Errors still halt the build;
warnings never do.

### Example Error Output

```
error[E0201]: type mismatch
  --> game.ne:42:15
   |
42 |   var x: u8 = -5
   |               ^^ expected u8, found negative integer
   |
   = help: use i8 if you need negative values: var x: i8 = -5
```

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

---

## Command Line

Compile a `.ne` source file into a `.nes` ROM:

```
nescript build game.ne
nescript build game.ne --output my_game.nes
nescript build game.ne --debug
nescript build game.ne --asm-dump
nescript build game.ne --dump-ir
```

| Flag            | Description                                                    |
|-----------------|----------------------------------------------------------------|
| `--output`      | Set output ROM file path (default: input.nes)                  |
| `--debug`       | Enable debug mode with runtime checks                          |
| `--asm-dump`    | Dump generated 6502 assembly to stdout                         |
| `--dump-ir`     | Dump the lowered IR program (after optimization) to stdout     |
| `--memory-map`  | Dump a memory map of variable allocations to stdout            |
| `--call-graph`  | Dump a call graph (which handler/function calls which) to stdout |

### Check

Type-check a source file without producing a ROM:

```
nescript check game.ne
```

---

## Complete Example

A full game demonstrating states, input, functions, constants, and transitions:

```
game "Coin Cavern" {
    mapper: NROM
}

const SPEED: u8 = 2
const SCREEN_RIGHT: u8 = 240
const COIN_X: u8 = 180
const COIN_Y: u8 = 100

var player_x: u8 = 40
var player_y: u8 = 200
var score: u8 = 0
var coins_left: u8 = 3

fun clamp_x(val: u8) -> u8 {
    if val > SCREEN_RIGHT {
        return 0
    }
    return val
}

state Title {
    on frame {
        draw Logo at: (100, 100)
        if button.start {
            transition Playing
        }
    }
}

state Playing {
    on enter {
        player_x = 40
        player_y = 200
        score = 0
        coins_left = 3
    }

    on frame {
        if button.right {
            player_x += SPEED
            if player_x > SCREEN_RIGHT {
                player_x = SCREEN_RIGHT
            }
        }
        if button.left {
            if player_x >= SPEED {
                player_x -= SPEED
            } else {
                player_x = 0
            }
        }

        if player_x >= COIN_X {
            if player_y >= COIN_Y {
                score += 1
                coins_left -= 1
                if coins_left == 0 {
                    transition GameOver
                }
            }
        }

        draw Player at: (player_x, player_y)
        draw Coin at: (COIN_X, COIN_Y)
    }
}

state GameOver {
    on frame {
        draw Trophy at: (120, 100)
        if button.start {
            transition Title
        }
    }
}

start Title
```

Build and run:

```
nescript build coin_cavern.ne
# produces coin_cavern.nes -- open in any NES emulator
```
