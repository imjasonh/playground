# Future Work

This document tracks the gaps between what NEScript currently compiles and
what the spec describes. Items are grouped by area. Anything implemented and
tested is omitted — `git log` is the authoritative record of what shipped.

---

## PNG-sourced assets

**What ships today.** `palette Name { colors: [...] }` and
`background Name { tiles: [...], attributes: [...] }` declarations with
inline byte arrays, plus `palette Name @palette("file.png")` and
`background Name @nametable("file.png")` for PNG-sourced variants.
The palette path maps each pixel to its nearest NES master-palette index
(via `nearest_nes_color()` in `src/assets/palette.rs`), deduplicates, and
emits the 32-byte blob; the nametable path slices a 256×240 PNG into the
32×30 tile grid, deduplicates (max 256 unique tiles), and emits the 960+64
byte nametable/attribute blobs. The nametable path now **also auto-generates
the per-tile CHR data** via `png_to_nametable_with_chr` and slots it into
CHR ROM after the user's sprite tile range — see
`examples/auto_chr_background.ne` for the end-to-end flow.
`--memory-map` reports per-blob PRG ROM addresses and a running total
alongside the variable layout.

**Still TODO.**
- **Per-state background rendering control** — programs currently load a
  single nametable at reset. Per-state swaps work but are limited by the
  NMI-time write budget (~2273 cycles, enough for a palette but not a
  full 1024-byte nametable).
- **Per-quadrant palette selection from PNG sources** — the
  `png_to_nametable_with_chr` attribute path picks sub-palettes based on
  brightness buckets, which is fine for grayscale demos but doesn't let
  the user say "this 32×32 tile uses sub-palette 2". A separate
  `palette_map:` shortcut exists for inline backgrounds; the PNG path
  could grow a sibling `@palette_map("hint.png")` that overrides the
  brightness buckets.

---

## User code distribution across switchable banks

**What ships today.** `bank Foo { fun bar() { ... } }` nesting places user
functions into a specific switchable bank. The codegen emits per-bank
instruction streams; the linker runs a two-pass assembly (discover labels
per-bank, then resolve with the merged label table) so banked code can
still reference fixed-bank symbols. Cross-bank calls — both fixed → banked
*and* banked → banked — are rewritten to `JSR __tramp_<name>`, where each
trampoline is a per-function stub in the fixed bank that reads the
caller's current bank from `ZP_BANK_CURRENT`, pushes it on the hardware
stack, switches to the target, JSRs the entry, then pulls and restores
the caller's bank. `gen_mapper_init` seeds `ZP_BANK_CURRENT` with the
fixed bank index at reset so the first cross-bank call from the fixed
bank still leaves the fixed bank mapped at $8000. See
`examples/uxrom_user_banked.ne` (fixed → banked) and
`examples/uxrom_banked_to_banked.ne` (banked → banked).

**Still TODO.**
- **Greedy size-packing.** Placement is explicit-only today — there is no
  pass that takes a program with too much fixed-bank code and
  automatically spills the biggest leaf functions to declared empty banks.
- **MMC3 per-state-handler split** — the `mmc3_per_state_split.ne`
  example still uses the legacy fixed-bank placement for its handlers.
  Extending the banked-fun syntax to state handlers (plus trampoline
  emission on handler dispatch) would unify the two paths. The blocker
  isn't the trampoline — those work for any caller now — but the
  state-handler dispatcher in the IR codegen needs to learn that
  state handlers can live in a switchable bank, and to JSR through a
  trampoline whose entry is the handler label.

---

## Language feature gaps (post-v0.1)

From the spec's "Reserved for Future Versions" section:

| Feature            | Description                                                           |
|--------------------|-----------------------------------------------------------------------|
| **Fixed-point**    | `fixed8.8` type for sub-pixel movement with operator support.         |
| **Text / HUD**     | Font sheet declarations + layout system for scores, health, menus.   |
| **Tilemaps**       | Declarative level data with built-in collision queries.              |
| **SRAM / saves**   | Persistent storage declarations for battery-backed save data.        |

NES 2.0 headers are now supported via `game Foo { header: nes2 }` — see
`src/rom/mod.rs`.

**Metasprites** are now supported via `metasprite Name { sprite: ...,
dx: [...], dy: [...], frame: [...] }` — see `examples/metasprite_demo.ne`.
The IR lowering expands `draw Hero at: (x, y)` into one `DrawSprite` op
per tile, with each tile's frame index offset by the underlying sprite's
base tile so the codegen sees a stream of regular draws and the OAM
cursor allocator picks them up unchanged. Negative offsets and
runtime-varying tile selection are still TODO — the current form takes
literal `u8` offsets.

### Struct / array field widths

Nested struct fields (`hero.pos.x`) and array struct fields
(`hero.inv[i]`) now compile end-to-end. The analyzer recursively
flattens the struct layout into per-leaf synthetic variables (with
intermediate `Struct(...)` symbols for the dotted prefixes), and the
parser loops the dotted chain in `parse_primary` and
`parse_assign_or_call` so the existing `format!("{name}.{field}")`
synthetic-name model still works without IR changes. Array-of-structs
is still rejected with E0201 — the synthetic-variable model can't
index per-element struct layouts without further codegen work, see
`src/analyzer/mod.rs::register_struct`.

---

## Audio pipeline

**What ships today.** Frame-walking pulse driver with `sfx Name { duty, pitch,
volume }` and `music Name { duty, volume, repeat, notes }` blocks; builtin
effects and tracks; a 60-entry period table; `__audio_used` marker that
elides the whole subsystem when no program statement references it. **Plus**
`channel: triangle` and `channel: noise` on `sfx` blocks, which splice in
per-channel slots that write to $4008-$400B (triangle) or $400C-$400F
(noise) when a program declares them. **Plus per-frame pitch envelopes
on Pulse-1 sfx** — a `pitch:` array with more than one distinct value
opts into a separate `__sfx_pitch_<name>` blob that the audio tick walks
in lockstep with the volume envelope, writing `$4002` on every NMI for a
real frequency-sweeping pulse channel. Pulse-only programs without
varying-pitch sfx still produce byte-identical driver code. See
`examples/noise_triangle_sfx.ne` and `examples/sfx_pitch_envelope.ne`.

**Still TODO for richer audio.**
- **DMC channel** — delta-modulation sample playback is not wired yet.
- **Multi-channel tracker playback** — one `notes` list per channel on
  `music` blocks (the triangle/noise SFX are one-shot envelopes, not a
  tracker).
- **`@sfx("file.nsf")` / `@music("file.ftm")`** — neither the NSF nor the
  FamiTracker format is parsed yet.
- **Per-frame pitch envelopes on triangle / noise sfx** — the data
  shape (a parallel pitch array on the `sfx` block) is the same as for
  Pulse-1, but the runtime triangle/noise tick blocks currently only
  write their volume registers (`$4008` / `$400C`). Extending them to
  also walk a per-channel pitch envelope and write `$400A` / `$400E`
  is the natural next step now that the pulse path is proven.

---

## Debug instrumentation

**What ships today.** `debug.log(...)` and `debug.assert(...)` lower to $4800
writes when `--debug` is passed, and are stripped entirely in release builds.
`--symbols <path>` writes a Mesen-compatible `.mlb` file listing function,
state-handler, and variable addresses (with PRG ROM offsets for code and
CPU addresses for RAM). `--source-map <path>` consumes the `SourceLoc` IR
op and writes a plain-text map of `<rom_offset> <file_id> <line> <col>`
entries for every lowered statement. **`--dbg <path>` writes a
ca65-compatible `.dbg` debug-info file** that Mesen / Mesen2 / fceuX pick
up automatically for source-level stepping, labelled variable inspection,
and symbol-based breakpoints. The file stitches together the linker's
label table, the `__src_<N>` IR markers, and the analyzer's variable
allocations into the `file`/`mod`/`seg`/`scope`/`span`/`line`/`sym`
records documented at
<https://cc65.github.io/doc/debugfile.html>. `ooffs` on the segment
record tracks the fixed bank's PRG-relative start, so banked ROMs
(MMC1/UxROM/MMC3) also map cleanly inside the debugger. Debug builds emit array bounds checks
(CMP against size, BCC past a `JMP __debug_halt` wedge) and bump an
overrun counter at `$07FF` in the NMI handler when the main loop didn't
reach `wait_frame` before the next vblank.

**Plus four query expressions** that mirror the counter/sticky pattern:
`debug.frame_overrun_count()` / `debug.frame_overran()` return the cumulative
overrun counter and a per-frame sticky bit so user code can write
`debug.assert(not debug.frame_overran())` guards, and
`debug.sprite_overflow_count()` / `debug.sprite_overflow()` do the same for
the NES PPU's sprite-per-scanline flag (`$2002` bit 5), which the NMI
handler samples once per frame in debug mode. All four sticky bits clear
on the next `wait_frame`.

**Still TODO.**
- **`debug.overlay(x, y, text)`** — needs the text/HUD subsystem (see
  Language feature gaps).

---

## Code quality / tooling

### Register allocator

IR temps still spill to a recycled zero-page slot (`$80-$FF`). Most of
the obvious waste is now handled:

- The `remove_dead_loads` peephole pass steps past opcodes that touch
  neither A nor the flags A cares about — INC/DEC/STX/STY/LDX/LDY in
  memory mode, INX/INY/DEX/DEY, and the flag ops
  (CLC/SEC/CLI/SEI/CLD/SED/CLV). That lets a later `LDA` overwrite
  kill a redundant earlier `LDA` even when an index-register load or
  counter bump sits between them. The canonical
  `LDA #imm / LDY oam_cursor / LDA #imm / STA $0200,Y` shape emitted
  by every single-tile `draw` collapses to just
  `LDY oam_cursor / LDA #imm / STA $0200,Y`, saving 2 bytes per draw.
  Across the committed examples this shaved 4-9 % of the LDA count
  in the larger programs (platformer, war, pong).
- Copy propagation + dead-store elimination in the same pass handle
  the `STA $80 / … / LDA $80` spill/reload pattern whenever the
  source and destination aren't separated by a JSR or a label.

**Constraint worth recording.** Any cycle-saving optimization shifts
audio timing: the SFX/music driver reads a frame counter on every NMI,
and shortening the main-loop pass between two `wait_frame` calls
changes how many poll iterations complete before the next NMI fires.
The emulator harness captures a sample-exact audio hash at frame 180,
so any such change flips the audio goldens for every audio-emitting
example (audio_demo, friendly_assets, noise_triangle_sfx, platformer,
pong, war). The visual PNG goldens stay stable — PPU writes still
land in the same vblank — but the audio churn is real and has to be
accepted on every pass that touches the codegen. The initial LDX/LDY
extension on this branch went through that re-baseline once; future
passes will too.

**Remaining wins to chase** if someone wants to push density further:

- **Cross-block A-tracking.** `remove_redundant_loads` clears its
  A-equivalence tracker on LDX/LDY because LDX/LDY clobber the N/Z
  flags that an immediately-following branch might rely on. Splitting
  the tracker into "value still valid" vs "flags still valid" lets it
  keep the value-side equivalence across LDX/LDY for downstream STA
  rewrites.
- **CFG-aware allocation into X / Y.** The codegen never picks X or Y
  as a temp slot today; they're used only in the specific shapes the
  existing IR ops emit. A pass that takes a temp with ≤2 uses, lives
  in a straight-line block, and picks X or Y would remove both the
  STA and the matching LDA.
- **Skipping the spill for temps consumed by the very next op.** The
  IR codegen always emits `STA slot` after producing a temp; when the
  next op's first source is that temp, the value could stay in A and
  the consumer skips its `LDA`. The peephole's `remove_sta_then_lda`
  + `remove_dead_temp_stores` already pick up most cases post-hoc,
  but producing tighter code at codegen avoids the overhead and
  handles cases where an intervening label blocks the peephole.

### State-local memory overlay follow-ups

State-local variables are now overlaid across mutually-exclusive states
(see the analyzer's per-state allocation cursor rewind and the IR
lowerer's `on_enter` initializer prologue), but a few pieces are still
missing:

- **Same-named locals across different states.** `register_var` stores
  state-locals under their bare name, so two states each declaring
  `var timer: u8` collide with E0501. A per-state symbol-table scope
  prefix would let each state carve its own namespace while keeping
  the overlay.
- **Struct-literal and array-literal initializers on state-locals.**
  The on-enter prologue lowers scalar initializers cleanly, and
  struct-literal initializers fall back to per-field stores, but
  array-literal initializers (`var xs: u8[4] = [1,2,3,4]`) are
  skipped. A runtime `memcpy` from a ROM blob into the overlay
  slot (mirroring the reset-time global path) is the natural
  lowering.
- **Handler-local overlay.** Handler-local `var`s declared inside
  `on_frame { ... }` are already per-handler scoped via
  `current_scope_prefix`, but they get a dedicated RAM slot for the
  program's lifetime. Overlaying them inside each handler's stack
  frame — using a per-handler bump allocator that resets on each
  call — would shave a few bytes more on programs with many deep
  handlers.

### Cross-block temp live-range analysis

The slot recycler is function-local per-block. Temps that flow across block
boundaries get a dedicated slot for the entire function, even if a later
block could reuse the slot.

### WASM build target

To build a browser IDE we would need to route file I/O through a trait so the
core pipeline works on `&str → Vec<u8>` without touching `std::fs`. Today the
parser's preprocess pass and the asset resolver read files directly.

---

## Error message polish

### Unused error codes

`ErrorCode` only defines codes that are actually emitted. Previously there
were placeholder variants (`E0202` invalid cast, `E0403` unreachable state)
marked `#[allow(dead_code)]`; those were removed during cleanup. If those
semantics come back, add the codes at that point.

---

## cc65/nesdoug parity gaps

The nesdoug tutorial series + neslib expose a broad surface that
NEScript can't currently express. This section enumerates the gaps
in the order they should probably be tackled (cheapest/highest-
leverage first). Anything we finish moves out of this section and
into the top of the file with a "ships today" note.

### A. Numeric types beyond `u8 / i8 / u16 / i16 / bool`

`i16` ships today; see `examples/i16_demo.ne` and `examples/signed_compare.ne`.
Signed ordering comparisons and narrow-to-wide sign-extension both ship
too — `Cmp{Lt,Gt,LtEq,GtEq}` and their 16-bit siblings carry a
`Signedness` field that drives the canonical `CMP / SBC / BVC / EOR #$80`
overflow-correction idiom in `gen_cmp_signed_set_n`, and `widen()` emits
`IrOp::SignExtend` for signed narrow values instead of the zero-extended
`LoadImm 0` it used to. Casts to `u8`/`u16` strip the signed flag so
explicit `as` opt-outs stay unsigned.

Lower-priority numeric follow-up:

- **`u32` / `i32`.** Realistically needed only for score totals and
  frame counters. A synthesizable pair of 16-bit halves is usually
  enough.

### B. Pointers & function pointers

NEScript has no pointer type. This blocks indirect-dispatch
tables (`jmp (vec,x)`), variable-size buffer manipulation, and
passing "which thing" to a helper. cc65's `__fastcall__` function
pointers via wrapped-call + bank IDs are load-bearing for every
game over 32 KB. Design sketch:

- Introduce `*T` / `fn(T) -> U` type grammar.
- Spell a new IR op `CallIndirect` that takes an address in a
  16-bit temp, plus a `BankHint` so cross-bank pointers trampoline
  automatically.
- For fixed-bank-only code we can lower to a raw `JSR ($vec)`
  equivalent (`JMP ($vec)` + return stub).

### C. Bitfields and unions

OAM attribute bytes, controller masks, collision-flag words, and
MMC3 register bits all want bitfield syntax (`struct OamAttr { pal:
u2, priority: u1, flip_h: u1, flip_v: u1 }`). Unions show up less
often but are useful for reading/writing the same bytes as two
different shapes (e.g. a 16-bit counter viewed as `lo: u8, hi: u8`).

### D. Full inline-assembly escape hatch

`.label:` ships today — the codegen mangles dot-labels into per-block
unique names (`__ilab_<N>_label`) so two inline-asm blocks in the
same function can both use `.loop:` without colliding. See
`tests/integration_test.rs::inline_asm_dot_labels_are_per_block_unique`.

Still TODO:

- Accept cc65's `asm()` format specifiers — `%b` (byte), `%w`
  (word), `%l` (long), `%v` (var), `%o` (offset), `%g` (global),
  `%s` (string) — so users can splat a compiler-allocated symbol
  into a hot-loop fragment.
- Extend the directive allow-list: `.byte`, `.word`, `.res`,
  `.repeat / .endrep`, `.macro / .endmacro`. The assembler can
  already encode these.

### E. Dense-`match` jump tables

`match u8 { 0 => ..., 1 => ..., ... }` desugars to an if/else
chain at parse time today, which is `O(n)` compares. For dense
(<= 256 entries with <= 4× spread) integer matches, lower to:

```
ASL A           ; index *= 2
TAX
LDA table_lo,X
STA $00
LDA table_hi,X
STA $01
JMP ($0000)
```

…with a per-branch `.word` table emitted in the function prologue.
This matters most for state dispatch and attack/weapon tables.

### F. Recursion stance (design constraint, not a bug)

The analyzer rejects recursive calls with E0402. That's the right
call for a compiler targeting a 6502 hardware stack, but it's not
documented as a **design choice** anywhere. Add a paragraph to the
language guide explaining why, plus a pointer to the hand-rolled
explicit-stack pattern (small `u8[N]` stack + `u8` top).

### G. VRAM update buffer follow-ups

`nt_set(x, y, tile)`, `nt_attr(x, y, value)`, and
`nt_fill_h(x, y, len, tile)` ship today — see
`examples/vram_buffer_demo.ne` (minimal drain test) and
`examples/hud_demo.ne` (realistic score/lives HUD with
shadow-compare writes and one-shot attribute paint). The runtime
ring lives at `$0400-$04FF` (gated on the `__vram_buf_used`
marker; the analyzer bumps the user-RAM bump pointer to `$0500`
when the buffer is in use). Each append lays down
`[len][addr_hi][addr_lo][data…]` and writes a fresh `0` sentinel;
the NMI drains the buffer at vblank via `LDA $0400,X / STA
$2007` indexed-absolute (4 cycles per data byte, no ZP cost),
then resets `$2006`/`$2005` to zero so the PPU's scroll latch is
clean for the next frame (otherwise trailing `$2006` writes shift
the rendered image by however many cells we wrote past `$2000`).

Still TODO:

- **Vertical (column) writes** — `nt_write_v(x, y, ...)` would set
  `$2000` bit 2 (auto-increment 32) before the data writes and
  clear it after. Useful for tilemap-driven scrolling.
- **Variable-length writes from a u8 array global** — today
  `nt_fill_h` repeats one tile; a `nt_copy_h(x, y, src_var, len)`
  variant that copies from a declared `u8[N]` global removes the
  fill-only restriction.
- **Buffer-overflow detection** — the runtime drain assumes the
  256-byte buffer never overflows. A debug-mode check that traps
  when `head` would advance past `$04FF` would catch the worst
  failure mode (writes wrapping into adjacent RAM).

### H. Metatiles + collision as a first-class construct

`metatileset Name { metatiles: [...] }` and `room Name { metatileset:
..., layout: [...] }` ship today — see `examples/metatiles_demo.ne`.
Each metatile bundles four CHR tile indices (TL / TR / BL / BR) plus
a `collide: true|false` flag; rooms lay them out as a 16×15 grid
that the compiler expands at compile time into a 32×30 nametable,
a 64-byte attribute table, and a 240-byte collision bitmap. All
three blobs land as PRG ROM data blocks with per-room labels
(`__room_tiles_N`, `__room_attrs_N`, `__room_col_N`).

`paint_room Name` reuses the existing `load_background` vblank-safe
update machinery against the room's tile/attribute blobs, and
additionally installs the room's collision bitmap pointer into
`ZP_ROOM_COL_LO` / `ZP_ROOM_COL_HI` (ZP `$18`/`$19`).
`collides_at(x: u8, y: u8) -> bool` JSRs into a small runtime
helper that reads `(room_col),Y` where `Y = (y & 0xF0) | (x >> 4)`
and returns the 0/1 bit directly. The helper is gated on a
`__collides_at_used` marker, so a program that declares a room but
never queries it pays zero bytes for the subroutine.

**Still TODO.**

- **NEXXT file import (`@room("file.nxt")`).** Today only inline
  `layout: [...]` (or `[value; count]` for repeated fills) is
  supported. The NEXXT exporter's `.nxt` format would let users
  author rooms in a dedicated editor.
- **Per-quadrant palette hints.** The generated attribute table
  is currently all zeros (sub-palette 0 for every quadrant). A
  `palette: 0..3` field on each metatile entry could drive the
  attribute table expansion.
- **`collides_at` against u16 coordinates.** The intrinsic takes
  u8 x/y today, which covers the full 256×240 visible area but
  can't address scrolling playfields bigger than one nametable.
- **Multi-room streaming.** The ZP pointer model already supports
  multiple rooms (each `paint_room` rewrites the collision
  pointer), but the nametable blit still uses the
  nametable-0-only `load_background` path. Streaming into a VRAM
  update buffer would let rooms swap without the vblank-budget
  risk.

### I. RLE + LZ4 nametable decompression

`vram_unrle` and `vram_unlz4` — for scrolling/multi-room games,
packing rooms is mandatory. cc65 ships both in neslib with
concrete timing (0.5f RLE vs 2.8f LZ4). The per-state background
swapping item in "What ships today" is exactly this problem:
without a decompressor that can stream into the VRAM buffer, the
NMI-time write budget (~2273 cycles) is too tight for a full
nametable. RLE is the smaller first step — emit a `nametable` that
can declare `compression: rle` and decompress at swap time.

### J. Palette-fade brightness LUT follow-up

`set_palette_brightness(level: u8)` and the blocking
`fade_out(step_frames)` / `fade_in(step_frames)` builtins all ship
today — see `examples/palette_brightness_demo.ne` and
`examples/fade_demo.ne`. One follow-up still worth doing: a
brightness-LUT path that recolours the active palette in addition
to the emphasis bits, for non-NTSC-assumption fades. The current
implementation only manipulates `$2001` emphasis bits, so the
"dimmed" end of the fade still shows colour tint rather than a
true colour-space darken.

### M. Sprite cycling follow-ups

Auto sprite cycling ships today via `game { sprite_flicker: true }`
— the IR lowerer injects an `IrOp::CycleSprites` at the top of
every `on frame` handler when the flag is set. See
`examples/auto_sprite_flicker.ne`. A companion `draw ... priority:
pinned` modifier for HUD sprites that must stay at low OAM slots
is still missing — today pinning has to be manual (draw the HUD
sprites first).

### O. DPCM / DMC sample playback

Already listed under Audio Pipeline. FamiStudio's DMC support
(including bankswitched DMC) is the reference API shape — import
`@dpcm("file.dmc")` into a named sample slot and expose
`play_dpcm(Slot, pitch: u8, loop: bool)`.

### P. Expansion audio (VRC6, MMC5, FDS, N163, S5B, VRC7)

FamiStudio has a single export path with `FAMISTUDIO_CFG_EXTERNAL`
and per-chip feature flags. If/when we import a FamiStudio-export
format (see Q), the expansion chips come along almost for free
— the runtime just has to wire up the extra write ports and the
mapper has to expose them (MMC5 for the extra pulse channels,
VRC6/VRC7 via their own mappers).

### Q. FamiStudio text-export import

`@music("file.famistudio.txt")`. FamiStudio's text export is the
pragmatic ingestion path; parsing it gives full tracker semantics
(volume/pitch slides, arpeggios, vibrato, release notes) without
reinventing the engine. FamiTracker's binary `.ftm` is a worse
target — undocumented, version-skewed.

### R. NEXXT metatile/collision import

NEXXT is the dominant asset editor in the nesdoug workflow; it
emits metatile tables + collision maps as ca65-compatible
assembler source. An `@metatiles("room.nxt")` loader (and
`@room("level1.nxt")` for layouts — see §H) removes a whole class
of hand-typed tile arrays.

### S. SRAM / battery-backed saves follow-ups

`save { var ... }` ships today — see `examples/sram_demo.ne`. The
analyzer allocates save vars from a separate `$6000+` bump pointer,
the linker flips iNES byte-6 bit-1, and `W0111` warns when a save
var carries an initializer (SRAM is preserved across power cycles
so initializers would either silently not run or clobber the
player's data on every boot). Two follow-ups are still worth doing:

- **First-power-on detection** — an `on first_boot { ... }` handler
  that runs once when a magic-byte sentinel is missing. Today users
  have to roll the sentinel check by hand.
- **Struct fields in save blocks** — currently rejected because the
  field-flattening path uses the main-RAM allocator. Routing it
  through the SRAM allocator instead is a few lines of analyzer
  refactor.

### T. PAL/NTSC region abstraction

Neslib exposes `ppu_wait_frame` as a virtual-50Hz wait on PAL. Add
a `region: ntsc | pal | dual` field on the `game { }` block. For
`dual`, the runtime probes `$2002` bit 7 timing at reset and sets a
ZP flag; the audio engine's frame tick and any frame-counted timing
respects the flag.

### U. Additional controller types

Expose Zapper (light-gun) and Power Pad via typed inputs:

```
input gun: zapper on port: 1
input mat: power_pad on port: 2
```

`gun.trigger`, `gun.light_detected`, `mat.button(i: u8)` are the
three reads every program needs.

### V. Additional mappers

AxROM (mapper 7), CNROM (mapper 3), and GNROM (mapper 66) all
ship today; see `examples/axrom_simple.ne`, `examples/cnrom_simple.ne`,
and `examples/gnrom_simple.ne`. CNROM and GNROM both have CHR
bankswitching but user-visible CHR swaps aren't reachable from
user source yet — the reset-time init writes bank 0 and the
`__bank_select` routine exists but has no user-exposed API. The
next set:

1. **MMC2** (mapper 9, Punch-Out only realistically). Medium.
2. **UNROM-512** (mapper 30). The modern homebrew sweet spot —
   512 KB PRG + CHR-RAM + self-flashing. Mapping is UxROM-like
   plus a one-screen bit.
3. **MMC5** (mapper 5). Big. Driven by FamiStudio's expansion
   audio more than by the extra PRG/CHR modes. Probably last.

Each new mapper needs a `Mapper::X` variant, a reset-time
`gen_xrom_init()` in the runtime, bank-select support in
`gen_bank_select()`, and an iNES mapper number in `rom::mapper_number`.
The PR checklist ("example + behaviour test + negative test") is
still the bar for each of these.

### W. NSF output target

The audio engine is already a standalone subsystem. An NSF-output
target (`--target nsf`) would wrap the existing music/sfx blocks
in the NSF header and expose `init`/`play` entry points. Nearly
free, gets the chiptune audience for ~a day of work.

### X. Mesen trace-log documentation follow-up

`game { debug_port: fceux | mesen | 0xXXXX }` ships today — see
the integration test `debug_log_targets_configured_port`. Mesen's
trace-log tool invocation still isn't documented anywhere in the
NEScript docs; a short section under `docs/nes-reference.md`
walking through how to hook a Mesen trace-log against a ROM built
with `debug_port: mesen` would close the gap.

### Y. FCEUX `.ld` line-info follow-up

`--fceux-labels <prefix>` ships today and emits
`<prefix>.<bank-index>.nl` + `<prefix>.ram.nl`. FCEUX also reads a
`.ld` line-info file for source-level stepping; wiring that up
against the existing source-map data would close the loop without
much code.

### Z. Explicit bank-placement hints on functions and data

`bank Foo { fun bar() }` already exists; extend the sugar to
attributes on individual items so users don't have to restructure
their source:

```
@bank(3) fun slow_helper() { ... }
@bank(3) const LEVEL_DATA: u8[1024] = [...]
```

This is particularly useful for `const` data, which today lands
wherever the analyzer decides; users sometimes need to pin data
to a specific bank to avoid bank-switch cost on a hot path.

### Priority ranking

Remaining gap items in order of user value:

1. Register allocator (existing section) — compounding size win,
   but with the audio-goldens caveat spelled out in that section.
2. NEXXT `@room(...)` import + per-quadrant palette hints
   (§H follow-ups) — most impactful extensions on top of the
   shipped metatiles base.
3. Inline-asm format specifiers + directive list (§D follow-ups).
4. VRAM buffer follow-ups (§G) — vertical writes, array copy,
   overflow detection.
5. Arrays-of-structs + bitfields (§C) + fn pointers (§B) —
   turns NEScript into a general-purpose NES language.
6. UNROM-512 + MMC5 (§V) — ecosystem fit.
7. FamiStudio import (§Q) + DPCM (§O) + expansion audio (§P).

---

## Open design questions

1. **Inline asm label syntax.** `.label:` (ca65 style) vs `label:` (generic)?
   Today the inline-asm parser accepts `label:` but not `.label`; migrating
   would be cheap but would invalidate any copy-pasted ca65 fragments.
2. **Debug port address.** $4800 is conventional but not universal. Should
   we support multiple debug output methods?
3. **Pinned OAM slots for HUD sprites.** Automatic sprite cycling is
   decided — both the manual `cycle_sprites` keyword and the
   `game { sprite_flicker: true }` attribute ship today (see §M).
   Open question: should we add a `draw ... priority: pinned`
   modifier that opts a specific sprite out of the rotation so HUD
   elements stay at low OAM slots?
4. **Error recovery granularity.** How aggressively should the parser
   recover? More recovery means more errors per compile but also risks
   cascading false errors.
