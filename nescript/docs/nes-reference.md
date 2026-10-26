# NES Hardware Quick Reference

A concise reference to the NES hardware for NEScript contributors. Understanding these constraints explains many of the compiler's design decisions.

---

## CPU: Ricoh 2A03 (MOS 6502 variant)

- **Clock speed:** 1.79 MHz (NTSC), 1.66 MHz (PAL)
- **Architecture:** 8-bit data bus, 16-bit address bus
- **Registers:**
  - `A` (Accumulator) -- 8-bit, used for arithmetic and logic
  - `X` (Index X) -- 8-bit, used for indexing and counting
  - `Y` (Index Y) -- 8-bit, used for indexing and counting
  - `SP` (Stack Pointer) -- 8-bit, points into the $0100-$01FF range
  - `P` (Status) -- 8-bit flags: N(egative), V(overflow), B(reak), D(ecimal), I(nterrupt), Z(ero), C(arry)
  - `PC` (Program Counter) -- 16-bit
- **No multiply, divide, or floating point instructions**
- **Instruction set:** 56 official opcodes with multiple addressing modes (implied, immediate, zero page, zero page X/Y, absolute, absolute X/Y, indirect, indexed indirect, indirect indexed)

### Why This Matters for NEScript

The 6502's 3-register architecture drives the compiler's register allocator. The lack of multiply/divide means the compiler emits software routines for `*`, `/`, and `%`. Zero-page addressing is 1 byte shorter and 1 cycle faster than absolute addressing, which is why `fast` variable placement matters.

---

## Memory Map

| Address Range     | Size       | Description                        |
|-------------------|------------|-------------------------------------|
| `$0000`-`$00FF`   | 256 bytes  | Zero page -- fast access            |
| `$0100`-`$01FF`   | 256 bytes  | Stack (grows downward)              |
| `$0200`-`$02FF`   | 256 bytes  | OAM shadow buffer (convention)      |
| `$0300`-`$07FF`   | 1280 bytes | General purpose RAM                 |
| `$0800`-`$1FFF`   | --         | Mirrors of $0000-$07FF              |
| `$2000`-`$2007`   | 8 bytes    | PPU registers                       |
| `$2008`-`$3FFF`   | --         | Mirrors of PPU registers            |
| `$4000`-`$4017`   | 24 bytes   | APU and I/O registers               |
| `$4018`-`$401F`   | 8 bytes    | CPU test mode (normally disabled)    |
| `$4020`-`$5FFF`   | --         | Expansion ROM (mapper-dependent)     |
| `$6000`-`$7FFF`   | 8 KB       | SRAM / PRG RAM (if present)          |
| `$8000`-`$BFFF`   | 16 KB      | PRG ROM lower bank                   |
| `$C000`-`$FFFF`   | 16 KB      | PRG ROM upper bank (or fixed bank)   |

### Interrupt Vectors

| Address  | Vector  | Description                              |
|----------|---------|------------------------------------------|
| `$FFFA`  | NMI     | Non-Maskable Interrupt (vertical blank)  |
| `$FFFC`  | RESET   | Power-on / reset entry point             |
| `$FFFE`  | IRQ     | Interrupt Request (mapper-dependent)     |

### NEScript Memory Usage

The compiler reserves the following:
- `$00`-`$0F`: System use (frame counter, input, OAM cursor, SFX/music pointers, mul/div scratch)
- `$10`: `ZP_BANK_CURRENT` (current switchable PRG bank index, only in banked programs)
- `$11`-`$17`: PPU update slots (palette/nametable flags and pending pointers, only when the program declares palette or background blocks)
- `$18`-`$7F`: Available for `fast` variables (user zero-page)
- `$80`-`$FF`: IR codegen temp slots (scratch for expression evaluation)
- `$0200`-`$02FF`: OAM shadow buffer (DMA'd to PPU each frame)
- `$0300`-`$07EE`: General variables, per-function RAM (parameter spill + locals), state-local storage
- `$07EF`: `SPRITE_CYCLE_ADDR` — rotating offset byte used by `cycle_sprites` (only when the program emits a `cycle_sprites` statement)
- `$07F0`-`$07F7`: Audio channel state (noise/triangle/sfx-pitch pointers; only when the program declares a matching sfx)
- `$07FC`: `DEBUG_SPRITE_OVERFLOW_FLAG_ADDR` — per-frame sticky bit (debug builds only)
- `$07FD`: `DEBUG_SPRITE_OVERFLOW_COUNT_ADDR` — cumulative PPU sprite overflow counter (debug builds only)
- `$07FE`: `DEBUG_FRAME_OVERRUN_FLAG_ADDR` — per-frame sticky bit (debug builds only)
- `$07FF`: `DEBUG_FRAME_OVERRUN_ADDR` — cumulative frame overrun counter (debug builds only)

Release-mode programs that don't opt into audio, banking, debug, or
sprite cycling leave the corresponding slots untouched and the
analyzer is free to allocate user globals over them.

---

## PPU (Picture Processing Unit)

- **Resolution:** 256 x 240 pixels
- **Refresh rate:** 60 Hz (NTSC), 50 Hz (PAL)
- **VRAM:** 2 KB internal (2 nametables), expandable by mapper
- **Pattern tables:** 2 tables of 256 tiles each (one for backgrounds, one for sprites), stored in CHR ROM/RAM
- **Tile size:** 8x8 pixels (or 8x16 for tall sprites)
- **Color depth:** 2 bits per pixel (4 colors per tile, selected from a sub-palette)

### Nametables

- 4 logical nametables, each 960 bytes of tile indices + 64 bytes of attribute data
- With 2 KB VRAM, 2 physical nametables exist; the other 2 are mirrors
- Mirroring arrangement (horizontal or vertical) is set by the cartridge/mapper

### Sprites (OAM)

- **64 sprites** total, each defined by 4 bytes:
  - Byte 0: Y position
  - Byte 1: Tile index
  - Byte 2: Attributes (palette, priority, flip H/V)
  - Byte 3: X position
- **8 sprites per scanline** maximum (excess sprites are dropped)
- OAM is 256 bytes, typically shadow-buffered at CPU `$0200` and DMA'd via `$4014`

### Palettes

- **Background:** 4 sub-palettes, each with 4 colors (first color shared across all)
- **Sprite:** 4 sub-palettes, each with 4 colors (first color is transparent)
- Colors are indices into the NES master palette (64 entries, `$00`-`$3F`)
- Palette RAM is 32 bytes total at PPU `$3F00`-`$3F1F`

### PPU Registers

| Address | Name     | Description                          |
|---------|----------|--------------------------------------|
| `$2000` | PPUCTRL  | NMI enable, sprite size, pattern table select, nametable select |
| `$2001` | PPUMASK  | Color emphasis, sprite/background enable, clipping             |
| `$2002` | PPUSTATUS| Vblank flag, sprite 0 hit, sprite overflow                     |
| `$2003` | OAMADDR  | OAM address for writes               |
| `$2004` | OAMDATA  | OAM data read/write                  |
| `$2005` | PPUSCROLL| Scroll position (write twice: X, Y)  |
| `$2006` | PPUADDR  | VRAM address (write twice: high, low)|
| `$2007` | PPUDATA  | VRAM data read/write                 |

### Rendering Timing

- **Vblank** starts at scanline 241 and lasts ~20 scanlines (~2,273 CPU cycles)
- PPU updates (palette, nametable, scroll) must happen during vblank
- `on frame` code runs during the visible frame; the implicit `wait_frame()` yields until the next vblank
- Approximately **29,780 CPU cycles per frame** (NTSC)

---

## APU (Audio Processing Unit)

| Channel   | Type       | Description                        |
|-----------|------------|------------------------------------|
| Pulse 1   | Square wave| Variable duty cycle (12.5/25/50/75%) |
| Pulse 2   | Square wave| Same as Pulse 1                    |
| Triangle  | Triangle   | Fixed volume, good for bass        |
| Noise     | Noise      | Pseudo-random, for percussion      |
| DMC       | Sample     | 1-bit delta-modulated samples      |

APU registers span `$4000`-`$4017`. The audio driver (included automatically when `sfx` or `music` declarations exist) runs during NMI.

---

## iNES ROM Format

The standard ROM file format for NES emulators:

```
Offset  Size     Description
------  -------  -----------
0       4 bytes  Magic number: "NES" followed by $1A
4       1 byte   PRG ROM size in 16 KB units
5       1 byte   CHR ROM size in 8 KB units
6       1 byte   Flags 6: mapper (low nibble), mirroring, battery, trainer
7       1 byte   Flags 7: mapper (high nibble), VS/Playchoice, NES 2.0
8-15    8 bytes  Padding (zeros)
16+     varies   PRG ROM data (N x 16384 bytes)
after   varies   CHR ROM data (N x 8192 bytes)
```

### Common Mapper Numbers

| Number | Name   | PRG ROM      | CHR         | Notes                      |
|--------|--------|-------------|-------------|----------------------------|
| 0      | NROM   | 16/32 KB    | 8 KB ROM    | No bank switching          |
| 1      | MMC1   | Up to 256 KB| Up to 128 KB| Switchable 16 KB PRG banks |
| 2      | UxROM  | Up to 256 KB| 8 KB RAM    | Switchable 16 KB PRG banks |
| 4      | MMC3   | Up to 512 KB| Up to 256 KB| Scanline counter, 8 KB banks|

### Mirroring

- **Horizontal:** nametables A-A-B-B (vertical scrolling games)
- **Vertical:** nametables A-B-A-B (horizontal scrolling games)
- Set in byte 6, bit 0 of the iNES header (0 = horizontal, 1 = vertical)

---

## Controller

Each controller has 8 buttons read as a serial shift register via `$4016` (port 1) and `$4017` (port 2).

Read sequence:
1. Write `$01` then `$00` to `$4016` to strobe (latch button states)
2. Read `$4016` (or `$4017`) 8 times; bit 0 of each read is one button

Button order: A, B, Select, Start, Up, Down, Left, Right.

The NEScript runtime handles this automatically. The programmer reads button state via `button.a`, `button.up`, etc.

---

## Key Constraints for NEScript

| Constraint              | Limit          | NEScript Response                        |
|-------------------------|----------------|------------------------------------------|
| Total RAM               | 2 KB           | Static allocation, no heap               |
| Zero page               | 256 bytes      | `fast`/`slow` hints, compiler promotion  |
| Stack                   | 256 bytes      | Call depth limit, no recursion           |
| Sprites per frame       | 64             | Compiler manages OAM buffer              |
| Sprites per scanline    | 8              | Hardware limit, no workaround            |
| Vblank time             | ~2,273 cycles  | PPU updates must be fast                 |
| Frame budget            | ~29,780 cycles | Frame overrun detection in debug mode    |
| No multiply/divide HW   | --             | Software routines, power-of-2 optimization|

---

## Debugger-assisted workflows

NEScript compiles three debugger-friendly sidecar files that Mesen,
Mesen2, and FCEUX can load alongside the `.nes`. All three are
off by default (release ROMs should be as small as possible) and
enabled per-run via CLI flags:

| Flag                            | Format                           | Consumers       |
|---------------------------------|----------------------------------|-----------------|
| `--symbols <path.mlb>`          | Mesen labels (`P:` / `R:` lines) | Mesen, Mesen2   |
| `--dbg <path.dbg>`              | ca65 debug-info format           | Mesen, Mesen2, FCEUX |
| `--fceux-labels <prefix>`       | `<prefix>.<bank>.nl` + `.ram.nl` | FCEUX           |

### Mesen trace-log

Mesen supports address-based execution tracing via its `log` /
`save-log` scripting APIs. Combined with NEScript's `debug.log`
builtin, the standard workflow is:

1. Build with `--debug` and `--symbols out.mlb`. `debug.log(value)`
   writes `value` to the emulator debug port every time it executes.
2. In the `game { }` block, set `debug_port: mesen` so writes land
   at `$4018` (Mesen's documented tracing port):

   ```
   game "MyGame" {
       mapper: NROM
       debug_port: mesen
   }
   ```

3. In Mesen, enable the trace log (Debug → Trace Logger), load
   the `.mlb`, and filter by memory operation on `$4018`. Each
   `debug.log(x)` call appears in the trace with the source
   function + line resolved from the label table.

For FCEUX on Linux, keep the default `debug_port: fceux` (writes
to `$4800`) and pass `--fceux-labels out` — FCEUX reads
`out.<bank>.nl` automatically when it opens the ROM from the same
directory. FCEUX's conditional-breakpoint syntax can match writes
to `$4800` directly (`A(4800)!=0`) so you can break when any log
fires.
