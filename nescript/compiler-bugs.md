// compiler-bugs.md — a running log of compiler issues surfaced
// while implementing the Pong example (examples/pong.ne et al).
//
// Format, one entry per bug:
//
// ## #N — one-line title
//
// **Status**: OPEN / WORKED-AROUND / FIXED
// **Phase**:   lexer / parser / analyzer / ir / optimizer / codegen / linker / runtime / asset
// **Surfaced in**: examples/pong/<file>.ne (brief context)
//
// ### Reproducer
// ```ne
// ... minimal .ne snippet that triggers the bad behaviour ...
// ```
//
// ### Expected vs actual
// What the user-visible behaviour should be; what the compiler actually does.
//
// ### Workaround (if applied)
// The current shape of the code in examples/pong/ that avoids the bug,
// and exactly what should be reverted once the fix lands. Every workaround
// in examples/pong/ MUST be tagged with `// BUG: compiler-bugs.md #N` so
// grep -r "BUG: compiler-bugs.md" finds every reverible workaround in one pass.
//
// ### Guess at the fix
// Which source file(s) and what kind of change is likely needed. Doesn't
// have to be right — it's a hint for the compiler-bug cleanup milestone.
//
// ---

## #1 — `UxROM` and `AxROM` emit CHR ROM, but both are CHR RAM boards

**Status**: OPEN
**Phase**: linker / rom
**Surfaced in**: examples/rampart.ne, reported as "doesn't boot on an
EverDrive"

### Reproducer
```ne
game "Rampart" {
    mapper: UxROM
    mirroring: horizontal
}
```
Build it and read the header: byte 5 is 1, so the image declares an
8 KB CHR **ROM** bank, and the linker appends the tile data there.

### Expected vs actual
Mapper 2 (`UxROM`) and mapper 7 (`AxROM`) are defined as CHR **RAM**
boards: the cartridge has 8 KiB of RAM wired to the PPU bus and no CHR
ROM at all. `docs/language-guide.md` already documents `UxROM` as
"8 KB CHR RAM". A board or flash cart that implements mapper 2 to spec
gives the PPU RAM, the game never uploads tiles into it, and every
pattern table stays empty — a blank or garbage screen. Emulators that
honour the header's CHR ROM bank instead of the mapper's board
definition run it fine, which is why this survived the jsnes goldens.

Re-headering `examples/rampart.nes` as CHR RAM (byte 5 = 0, tile data
dropped) reproduces the blank screen in Mesen.

Affects `examples/rampart.ne`, `examples/uxrom_banked.ne`,
`examples/uxrom_banked_to_banked.ne`, `examples/uxrom_user_banked.ne`,
and `examples/axrom_simple.ne`.

### Workaround (if applied)
None. The examples still ship CHR ROM headers.

### Guess at the fix
Two halves, and the second is the bigger one:

1. `src/rom/mod.rs` — for mappers 2 and 7, declare 0 CHR banks and
   don't append the CHR blob to the image. `validate_ines` should
   reject a mapper 2 or 7 header that claims CHR ROM, the same way it
   now rejects an MMC3 reset vector below `$E000`.
2. `src/runtime/mod.rs` — the reset path has to copy the tile data
   into CHR RAM through `$2006`/`$2007` before enabling rendering,
   which means the blob moves into PRG and needs 8 KB of a PRG bank
   plus an upload loop. For `UxROM` that blob has to live in the fixed
   bank or be paged in deliberately.

Until then, the honest alternative is to reject `UxROM` and `AxROM`
with a diagnostic rather than emit an image that only runs on lenient
emulators.

---
