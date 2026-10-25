// Demonstrates inline assembly with `{var}` substitution.
//
// Mixes NEScript and hand-written 6502 for performance-critical
// sections. Shows the three inline-asm mechanisms:
//
//   1. `asm { ... }` — NEScript-managed, variables resolved by name
//   2. `raw asm { ... }` — unmanaged; passed through verbatim
//   3. `poke(addr, value)` / `peek(addr)` — intrinsic for single
//      memory-mapped-register accesses

game "InlineAsmDemo" { mapper: NROM }

var x: u8 = 0
var y: u8 = 100
var frame_count: u8 = 0

// Fast "multiply by 4" using shifts written directly in assembly.
// The NEScript compiler would strength-reduce `a * 4` to two ASLs
// anyway, but this demonstrates that hand-written asm can reference
// NEScript locals via `{name}` substitution.
fun times_four(input: u8) -> u8 {
    var result: u8 = input
    asm {
        LDA {result}
        ASL A
        ASL A
        STA {result}
    }
    return result
}

on frame {
    // Increment the frame counter via inline asm. The `{frame_count}`
    // placeholder is replaced with the variable's zero-page address
    // by the compiler before the asm parser sees it.
    asm {
        LDA {frame_count}
        CLC
        ADC #$01
        STA {frame_count}
    }

    // Use `poke` to clear the PPU scroll back to (0, 0) every frame.
    poke(0x2005, 0)
    poke(0x2005, 0)

    // Use `times_four` (which itself uses inline asm) to animate the
    // sprite position.
    x = times_four(frame_count)
    draw Smiley at: (x, y)

    wait_frame
}
start Main
