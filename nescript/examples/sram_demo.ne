// SRAM demo — a `save { var ... }` block declares battery-backed
// state in the iNES `$6000-$7FFF` SRAM window. The compiler:
//   * allocates `high_score`, `coins`, and `initials` at $6000+
//     instead of main RAM,
//   * sets the iNES header byte-6 bit-1 (battery flag), and
//   * emits absolute-mode loads/stores that target SRAM directly.
//
// Real cartridge boards persist this region to a `.sav` file; in
// most emulators (FCEUX, Mesen, Nestopia) the file lives next to
// the ROM. SRAM is uninitialized at first power-on, so production
// games should reserve a magic-byte sentinel and validate it
// before trusting the rest of the data — this demo skips the
// validation step for brevity.

game "SRAM Demo" {
    mapper: NROM
}

// Save vars don't take initializers — SRAM is preserved across
// power cycles, so an init expression would either silently
// never run or clobber the player's saved data on every boot.
// Production games guard their save data with a magic-byte
// sentinel: check a known signature on boot and only seed
// defaults if it's missing.
save {
    var high_score: u16
    var coins:      u8
}

var px: u8 = 64

on frame {
    // Bump the in-SRAM coin counter every frame; when it wraps
    // past 256 we treat that as "scored a power-up" and bump
    // the high score.
    coins += 1
    if coins == 0 {
        high_score += 1
    }

    // Move a sprite so the demo has visible output for the
    // emulator golden — frame 180 captures the sprite at
    // x = 64 + 180 (mod 256) = 244.
    px += 1
    draw Ball at: (px, 100)
}

start Main
