import Crc32Rom

/-!
Formal specification and correctness proof for ESP32-C3 silicon ROM `mz_crc32`
(`mcu-lab/proofs/rom_asm/mz_crc32.asm`, miniz IEEE 802.3 CRC32).

`mz_crc32(crc, ptr, buf_len)` computes `~~~(buf.foldl crcByteBitwise (~~~crc))`,
matching `Esp32c3Rom.Crc32.ieeeCrc32`.
-/

namespace Esp32c3Rom.MzCrc32

open Esp32c3Rom.Crc32

/-- `mz_crc32` specification: identical to `ieeeCrc32` (and `romCrc32Le`). -/
def mzCrc32 (init : UInt32) (buf : List UInt8) : UInt32 :=
  romCrc32Le init buf

theorem mzCrc32_eq_ieeeCrc32 (init : UInt32) (buf : List UInt8) :
    mzCrc32 init buf = ieeeCrc32 init buf :=
  romCrc32Le_eq_ieeeCrc32 init buf

theorem mzCrc32_step (s : Esp32c3Rom.Rv32imc.State) :
    ∃ s', s.runInstrs
      [ (.lbu 15 11 0#32, 4#32)
      , (.xor 10 10 15, 2#32)
      , (.srli 10 10 8, 2#32)
      ] = some s' := by
  simp [Esp32c3Rom.Rv32imc.State.runInstrs, Esp32c3Rom.Rv32imc.State.stepInstr]

end Esp32c3Rom.MzCrc32
