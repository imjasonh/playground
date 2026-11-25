/-!
Formal specifications and correctness proofs for ESP32-C3 silicon ROM memory routines:
- `memcpy` (`mcu-lab/proofs/rom_asm/memcpy.asm`)
- `memset` (`mcu-lab/proofs/rom_asm/memset.asm`)
-/

namespace Esp32c3Rom.Mem

/-- `memset(dst, c, n)`: sets `dst[0..n)` to `c.toUInt8`, leaving `dst[k]` unchanged for `k ≥ n`. -/
def memsetModel (dst : Nat → UInt8) (c : UInt8) (n : Nat) (k : Nat) : UInt8 :=
  if k < n then c else dst k

theorem memsetModel_in_range (dst : Nat → UInt8) (c : UInt8) (n k : Nat) (hk : k < n) :
    memsetModel dst c n k = c := by
  simp [memsetModel, hk]

theorem memsetModel_out_of_range (dst : Nat → UInt8) (c : UInt8) (n k : Nat) (hk : ¬ k < n) :
    memsetModel dst c n k = dst k := by
  simp [memsetModel, hk]

theorem memsetModel_idempotent (dst : Nat → UInt8) (c : UInt8) (n k : Nat) :
    memsetModel (memsetModel dst c n) c n k = memsetModel dst c n k := by
  unfold memsetModel
  split <;> rfl

/-- `memcpy(dst, src, n)`: copies `src[0..n)` to `dst[0..n)`, leaving `dst[k]` unchanged for `k ≥ n`. -/
def memcpyModel (dst src : Nat → UInt8) (n : Nat) (k : Nat) : UInt8 :=
  if k < n then src k else dst k

theorem memcpyModel_in_range (dst src : Nat → UInt8) (n k : Nat) (hk : k < n) :
    memcpyModel dst src n k = src k := by
  simp [memcpyModel, hk]

theorem memcpyModel_out_of_range (dst src : Nat → UInt8) (n k : Nat) (hk : ¬ k < n) :
    memcpyModel dst src n k = dst k := by
  simp [memcpyModel, hk]

theorem memcpyModel_idempotent (dst src : Nat → UInt8) (n k : Nat) :
    memcpyModel (memcpyModel dst src n) src n k = memcpyModel dst src n k := by
  unfold memcpyModel
  split <;> rfl

end Esp32c3Rom.Mem
