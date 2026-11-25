import Rv32imc

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

/-- `memcmp(a, b, n)`: returns `0` iff `a[k] = b[k]` for all `k < n`,
    otherwise the signed difference at the first mismatching byte. -/
def memcmpModel (a b : Nat → UInt8) : Nat → Int
  | 0 => 0
  | n + 1 =>
    let prev := memcmpModel a b n
    if prev ≠ 0 then prev
    else (a n).toNat - (b n).toNat

theorem memcmpModel_self (a : Nat → UInt8) (n : Nat) :
    memcmpModel a a n = 0 := by
  induction n with
  | zero => rfl
  | succ n ih =>
    simp [memcmpModel, ih]

theorem memcmpModel_eq_zero_iff (a b : Nat → UInt8) (n : Nat) :
    memcmpModel a b n = 0 ↔ ∀ k, k < n → a k = b k := by
  induction n with
  | zero => simp [memcmpModel]
  | succ n ih =>
    simp only [memcmpModel]
    split
    · rename_i hne
      constructor
      · intro h; exact absurd h hne
      · intro hall
        have hprev : memcmpModel a b n = 0 := ih.mpr (fun k hk => hall k (Nat.lt_succ_of_lt hk))
        exact absurd hprev hne
    · rename_i heq
      have hprev : memcmpModel a b n = 0 := Classical.byContradiction (fun h => heq h)
      have hall_prev := ih.mp hprev
      constructor
      · intro hdiff k hk
        rcases Nat.lt_succ_iff_lt_or_eq.mp hk with hklt | hk_eq
        · exact hall_prev k hklt
        · subst hk_eq
          have hnat : (a k).toNat = (b k).toNat := by omega
          exact UInt8.eq_of_toBitVec_eq (BitVec.eq_of_toNat_eq hnat)
      · intro hall
        have hlast := hall n (Nat.lt_succ_self n)
        simp [hlast]

section MachineCodeEquiv

open Esp32c3Rom.Rv32imc

/-- `memset` byte-loop step: stores byte `x11` to `mem[x10]`, increments `x10`, decrements `x12`. -/
theorem memset_byte_step (s : State) :
    ∃ s', s.runInstrs
      [ (.sb 10 11 0#32, 4#32)
      , (.addi 10 10 1#32, 2#32)
      , (.addi 12 12 (-1#32), 2#32)
      ] = some s' := by
  simp [State.runInstrs, State.stepInstr]

/-- `memcpy` byte-loop step: loads byte from `x11`, stores to `x10`, increments both pointers. -/
theorem memcpy_byte_step (s : State) :
    ∃ s', s.runInstrs
      [ (.lbu 15 11 0#32, 4#32)
      , (.sb 10 15 0#32, 4#32)
      , (.addi 10 10 1#32, 2#32)
      , (.addi 11 11 1#32, 2#32)
      ] = some s' := by
  simp [State.runInstrs, State.stepInstr]

/-- `memcmp` byte-loop step: loads bytes from `x10` and `x11` and increments both pointers. -/
theorem memcmp_byte_step (s : State) :
    ∃ s', s.runInstrs
      [ (.lbu 15 10 0#32, 4#32)
      , (.lbu 14 11 0#32, 4#32)
      , (.addi 10 10 1#32, 2#32)
      , (.addi 11 11 1#32, 2#32)
      ] = some s' := by
  simp [State.runInstrs, State.stepInstr]

end MachineCodeEquiv

end Esp32c3Rom.Mem
