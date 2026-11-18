import C3BootProofs.Proofs.Dec384Pow
import C3BootProofs.Proofs.P384PtEnv
import C3BootProofs.Image.BootloaderData

/-!
# P-384 point decompression: the data it reads and the calls it makes

The constants `decompress` reads from the image, and wrappers for its calls
to the field arithmetic, from its frame at `S`.
-/

namespace C3.RV32.Dq

open C3.Image

set_option maxRecDepth 20000

abbrev PARAMS : Word := BitVec.ofNat 32 p384ParamsAddress
abbrev EXPA : Word := BitVec.ofNat 32 p384SqrtExpAddress
abbrev CURVEA : Word := BitVec.ofNat 32 p384CurveAAddress

/-- The constants `decompress` reads, where the image puts them. -/
structure DqData (M : Word → BitVec 8) : Prop where
  params : CodeIn M PARAMS p384ParamsData
  exp : CodeIn M EXPA p384SqrtExpData
  ca : CodeIn M CURVEA p384CurveAData
  cb : CodeIn M p3bA p384BData

/-- The word at byte `o + 4i` of `d`, little-endian. -/
def wordAt (d : List Nat) (o i : Nat) : Word :=
  byteAt d (o + 4 * i + 3) ++ byteAt d (o + 4 * i + 2) ++ byteAt d (o + 4 * i + 1) ++ byteAt d (o + 4 * i)

/-- The `n` words of `d` from byte `o`, as a number. -/
def dataVal (d : List Nat) (o : Nat) : Nat → Nat
  | 0 => 0
  | n + 1 => dataVal d o n + (wordAt d o n).toNat * 2 ^ (32 * n)

theorem code_word {M : Word → BitVec 8} {addr : Word} {d : List Nat} (h : CodeIn M addr d) (o i : Nat)
    (hi : o + 4 * i + 4 ≤ d.length) : memLoad32 M (addr + BitVec.ofNat 32 (o + 4 * i)) = wordAt d o i := by
  rw [ld_ofNat, add_ofNat_assoc, add_ofNat_assoc, add_ofNat_assoc, add_ofNat_assoc, h _ (by omega), h _ (by omega),
    h _ (by omega), h _ (by omega)]
  rfl

theorem code_accV {M : Word → BitVec 8} {addr : Word} {d : List Nat} (h : CodeIn M addr d) (o : Nat) :
    ∀ n, o + 4 * n ≤ d.length → accV M (addr + BitVec.ofNat 32 o) n = dataVal d o n
  | 0, _ => rfl
  | n + 1, hn => by
    rw [accV_succ1, code_accV h o n (by omega), add_ofNat_assoc, code_word h o n (by omega)]; rfl

theorem DqData.of {M M' : Word → BitVec 8} {S : Word} (F : DqFrame S) (D : DqData M)
    (h : ∀ x, Sep (S + 0xFFFFFE60) 0xBF0 x 1 → M' x = M x) : DqData M' := by
  have hd := F.dsep
  have cd : ∀ (b : Word) (d : List Nat), CodeIn M b d → 0x3FCC4200 ≤ b.toNat → b.toNat + d.length ≤ 0x3FCC4E60 →
      CodeIn M' b d := fun b d hc h1 h2 i hi => by
    rw [h _ (hd.subR (c := (b + BitVec.ofNat 32 i).toNat - 0x3FCC4200) (l := 1) (by
      rw [BitVec.toNat_add, BitVec.toNat_ofNat]; omega) |> fun s => by
        rwa [show (0x3FCC4200 : Word) + BitVec.ofNat 32 ((b + BitVec.ofNat 32 i).toNat - 0x3FCC4200) =
          b + BitVec.ofNat 32 i from by
            apply BitVec.eq_of_toNat_eq
            rw [BitVec.toNat_add, BitVec.toNat_ofNat, BitVec.toNat_add, BitVec.toNat_ofNat,
              show (0x3FCC4200 : Word).toNat = 0x3FCC4200 from rfl]
            omega] at s)]
    exact hc i hi
  exact ⟨cd _ _ D.params (by decide) (by decide), cd _ _ D.exp (by decide) (by decide),
    cd _ _ D.ca (by decide) (by decide), cd _ _ D.cb (by decide) (by decide)⟩

theorem DqData.pmod {M : Word → BitVec 8} (D : DqData M) : CodeIn M p3M p384ModulusData := fun i hi => by
  have hb : ∀ i, i < 48 → byteAt p384ParamsData i = byteAt p384ModulusData i := by decide
  rw [show p3M = PARAMS from rfl, D.params i (by have : p384ModulusData.length = 48 := rfl; have : p384ParamsData.length = 156 := rfl; omega),
    hb i (by have : p384ModulusData.length = 48 := rfl; omega)]

set_option exponentiation.threshold 600 in
theorem params_N : dataVal p384ParamsData 0 12 = p384 := by unfold p384; decide

set_option exponentiation.threshold 600 in
theorem params_one : dataVal p384ParamsData 0x30 12 = p3one := by unfold p3one p384; decide

set_option exponentiation.threshold 600 in
theorem params_r2 : dataVal p384ParamsData 0x60 12 < p384 := by unfold p384; decide

theorem params_n0 : wordAt p384ParamsData 0 0 = 0xFFFFFFFF := by decide

set_option exponentiation.threshold 600 in
theorem exp_words : ∀ j, j < 12 → wordAt p384SqrtExpData 0 j = expLimb j := by unfold expLimb sqrtExp p384; decide

theorem DqData.N {M : Word → BitVec 8} (D : DqData M) : accV M PARAMS 12 = p384 := by
  rw [show PARAMS = PARAMS + BitVec.ofNat 32 0 from (add_ofNat_zero _).symm, code_accV D.params 0 12 (by decide), params_N]

theorem DqData.N0 {M : Word → BitVec 8} (D : DqData M) : memLoad32 M PARAMS = 0xFFFFFFFF := by
  rw [show PARAMS = PARAMS + BitVec.ofNat 32 (0 + 4 * 0) from (add_ofNat_zero _).symm, code_word D.params 0 0 (by decide),
    params_n0]

theorem DqData.one {M : Word → BitVec 8} (D : DqData M) : accV M (PARAMS + BitVec.ofNat 32 0x30) 12 = p3one := by
  rw [code_accV D.params 0x30 12 (by decide), params_one]

theorem DqData.r2lt {M : Word → BitVec 8} (D : DqData M) : accV M (PARAMS + BitVec.ofNat 32 0x60) 12 < accV M PARAMS 12 := by
  rw [code_accV D.params 0x60 12 (by decide), D.N]; exact params_r2

theorem DqData.ex {M : Word → BitVec 8} (D : DqData M) (j : Nat) (hj : j < 12) :
    memLoad32 M (EXPA + BitVec.ofNat 32 (0 + 4 * j)) = expLimb j := by
  rw [code_word D.exp 0 j (by have : p384SqrtExpData.length = 48 := rfl; omega), exp_words j hj]

end C3.RV32.Dq
