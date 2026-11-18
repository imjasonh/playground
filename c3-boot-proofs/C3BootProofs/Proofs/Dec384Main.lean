import C3BootProofs.Proofs.Dec384Pre
import C3BootProofs.Proofs.Dec384Calls

/-!
# P-384 point decompression

`<primeorder::affine::AffinePoint<NistP384> as DecompressPoint>::decompress`
from its entry to its return.
-/

namespace C3.RV32.Dq

open C3.Image

set_option maxRecDepth 20000

set_option exponentiation.threshold 600 in
theorem r2_mont : dataVal p384ParamsData 0x60 12 * p3RInv % p384 = 2 ^ 384 % p384 := by unfold p384 p3RInv; decide

/-- `from_repr`'s congruence pins its result: `x` in Montgomery form. -/
theorem frp_val {X x : Nat} (hX : X < p384) (h : X * 2 ^ 384 % p384 = x * dataVal p384ParamsData 0x60 12 % p384) :
    X = x * 2 ^ 384 % p384 := by
  rw [p3_mont hX h]; unfold p3fm
  rw [Nat.mul_assoc, Nat.mul_mod, r2_mont, ← Nat.mul_mod]

def dqA1 : List BInstr :=
  [.aluImm .add sp sp 0xFFFFF810, .aluImm .add a3 sp 0x780, .sw a3 ra 0x6C, .sw a3 (8 : Fin 32) 0x68,
   .sw a3 (9 : Fin 32) 0x64, .sw a3 (18 : Fin 32) 0x60, .sw a3 (19 : Fin 32) 0x5C, .sw a3 (20 : Fin 32) 0x58,
   .sw a3 (21 : Fin 32) 0x54, .sw a3 (22 : Fin 32) 0x50, .sw a3 (23 : Fin 32) 0x4C, .sw a3 (24 : Fin 32) 0x48,
   .sw a3 (25 : Fin 32) 0x44, .sw a3 (26 : Fin 32) 0x40, .sw a3 (27 : Fin 32) 0x3C, .aluImm .add sp sp 0xFFFFFDA0,
   .alu .add (21 : Fin 32) x0 a2, .alu .add (19 : Fin 32) x0 a0, .aluImm .add (25 : Fin 32) sp 0x7FF,
   .aluImm .add (25 : Fin 32) (25 : Fin 32) 0x18D, .aluImm .add a0 sp 0x40]
def dqA2 : List BInstr := [.aluImm .add a0 sp 0x74, .aluImm .add a2 x0 0x30, .aluImm .add a1 x0 0x0]
def dqA3 : List BInstr :=
  [.lbu (20 : Fin 32) sp 0x70, .aluImm .add a0 sp 0xA4, .aluImm .add a1 sp 0x74, .aluImm .add a2 sp 0x40,
   .alu .add a3 x0 (20 : Fin 32)]

theorem dqA1_end : blockEnd p384DecompressCode 0 dqA1 = some 0x4A := by decide
theorem dqA2_end : blockEnd p384DecompressCode 0x52 dqA2 = some 0x5A := by decide
theorem dqA3_end : blockEnd p384DecompressCode 0x62 dqA3 = some 0x6E := by decide

/-- The registers the prologue saves, by their slot below the caller's `sp`. -/
def savedReg : Nat → Fin 32
  | 0 => ra | 1 => 8 | 2 => 9 | 3 => 18 | 4 => 19 | 5 => 20 | 6 => 21 | 7 => 22 | 8 => 23 | 9 => 24 | 10 => 25
  | 11 => 26 | _ => 27

theorem ld_st_frame {M : Word → BitVec 8} {S v : Word} {c d : Nat} (hc : c % 4 = 0) (hd : d % 4 = 0)
    (hc' : c + 4 ≤ 0xA50) (hd' : d + 4 ≤ 0xA50) :
    memLoad32 (memStore32 M (S + BitVec.ofNat 32 c) v) (S + BitVec.ofNat 32 d) =
      if c = d then v else memLoad32 M (S + BitVec.ofNat 32 d) := by
  by_cases h : c = d
  · subst h; rw [ite_eq_left rfl, memLoad32_store32_same]
  · rw [ite_eq_right h, memLoad32_store32_sep (sepS S (by omega) (by omega) (by omega))]

theorem frame_lit {S : Word} {c : Nat} (k : Word) (h : c + k.toNat < 2 ^ 32) :
    S + BitVec.ofNat 32 c + k = S + BitVec.ofNat 32 (c + k.toNat) := by
  rw [BitVec.add_assoc]; congr 1
  apply BitVec.eq_of_toNat_eq
  rw [BitVec.toNat_add, BitVec.toNat_ofNat, BitVec.toNat_ofNat]; have := k.isLt; omega

/-- The prologue's saves, in order. -/
def dqSaves (M : Word → BitVec 8) (S : Word) (n : Machine) : Word → BitVec 8 :=
  memStore32 (memStore32 (memStore32 (memStore32 (memStore32 (memStore32 (memStore32 (memStore32 (memStore32 (memStore32 (memStore32 (memStore32 (memStore32 (M) (S + BitVec.ofNat 32 0xa4c) (reg n ra)) (S + BitVec.ofNat 32 0xa48) (reg n (8 : Fin 32))) (S + BitVec.ofNat 32 0xa44) (reg n (9 : Fin 32))) (S + BitVec.ofNat 32 0xa40) (reg n (18 : Fin 32))) (S + BitVec.ofNat 32 0xa3c) (reg n (19 : Fin 32))) (S + BitVec.ofNat 32 0xa38) (reg n (20 : Fin 32))) (S + BitVec.ofNat 32 0xa34) (reg n (21 : Fin 32))) (S + BitVec.ofNat 32 0xa30) (reg n (22 : Fin 32))) (S + BitVec.ofNat 32 0xa2c) (reg n (23 : Fin 32))) (S + BitVec.ofNat 32 0xa28) (reg n (24 : Fin 32))) (S + BitVec.ofNat 32 0xa24) (reg n (25 : Fin 32))) (S + BitVec.ofNat 32 0xa20) (reg n (26 : Fin 32))) (S + BitVec.ofNat 32 0xa1c) (reg n (27 : Fin 32))

set_option maxRecDepth 100000 in
set_option maxHeartbeats 16000000 in
/-- **The prologue**, from the entry to `from_repr`'s call at 0x4A: save `ra`
and `s0..s11` at the top of the frame, and open the frame at `S`. -/
theorem dq_pro {M : Word → BitVec 8} {n : Machine} {S : Word} (C : DqCode M) (F : DqFrame S)
    (s : St M DP n 0 (reg n)) (rsp : reg n sp = S + 0xA50) :
    ∃ n', Steps n n' ∧ St (dqSaves M S n) DP n' 0x4A (reg n') ∧
      reg n' sp = S ∧ reg n' (21 : Fin 32) = reg n a2 ∧ reg n' (19 : Fin 32) = reg n a0 ∧
      reg n' (25 : Fin 32) = S + BitVec.ofNat 32 0x98C ∧ reg n' a0 = S + BitVec.ofNat 32 0x40 ∧
      ∀ q, q.val ∈ [3, 4, 11] → reg n' q = reg n q := by
  have hz := s.zero
  have hSl := F.lo; have hSh := F.hi; have hSa := F.al
  have hA3 : aluEval .add (aluEval .add (S + 0xA50) 0xFFFFF810) 0x780 = S + BitVec.ofNat 32 0x9E0 := by
    show S + 0xA50 + 0xFFFFF810 + 0x780 = S + BitVec.ofNat 32 0x9E0
    rw [BitVec.add_assoc, BitVec.add_assoc]; rfl
  have alB : ∀ k : Word, 0x9E0 + k.toNat + 4 ≤ 0xA50 → k.toNat % 4 = 0 →
      (S + BitVec.ofNat 32 0x9E0 + k).toNat % 4 = 0 := fun k h1 h2 => by
    rw [frame_lit k (by omega), F.at _ (by omega)]; omega
  have sepB : ∀ k : Word, 0x9E0 + k.toNat + 4 ≤ 0xA50 →
      Sep (S + BitVec.ofNat 32 0x9E0 + k) 4 DP p384DecompressCode.length := fun k h1 => by
    rw [frame_lit k (by omega)]; exact F.sepHi (by omega) (by decide) (by decide)
  obtain ⟨n1, c1, u1⟩ := s.block dqA1 C.self dqA1_end (by
    simp only [BlockOk, BInstr.ok, BInstr.run, dqA1]; simp +decide only [upd, ↓reduceIte, true_and, and_true]
    rw [rsp, hA3]
    exact ⟨⟨alB 0x6C (by decide) (by decide), sepB 0x6C (by decide)⟩, ⟨alB 0x68 (by decide) (by decide), sepB 0x68 (by decide)⟩, ⟨alB 0x64 (by decide) (by decide), sepB 0x64 (by decide)⟩, ⟨alB 0x60 (by decide) (by decide), sepB 0x60 (by decide)⟩, ⟨alB 0x5C (by decide) (by decide), sepB 0x5C (by decide)⟩, ⟨alB 0x58 (by decide) (by decide), sepB 0x58 (by decide)⟩, ⟨alB 0x54 (by decide) (by decide), sepB 0x54 (by decide)⟩, ⟨alB 0x50 (by decide) (by decide), sepB 0x50 (by decide)⟩, ⟨alB 0x4C (by decide) (by decide), sepB 0x4C (by decide)⟩, ⟨alB 0x48 (by decide) (by decide), sepB 0x48 (by decide)⟩, ⟨alB 0x44 (by decide) (by decide), sepB 0x44 (by decide)⟩, ⟨alB 0x40 (by decide) (by decide), sepB 0x40 (by decide)⟩, ⟨alB 0x3C (by decide) (by decide), sepB 0x3C (by decide)⟩⟩)
  have m1 : n1.mem = dqSaves M S n := by
    rw [u1.mem]; simp only [runBlock, BInstr.run, dqA1]; simp +decide only [upd, ↓reduceIte]
    rw [rsp, hA3]
    simp (disch := decide) only [frame_lit]
    rfl
  refine ⟨n1, c1, ⟨u1.pc, m1, fun _ => rfl⟩, ?_, ?_, ?_, ?_, ?_, fun q hq => ?_⟩
  · rw [u1.regs]; simp +decide only [runBlock, BInstr.run, dqA1, upd, ↓reduceIte]; rw [rsp]
    show S + 0xA50 + 0xFFFFF810 + 0xFFFFFDA0 = S
    rw [BitVec.add_assoc, BitVec.add_assoc]; exact BitVec.add_zero S
  · rw [u1.regs]; simp +decide only [runBlock, BInstr.run, dqA1, upd, ↓reduceIte]; exact BitVec.zero_add _
  · rw [u1.regs]; simp +decide only [runBlock, BInstr.run, dqA1, upd, ↓reduceIte]; exact BitVec.zero_add _
  · rw [u1.regs]; simp +decide only [runBlock, BInstr.run, dqA1, upd, ↓reduceIte]; rw [rsp]
    show S + 0xA50 + 0xFFFFF810 + 0xFFFFFDA0 + 0x7FF + 0x18D = S + BitVec.ofNat 32 0x98C
    rw [BitVec.add_assoc, BitVec.add_assoc, BitVec.add_assoc, BitVec.add_assoc]; rfl
  · rw [u1.regs]; simp +decide only [runBlock, BInstr.run, dqA1, upd, ↓reduceIte]; rw [rsp]
    show S + 0xA50 + 0xFFFFF810 + 0xFFFFFDA0 + 0x40 = S + BitVec.ofNat 32 0x40
    rw [BitVec.add_assoc, BitVec.add_assoc, BitVec.add_assoc]; rfl
  · rw [u1.regs, runBlock_reg _ _ _ q hz (by simp only [dqA1]; revert hq; revert q; decide)]

theorem dqSaves_read {M : Word → BitVec 8} {S : Word} {n : Machine} :
    ∀ k, k < 13 → memLoad32 (dqSaves M S n) (S + BitVec.ofNat 32 (0xA4C - 4 * k)) = reg n (savedReg k) := by
  intro k hk
  match k, hk with
  | 0, _ => unfold dqSaves; rw [ld_st_frame (by decide) (by decide) (by decide) (by decide), ite_eq_right (by decide), ld_st_frame (by decide) (by decide) (by decide) (by decide), ite_eq_right (by decide), ld_st_frame (by decide) (by decide) (by decide) (by decide), ite_eq_right (by decide), ld_st_frame (by decide) (by decide) (by decide) (by decide), ite_eq_right (by decide), ld_st_frame (by decide) (by decide) (by decide) (by decide), ite_eq_right (by decide), ld_st_frame (by decide) (by decide) (by decide) (by decide), ite_eq_right (by decide), ld_st_frame (by decide) (by decide) (by decide) (by decide), ite_eq_right (by decide), ld_st_frame (by decide) (by decide) (by decide) (by decide), ite_eq_right (by decide), ld_st_frame (by decide) (by decide) (by decide) (by decide), ite_eq_right (by decide), ld_st_frame (by decide) (by decide) (by decide) (by decide), ite_eq_right (by decide), ld_st_frame (by decide) (by decide) (by decide) (by decide), ite_eq_right (by decide), ld_st_frame (by decide) (by decide) (by decide) (by decide), ite_eq_right (by decide), ld_st_frame (by decide) (by decide) (by decide) (by decide), ite_eq_left (by decide)]; rfl
  | 1, _ => unfold dqSaves; rw [ld_st_frame (by decide) (by decide) (by decide) (by decide), ite_eq_right (by decide), ld_st_frame (by decide) (by decide) (by decide) (by decide), ite_eq_right (by decide), ld_st_frame (by decide) (by decide) (by decide) (by decide), ite_eq_right (by decide), ld_st_frame (by decide) (by decide) (by decide) (by decide), ite_eq_right (by decide), ld_st_frame (by decide) (by decide) (by decide) (by decide), ite_eq_right (by decide), ld_st_frame (by decide) (by decide) (by decide) (by decide), ite_eq_right (by decide), ld_st_frame (by decide) (by decide) (by decide) (by decide), ite_eq_right (by decide), ld_st_frame (by decide) (by decide) (by decide) (by decide), ite_eq_right (by decide), ld_st_frame (by decide) (by decide) (by decide) (by decide), ite_eq_right (by decide), ld_st_frame (by decide) (by decide) (by decide) (by decide), ite_eq_right (by decide), ld_st_frame (by decide) (by decide) (by decide) (by decide), ite_eq_right (by decide), ld_st_frame (by decide) (by decide) (by decide) (by decide), ite_eq_left (by decide)]; rfl
  | 2, _ => unfold dqSaves; rw [ld_st_frame (by decide) (by decide) (by decide) (by decide), ite_eq_right (by decide), ld_st_frame (by decide) (by decide) (by decide) (by decide), ite_eq_right (by decide), ld_st_frame (by decide) (by decide) (by decide) (by decide), ite_eq_right (by decide), ld_st_frame (by decide) (by decide) (by decide) (by decide), ite_eq_right (by decide), ld_st_frame (by decide) (by decide) (by decide) (by decide), ite_eq_right (by decide), ld_st_frame (by decide) (by decide) (by decide) (by decide), ite_eq_right (by decide), ld_st_frame (by decide) (by decide) (by decide) (by decide), ite_eq_right (by decide), ld_st_frame (by decide) (by decide) (by decide) (by decide), ite_eq_right (by decide), ld_st_frame (by decide) (by decide) (by decide) (by decide), ite_eq_right (by decide), ld_st_frame (by decide) (by decide) (by decide) (by decide), ite_eq_right (by decide), ld_st_frame (by decide) (by decide) (by decide) (by decide), ite_eq_left (by decide)]; rfl
  | 3, _ => unfold dqSaves; rw [ld_st_frame (by decide) (by decide) (by decide) (by decide), ite_eq_right (by decide), ld_st_frame (by decide) (by decide) (by decide) (by decide), ite_eq_right (by decide), ld_st_frame (by decide) (by decide) (by decide) (by decide), ite_eq_right (by decide), ld_st_frame (by decide) (by decide) (by decide) (by decide), ite_eq_right (by decide), ld_st_frame (by decide) (by decide) (by decide) (by decide), ite_eq_right (by decide), ld_st_frame (by decide) (by decide) (by decide) (by decide), ite_eq_right (by decide), ld_st_frame (by decide) (by decide) (by decide) (by decide), ite_eq_right (by decide), ld_st_frame (by decide) (by decide) (by decide) (by decide), ite_eq_right (by decide), ld_st_frame (by decide) (by decide) (by decide) (by decide), ite_eq_right (by decide), ld_st_frame (by decide) (by decide) (by decide) (by decide), ite_eq_left (by decide)]; rfl
  | 4, _ => unfold dqSaves; rw [ld_st_frame (by decide) (by decide) (by decide) (by decide), ite_eq_right (by decide), ld_st_frame (by decide) (by decide) (by decide) (by decide), ite_eq_right (by decide), ld_st_frame (by decide) (by decide) (by decide) (by decide), ite_eq_right (by decide), ld_st_frame (by decide) (by decide) (by decide) (by decide), ite_eq_right (by decide), ld_st_frame (by decide) (by decide) (by decide) (by decide), ite_eq_right (by decide), ld_st_frame (by decide) (by decide) (by decide) (by decide), ite_eq_right (by decide), ld_st_frame (by decide) (by decide) (by decide) (by decide), ite_eq_right (by decide), ld_st_frame (by decide) (by decide) (by decide) (by decide), ite_eq_right (by decide), ld_st_frame (by decide) (by decide) (by decide) (by decide), ite_eq_left (by decide)]; rfl
  | 5, _ => unfold dqSaves; rw [ld_st_frame (by decide) (by decide) (by decide) (by decide), ite_eq_right (by decide), ld_st_frame (by decide) (by decide) (by decide) (by decide), ite_eq_right (by decide), ld_st_frame (by decide) (by decide) (by decide) (by decide), ite_eq_right (by decide), ld_st_frame (by decide) (by decide) (by decide) (by decide), ite_eq_right (by decide), ld_st_frame (by decide) (by decide) (by decide) (by decide), ite_eq_right (by decide), ld_st_frame (by decide) (by decide) (by decide) (by decide), ite_eq_right (by decide), ld_st_frame (by decide) (by decide) (by decide) (by decide), ite_eq_right (by decide), ld_st_frame (by decide) (by decide) (by decide) (by decide), ite_eq_left (by decide)]; rfl
  | 6, _ => unfold dqSaves; rw [ld_st_frame (by decide) (by decide) (by decide) (by decide), ite_eq_right (by decide), ld_st_frame (by decide) (by decide) (by decide) (by decide), ite_eq_right (by decide), ld_st_frame (by decide) (by decide) (by decide) (by decide), ite_eq_right (by decide), ld_st_frame (by decide) (by decide) (by decide) (by decide), ite_eq_right (by decide), ld_st_frame (by decide) (by decide) (by decide) (by decide), ite_eq_right (by decide), ld_st_frame (by decide) (by decide) (by decide) (by decide), ite_eq_right (by decide), ld_st_frame (by decide) (by decide) (by decide) (by decide), ite_eq_left (by decide)]; rfl
  | 7, _ => unfold dqSaves; rw [ld_st_frame (by decide) (by decide) (by decide) (by decide), ite_eq_right (by decide), ld_st_frame (by decide) (by decide) (by decide) (by decide), ite_eq_right (by decide), ld_st_frame (by decide) (by decide) (by decide) (by decide), ite_eq_right (by decide), ld_st_frame (by decide) (by decide) (by decide) (by decide), ite_eq_right (by decide), ld_st_frame (by decide) (by decide) (by decide) (by decide), ite_eq_right (by decide), ld_st_frame (by decide) (by decide) (by decide) (by decide), ite_eq_left (by decide)]; rfl
  | 8, _ => unfold dqSaves; rw [ld_st_frame (by decide) (by decide) (by decide) (by decide), ite_eq_right (by decide), ld_st_frame (by decide) (by decide) (by decide) (by decide), ite_eq_right (by decide), ld_st_frame (by decide) (by decide) (by decide) (by decide), ite_eq_right (by decide), ld_st_frame (by decide) (by decide) (by decide) (by decide), ite_eq_right (by decide), ld_st_frame (by decide) (by decide) (by decide) (by decide), ite_eq_left (by decide)]; rfl
  | 9, _ => unfold dqSaves; rw [ld_st_frame (by decide) (by decide) (by decide) (by decide), ite_eq_right (by decide), ld_st_frame (by decide) (by decide) (by decide) (by decide), ite_eq_right (by decide), ld_st_frame (by decide) (by decide) (by decide) (by decide), ite_eq_right (by decide), ld_st_frame (by decide) (by decide) (by decide) (by decide), ite_eq_left (by decide)]; rfl
  | 10, _ => unfold dqSaves; rw [ld_st_frame (by decide) (by decide) (by decide) (by decide), ite_eq_right (by decide), ld_st_frame (by decide) (by decide) (by decide) (by decide), ite_eq_right (by decide), ld_st_frame (by decide) (by decide) (by decide) (by decide), ite_eq_left (by decide)]; rfl
  | 11, _ => unfold dqSaves; rw [ld_st_frame (by decide) (by decide) (by decide) (by decide), ite_eq_right (by decide), ld_st_frame (by decide) (by decide) (by decide) (by decide), ite_eq_left (by decide)]; rfl
  | 12, _ => unfold dqSaves; rw [ld_st_frame (by decide) (by decide) (by decide) (by decide), ite_eq_left (by decide)]; rfl

theorem dqSaves_out {M : Word → BitVec 8} {S : Word} {n : Machine} {x : Word}
    (h : Sep (S + BitVec.ofNat 32 0xA1C) 0x34 x 1) : dqSaves M S n x = M x := by
  have hs : ∀ c, 0xA1C ≤ c → c + 4 ≤ 0xA50 → Sep (S + BitVec.ofNat 32 c) 4 x 1 := fun c h1 h2 => by
    have := h.sub (c := c - 0xA1C) (l := 4) (by omega)
    rwa [add_ofNat_assoc, show 0xA1C + (c - 0xA1C) = c by omega] at this
  unfold dqSaves
  rw [memStore32_get_sep (hs 0xa1c (by decide) (by decide))]
  rw [memStore32_get_sep (hs 0xa20 (by decide) (by decide))]
  rw [memStore32_get_sep (hs 0xa24 (by decide) (by decide))]
  rw [memStore32_get_sep (hs 0xa28 (by decide) (by decide))]
  rw [memStore32_get_sep (hs 0xa2c (by decide) (by decide))]
  rw [memStore32_get_sep (hs 0xa30 (by decide) (by decide))]
  rw [memStore32_get_sep (hs 0xa34 (by decide) (by decide))]
  rw [memStore32_get_sep (hs 0xa38 (by decide) (by decide))]
  rw [memStore32_get_sep (hs 0xa3c (by decide) (by decide))]
  rw [memStore32_get_sep (hs 0xa40 (by decide) (by decide))]
  rw [memStore32_get_sep (hs 0xa44 (by decide) (by decide))]
  rw [memStore32_get_sep (hs 0xa48 (by decide) (by decide))]
  rw [memStore32_get_sep (hs 0xa4c (by decide) (by decide))]

end C3.RV32.Dq
