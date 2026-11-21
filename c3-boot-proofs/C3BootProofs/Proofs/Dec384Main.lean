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

/-- What `decompress` leaves after `from_repr`: `s4` holds whether the input
`x` is below `p`, and `S + 0xA4` holds `x` in Montgomery form, or zero. -/
def XOk (x : Nat) (ok : Word) (X : Nat) : Prop :=
  (x < p384 → ok = 1 ∧ X = x * 2 ^ 384 % p384) ∧ (p384 ≤ x → ok = 0 ∧ X = 0)

set_option maxRecDepth 100000 in
set_option maxHeartbeats 16000000 in
/-- **Decoding `x`**, from the entry to 0x76: the prologue, `from_repr`, and
the conditional select of the result or zero into `S + 0xA4`. -/
theorem dq_stA {M : Word → BitVec 8} {n : Machine} {S inp : Word} (C : DqCode M) (D : DqData M) (F : DqFrame S)
    (s : St M DP n 0 (reg n)) (rsp : reg n sp = S + 0xA50) (ra1 : reg n a1 = inp)
    (sI : Sep inp 48 (S + 0xFFFFFE60) 0xBF0) :
    ∃ n', Steps n n' ∧ St n'.mem DP n' 0x76 (reg n') ∧ DqCode n'.mem ∧ DqData n'.mem ∧
      (∀ k, k < 13 → memLoad32 n'.mem (S + BitVec.ofNat 32 (0xA4C - 4 * k)) = reg n (savedReg k)) ∧
      XOk (beNat (memBytes M inp 48)) (reg n' (20 : Fin 32)) (accV n'.mem (S + BitVec.ofNat 32 0xA4) 12) ∧
      (∀ x, Sep (S + 0xFFFFFE60) 0x1A0 x 1 → Sep (S + BitVec.ofNat 32 0x40) 0x94 x 1 →
        Sep (S + BitVec.ofNat 32 0xA1C) 0x34 x 1 → n'.mem x = M x) ∧
      reg n' sp = S ∧ reg n' (21 : Fin 32) = reg n a2 ∧ reg n' (19 : Fin 32) = reg n a0 ∧
      reg n' (25 : Fin 32) = S + BitVec.ofNat 32 0x98C ∧
      reg n' (3 : Fin 32) = reg n (3 : Fin 32) ∧ reg n' (4 : Fin 32) = reg n (4 : Fin 32) := by
  have hSl := F.lo; have hSh := F.hi; have hSa := F.al
  obtain ⟨n1, c1, u1, sp1, e21, e19, e25, e10, k1⟩ := dq_pro C F s rsp
  have hsv : ∀ x, Sep (S + BitVec.ofNat 32 0xA1C) 0x34 x 1 → dqSaves M S n x = M x := fun x h => dqSaves_out h
  have hihi : ∀ x : Word, 0x40000000 ≤ x.toNat → dqSaves M S n x = M x := fun x hx =>
    hsv x (F.hiOut (by decide) hx)
  have C1 := C.hi hihi
  have dS : ∀ x, Sep (S + 0xFFFFFE60) 0xBF0 x 1 → dqSaves M S n x = M x := fun x hx => by
    exact (hsv x) (by
      have := hx.sub (c := 0x1A0 + 0xA1C) (l := 0x34) (by decide)
      rwa [BitVec.add_assoc, show (0xFFFFFE60 : Word) + BitVec.ofNat 32 (0x1A0 + 0xA1C) = BitVec.ofNat 32 0xA1C from rfl]
        at this)
  have D1 := D.of F dS
  have hin : memBytes (dqSaves M S n) inp 48 = memBytes M inp 48 :=
    memBytes_congr fun i hi => dS _ (sI.symm.subR (c := i) (l := 1) (by omega))
  -- from_repr
  obtain ⟨n2, c2, u2, ok2, bad2, fr2, sp2, k2⟩ := dq_frp (out := S + BitVec.ofNat 32 0x40) (inp := inp) u1 C1 D1 F
    dp_at_4a dp_at_4e (by decide) (by decide) sp1 e10 (by rw [k1 11 (by decide)]; exact ra1) (co := 0x40) (by decide) rfl
    (sI.subR (c := 0) (l := 0x1A0) (by decide) |> fun h => by rwa [add_ofNat_zero] at h)
  rw [hin] at ok2 bad2
  have hbF : (S + 0xFFFFFE60).toNat = S.toNat - 0x1A0 := F.below 0x1A0 (by decide) (by decide)
  have h2hi : ∀ x : Word, 0x40000000 ≤ x.toNat → n2.mem x = M x := fun x hx => by
    rw [fr2 x (sep_of_le (by rw [hbF]; omega) (by have := x.isLt; omega)) (F.hiOut (c := 0x40) (n := 49) (by decide) hx),
      hihi x hx]
  have C2 := C.hi h2hi
  have D2 : DqData n2.mem := D1.of F fun x hx => fr2 x (hx.sub (c := 0) (l := 0x1A0) (by decide) |> fun h => by
    rwa [add_ofNat_zero] at h) (by
      have := hx.sub (c := 0x1A0 + 0x40) (l := 49) (by decide)
      rwa [BitVec.add_assoc, show (0xFFFFFE60 : Word) + BitVec.ofNat 32 (0x1A0 + 0x40) = BitVec.ofNat 32 0x40 from rfl] at this)
  -- zero the other operand
  obtain ⟨n3, c3, u3⟩ := u2.block dqA2 C2.self dqA2_end ⟨trivial, trivial, trivial, trivial⟩
  have r3 : ∀ q, reg n3 q = (runBlock dqA2 (n2.mem, reg n2)).2 q := fun q => by rw [u3.regs]
  obtain ⟨n4, c4, u4, mem4, k4⟩ := dq_memset (dst := S + BitVec.ofNat 32 0x74) (b := 0) (N := 48)
    (⟨u3.pc, u3.mem, fun _ => rfl⟩ : St n2.mem DP n3 0x5A (reg n3)) C2 dp_at_5a dp_at_5e (by decide) (by decide)
    (by rw [r3]; simp +decide only [runBlock, BInstr.run, dqA2, upd, ↓reduceIte]; rw [sp2]; rfl)
    (by rw [r3]; simp +decide only [runBlock, BInstr.run, dqA2, upd, ↓reduceIte]; (try rw [u2.zero]); try rfl)
    (by rw [r3]; simp +decide only [runBlock, BInstr.run, dqA2, upd, ↓reduceIte]; (try rw [u2.zero]); try rfl)
    (by rw [F.at _ (by decide)]; omega) (F.sepHi (by decide) (by decide) (by decide))
  have h4 : ∀ x, Sep (S + BitVec.ofNat 32 0x74) 48 x 1 → n4.mem x = n2.mem x := fun x hx => by
    rw [mem4, fillBytes_sep hx (Nat.le_refl _)]
  have C4 := C2.hi fun x hx => h4 x (F.hiOut (by decide) hx)
  have k4' : ∀ q, q ≠ a0 → q ≠ a1 → q ≠ a2 → q ≠ a3 → q ≠ a4 → q ≠ a5 → q ≠ a6 → q ≠ ra → reg n4 q = reg n2 q :=
    fun q h0 h1 h2 h3 h4 h5 h6 hr => by
      rw [k4 q h0 h2 h3 h4 h5 h6 hr, r3, runBlock_reg _ _ _ q u2.zero (by simp only [dqA2]; revert h0 h1 h2; revert q; decide)]
  have sp4 : reg n4 sp = S := by
    rw [k4' sp (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)]; exact sp2
  -- the select
  have a70 : n4.mem (S + BitVec.ofNat 32 0x40 + 0x30) = n2.mem (S + BitVec.ofNat 32 0x40 + 0x30) :=
    h4 _ (sepS S (c := 0x74) (n := 48) (d := 0x70) (k := 1) (.inr (by decide)) (by decide) (by decide) |> fun h => by
      rwa [show S + BitVec.ofNat 32 0x70 = S + BitVec.ofNat 32 0x40 + 0x30 from by rw [BitVec.add_assoc]; rfl] at h)
  obtain ⟨n5, c5, u5⟩ := u4.block dqA3 C4.self dqA3_end ⟨trivial, trivial, trivial, trivial, trivial, trivial⟩
  have r5 : ∀ q, reg n5 q = (runBlock dqA3 (n4.mem, reg n4)).2 q := fun q => by rw [u5.regs]
  have e20 : reg n5 (20 : Fin 32) = (n2.mem (S + BitVec.ofNat 32 0x40 + 0x30)).zeroExtend 32 := by
    rw [r5]; simp +decide only [runBlock, BInstr.run, dqA3, upd, ↓reduceIte]; rw [sp4, ← a70]
    rw [show S + BitVec.ofNat 32 0x40 + 0x30 = S + 0x70 from by rw [BitVec.add_assoc]; rfl]
  have hc01 : (n2.mem (S + BitVec.ofNat 32 0x40 + 0x30)).zeroExtend 32 = (0 : Word) ∨
      (n2.mem (S + BitVec.ofNat 32 0x40 + 0x30)).zeroExtend 32 = (1 : Word) := by
    by_cases hx : beNat (memBytes M inp 48) < p384
    · rw [(ok2 hx).1]; exact .inr rfl
    · rw [(bad2 (by omega)).1]; exact .inl rfl
  obtain ⟨n6, c6, u6, vals6, fr6, sp6, k6⟩ := dq_csel (out := S + BitVec.ofNat 32 0xA4) (a := S + BitVec.ofNat 32 0x74)
    (b := S + BitVec.ofNat 32 0x40) (c := (n2.mem (S + BitVec.ofNat 32 0x40 + 0x30)).zeroExtend 32)
    (⟨u5.pc, u5.mem, fun _ => rfl⟩ : St n4.mem DP n5 0x6E (reg n5)) C4 F dp_at_6e dp_at_72 (by decide) (by decide)
    (by rw [r5, runBlock_reg _ _ _ sp u4.zero (by decide)]; exact sp4)
    (by rw [r5]; simp +decide only [runBlock, BInstr.run, dqA3, upd, ↓reduceIte]; rw [sp4]; rfl)
    (by rw [r5]; simp +decide only [runBlock, BInstr.run, dqA3, upd, ↓reduceIte]; rw [sp4]; rfl)
    (by rw [r5]; simp +decide only [runBlock, BInstr.run, dqA3, upd, ↓reduceIte]; rw [sp4]; rfl)
    (by rw [r5]; simp +decide only [runBlock, BInstr.run, dqA3, upd, ↓reduceIte]; rw [sp4]
        show aluEval .add 0 ((n4.mem (S + 0x70)).zeroExtend 32) = _
        rw [show (S + 0x70 : Word) = S + BitVec.ofNat 32 0x40 + 0x30 from by rw [BitVec.add_assoc]; rfl, a70]
        exact BitVec.zero_add _)
    hc01 (co := 0xA4) (ca := 0x74) (cb := 0x40) (by decide) (by decide) (by decide) rfl rfl rfl (by decide)
  have hb60 : (S + 0xFFFFFFA0).toNat = S.toNat - 0x60 := F.below 0x60 (by decide) (by decide)
  have h6hi : ∀ x : Word, 0x40000000 ≤ x.toNat → n6.mem x = M x := fun x hx => by
    rw [fr6 x (sep_of_le (by rw [hb60]; omega) (by have := x.isLt; omega)) (F.hiOut (c := 0xA4) (n := 48) (by decide) hx),
      h4 x (F.hiOut (by decide) hx), h2hi x hx]
  -- the whole frame of this stage
  have frame : ∀ x, Sep (S + 0xFFFFFE60) 0x1A0 x 1 → Sep (S + BitVec.ofNat 32 0x40) 0x94 x 1 →
      Sep (S + BitVec.ofNat 32 0xA1C) 0x34 x 1 → n6.mem x = M x := by
    intro x hF h40 hA
    have h60 : Sep (S + 0xFFFFFFA0) 0x60 x 1 := by
      have := hF.sub (c := 0x140) (l := 0x60) (by decide)
      rwa [show S + 0xFFFFFE60 + BitVec.ofNat 32 0x140 = S + 0xFFFFFFA0 by rw [BitVec.add_assoc]; rfl] at this
    have hA4 : Sep (S + BitVec.ofNat 32 0xA4) 48 x 1 := by
      have := h40.sub (c := 0x64) (l := 48) (by decide); rwa [add_ofNat_assoc] at this
    have h74 : Sep (S + BitVec.ofNat 32 0x74) 48 x 1 := by
      have := h40.sub (c := 0x34) (l := 48) (by decide); rwa [add_ofNat_assoc] at this
    have h4049 : Sep (S + BitVec.ofNat 32 0x40) 49 x 1 := by
      have := h40.sub (c := 0) (l := 49) (by decide); rwa [add_ofNat_zero] at this
    rw [fr6 x h60 hA4, h4 x h74, fr2 x hF h4049, hsv x hA]
  have D6 : DqData n6.mem := D.of F fun x hx => frame x (hx.sub (c := 0) (l := 0x1A0) (by decide) |> fun h => by
      rwa [add_ofNat_zero] at h)
    (by have := hx.sub (c := 0x1A0 + 0x40) (l := 0x94) (by decide)
        rwa [BitVec.add_assoc, show (0xFFFFFE60 : Word) + BitVec.ofNat 32 (0x1A0 + 0x40) = BitVec.ofNat 32 0x40 from rfl]
          at this)
    (by have := hx.sub (c := 0x1A0 + 0xA1C) (l := 0x34) (by decide)
        rwa [BitVec.add_assoc, show (0xFFFFFE60 : Word) + BitVec.ofNat 32 (0x1A0 + 0xA1C) = BitVec.ofNat 32 0xA1C from rfl]
          at this)
  have hbelow : ∀ d, d + 4 ≤ 0xA50 → Sep (S + 0xFFFFFE60) 0x1A0 (S + BitVec.ofNat 32 d) 4 := fun d hd =>
    sep_of_le (by rw [hbF, F.at _ (by omega)]; omega) (by rw [F.at _ (by omega)]; omega)
  have hb60' : ∀ d, d + 4 ≤ 0xA50 → Sep (S + 0xFFFFFFA0) 0x60 (S + BitVec.ofNat 32 d) 4 := fun d hd =>
    sep_of_le (by rw [hb60, F.at _ (by omega)]; omega) (by rw [F.at _ (by omega)]; omega)
  have e620 : reg n6 (20 : Fin 32) = (n2.mem (S + BitVec.ofNat 32 0x40 + 0x30)).zeroExtend 32 := by
    rw [k6 20 (by decide), e20]
  refine ⟨n6, c1.trans (c2.trans (c3.trans (c4.trans (c5.trans c6)))), u6, C.hi h6hi, D6, fun k hk => ?_, ⟨fun hx => ?_,
    fun hx => ?_⟩, frame, sp6, ?_, ?_, ?_, ?_, ?_⟩
  · rw [← dqSaves_read k hk]
    refine memLoad32_congr fun q hq => ?_
    rw [add_ofNat_assoc]
    have e1 : n6.mem (S + BitVec.ofNat 32 (0xA4C - 4 * k + q)) = n4.mem (S + BitVec.ofNat 32 (0xA4C - 4 * k + q)) :=
      fr6 _ (sep_of_le (by rw [hb60, F.at _ (by omega)]; omega) (by rw [F.at _ (by omega)]; omega))
        (sepS S (.inl (by omega)) (by decide) (by omega))
    rw [e1, h4 _ (sepS S (.inl (by omega)) (by decide) (by omega)),
      fr2 _ (sep_of_le (by rw [hbF, F.at _ (by omega)]; omega) (by rw [F.at _ (by omega)]; omega))
        (sepS S (.inl (by omega)) (by decide) (by omega))]
  · obtain ⟨o1, olt, ocg⟩ := ok2 hx
    have hc1 : (n2.mem (S + BitVec.ofNat 32 0x40 + 0x30)).zeroExtend 32 = (1 : Word) := by rw [o1]; rfl
    refine ⟨by rw [e620, hc1], ?_⟩
    have eA : accV n6.mem (S + BitVec.ofNat 32 0xA4) 12 = accV n2.mem (S + BitVec.ofNat 32 0x40) 12 :=
      accV_congr2 12 fun i hi => by
        rw [vals6 i hi, ite_eq_left hc1]
        exact memLoad32_congr fun q hq => by
          rw [add_ofNat_assoc, add_ofNat_assoc]
          exact h4 _ (sepS S (.inr (by omega)) (by decide) (by omega))
    rw [eA]
    have hR : accV (dqSaves M S n) (PARAMS + BitVec.ofNat 32 0x60) 12 = dataVal p384ParamsData 0x60 12 :=
      code_accV D1.params 0x60 12 (by decide)
    rw [hR] at ocg
    exact frp_val olt ocg
  · obtain ⟨o0, _⟩ := bad2 (by omega)
    have hc0 : (n2.mem (S + BitVec.ofNat 32 0x40 + 0x30)).zeroExtend 32 = (0 : Word) := by rw [o0]; rfl
    refine ⟨by rw [e620, hc0], ?_⟩
    exact accV_zero 12 fun i hi => by
      rw [vals6 i hi, ite_eq_right (by rw [hc0]; decide), mem4]
      exact fill_word0 (by omega) (by decide)
  · rw [k6 21 (by decide), r5, runBlock_reg _ _ _ 21 u4.zero (by decide), k4' 21 (by decide) (by decide) (by decide)
      (by decide) (by decide) (by decide) (by decide) (by decide), k2 21 (by decide), e21]
  · rw [k6 19 (by decide), r5, runBlock_reg _ _ _ 19 u4.zero (by decide), k4' 19 (by decide) (by decide) (by decide)
      (by decide) (by decide) (by decide) (by decide) (by decide), k2 19 (by decide), e19]
  · rw [k6 25 (by decide), r5, runBlock_reg _ _ _ 25 u4.zero (by decide), k4' 25 (by decide) (by decide) (by decide)
      (by decide) (by decide) (by decide) (by decide) (by decide), k2 25 (by decide), e25]
  · rw [k6 3 (by decide), r5, runBlock_reg _ _ _ 3 u4.zero (by decide), k4' 3 (by decide) (by decide) (by decide)
      (by decide) (by decide) (by decide) (by decide) (by decide), k2 3 (by decide), k1 3 (by decide)]
  · rw [k6 4 (by decide), r5, runBlock_reg _ _ _ 4 u4.zero (by decide), k4' 4 (by decide) (by decide) (by decide)
      (by decide) (by decide) (by decide) (by decide) (by decide), k2 4 (by decide), k1 4 (by decide)]

/-! ## `α = x³ + ax + b` -/

/-- P-384's `a = p - 3` in Montgomery form, as the image stores it. -/
def p3A : Nat := 0xfffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffbfffffffc0000000000000003fffffffc

set_option exponentiation.threshold 600 in
theorem p3A_mont : p3A = (p384 - 3) * 2 ^ 384 % p384 := by unfold p3A p384; decide

set_option exponentiation.threshold 600 in
theorem p3A_lt : p3A < p384 := by unfold p3A p384; decide

set_option exponentiation.threshold 600 in
theorem curveA_val : dataVal p384CurveAData 0 12 = p3A := by unfold p3A; decide

/-- `x³ + ax + b` in Montgomery form, as `decompress` computes it from `x`'s
Montgomery form `X`. -/
def dqAlpha (X : Nat) : Nat := p3AddRes (p3AddRes (p3fm (p3fm X X) X) (p3fm p3A X)) p3B

theorem dqAlpha_lt (X : Nat) : dqAlpha X < p384 := by
  unfold dqAlpha
  rw [p3AddRes_mod (by rw [p3AddRes_mod (p3fm_lt _ _) (p3fm_lt _ _)]; exact Nat.mod_lt _ p384_pos) p3B_lt]
  exact Nat.mod_lt _ p384_pos

def dqB1 : List BInstr := [.aluImm .add a0 sp 0x62C, .aluImm .add a1 sp 0xA4, .aluImm .add a2 sp 0xA4, .aluImm .add (8 : Fin 32) sp 0x62C]
def dqB2 : List BInstr := [.aluImm .add a0 sp 0x2FC, .aluImm .add a1 sp 0x62C, .aluImm .add a2 sp 0xA4]
def dqB3 : List BInstr := [.lui a1 0x3FCC4000, .aluImm .add a1 a1 0x204, .aluImm .add a0 sp 0x62C, .aluImm .add a2 sp 0xA4]
def dqB4 : List BInstr := [.aluImm .add a0 sp 0x29C, .aluImm .add a1 sp 0x2FC, .aluImm .add a2 sp 0x62C]
def dqB5 : List BInstr := [.lui a2 0x3FCC4000, .aluImm .add a2 a2 0x234, .aluImm .add a0 sp 0x104, .aluImm .add a1 sp 0x29C]

theorem dqB1_end : blockEnd p384DecompressCode 0x76 dqB1 = some 0x82 := by decide
theorem dqB2_end : blockEnd p384DecompressCode 0x8A dqB2 = some 0x92 := by decide
theorem dqB3_end : blockEnd p384DecompressCode 0x9A dqB3 = some 0xA8 := by decide
theorem dqB4_end : blockEnd p384DecompressCode 0xB0 dqB4 = some 0xB8 := by decide
theorem dqB5_end : blockEnd p384DecompressCode 0xC0 dqB5 = some 0xCC := by decide

/-- The registers the field calls of `decompress` leave alone. -/
def fKeep (q : Fin 32) : Bool := q.val ∈ [2, 3, 4, 9, 18, 19, 20, 21, 22, 23, 24, 25, 26, 27]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 16000000 in
/-- **`α = x³ + ax + b`**, from 0x76 to 0xD4: three Montgomery products and
two sums, into `S + 0x104`. -/
theorem dq_stB {M : Word → BitVec 8} {n : Machine} {S : Word} (C : DqCode M) (D : DqData M) (F : DqFrame S)
    (s : St M DP n 0x76 (reg n)) (rsp : reg n sp = S) (hX : accV M (S + BitVec.ofNat 32 0xA4) 12 < p384) :
    ∃ n', Steps n n' ∧ St n'.mem DP n' 0xD4 (reg n') ∧ DqCode n'.mem ∧ DqData n'.mem ∧
      accV n'.mem (S + BitVec.ofNat 32 0x104) 12 = dqAlpha (accV M (S + BitVec.ofNat 32 0xA4) 12) ∧
      (∀ x, Sep (S + 0xFFFFFF10) 0xF0 x 1 → Sep (S + BitVec.ofNat 32 0x104) 48 x 1 →
        Sep (S + BitVec.ofNat 32 0x29C) 0x90 x 1 → Sep (S + BitVec.ofNat 32 0x62C) 48 x 1 → n'.mem x = M x) ∧
      ∀ q, fKeep q = true → reg n' q = reg n q := by
  have hz := s.zero
  have hSl := F.lo; have hSh := F.hi; have hSa := F.al
  have hbF : (S + 0xFFFFFF10).toNat = S.toNat - 0xF0 := F.below 0xF0 (by decide) (by decide)
  have hbA : (S + 0xFFFFFF4C).toNat = S.toNat - 0xB4 := F.below 0xB4 (by decide) (by decide)
  have sF : ∀ c, c + 48 ≤ 0xA50 → Sep (S + BitVec.ofNat 32 c) 48 (S + 0xFFFFFF10) 0xF0 := fun c h =>
    (sep_of_le (by rw [hbF, F.at c (by omega)]; omega) (by rw [F.at c (by omega)]; omega)).symm
  have sA : ∀ c, c + 48 ≤ 0xA50 → Sep (S + BitVec.ofNat 32 c) 48 (S + 0xFFFFFF4C) 0xB4 := fun c h =>
    (sep_of_le (by rw [hbA, F.at c (by omega)]; omega) (by rw [F.at c (by omega)]; omega)).symm
  have al : ∀ c, c + 4 ≤ 0xA50 → c % 4 = 0 → (S + BitVec.ofNat 32 c).toNat % 4 = 0 := fun c h1 h2 => by
    rw [F.at c (by omega)]; omega
  have hiF : ∀ x : Word, 0x40000000 ≤ x.toNat → Sep (S + 0xFFFFFF10) 0xF0 x 1 := fun x hx =>
    sep_of_le (by rw [hbF]; omega) (by have := x.isLt; omega)
  have hiA : ∀ x : Word, 0x40000000 ≤ x.toNat → Sep (S + 0xFFFFFF4C) 0xB4 x 1 := fun x hx =>
    sep_of_le (by rw [hbA]; omega) (by have := x.isLt; omega)
  -- a word of the frame that a call with result at `c` leaves alone
  have keepF : ∀ {Mx My : Word → BitVec 8} {c : Nat}, (∀ x, Sep (S + 0xFFFFFF10) 0xF0 x 1 →
      Sep (S + BitVec.ofNat 32 c) 48 x 1 → My x = Mx x) → ∀ d, d + 48 ≤ 0xA50 → c + 48 ≤ 0xA50 →
      (c + 48 ≤ d ∨ d + 48 ≤ c) → accV My (S + BitVec.ofNat 32 d) 12 = accV Mx (S + BitVec.ofNat 32 d) 12 :=
    fun {Mx My c} h d hd hc hcd => accV_congr2 12 fun i hi => memLoad32_congr fun q hq => by
      rw [add_ofNat_assoc, add_ofNat_assoc]
      exact h _ (sep_of_le (by rw [hbF, F.at _ (by omega)]; omega) (by rw [F.at _ (by omega)]; omega))
        (sepS S (by rcases hcd with h | h; exact .inl (by omega); exact .inr (by omega)) (by omega) (by omega))
  -- x²
  obtain ⟨n1, c1, u1⟩ := s.block dqB1 C.self dqB1_end ⟨trivial, trivial, trivial, trivial, trivial⟩
  have r1 : ∀ q, reg n1 q = (runBlock dqB1 (M, reg n)).2 q := fun q => by rw [u1.regs]
  obtain ⟨n2, c2, u2, v2, fr2, sp2, k2⟩ := dq_p3mul (out := S + BitVec.ofNat 32 0x62C) (xp := S + BitVec.ofNat 32 0xA4)
    (yp := S + BitVec.ofNat 32 0xA4) (⟨u1.pc, u1.mem, fun _ => rfl⟩ : St M DP n1 0x82 (reg n1)) C D F dp_at_82 dp_at_86
    (by decide) (by decide) (by rw [r1, runBlock_reg _ _ _ sp hz (by decide)]; exact rsp)
    (by rw [r1]; simp +decide only [runBlock, BInstr.run, dqB1, upd, ↓reduceIte]; rw [rsp]; rfl)
    (by rw [r1]; simp +decide only [runBlock, BInstr.run, dqB1, upd, ↓reduceIte]; rw [rsp]; rfl)
    (by rw [r1]; simp +decide only [runBlock, BInstr.run, dqB1, upd, ↓reduceIte]; rw [rsp]; rfl)
    (co := 0x62C) (by decide) rfl (by decide) (sF _ (by decide)) (al _ (by decide) (by decide)) (sF _ (by decide))
    (al _ (by decide) (by decide)) (by rw [limbVal_wordsAt]; exact hX)
  simp only [limbVal_wordsAt] at v2
  have h2 : ∀ x : Word, 0x40000000 ≤ x.toNat → n2.mem x = M x := fun x hx =>
    fr2 x (hiF x hx) (F.hiOut (by decide) hx)
  have C2 := C.hi h2
  have D2 : DqData n2.mem := D.of F fun x hx => fr2 x (by
      have := hx.sub (c := 0x1A0 - 0xF0) (l := 0xF0) (by decide)
      rwa [BitVec.add_assoc, show (0xFFFFFE60 : Word) + BitVec.ofNat 32 (0x1A0 - 0xF0) = 0xFFFFFF10 from rfl] at this)
    (by have := hx.sub (c := 0x1A0 + 0x62C) (l := 48) (by decide)
        rwa [BitVec.add_assoc, show (0xFFFFFE60 : Word) + BitVec.ofNat 32 (0x1A0 + 0x62C) = BitVec.ofNat 32 0x62C from rfl]
          at this)
  have kk2 : ∀ q : Fin 32, q.val ∈ [3, 4, 9, 18, 19, 20, 21, 22, 23, 24, 25, 26, 27] → reg n2 q = reg n q := fun q hq => by
    rw [k2 q (by revert hq; revert q; decide), r1, runBlock_reg _ _ _ q hz (by simp only [dqB1]; revert hq; revert q; decide)]
  have eX2 : accV n2.mem (S + BitVec.ofNat 32 0xA4) 12 = accV M (S + BitVec.ofNat 32 0xA4) 12 :=
    keepF fr2 0xA4 (by decide) (by decide) (.inr (by decide))
  -- x³
  obtain ⟨n3, c3, u3⟩ := u2.block dqB2 C2.self dqB2_end ⟨trivial, trivial, trivial, trivial⟩
  have r3 : ∀ q, reg n3 q = (runBlock dqB2 (n2.mem, reg n2)).2 q := fun q => by rw [u3.regs]
  obtain ⟨n4, c4, u4, v4, fr4, sp4, k4⟩ := dq_p3mul (out := S + BitVec.ofNat 32 0x2FC) (xp := S + BitVec.ofNat 32 0x62C)
    (yp := S + BitVec.ofNat 32 0xA4) (⟨u3.pc, u3.mem, fun _ => rfl⟩ : St n2.mem DP n3 0x92 (reg n3)) C2 D2 F dp_at_92
    dp_at_96 (by decide) (by decide) (by rw [r3, runBlock_reg _ _ _ sp u2.zero (by decide)]; exact sp2)
    (by rw [r3]; simp +decide only [runBlock, BInstr.run, dqB2, upd, ↓reduceIte]; rw [sp2]; rfl)
    (by rw [r3]; simp +decide only [runBlock, BInstr.run, dqB2, upd, ↓reduceIte]; rw [sp2]; rfl)
    (by rw [r3]; simp +decide only [runBlock, BInstr.run, dqB2, upd, ↓reduceIte]; rw [sp2]; rfl)
    (co := 0x2FC) (by decide) rfl (by decide) (sF _ (by decide)) (al _ (by decide) (by decide)) (sF _ (by decide))
    (al _ (by decide) (by decide)) (by rw [limbVal_wordsAt, eX2]; exact hX)
  simp only [limbVal_wordsAt] at v4
  rw [v2, eX2] at v4
  have C4 := C2.hi fun x hx => fr4 x (hiF x hx) (F.hiOut (by decide) hx)
  have D4 : DqData n4.mem := D2.of F fun x hx => fr4 x (by
      have := hx.sub (c := 0x1A0 - 0xF0) (l := 0xF0) (by decide)
      rwa [BitVec.add_assoc, show (0xFFFFFE60 : Word) + BitVec.ofNat 32 (0x1A0 - 0xF0) = 0xFFFFFF10 from rfl] at this)
    (by have := hx.sub (c := 0x1A0 + 0x2FC) (l := 48) (by decide)
        rwa [BitVec.add_assoc, show (0xFFFFFE60 : Word) + BitVec.ofNat 32 (0x1A0 + 0x2FC) = BitVec.ofNat 32 0x2FC from rfl]
          at this)
  have kk4 : ∀ q : Fin 32, q.val ∈ [3, 4, 9, 18, 19, 20, 21, 22, 23, 24, 25, 26, 27] → reg n4 q = reg n q := fun q hq => by
    rw [k4 q (by revert hq; revert q; decide), r3, runBlock_reg _ _ _ q u2.zero (by simp only [dqB2]; revert hq; revert q; decide), kk2 q hq]
  have eX4 : accV n4.mem (S + BitVec.ofNat 32 0xA4) 12 = accV M (S + BitVec.ofNat 32 0xA4) 12 := by
    rw [keepF fr4 0xA4 (by decide) (by decide) (.inr (by decide)), eX2]
  -- ax
  obtain ⟨n5, c5, u5⟩ := u4.block dqB3 C4.self dqB3_end ⟨trivial, trivial, trivial, trivial, trivial⟩
  have r5 : ∀ q, reg n5 q = (runBlock dqB3 (n4.mem, reg n4)).2 q := fun q => by rw [u5.regs]
  have hAv : accV n4.mem CURVEA 12 = p3A := by
    rw [show CURVEA = CURVEA + BitVec.ofNat 32 0 from (add_ofNat_zero _).symm, code_accV D4.ca 0 12 (by decide),
      curveA_val]
  obtain ⟨n6, c6, u6, v6, fr6, sp6, k6⟩ := dq_p3mul (out := S + BitVec.ofNat 32 0x62C) (xp := CURVEA)
    (yp := S + BitVec.ofNat 32 0xA4) (⟨u5.pc, u5.mem, fun _ => rfl⟩ : St n4.mem DP n5 0xA8 (reg n5)) C4 D4 F dp_at_a8
    dp_at_ac (by decide) (by decide) (by rw [r5, runBlock_reg _ _ _ sp u4.zero (by decide)]; exact sp4)
    (by rw [r5]; simp +decide only [runBlock, BInstr.run, dqB3, upd, ↓reduceIte]; rw [sp4]; rfl)
    (by rw [r5]; simp +decide only [runBlock, BInstr.run, dqB3, upd, ↓reduceIte]; try rfl)
    (by rw [r5]; simp +decide only [runBlock, BInstr.run, dqB3, upd, ↓reduceIte]; rw [sp4]; rfl)
    (co := 0x62C) (by decide) rfl (by decide) (F.lowData (c := 0xF0) (by decide) rfl (by decide) (by decide)).symm
    (by decide) (sF _ (by decide)) (al _ (by decide) (by decide)) (by rw [limbVal_wordsAt, eX4]; exact hX)
  simp only [limbVal_wordsAt] at v6
  rw [hAv, eX4] at v6
  have C6 := C4.hi fun x hx => fr6 x (hiF x hx) (F.hiOut (by decide) hx)
  have D6 : DqData n6.mem := D4.of F fun x hx => fr6 x (by
      have := hx.sub (c := 0x1A0 - 0xF0) (l := 0xF0) (by decide)
      rwa [BitVec.add_assoc, show (0xFFFFFE60 : Word) + BitVec.ofNat 32 (0x1A0 - 0xF0) = 0xFFFFFF10 from rfl] at this)
    (by have := hx.sub (c := 0x1A0 + 0x62C) (l := 48) (by decide)
        rwa [BitVec.add_assoc, show (0xFFFFFE60 : Word) + BitVec.ofNat 32 (0x1A0 + 0x62C) = BitVec.ofNat 32 0x62C from rfl]
          at this)
  have kk6 : ∀ q : Fin 32, q.val ∈ [3, 4, 9, 18, 19, 20, 21, 22, 23, 24, 25, 26, 27] → reg n6 q = reg n q := fun q hq => by
    rw [k6 q (by revert hq; revert q; decide), r5, runBlock_reg _ _ _ q u4.zero (by simp only [dqB3]; revert hq; revert q; decide), kk4 q hq]
  have e6x3 : accV n6.mem (S + BitVec.ofNat 32 0x2FC) 12 = p3fm (p3fm (accV M (S + BitVec.ofNat 32 0xA4) 12)
      (accV M (S + BitVec.ofNat 32 0xA4) 12)) (accV M (S + BitVec.ofNat 32 0xA4) 12) := by
    rw [keepF fr6 0x2FC (by decide) (by decide) (.inr (by decide)), v4]
  -- the frame of a sum, inside the products'
  have keepA : ∀ {Mx My : Word → BitVec 8} {c : Nat}, (∀ x, Sep (S + 0xFFFFFF4C) 0xB4 x 1 →
      Sep (S + BitVec.ofNat 32 c) 48 x 1 → My x = Mx x) → (∀ x, Sep (S + 0xFFFFFF10) 0xF0 x 1 →
      Sep (S + BitVec.ofNat 32 c) 48 x 1 → My x = Mx x) := fun h x hF hc => h x (by
        have := hF.sub (c := 0x3C) (l := 0xB4) (by decide)
        rwa [show S + 0xFFFFFF10 + BitVec.ofNat 32 0x3C = S + 0xFFFFFF4C by rw [BitVec.add_assoc]; rfl] at this) hc
  -- x³ + ax
  obtain ⟨n7, c7, u7⟩ := u6.block dqB4 C6.self dqB4_end ⟨trivial, trivial, trivial, trivial⟩
  have r7 : ∀ q, reg n7 q = (runBlock dqB4 (n6.mem, reg n6)).2 q := fun q => by rw [u7.regs]
  obtain ⟨n8, c8, u8, v8, fr8, sp8, k8⟩ := dq_p3add (out := S + BitVec.ofNat 32 0x29C) (lp := S + BitVec.ofNat 32 0x2FC)
    (rp := S + BitVec.ofNat 32 0x62C) (⟨u7.pc, u7.mem, fun _ => rfl⟩ : St n6.mem DP n7 0xB8 (reg n7)) C6 D6 F dp_at_b8
    dp_at_bc (by decide) (by decide) (by rw [r7, runBlock_reg _ _ _ sp u6.zero (by decide)]; exact sp6)
    (by rw [r7]; simp +decide only [runBlock, BInstr.run, dqB4, upd, ↓reduceIte]; rw [sp6]; rfl)
    (by rw [r7]; simp +decide only [runBlock, BInstr.run, dqB4, upd, ↓reduceIte]; rw [sp6]; rfl)
    (by rw [r7]; simp +decide only [runBlock, BInstr.run, dqB4, upd, ↓reduceIte]; rw [sp6]; rfl)
    (co := 0x29C) (by decide) rfl (by decide) (sA _ (by decide)) (al _ (by decide) (by decide)) (sA _ (by decide))
    (al _ (by decide) (by decide))
  simp only [limbVal_wordsAt] at v8
  rw [e6x3, v6] at v8
  have fr8' := keepA fr8
  have C8 := C6.hi fun x hx => fr8 x (hiA x hx) (F.hiOut (by decide) hx)
  have D8 : DqData n8.mem := D6.of F fun x hx => fr8' x (by
      have := hx.sub (c := 0x1A0 - 0xF0) (l := 0xF0) (by decide)
      rwa [BitVec.add_assoc, show (0xFFFFFE60 : Word) + BitVec.ofNat 32 (0x1A0 - 0xF0) = 0xFFFFFF10 from rfl] at this)
    (by have := hx.sub (c := 0x1A0 + 0x29C) (l := 48) (by decide)
        rwa [BitVec.add_assoc, show (0xFFFFFE60 : Word) + BitVec.ofNat 32 (0x1A0 + 0x29C) = BitVec.ofNat 32 0x29C from rfl]
          at this)
  have kk8 : ∀ q : Fin 32, q.val ∈ [3, 4, 9, 18, 19, 20, 21, 22, 23, 24, 25, 26, 27] → reg n8 q = reg n q := fun q hq => by
    rw [k8 q (by revert hq; revert q; decide) (by revert hq; revert q; decide) (by revert hq; revert q; decide)
      (by revert hq; revert q; decide) (by revert hq; revert q; decide) (by revert hq; revert q; decide)
      (by revert hq; revert q; decide) (by revert hq; revert q; decide) (by revert hq; revert q; decide)
      (by revert hq; revert q; decide) (by revert hq; revert q; decide), r7,
      runBlock_reg _ _ _ q u6.zero (by simp only [dqB4]; revert hq; revert q; decide), kk6 q hq]
  -- + b
  obtain ⟨n9, c9, u9⟩ := u8.block dqB5 C8.self dqB5_end ⟨trivial, trivial, trivial, trivial, trivial⟩
  have r9 : ∀ q, reg n9 q = (runBlock dqB5 (n8.mem, reg n8)).2 q := fun q => by rw [u9.regs]
  obtain ⟨n10, c10, u10, v10, fr10, sp10, k10⟩ := dq_p3add (out := S + BitVec.ofNat 32 0x104)
    (lp := S + BitVec.ofNat 32 0x29C) (rp := p3bA) (⟨u9.pc, u9.mem, fun _ => rfl⟩ : St n8.mem DP n9 0xCC (reg n9)) C8 D8 F
    dp_at_cc dp_at_d0 (by decide) (by decide) (by rw [r9, runBlock_reg _ _ _ sp u8.zero (by decide)]; exact sp8)
    (by rw [r9]; simp +decide only [runBlock, BInstr.run, dqB5, upd, ↓reduceIte]; rw [sp8]; rfl)
    (by rw [r9]; simp +decide only [runBlock, BInstr.run, dqB5, upd, ↓reduceIte]; rw [sp8]; rfl)
    (by rw [r9]; simp +decide only [runBlock, BInstr.run, dqB5, upd, ↓reduceIte]; try rfl)
    (co := 0x104) (by decide) rfl (by decide) (sA _ (by decide)) (al _ (by decide) (by decide))
    (F.lowData (c := 0xB4) (by decide) rfl (by decide) (by decide)).symm (by decide)
  rw [p3B_val D8.cb, limbVal_wordsAt, limbVal_wordsAt, v8] at v10
  have fr10' := keepA fr10
  refine ⟨n10, c1.trans (c2.trans (c3.trans (c4.trans (c5.trans (c6.trans (c7.trans (c8.trans (c9.trans c10)))))))),
    u10, C8.hi fun x hx => fr10 x (hiA x hx) (F.hiOut (by decide) hx),
    D8.of F fun x hx => fr10' x (by
      have := hx.sub (c := 0x1A0 - 0xF0) (l := 0xF0) (by decide)
      rwa [BitVec.add_assoc, show (0xFFFFFE60 : Word) + BitVec.ofNat 32 (0x1A0 - 0xF0) = 0xFFFFFF10 from rfl] at this)
    (by have := hx.sub (c := 0x1A0 + 0x104) (l := 48) (by decide)
        rwa [BitVec.add_assoc, show (0xFFFFFE60 : Word) + BitVec.ofNat 32 (0x1A0 + 0x104) = BitVec.ofNat 32 0x104 from rfl]
          at this), v10, fun x hF h104 h29C h62C => ?_, fun q hq => ?_⟩
  · have h29C48 : Sep (S + BitVec.ofNat 32 0x29C) 48 x 1 := by
      have := h29C.sub (c := 0) (l := 48) (by decide); rwa [add_ofNat_zero] at this
    have h2FC : Sep (S + BitVec.ofNat 32 0x2FC) 48 x 1 := by
      have := h29C.sub (c := 0x60) (l := 48) (by decide); rwa [add_ofNat_assoc] at this
    rw [fr10' x hF h104, fr8' x hF h29C48, fr6 x hF h62C, fr4 x hF h2FC, fr2 x hF h62C]
  · by_cases hs : q = sp
    · subst hs; rw [sp10, rsp]
    · rw [k10 q (by revert hs hq; revert q; decide) (by revert hq; revert q; decide) (by revert hq; revert q; decide)
        (by revert hq; revert q; decide) (by revert hq; revert q; decide) (by revert hq; revert q; decide)
        (by revert hq; revert q; decide) (by revert hq; revert q; decide) (by revert hq; revert q; decide)
        (by revert hq; revert q; decide) (by revert hq; revert q; decide), r9,
        runBlock_reg _ _ _ q u8.zero (by simp only [dqB5]; revert hq; revert q; decide), kk8 q (by revert hs hq; revert q; decide)]

/-! ## Copying the constants -/

def dqC1 : List BInstr :=
  [.aluImm .add a0 sp 0x134, .lui (24 : Fin 32) 0x3FCC5000, .aluImm .add (24 : Fin 32) (24 : Fin 32) 0xFFFFFC8C,
   .aluImm .add a2 x0 0x9C, .alu .add a1 x0 (24 : Fin 32)]
def dqC2 : List BInstr :=
  [.aluImm .add (9 : Fin 32) x0 0x180, .alu .sub (18 : Fin 32) (9 : Fin 32) (8 : Fin 32), .aluImm .add a0 sp 0x29C,
   .aluImm .add a1 sp 0x104, .aluImm .add a2 x0 0x30]
def dqC3 : List BInstr :=
  [.aluImm .add a0 sp 0x2CC, .lui (22 : Fin 32) 0x3FCC5000, .aluImm .add (22 : Fin 32) (22 : Fin 32) 0xFFFFFE2C,
   .aluImm .add a2 x0 0x30, .alu .add a1 x0 (22 : Fin 32)]

theorem dqC1_end : blockEnd p384DecompressCode 0xD4 dqC1 = some 0xE4 := by decide
theorem dqC2_end : blockEnd p384DecompressCode 0x14C dqC2 = some 0x15C := by decide
theorem dqC3_end : blockEnd p384DecompressCode 0x164 dqC3 = some 0x174 := by decide

/-- The 16 bytes below `S` that `memcpy` uses, apart from the code and the frame. -/
theorem DqFrame.mc {S : Word} (F : DqFrame S) :
    (S + 0xFFFFFFF0).toNat % 4 = 0 ∧ (S + 0xFFFFFFF0).toNat + 16 ≤ 2 ^ 32 ∧
      Sep (S + 0xFFFFFFF0) 16 (MCS + 8) memcpyBodyCode.length ∧
      (∀ c, c + 48 ≤ 0xA50 → Sep (S + BitVec.ofNat 32 c) 48 (S + 0xFFFFFFF0) 16) := by
  have hb16 : (S + 0xFFFFFFF0).toNat = S.toNat - 16 := F.below 16 (by decide) (by decide)
  have := F.lo; have := F.hi; have := F.al
  refine ⟨by rw [hb16]; omega, by rw [hb16]; omega,
    sep_of_le (by rw [hb16, show (MCS + 8).toNat = 0x403b4856 from rfl]; omega) (by decide), fun c hc => ?_⟩
  exact (sep_of_le (by rw [hb16, F.at c (by omega)]; omega) (by rw [F.at c (by omega)]; omega)).symm

theorem DqFrame.mcN {S : Word} (F : DqFrame S) {c n : Nat} (h : c + n ≤ 0xA50) :
    Sep (S + BitVec.ofNat 32 c) n (S + 0xFFFFFFF0) 16 := by
  have hb16 : (S + 0xFFFFFFF0).toNat = S.toNat - 16 := F.below 16 (by decide) (by decide)
  have := F.lo; have := F.hi
  exact (sep_of_le (by rw [hb16, F.at c (by omega)]; omega) (by rw [F.at c (by omega)]; omega)).symm

set_option maxRecDepth 100000 in
set_option maxHeartbeats 16000000 in
/-- **Copying the constants**, from 0xD4 to 0x19E: the parameters to
`S + 0x134`, `α` to `S + 0x29C`, and the exponent to `S + 0x2CC`; the
exponent's bit width 382 to `s2`. -/
theorem dq_stC {M : Word → BitVec 8} {n : Machine} {S : Word} (C : DqCode M) (D : DqData M) (F : DqFrame S)
    (s : St M DP n 0xD4 (reg n)) (rsp : reg n sp = S) :
    ∃ n', Steps n n' ∧ St n'.mem DP n' 0x19E (reg n') ∧ DqCode n'.mem ∧ DqData n'.mem ∧
      memLoad32 n'.mem (S + BitVec.ofNat 32 0x134) = 0xFFFFFFFF ∧ accV n'.mem (S + BitVec.ofNat 32 0x134) 12 = p384 ∧
      accV n'.mem (S + BitVec.ofNat 32 0x29C) 12 = accV M (S + BitVec.ofNat 32 0x104) 12 ∧
      reg n' (24 : Fin 32) = PARAMS ∧ reg n' (18 : Fin 32) = 0x17E ∧ reg n' (22 : Fin 32) = EXPA ∧
      (∀ x, Sep (S + 0xFFFFFFF0) 16 x 1 → Sep (S + BitVec.ofNat 32 0x134) 0x9C x 1 →
        Sep (S + BitVec.ofNat 32 0x29C) 0x60 x 1 → Sep (S + BitVec.ofNat 32 0x62C) 4 x 1 → n'.mem x = M x) ∧
      ∀ q : Fin 32, q.val ∈ [2, 3, 4, 19, 20, 21, 25] → reg n' q = reg n q := by
  have hz := s.zero
  have hSl := F.lo; have hSh := F.hi; have hSa := F.al
  obtain ⟨fA, fW, hFC, b16⟩ := F.mc
  have hb16 : (S + 0xFFFFFFF0).toNat = S.toNat - 16 := F.below 16 (by decide) (by decide)
  have lo16 : ∀ x : Word, 0x40000000 ≤ x.toNat → Sep (S + 0xFFFFFFF0) 16 x 1 := fun x hx =>
    sep_of_le (by rw [hb16]; omega) (by have := x.isLt; omega)
  have l16 : ∀ d, d + 4 ≤ 0xA50 → Sep (S + 0xFFFFFFF0) 16 (S + BitVec.ofNat 32 d) 4 := fun d hd =>
    sep_of_le (by rw [hb16, F.at d (by omega)]; omega) (by rw [F.at d (by omega)]; omega)
  have l16b : ∀ d, d + 1 ≤ 0xA50 → Sep (S + 0xFFFFFFF0) 16 (S + BitVec.ofNat 32 d) 1 := fun d hd =>
    sep_of_le (by rw [hb16, F.at d (by omega)]; omega) (by rw [F.at d (by omega)]; omega)
  have toData : ∀ {Mx My : Word → BitVec 8} {cs : List Nat}, (∀ x, Sep (S + 0xFFFFFE60) 0xBF0 x 1 → My x = Mx x) →
      DqData Mx → DqData My := fun h Dx => Dx.of F h
  have inFrame : ∀ {c l : Nat} {x : Word}, c + l ≤ 0xA50 → Sep (S + 0xFFFFFE60) 0xBF0 x 1 →
      Sep (S + BitVec.ofNat 32 c) l x 1 := fun {c l x} h hx => by
    have := hx.sub (c := 0x1A0 + c) (l := l) (by omega)
    rwa [BitVec.add_assoc, show (0xFFFFFE60 : Word) + BitVec.ofNat 32 (0x1A0 + c) = BitVec.ofNat 32 c by
      apply BitVec.eq_of_toNat_eq
      rw [BitVec.toNat_add, BitVec.toNat_ofNat, BitVec.toNat_ofNat, show (0xFFFFFE60 : Word).toNat = 0xFFFFFE60 from rfl]
      omega] at this
  have below16 : ∀ {x : Word}, Sep (S + 0xFFFFFE60) 0xBF0 x 1 → Sep (S + 0xFFFFFFF0) 16 x 1 := fun {x} hx => by
    have := hx.sub (c := 0x190) (l := 16) (by decide)
    rwa [show S + 0xFFFFFE60 + BitVec.ofNat 32 0x190 = S + 0xFFFFFFF0 by rw [BitVec.add_assoc]; rfl] at this
  -- the parameters
  obtain ⟨n1, c1, u1⟩ := s.block dqC1 C.self dqC1_end ⟨trivial, trivial, trivial, trivial, trivial, trivial⟩
  have r1 : ∀ q, reg n1 q = (runBlock dqC1 (M, reg n)).2 q := fun q => by rw [u1.regs]
  have e24 : reg n1 (24 : Fin 32) = PARAMS := by
    rw [r1]; simp +decide only [runBlock, BInstr.run, dqC1, upd, ↓reduceIte]; try rfl
  obtain ⟨n2, c2, u2, fr2, k2⟩ := dq_memcpy (dst := S + BitVec.ofNat 32 0x134) (src := PARAMS) (S := S) (N := 0x9C)
    (⟨u1.pc, u1.mem, fun _ => rfl⟩ : St M DP n1 0xE4 (reg n1)) C dp_at_e4 dp_at_e8 (by decide) (by decide)
    (by rw [r1, runBlock_reg _ _ _ sp hz (by decide)]; exact rsp)
    (by rw [r1]; simp +decide only [runBlock, BInstr.run, dqC1, upd, ↓reduceIte]; rw [rsp]; rfl)
    (by rw [r1]; simp +decide only [runBlock, BInstr.run, dqC1, upd, ↓reduceIte]; try rfl)
    (by rw [r1]; simp +decide only [runBlock, BInstr.run, dqC1, upd, ↓reduceIte]; (try rw [hz]); try rfl)
    ⟨C.body, F.sepHi (by decide) (by decide) (by decide), hFC, F.mcN (by decide),
      (F.lowData (c := 16) (by decide) rfl (by decide) (by decide)).symm, F.bufData (by decide) (by decide) (by decide),
      fA, fW, by rw [F.at _ (by decide)]; omega, by decide⟩
  have fr2' : ∀ x, Sep (S + 0xFFFFFFF0) 16 x 1 → Sep (S + BitVec.ofNat 32 0x134) 0x9C x 1 → n2.mem x = M x :=
    fun x a b => by rw [fr2 x a, copyBytes_sep b (Nat.le_refl _)]
  have C2 := C.hi fun x hx => fr2' x (lo16 x hx) (F.hiOut (by decide) hx)
  have D2 : DqData n2.mem := D.of F fun x hx => fr2' x (below16 hx) (inFrame (by decide) hx)
  have hP : ∀ i, i < 12 → memLoad32 n2.mem (S + BitVec.ofNat 32 0x134 + BitVec.ofNat 32 (4 * i)) =
      memLoad32 M (PARAMS + BitVec.ofNat 32 (4 * i)) := fun i hi => by
    rw [load_frame fr2 (by rw [add_ofNat_assoc]; exact l16 _ (by omega)), cp_word (by omega) (by decide)]
  have kk2 : ∀ q : Fin 32, q.val ∈ [2, 3, 4, 8, 9, 18, 19, 20, 21, 22, 23, 25, 26, 27] → reg n2 q = reg n q := fun q hq => by
    rw [k2 q (by revert hq; revert q; decide) (by revert hq; revert q; decide) (by revert hq; revert q; decide)
      (by revert hq; revert q; decide) (by revert hq; revert q; decide) (by revert hq; revert q; decide)
      (by revert hq; revert q; decide) (by revert hq; revert q; decide) (by revert hq; revert q; decide)
      (by revert hq; revert q; decide) (by revert hq; revert q; decide) (by revert hq; revert q; decide)
      (by revert hq; revert q; decide) (by revert hq; revert q; decide) (by revert hq; revert q; decide)]
    rw [r1, runBlock_reg _ _ _ q hz (by simp only [dqC1]; revert hq; revert q; decide)]
  have e224 : reg n2 (24 : Fin 32) = PARAMS := by
    rw [k2 24 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
      (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide), e24]
  -- the bit width
  obtain ⟨n3, c3, u3, C3, fr3, e38, k3⟩ := dq_lz C2 F u2 (by rw [kk2 sp (by decide)]; exact rsp)
  have k3' : ∀ q : Fin 32, q.val ∈ [2, 3, 4, 9, 18, 19, 20, 21, 22, 23, 25, 26, 27] → reg n3 q = reg n q := fun q hq => by
    rw [k3 q (by revert hq; revert q; decide) (by revert hq; revert q; decide) (by revert hq; revert q; decide)
      (by revert hq; revert q; decide) (by revert hq; revert q; decide) (by revert hq; revert q; decide),
      kk2 q (by revert hq; revert q; decide)]
  have D3 : DqData n3.mem := D2.of F fun x hx => fr3 x (inFrame (by decide) hx)
  have e324 : reg n3 (24 : Fin 32) = PARAMS := by
    rw [k3 24 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide), e224]
  -- copy α
  obtain ⟨n4, c4, u4⟩ := u3.block dqC2 C3.self dqC2_end ⟨trivial, trivial, trivial, trivial, trivial, trivial⟩
  have r4 : ∀ q, reg n4 q = (runBlock dqC2 (n3.mem, reg n3)).2 q := fun q => by rw [u4.regs]
  have sp3 : reg n3 sp = S := by rw [k3' sp (by decide)]; exact rsp
  obtain ⟨n5, c5, u5, fr5, k5⟩ := dq_memcpy (dst := S + BitVec.ofNat 32 0x29C) (src := S + BitVec.ofNat 32 0x104)
    (S := S) (N := 48) (⟨u4.pc, u4.mem, fun _ => rfl⟩ : St n3.mem DP n4 0x15C (reg n4)) C3 dp_at_15c dp_at_160
    (by decide) (by decide) (by rw [r4, runBlock_reg _ _ _ sp u3.zero (by decide)]; exact sp3)
    (by rw [r4]; simp +decide only [runBlock, BInstr.run, dqC2, upd, ↓reduceIte]; rw [sp3]; rfl)
    (by rw [r4]; simp +decide only [runBlock, BInstr.run, dqC2, upd, ↓reduceIte]; rw [sp3]; rfl)
    (by rw [r4]; simp +decide only [runBlock, BInstr.run, dqC2, upd, ↓reduceIte]; (try rw [u3.zero]); try rfl)
    ⟨C3.body, F.sepHi (by decide) (by decide) (by decide), hFC, F.mcN (by decide), F.mcN (by decide),
      sepS S (.inr (by decide)) (by decide) (by decide), fA, fW, by rw [F.at _ (by decide)]; omega,
      by rw [F.at _ (by decide)]; omega⟩
  have fr5' : ∀ x, Sep (S + 0xFFFFFFF0) 16 x 1 → Sep (S + BitVec.ofNat 32 0x29C) 48 x 1 → n5.mem x = n3.mem x :=
    fun x a b => by rw [fr5 x a, copyBytes_sep b (Nat.le_refl _)]
  have C5 := C3.hi fun x hx => fr5' x (lo16 x hx) (F.hiOut (by decide) hx)
  have D5 : DqData n5.mem := D3.of F fun x hx => fr5' x (below16 hx) (inFrame (by decide) hx)
  have hA : accV n5.mem (S + BitVec.ofNat 32 0x29C) 12 = accV n3.mem (S + BitVec.ofNat 32 0x104) 12 :=
    accV_congr2 12 fun i hi => by
      rw [load_frame fr5 (by rw [add_ofNat_assoc]; exact l16 _ (by omega)), cp_word (by omega) (by decide)]
  have k5' : ∀ q : Fin 32, q.val ∈ [2, 3, 4, 8, 19, 20, 21, 22, 23, 24, 25, 26, 27] → reg n5 q = reg n3 q := fun q hq => by
    rw [k5 q (by revert hq; revert q; decide) (by revert hq; revert q; decide) (by revert hq; revert q; decide)
      (by revert hq; revert q; decide) (by revert hq; revert q; decide) (by revert hq; revert q; decide)
      (by revert hq; revert q; decide) (by revert hq; revert q; decide) (by revert hq; revert q; decide)
      (by revert hq; revert q; decide) (by revert hq; revert q; decide) (by revert hq; revert q; decide)
      (by revert hq; revert q; decide) (by revert hq; revert q; decide) (by revert hq; revert q; decide), r4,
      runBlock_reg _ _ _ q u3.zero (by simp only [dqC2]; revert hq; revert q; decide)]
  have e518 : reg n5 (18 : Fin 32) = 0x17E := by
    rw [k5 18 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
      (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide), r4]
    simp +decide only [runBlock, BInstr.run, dqC2, upd, ↓reduceIte]; rw [e38, u3.zero]; rfl
  have e59 : reg n5 (9 : Fin 32) = 0x180 := by
    rw [k5 9 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
      (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide), r4]
    simp +decide only [runBlock, BInstr.run, dqC2, upd, ↓reduceIte]; (try rw [u3.zero]); try rfl
  -- copy the exponent
  obtain ⟨n6, c6, u6⟩ := u5.block dqC3 C5.self dqC3_end ⟨trivial, trivial, trivial, trivial, trivial, trivial⟩
  have r6 : ∀ q, reg n6 q = (runBlock dqC3 (n5.mem, reg n5)).2 q := fun q => by rw [u6.regs]
  have sp5 : reg n5 sp = S := by rw [k5' sp (by decide)]; exact sp3
  obtain ⟨n7, c7, u7, fr7, k7⟩ := dq_memcpy (dst := S + BitVec.ofNat 32 0x2CC) (src := EXPA) (S := S) (N := 48)
    (⟨u6.pc, u6.mem, fun _ => rfl⟩ : St n5.mem DP n6 0x174 (reg n6)) C5 dp_at_174 dp_at_178 (by decide) (by decide)
    (by rw [r6, runBlock_reg _ _ _ sp u5.zero (by decide)]; exact sp5)
    (by rw [r6]; simp +decide only [runBlock, BInstr.run, dqC3, upd, ↓reduceIte]; rw [sp5]; rfl)
    (by rw [r6]; simp +decide only [runBlock, BInstr.run, dqC3, upd, ↓reduceIte]; try rfl)
    (by rw [r6]; simp +decide only [runBlock, BInstr.run, dqC3, upd, ↓reduceIte]; (try rw [u5.zero]); try rfl)
    ⟨C5.body, F.sepHi (by decide) (by decide) (by decide), hFC, F.mcN (by decide),
      (F.lowData (c := 16) (by decide) rfl (by decide) (by decide)).symm, F.bufData (by decide) (by decide) (by decide),
      fA, fW, by rw [F.at _ (by decide)]; omega, by decide⟩
  have fr7' : ∀ x, Sep (S + 0xFFFFFFF0) 16 x 1 → Sep (S + BitVec.ofNat 32 0x2CC) 48 x 1 → n7.mem x = n5.mem x :=
    fun x a b => by rw [fr7 x a, copyBytes_sep b (Nat.le_refl _)]
  have C7 := C5.hi fun x hx => fr7' x (lo16 x hx) (F.hiOut (by decide) hx)
  have D7 : DqData n7.mem := D5.of F fun x hx => fr7' x (below16 hx) (inFrame (by decide) hx)
  have k7' : ∀ q : Fin 32, q.val ∈ [2, 3, 4, 8, 9, 18, 19, 20, 21, 23, 24, 25, 26, 27] → reg n7 q = reg n5 q := fun q hq => by
    rw [k7 q (by revert hq; revert q; decide) (by revert hq; revert q; decide) (by revert hq; revert q; decide)
      (by revert hq; revert q; decide) (by revert hq; revert q; decide) (by revert hq; revert q; decide)
      (by revert hq; revert q; decide) (by revert hq; revert q; decide) (by revert hq; revert q; decide)
      (by revert hq; revert q; decide) (by revert hq; revert q; decide) (by revert hq; revert q; decide)
      (by revert hq; revert q; decide) (by revert hq; revert q; decide) (by revert hq; revert q; decide), r6,
      runBlock_reg _ _ _ q u5.zero (by simp only [dqC3]; revert hq; revert q; decide)]
  -- the two tests the constant exponent passes
  obtain ⟨n8, d8, u8⟩ := u7.taken C7.self 0x184 dp_at_17c (by decide) (by
    show branchTaken .bltu (reg n7 (18 : Fin 32)) (reg n7 (9 : Fin 32)) = true
    rw [k7' 18 (by decide), k7' 9 (by decide), e518, e59]; decide)
  obtain ⟨n9, d9, u9⟩ := u8.self.aluImm C7.self dp_at_184 (off' := 0x188) (by decide)
  obtain ⟨n10, d10, u10⟩ := u9.self.taken C7.self 0x19E dp_at_188 (by decide) (by
    show branchTaken .bne (reg n9 a0) (reg n9 x0) = true
    rw [u9.regs]; simp +decide only [upd, ↓reduceIte]
    rw [u8.regs, k7' 8 (by decide), k5' 8 (by decide), e38, u9.self.zero]; decide)
  have g10 : ∀ q, q ≠ a0 → reg n10 q = reg n7 q := fun q h => by rw [u10.regs, u9.regs, updz u8.self.zero h, u8.regs]
  refine ⟨n10, c1.trans (c2.trans (c3.trans (c4.trans (c5.trans (c6.trans (c7.trans (.cons d8 (.cons d9
    (.single d10))))))))), ⟨u10.pc, by rw [u10.mem], fun _ => rfl⟩,
    by rw [u10.mem]; exact C7, by rw [u10.mem]; exact D7, ?_, ?_, ?_,
    by rw [g10 24 (by decide), k7' 24 (by decide), k5' 24 (by decide), e324],
    by rw [g10 18 (by decide), k7' 18 (by decide), e518], ?_, fun x h16 h134 h29C h62C => ?_, fun q hq => ?_⟩
  · rw [u10.mem]
    have := hP 0 (by decide)
    rw [Nat.mul_zero, add_ofNat_zero, add_ofNat_zero] at this
    rw [show memLoad32 n7.mem (S + BitVec.ofNat 32 0x134) = memLoad32 n2.mem (S + BitVec.ofNat 32 0x134) from
      memLoad32_congr fun q hq => by
        rw [add_ofNat_assoc]
        rw [fr7' _ (l16b _ (by omega))
          (sepS S (.inr (by omega)) (by decide) (by omega)),
          fr5' _ (l16b _ (by omega))
          (sepS S (.inr (by omega)) (by decide) (by omega)),
          fr3 _ (sepS S (.inr (by omega)) (by decide) (by omega))], this, D.N0]
  · rw [u10.mem, ← D.N]
    refine accV_congr2 12 fun i hi => ?_
    rw [← hP i hi]
    refine memLoad32_congr fun q hq => ?_
    rw [add_ofNat_assoc, add_ofNat_assoc]
    rw [fr7' _ (l16b _ (by omega))
        (sepS S (.inr (by omega)) (by decide) (by omega)),
      fr5' _ (l16b _ (by omega))
        (sepS S (.inr (by omega)) (by decide) (by omega)),
      fr3 _ (sepS S (.inr (by omega)) (by decide) (by omega))]
  · rw [u10.mem]
    have e7 : accV n7.mem (S + BitVec.ofNat 32 0x29C) 12 = accV n5.mem (S + BitVec.ofNat 32 0x29C) 12 :=
      accV_congr2 12 fun i hi => memLoad32_congr fun q hq => by
        rw [add_ofNat_assoc, add_ofNat_assoc]
        exact fr7' _ (l16b _ (by omega))
          (sepS S (.inr (by omega)) (by decide) (by omega))
    rw [e7, hA]
    exact accV_congr2 12 fun i hi => memLoad32_congr fun q hq => by
      rw [add_ofNat_assoc, add_ofNat_assoc]
      rw [fr3 _ (sepS S (.inr (by omega)) (by decide) (by omega)),
        fr2' _ (l16b _ (by omega))
          (sepS S (.inr (by omega)) (by decide) (by omega))]
  · rw [g10 22 (by decide), k7 22 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
      (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide), r6]
    simp +decide only [runBlock, BInstr.run, dqC3, upd, ↓reduceIte]; try rfl
  · have h29C48 : Sep (S + BitVec.ofNat 32 0x29C) 48 x 1 := by
      have := h29C.sub (c := 0) (l := 48) (by decide); rwa [add_ofNat_zero] at this
    have h2CC : Sep (S + BitVec.ofNat 32 0x2CC) 48 x 1 := by
      have := h29C.sub (c := 0x30) (l := 48) (by decide); rwa [add_ofNat_assoc] at this
    rw [u10.mem, fr7' x h16 h2CC, fr5' x h16 h29C48, fr3 x h62C, fr2' x h16 h134]
  · rw [g10 q (by revert hq; revert q; decide), k7' q (by revert hq; revert q; decide), k5' q (by revert hq; revert q; decide),
      k3' q (by revert hq; revert q; decide)]

/-! ## Starting the table -/

def dqE0 : List BInstr := [.aluImm .add (8 : Fin 32) sp 0x2FC, .aluImm .add (9 : Fin 32) x0 0x10]
def dqE1 : List BInstr :=
  [.sw sp (19 : Fin 32) 0x18, .aluImm .add a0 sp 0x62C, .aluImm .add a1 sp 0x2FC, .aluImm .add a2 x0 0x300,
   .aluImm .add (9 : Fin 32) sp 0x62C]
def dqE2 : List BInstr := [.aluImm .add a0 sp 0x7FF, .aluImm .add a0 a0 0x12D, .aluImm .add a2 x0 0x30, .aluImm .add a1 x0 0x0]
def dqE3 : List BInstr := [.aluImm .add a0 sp 0x2FC, .aluImm .add a1 sp 0x62C, .aluImm .add a2 x0 0x330]
def dqE4 : List BInstr :=
  [.aluImm .add (19 : Fin 32) sp 0x65C, .aluImm .add (8 : Fin 32) x0 0x10, .aluImm .add (24 : Fin 32) (24 : Fin 32) 0x30]
def dqE5 : List BInstr := [.aluImm .add a1 sp 0x104, .aluImm .add a2 x0 0x30, .alu .add a0 x0 (19 : Fin 32)]

theorem dqE0_end : blockEnd p384DecompressCode 0x19E dqE0 = some 0x1A2 := by decide
theorem dqE1_end : blockEnd p384DecompressCode 0x1BC dqE1 = some 0x1CC := by decide
theorem dqE2_end : blockEnd p384DecompressCode 0x1D4 dqE2 = some 0x1E2 := by decide
theorem dqE3_end : blockEnd p384DecompressCode 0x1EA dqE3 = some 0x1F4 := by decide
theorem dqE4_end : blockEnd p384DecompressCode 0x1FC dqE4 = some 0x206 := by decide
theorem dqE5_end : blockEnd p384DecompressCode 0x220 dqE5 = some 0x228 := by decide

set_option maxRecDepth 100000 in
set_option maxHeartbeats 16000000 in
/-- **Starting the table**, from 0x19E to the table loop at 0x230: entry 0
of the table at `S + 0x62C` is 1 and entry 1 is `α`, in Montgomery form. -/
theorem dq_stD {M : Word → BitVec 8} {n : Machine} {S : Word} (C : DqCode M) (D : DqData M) (F : DqFrame S)
    (s : St M DP n 0x19E (reg n)) (rsp : reg n sp = S) (r24 : reg n (24 : Fin 32) = PARAMS)
    (hA : accV M (S + BitVec.ofNat 32 0x104) 12 < p384) :
    ∃ n', Steps n n' ∧ St n'.mem DP n' 0x230 (reg n') ∧ DqCode n'.mem ∧ DqData n'.mem ∧
      (∀ j, j ≤ 1 → accV n'.mem (S + BitVec.ofNat 32 (0x62C + 48 * j)) 12 = mpow (accV M (S + BitVec.ofNat 32 0x104) 12) j) ∧
      memLoad32 n'.mem (S + BitVec.ofNat 32 0x18) = reg n (19 : Fin 32) ∧
      reg n' (19 : Fin 32) = S + BitVec.ofNat 32 0x65C ∧ reg n' (24 : Fin 32) = PARAMS + 0x30 ∧
      (∀ x, Sep (S + 0xFFFFFFF0) 16 x 1 → Sep (S + BitVec.ofNat 32 0x18) 4 x 1 →
        Sep (S + BitVec.ofNat 32 0x2FC) 0x660 x 1 → n'.mem x = M x) ∧
      ∀ q : Fin 32, q.val ∈ [2, 3, 4, 18, 20, 21, 22, 23, 25, 26, 27] → reg n' q = reg n q := by
  have hz := s.zero
  have hSl := F.lo; have hSh := F.hi; have hSa := F.al
  obtain ⟨fA, fW, hFC, b16⟩ := F.mc
  have hb16 : (S + 0xFFFFFFF0).toNat = S.toNat - 16 := F.below 16 (by decide) (by decide)
  have lo16 : ∀ x : Word, 0x40000000 ≤ x.toNat → Sep (S + 0xFFFFFFF0) 16 x 1 := fun x hx =>
    sep_of_le (by rw [hb16]; omega) (by have := x.isLt; omega)
  have l16b : ∀ d, d + 1 ≤ 0xA50 → Sep (S + 0xFFFFFFF0) 16 (S + BitVec.ofNat 32 d) 1 := fun d hd =>
    sep_of_le (by rw [hb16, F.at d (by omega)]; omega) (by rw [F.at d (by omega)]; omega)
  have inFrame : ∀ {c l : Nat} {x : Word}, c + l ≤ 0xA50 → Sep (S + 0xFFFFFE60) 0xBF0 x 1 →
      Sep (S + BitVec.ofNat 32 c) l x 1 := fun {c l x} h hx => by
    have := hx.sub (c := 0x1A0 + c) (l := l) (by omega)
    rwa [BitVec.add_assoc, show (0xFFFFFE60 : Word) + BitVec.ofNat 32 (0x1A0 + c) = BitVec.ofNat 32 c by
      apply BitVec.eq_of_toNat_eq
      rw [BitVec.toNat_add, BitVec.toNat_ofNat, BitVec.toNat_ofNat, show (0xFFFFFE60 : Word).toNat = 0xFFFFFE60 from rfl]
      omega] at this
  have below16 : ∀ {x : Word}, Sep (S + 0xFFFFFE60) 0xBF0 x 1 → Sep (S + 0xFFFFFFF0) 16 x 1 := fun {x} hx => by
    have := hx.sub (c := 0x190) (l := 16) (by decide)
    rwa [show S + 0xFFFFFE60 + BitVec.ofNat 32 0x190 = S + 0xFFFFFFF0 by rw [BitVec.add_assoc]; rfl] at this
  -- zero the powers
  obtain ⟨n1, c1, u1⟩ := s.block dqE0 C.self dqE0_end ⟨trivial, trivial, trivial⟩
  have r1 : ∀ q, reg n1 q = (runBlock dqE0 (M, reg n)).2 q := fun q => by rw [u1.regs]
  have v1 : St M DP n1 0x1A2 (reg n1) := ⟨u1.pc, u1.mem, fun _ => rfl⟩
  obtain ⟨n2, d2, u2⟩ := v1.notTaken C.self 0x1A4 dp_at_1a2 (by decide) (by
    show (reg n1 (9 : Fin 32) == reg n1 x0) = false
    rw [r1]; simp +decide only [runBlock, BInstr.run, dqE0, upd, ↓reduceIte]; rw [v1.zero]; rfl)
  obtain ⟨n3, c3, u3, C3, fr3, k3⟩ := dq_zero16 F 15 0 (by decide) C u2.self
    (by rw [u2.regs, r1]; simp +decide only [runBlock, BInstr.run, dqE0, upd, ↓reduceIte]; rw [rsp]; rfl)
    (by rw [u2.regs, r1]; simp +decide only [runBlock, BInstr.run, dqE0, upd, ↓reduceIte]; (try rw [hz]); try rfl)
  have k3' : ∀ q : Fin 32, q.val ∈ [2, 3, 4, 18, 19, 20, 21, 22, 23, 24, 25, 26, 27] → reg n3 q = reg n q := fun q hq => by
    rw [k3 q (by revert hq; revert q; decide) (by revert hq; revert q; decide) (by revert hq; revert q; decide)
      (by revert hq; revert q; decide) (by revert hq; revert q; decide) (by revert hq; revert q; decide)
      (by revert hq; revert q; decide) (by revert hq; revert q; decide) (by revert hq; revert q; decide)
      (by revert hq; revert q; decide), u2.regs, r1, runBlock_reg _ _ _ q hz (by simp only [dqE0]; revert hq; revert q; decide)]
  have D3 : DqData n3.mem := D.of F fun x hx => fr3 x (inFrame (by decide) hx)
  have sp3 : reg n3 sp = S := by rw [k3' sp (by decide)]; exact rsp
  -- spill the result's address, and copy the zeros up
  have a18 : (S + BitVec.ofNat 32 0x18).toNat % 4 = 0 := by rw [F.at _ (by decide)]; omega
  obtain ⟨n4, c4, u4⟩ := u3.block dqE1 C3.self dqE1_end (by
    simp only [BlockOk, BInstr.ok, BInstr.run, dqE1]; simp +decide only [upd, ↓reduceIte, true_and, and_true]
    rw [sp3]; exact ⟨a18, F.sepHi (by decide) (by decide) (by decide)⟩)
  have r4 : ∀ q, reg n4 q = (runBlock dqE1 (n3.mem, reg n3)).2 q := fun q => by rw [u4.regs]
  obtain ⟨M4, hM4⟩ : ∃ M4, memStore32 n3.mem (S + BitVec.ofNat 32 0x18) (reg n (19 : Fin 32)) = M4 := ⟨_, rfl⟩
  have m4 : n4.mem = M4 := by
    rw [u4.mem, ← hM4]; simp +decide only [runBlock, BInstr.run, dqE1, upd, ↓reduceIte]
    rw [sp3, k3' 19 (by decide)]; rfl
  have h4 : ∀ x, Sep (S + BitVec.ofNat 32 0x18) 4 x 1 → M4 x = n3.mem x := fun x hx => by
    rw [← hM4]; exact memStore32_get_sep hx
  have C4 : DqCode M4 := C3.hi fun x hx => h4 x (F.hiOut (by decide) hx)
  have D4 : DqData M4 := D3.of F fun x hx => h4 x (inFrame (by decide) hx)
  obtain ⟨n5, c5, u5, fr5, k5⟩ := dq_memcpy (dst := S + BitVec.ofNat 32 0x62C) (src := S + BitVec.ofNat 32 0x2FC)
    (S := S) (N := 0x300) (⟨u4.pc, m4, fun _ => rfl⟩ : St M4 DP n4 0x1CC (reg n4)) C4 dp_at_1cc dp_at_1d0
    (by decide) (by decide) (by rw [r4, runBlock_reg _ _ _ sp u3.zero (by decide)]; exact sp3)
    (by rw [r4]; simp +decide only [runBlock, BInstr.run, dqE1, upd, ↓reduceIte]; rw [sp3]; rfl)
    (by rw [r4]; simp +decide only [runBlock, BInstr.run, dqE1, upd, ↓reduceIte]; rw [sp3]; rfl)
    (by rw [r4]; simp +decide only [runBlock, BInstr.run, dqE1, upd, ↓reduceIte]; (try rw [u3.zero]); try rfl)
    ⟨C4.body, F.sepHi (by decide) (by decide) (by decide), hFC, F.mcN (by decide), F.mcN (by decide),
      sepS S (.inr (by decide)) (by decide) (by decide), fA, fW, by rw [F.at _ (by decide)]; omega,
      by rw [F.at _ (by decide)]; omega⟩
  have fr5' : ∀ x, Sep (S + 0xFFFFFFF0) 16 x 1 → Sep (S + BitVec.ofNat 32 0x62C) 0x300 x 1 → n5.mem x = M4 x :=
    fun x a b => by rw [fr5 x a, copyBytes_sep b (Nat.le_refl _)]
  have C5 := C4.hi fun x hx => fr5' x (lo16 x hx) (F.hiOut (by decide) hx)
  have D5 : DqData n5.mem := D4.of F fun x hx => fr5' x (below16 hx) (inFrame (by decide) hx)
  have kc : ∀ {m m' : Machine}, (∀ q, q ≠ a0 → q ≠ a1 → q ≠ a2 → q ≠ a3 → q ≠ a4 → q ≠ a5 → q ≠ a6 → q ≠ a7 → q ≠ t0 →
      q ≠ t1 → q ≠ (7 : Fin 32) → q ≠ (28 : Fin 32) → q ≠ (29 : Fin 32) → q ≠ (30 : Fin 32) → q ≠ ra → reg m' q = reg m q) →
      ∀ q : Fin 32, q.val ∈ [2, 3, 4, 8, 9, 18, 19, 20, 21, 22, 23, 24, 25, 26, 27] → reg m' q = reg m q :=
    fun h q hq => h q (by revert hq; revert q; decide) (by revert hq; revert q; decide) (by revert hq; revert q; decide)
      (by revert hq; revert q; decide) (by revert hq; revert q; decide) (by revert hq; revert q; decide)
      (by revert hq; revert q; decide) (by revert hq; revert q; decide) (by revert hq; revert q; decide)
      (by revert hq; revert q; decide) (by revert hq; revert q; decide) (by revert hq; revert q; decide)
      (by revert hq; revert q; decide) (by revert hq; revert q; decide) (by revert hq; revert q; decide)
  have k5' := kc k5
  have g4 : ∀ q : Fin 32, q.val ∈ [2, 3, 4, 8, 18, 19, 20, 21, 22, 23, 24, 25, 26, 27] → reg n4 q = reg n3 q := fun q hq => by
    rw [r4, runBlock_reg _ _ _ q u3.zero (by simp only [dqE1]; revert hq; revert q; decide)]
  have sp5 : reg n5 sp = S := by rw [k5' sp (by decide), g4 sp (by decide)]; exact sp3
  have e59 : reg n5 (9 : Fin 32) = S + BitVec.ofNat 32 0x62C := by
    rw [k5' 9 (by decide), r4]; simp +decide only [runBlock, BInstr.run, dqE1, upd, ↓reduceIte]; rw [sp3]; rfl
  -- clear the slot above the table, and copy everything down
  obtain ⟨n6, c6, u6⟩ := u5.block dqE2 C5.self dqE2_end ⟨trivial, trivial, trivial, trivial, trivial⟩
  have r6 : ∀ q, reg n6 q = (runBlock dqE2 (n5.mem, reg n5)).2 q := fun q => by rw [u6.regs]
  obtain ⟨n7, c7, u7, mem7, k7⟩ := dq_memset (dst := S + BitVec.ofNat 32 0x92C) (b := 0) (N := 48)
    (⟨u6.pc, u6.mem, fun _ => rfl⟩ : St n5.mem DP n6 0x1E2 (reg n6)) C5 dp_at_1e2 dp_at_1e6 (by decide) (by decide)
    (by rw [r6]; simp +decide only [runBlock, BInstr.run, dqE2, upd, ↓reduceIte]; rw [sp5, spo]; rfl)
    (by rw [r6]; simp +decide only [runBlock, BInstr.run, dqE2, upd, ↓reduceIte]; (try rw [u5.zero]); try rfl)
    (by rw [r6]; simp +decide only [runBlock, BInstr.run, dqE2, upd, ↓reduceIte]; (try rw [u5.zero]); try rfl)
    (by rw [F.at _ (by decide)]; omega) (F.sepHi (by decide) (by decide) (by decide))
  have h7 : ∀ x, Sep (S + BitVec.ofNat 32 0x92C) 48 x 1 → n7.mem x = n5.mem x := fun x hx => by
    rw [mem7, fillBytes_sep hx (Nat.le_refl _)]
  have C7 := C5.hi fun x hx => h7 x (F.hiOut (by decide) hx)
  have D7 : DqData n7.mem := D5.of F fun x hx => h7 x (inFrame (by decide) hx)
  have k7' : ∀ q : Fin 32, q.val ∈ [2, 3, 4, 8, 9, 18, 19, 20, 21, 22, 23, 24, 25, 26, 27] → reg n7 q = reg n5 q := fun q hq => by
    rw [k7 q (by revert hq; revert q; decide) (by revert hq; revert q; decide) (by revert hq; revert q; decide)
      (by revert hq; revert q; decide) (by revert hq; revert q; decide) (by revert hq; revert q; decide)
      (by revert hq; revert q; decide), r6, runBlock_reg _ _ _ q u5.zero (by simp only [dqE2]; revert hq; revert q; decide)]
  obtain ⟨n8, c8, u8⟩ := u7.block dqE3 C7.self dqE3_end ⟨trivial, trivial, trivial, trivial⟩
  have r8 : ∀ q, reg n8 q = (runBlock dqE3 (n7.mem, reg n7)).2 q := fun q => by rw [u8.regs]
  have sp7 : reg n7 sp = S := by rw [k7' sp (by decide)]; exact sp5
  obtain ⟨n9, c9, u9, fr9, k9⟩ := dq_memcpy (dst := S + BitVec.ofNat 32 0x2FC) (src := S + BitVec.ofNat 32 0x62C)
    (S := S) (N := 0x330) (⟨u8.pc, u8.mem, fun _ => rfl⟩ : St n7.mem DP n8 0x1F4 (reg n8)) C7 dp_at_1f4 dp_at_1f8
    (by decide) (by decide) (by rw [r8, runBlock_reg _ _ _ sp u7.zero (by decide)]; exact sp7)
    (by rw [r8]; simp +decide only [runBlock, BInstr.run, dqE3, upd, ↓reduceIte]; rw [sp7]; rfl)
    (by rw [r8]; simp +decide only [runBlock, BInstr.run, dqE3, upd, ↓reduceIte]; rw [sp7]; rfl)
    (by rw [r8]; simp +decide only [runBlock, BInstr.run, dqE3, upd, ↓reduceIte]; (try rw [u7.zero]); try rfl)
    ⟨C7.body, F.sepHi (by decide) (by decide) (by decide), hFC, F.mcN (by decide), F.mcN (by decide),
      sepS S (.inl (by decide)) (by decide) (by decide), fA, fW, by rw [F.at _ (by decide)]; omega,
      by rw [F.at _ (by decide)]; omega⟩
  have fr9' : ∀ x, Sep (S + 0xFFFFFFF0) 16 x 1 → Sep (S + BitVec.ofNat 32 0x2FC) 0x330 x 1 → n9.mem x = n7.mem x :=
    fun x a b => by rw [fr9 x a, copyBytes_sep b (Nat.le_refl _)]
  have C9 := C7.hi fun x hx => fr9' x (lo16 x hx) (F.hiOut (by decide) hx)
  have D9 : DqData n9.mem := D7.of F fun x hx => fr9' x (below16 hx) (inFrame (by decide) hx)
  have k9' := kc k9
  have g8 : ∀ q : Fin 32, q.val ∈ [2, 3, 4, 8, 9, 18, 19, 20, 21, 22, 23, 24, 25, 26, 27] → reg n8 q = reg n7 q := fun q hq => by
    rw [r8, runBlock_reg _ _ _ q u7.zero (by simp only [dqE3]; revert hq; revert q; decide)]
  have k79 : ∀ q : Fin 32, q.val ∈ [2, 3, 4, 8, 9, 18, 19, 20, 21, 22, 23, 24, 25, 26, 27] → reg n9 q = reg n5 q :=
    fun q hq => by rw [k9' q hq, g8 q hq, k7' q hq]
  -- the ones
  obtain ⟨n10, c10, u10⟩ := u9.block dqE4 C9.self dqE4_end ⟨trivial, trivial, trivial, trivial⟩
  have r10 : ∀ q, reg n10 q = (runBlock dqE4 (n9.mem, reg n9)).2 q := fun q => by rw [u10.regs]
  have t10 : St n9.mem DP n10 0x206 (reg n10) := ⟨u10.pc, u10.mem, fun _ => rfl⟩
  obtain ⟨n11, d11, u11⟩ := t10.notTaken C9.self 0x208 dp_at_206 (by decide) (by
    show (reg n10 (8 : Fin 32) == reg n10 x0) = false
    rw [r10]; simp +decide only [runBlock, BInstr.run, dqE4, upd, ↓reduceIte]; rw [t10.zero]; (try rw [u9.zero]); rfl)
  have e1024 : reg n10 (24 : Fin 32) = PARAMS + 0x30 := by
    rw [r10]; simp +decide only [runBlock, BInstr.run, dqE4, upd, ↓reduceIte]
    rw [k79 24 (by decide), k5' 24 (by decide), g4 24 (by decide), k3' 24 (by decide), r24]; rfl
  have hOF : Sep (S + 0xFFFFFFF0) 16 (PARAMS + 0x30) 48 := F.lowData (c := 16) (by decide) rfl (by decide) (by decide)
  have hOT : Sep (S + BitVec.ofNat 32 0x62C) 0x300 (PARAMS + 0x30) 48 := F.bufData (by decide) (by decide) (by decide)
  obtain ⟨n12, c12, u12, C12, hT12, fr12, k12⟩ := dq_ones16 F hOF hOT (by decide) 15 0 (by decide) C9 u11.self
    (by rw [u11.regs, r10, runBlock_reg _ _ _ sp u9.zero (by decide), k79 sp (by decide)]; exact sp5)
    (by rw [u11.regs, r10, runBlock_reg _ _ _ 9 u9.zero (by decide), k79 9 (by decide), e59])
    (by rw [u11.regs, r10]; simp +decide only [runBlock, BInstr.run, dqE4, upd, ↓reduceIte]; (try rw [u9.zero]); try rfl)
    (by rw [u11.regs, e1024])
  have k12' : ∀ q : Fin 32, q.val ∈ [2, 3, 4, 18, 19, 20, 21, 22, 23, 24, 25, 26, 27] → reg n12 q = reg n10 q := fun q hq => by
    rw [k12 q (by revert hq; revert q; decide) (by revert hq; revert q; decide) (by revert hq; revert q; decide)
      (by revert hq; revert q; decide) (by revert hq; revert q; decide) (by revert hq; revert q; decide)
      (by revert hq; revert q; decide) (by revert hq; revert q; decide) (by revert hq; revert q; decide)
      (by revert hq; revert q; decide) (by revert hq; revert q; decide) (by revert hq; revert q; decide)
      (by revert hq; revert q; decide) (by revert hq; revert q; decide) (by revert hq; revert q; decide)
      (by revert hq; revert q; decide) (by revert hq; revert q; decide), u11.regs]
  have e1019 : reg n10 (19 : Fin 32) = S + BitVec.ofNat 32 0x65C := by
    rw [r10]; simp +decide only [runBlock, BInstr.run, dqE4, upd, ↓reduceIte]; rw [k79 sp (by decide), sp5]; rfl
  have g10 : ∀ q : Fin 32, q.val ∈ [2, 3, 4, 18, 20, 21, 22, 23, 25, 26, 27] → reg n10 q = reg n9 q := fun q hq => by
    rw [r10, runBlock_reg _ _ _ q u9.zero (by simp only [dqE4]; revert hq; revert q; decide)]
  have fr12' : ∀ x, Sep (S + 0xFFFFFFF0) 16 x 1 → Sep (S + BitVec.ofNat 32 0x62C) 0x300 x 1 → n12.mem x = n9.mem x := by
    intro x a b; exact fr12 x a (by rwa [show 0x62C + 48 * 0 = 0x62C from rfl, show 48 * (16 - 0) = 0x300 from rfl])
  have D12 : DqData n12.mem := D9.of F fun x hx => fr12' x (below16 hx) (inFrame (by decide) hx)
  -- α to entry 1
  obtain ⟨n13, c13, u13⟩ := u12.block dqE5 C12.self dqE5_end ⟨trivial, trivial, trivial, trivial⟩
  have r13 : ∀ q, reg n13 q = (runBlock dqE5 (n12.mem, reg n12)).2 q := fun q => by rw [u13.regs]
  have sp12 : reg n12 sp = S := by rw [k12' sp (by decide), g10 sp (by decide), k79 sp (by decide)]; exact sp5
  have e1219 : reg n12 (19 : Fin 32) = S + BitVec.ofNat 32 0x65C := by rw [k12' 19 (by decide), e1019]
  obtain ⟨n14, c14, u14, fr14, k14⟩ := dq_memcpy (dst := S + BitVec.ofNat 32 0x65C) (src := S + BitVec.ofNat 32 0x104)
    (S := S) (N := 48) (⟨u13.pc, u13.mem, fun _ => rfl⟩ : St n12.mem DP n13 0x228 (reg n13)) C12 dp_at_228 dp_at_22c
    (by decide) (by decide) (by rw [r13, runBlock_reg _ _ _ sp u12.zero (by decide)]; exact sp12)
    (by rw [r13]; simp +decide only [runBlock, BInstr.run, dqE5, upd, ↓reduceIte]; rw [e1219]
        exact BitVec.zero_add _)
    (by rw [r13]; simp +decide only [runBlock, BInstr.run, dqE5, upd, ↓reduceIte]; rw [sp12]; rfl)
    (by rw [r13]; simp +decide only [runBlock, BInstr.run, dqE5, upd, ↓reduceIte]; (try rw [u12.zero]); try rfl)
    ⟨C12.body, F.sepHi (by decide) (by decide) (by decide), hFC, F.mcN (by decide), F.mcN (by decide),
      sepS S (.inr (by decide)) (by decide) (by decide), fA, fW, by rw [F.at _ (by decide)]; omega,
      by rw [F.at _ (by decide)]; omega⟩
  have fr14' : ∀ x, Sep (S + 0xFFFFFFF0) 16 x 1 → Sep (S + BitVec.ofNat 32 0x65C) 48 x 1 → n14.mem x = n12.mem x :=
    fun x a b => by rw [fr14 x a, copyBytes_sep b (Nat.le_refl _)]
  have k14' := kc k14
  have g13 : ∀ q : Fin 32, q.val ∈ [2, 3, 4, 8, 9, 18, 19, 20, 21, 22, 23, 24, 25, 26, 27] → reg n13 q = reg n12 q := fun q hq => by
    rw [r13, runBlock_reg _ _ _ q u12.zero (by simp only [dqE5]; revert hq; revert q; decide)]
  -- the frame, through each step
  have frame : ∀ x, Sep (S + 0xFFFFFFF0) 16 x 1 → Sep (S + BitVec.ofNat 32 0x18) 4 x 1 →
      Sep (S + BitVec.ofNat 32 0x2FC) 0x660 x 1 → n14.mem x = M x := by
    intro x h16 h18 h2FC
    have s62C : Sep (S + BitVec.ofNat 32 0x62C) 0x300 x 1 := by
      have := h2FC.sub (c := 0x330) (l := 0x300) (by decide); rwa [add_ofNat_assoc] at this
    have s65C : Sep (S + BitVec.ofNat 32 0x65C) 48 x 1 := by
      have := h2FC.sub (c := 0x360) (l := 48) (by decide); rwa [add_ofNat_assoc] at this
    have s2FC : Sep (S + BitVec.ofNat 32 0x2FC) 0x330 x 1 := by
      have := h2FC.sub (c := 0) (l := 0x330) (by decide); rwa [add_ofNat_zero] at this
    have s2FC3 : Sep (S + BitVec.ofNat 32 0x2FC) 0x300 x 1 := by
      have := h2FC.sub (c := 0) (l := 0x300) (by decide); rwa [add_ofNat_zero] at this
    have s92C : Sep (S + BitVec.ofNat 32 0x92C) 48 x 1 := by
      have := h2FC.sub (c := 0x630) (l := 48) (by decide); rwa [add_ofNat_assoc] at this
    rw [fr14' x h16 s65C, fr12' x h16 s62C, fr9' x h16 s2FC, h7 x s92C, fr5' x h16 s62C, h4 x h18, fr3 x s2FC3]
  have hAv : accV n12.mem (S + BitVec.ofNat 32 0x104) 12 = accV M (S + BitVec.ofNat 32 0x104) 12 := by
    rw [← show accV n14.mem (S + BitVec.ofNat 32 0x104) 12 = accV n12.mem (S + BitVec.ofNat 32 0x104) 12 from
      accV_congr2 12 fun i hi => memLoad32_congr fun q hq => by
        rw [add_ofNat_assoc, add_ofNat_assoc]
        exact fr14' _ (l16b _ (by omega)) (sepS S (.inr (by omega)) (by decide) (by omega))]
    exact accV_congr2 12 fun i hi => memLoad32_congr fun q hq => by
      rw [add_ofNat_assoc, add_ofNat_assoc]
      exact frame _ (l16b _ (by omega)) (sepS S (.inl (by omega)) (by decide) (by omega))
        (sepS S (.inr (by omega)) (by decide) (by omega))
  refine ⟨n14, c1.trans (.cons d2 (c3.trans (c4.trans (c5.trans (c6.trans (c7.trans (c8.trans (c9.trans (c10.trans
    (.cons d11 (c12.trans (c13.trans c14)))))))))))), u14,
    C12.hi fun x hx => fr14' x (lo16 x hx) (F.hiOut (by decide) hx),
    D12.of F fun x hx => fr14' x (below16 hx) (inFrame (by decide) hx), fun j hj => ?_, ?_, ?_, ?_, frame, fun q hq => ?_⟩
  · rcases Nat.le_one_iff_eq_zero_or_eq_one.mp hj with rfl | rfl
    · show accV n14.mem (S + BitVec.ofNat 32 (0x62C + 48 * 0)) 12 = p3one
      rw [show 0x62C + 48 * 0 = 0x62C from rfl]
      rw [show accV n14.mem (S + BitVec.ofNat 32 0x62C) 12 = accV n12.mem (S + BitVec.ofNat 32 0x62C) 12 from
        accV_congr2 12 fun i hi => memLoad32_congr fun q hq => by
          rw [add_ofNat_assoc, add_ofNat_assoc]
          exact fr14' _ (l16b _ (by omega)) (sepS S (.inr (by omega)) (by decide) (by omega))]
      rw [show S + BitVec.ofNat 32 0x62C = S + BitVec.ofNat 32 (0x62C + 48 * 0) from rfl, hT12 0 (Nat.le_refl 0) (by decide)]
      have e9 : accV n9.mem (PARAMS + 0x30) 12 = p3one := D9.one
      exact e9
    · rw [mpow_one _ hA, ← hAv]
      refine cp_accV (by decide) (by decide) fun i hi => ?_
      have hs : Sep (S + 0xFFFFFFF0) 16 (S + BitVec.ofNat 32 (0x65C + 4 * i)) 4 :=
        sep_of_le (by rw [hb16, F.at _ (by omega)]; omega) (by rw [F.at _ (by omega)]; omega)
      rw [show 0x62C + 48 * 1 + 4 * i = 0x65C + 4 * i by omega, load_frame fr14 hs, ← add_ofNat_assoc S 0x65C,
        cp_word (by omega) (by decide), add_ofNat_assoc]
  · rw [show memLoad32 n14.mem (S + BitVec.ofNat 32 0x18) = memLoad32 M4 (S + BitVec.ofNat 32 0x18) from
      memLoad32_congr fun q hq => by
        rw [add_ofNat_assoc]
        rw [fr14' _ (l16b _ (by omega)) (sepS S (.inr (by omega)) (by decide) (by omega)),
          fr12' _ (l16b _ (by omega)) (sepS S (.inr (by omega)) (by decide) (by omega)),
          fr9' _ (l16b _ (by omega)) (sepS S (.inr (by omega)) (by decide) (by omega)),
          h7 _ (sepS S (.inr (by omega)) (by decide) (by omega)),
          fr5' _ (l16b _ (by omega)) (sepS S (.inr (by omega)) (by decide) (by omega))], ← hM4,
      memLoad32_store32_same]
  · rw [k14' 19 (by decide), g13 19 (by decide), e1219]
  · rw [k14' 24 (by decide), g13 24 (by decide), k12' 24 (by decide), e1024]
  · rw [k14' q (by revert hq; revert q; decide), g13 q (by revert hq; revert q; decide), k12' q (by revert hq; revert q; decide),
      g10 q hq, k79 q (by revert hq; revert q; decide), k5' q (by revert hq; revert q; decide),
      g4 q (by revert hq; revert q; decide), k3' q (by revert hq; revert q; decide)]

/-! ## Setting up the exponentiation -/

def dqF1 : List BInstr :=
  [.sw sp (21 : Fin 32) 0x10, .sw sp (20 : Fin 32) 0x14, .aluImm .add a0 sp 0x2FC, .aluImm .add a1 sp 0x62C,
   .aluImm .add a2 x0 0x300]
def dqF2 : List BInstr := [.aluImm .add a2 x0 0x30, .aluImm .add a0 sp 0x5FC, .alu .add a1 x0 (22 : Fin 32)]
def dqF3 : List BInstr :=
  [.aluImm .add (18 : Fin 32) (18 : Fin 32) 0xFFFFFFFF, .aluImm .srl (9 : Fin 32) (18 : Fin 32) 0x5,
   .aluImm .and a0 (18 : Fin 32) 0x3, .aluImm .add a1 x0 0x2, .aluImm .sll (18 : Fin 32) (18 : Fin 32) 0x1B,
   .alu .sll a0 a1 a0, .aluImm .srl (8 : Fin 32) (18 : Fin 32) 0x1D, .aluImm .add (18 : Fin 32) a0 0xFFFFFFFF,
   .aluImm .add a0 sp 0x7FF, .aluImm .add a0 a0 0x15D, .aluImm .add a2 x0 0x30, .alu .add a1 x0 (24 : Fin 32)]
def dqF4 : List BInstr :=
  [.sw sp (9 : Fin 32) 0x34, .aluImm .add (9 : Fin 32) (9 : Fin 32) 0x1, .sw sp (8 : Fin 32) 0x30,
   .aluImm .add (8 : Fin 32) (8 : Fin 32) 0x1, .sw sp (8 : Fin 32) 0x1C, .aluImm .and a0 (18 : Fin 32) 0xF, .sw sp a0 0x24,
   .aluImm .add (18 : Fin 32) sp 0x7FF, .aluImm .add (18 : Fin 32) (18 : Fin 32) 0x1C1, .aluImm .add (26 : Fin 32) sp 0x7FF,
   .aluImm .add (26 : Fin 32) (26 : Fin 32) 0x191, .aluImm .add (21 : Fin 32) sp 0x138, .aluImm .add (19 : Fin 32) sp 0x7FF,
   .aluImm .add (19 : Fin 32) (19 : Fin 32) 0x1BD, .aluImm .add (22 : Fin 32) x0 0xC,
   .aluImm .add (23 : Fin 32) x0 0xFFFFFFFF]

theorem dqF1_end : blockEnd p384DecompressCode 0x26C dqF1 = some 0x27A := by decide
theorem dqF2_end : blockEnd p384DecompressCode 0x282 dqF2 = some 0x28C := by decide
theorem dqF3_end : blockEnd p384DecompressCode 0x294 dqF3 = some 0x2BC := by decide
theorem dqF4_end : blockEnd p384DecompressCode 0x2C4 dqF4 = some 0x2F4 := by decide

set_option maxRecDepth 100000 in
set_option maxHeartbeats 16000000 in
/-- **Setting up the exponentiation**, from 0x26C to the limb loop at 0x2F8:
copy the table to `S + 0x2FC` and the exponent to `S + 0x5FC`, set `z` to
1, and spill the loop's counters. -/
theorem dq_stF {M : Word → BitVec 8} {n : Machine} {S : Word} {A : Nat} (C : DqCode M) (D : DqData M)
    (F : DqFrame S) (s : St M DP n 0x26C (reg n)) (rsp : reg n sp = S) (r18 : reg n (18 : Fin 32) = 0x17E)
    (r22 : reg n (22 : Fin 32) = EXPA) (r24 : reg n (24 : Fin 32) = PARAMS + 0x30)
    (r25 : reg n (25 : Fin 32) = S + BitVec.ofNat 32 0x98C)
    (hT : ∀ j, j < 16 → accV M (S + BitVec.ofNat 32 (0x62C + 48 * j)) 12 = mpow A j)
    (hN0 : memLoad32 M (S + BitVec.ofNat 32 0x134) = 0xFFFFFFFF) (hN : accV M (S + BitVec.ofNat 32 0x134) 12 = p384) :
    ∃ n', Steps n n' ∧ St n'.mem DP n' 0x2F8 (reg n') ∧ DqCode n'.mem ∧ DqData n'.mem ∧ DqBase n'.mem S A ∧
      DqRegs n' S ∧ reg n' (9 : Fin 32) = BitVec.ofNat 32 (11 + 1) ∧
      accV n'.mem (S + BitVec.ofNat 32 0x95C) 12 = mpow A (sqrtExp / 2 ^ (4 * (8 * 11 + 8))) ∧
      memLoad32 n'.mem (S + BitVec.ofNat 32 0x10) = reg n (21 : Fin 32) ∧
      memLoad32 n'.mem (S + BitVec.ofNat 32 0x14) = reg n (20 : Fin 32) ∧
      (∀ x, Sep (S + 0xFFFFFFF0) 16 x 1 → Sep (S + BitVec.ofNat 32 0x10) 8 x 1 → Sep (S + BitVec.ofNat 32 0x1C) 0x1C x 1 →
        Sep (S + BitVec.ofNat 32 0x2FC) 0x330 x 1 → Sep (S + BitVec.ofNat 32 0x95C) 48 x 1 → n'.mem x = M x) ∧
      ∀ q : Fin 32, q.val ∈ [3, 4, 20, 24, 27] → reg n' q = reg n q := by
  have hz := s.zero
  have hSl := F.lo; have hSh := F.hi; have hSa := F.al
  obtain ⟨fA, fW, hFC, b16⟩ := F.mc
  have hb16 : (S + 0xFFFFFFF0).toNat = S.toNat - 16 := F.below 16 (by decide) (by decide)
  have lo16 : ∀ x : Word, 0x40000000 ≤ x.toNat → Sep (S + 0xFFFFFFF0) 16 x 1 := fun x hx =>
    sep_of_le (by rw [hb16]; omega) (by have := x.isLt; omega)
  have l16b : ∀ d, d + 1 ≤ 0xA50 → Sep (S + 0xFFFFFFF0) 16 (S + BitVec.ofNat 32 d) 1 := fun d hd =>
    sep_of_le (by rw [hb16, F.at d (by omega)]; omega) (by rw [F.at d (by omega)]; omega)
  have inFrame : ∀ {c l : Nat} {x : Word}, c + l ≤ 0xA50 → Sep (S + 0xFFFFFE60) 0xBF0 x 1 →
      Sep (S + BitVec.ofNat 32 c) l x 1 := fun {c l x} h hx => by
    have := hx.sub (c := 0x1A0 + c) (l := l) (by omega)
    rwa [BitVec.add_assoc, show (0xFFFFFE60 : Word) + BitVec.ofNat 32 (0x1A0 + c) = BitVec.ofNat 32 c by
      apply BitVec.eq_of_toNat_eq
      rw [BitVec.toNat_add, BitVec.toNat_ofNat, BitVec.toNat_ofNat, show (0xFFFFFE60 : Word).toNat = 0xFFFFFE60 from rfl]
      omega] at this
  have below16 : ∀ {x : Word}, Sep (S + 0xFFFFFE60) 0xBF0 x 1 → Sep (S + 0xFFFFFFF0) 16 x 1 := fun {x} hx => by
    have := hx.sub (c := 0x190) (l := 16) (by decide)
    rwa [show S + 0xFFFFFE60 + BitVec.ofNat 32 0x190 = S + 0xFFFFFFF0 by rw [BitVec.add_assoc]; rfl] at this
  have al : ∀ c, c + 4 ≤ 0xA50 → c % 4 = 0 → (S + BitVec.ofNat 32 c).toNat % 4 = 0 := fun c h1 h2 => by
    rw [F.at c (by omega)]; omega
  have kc : ∀ {m m' : Machine}, (∀ q, q ≠ a0 → q ≠ a1 → q ≠ a2 → q ≠ a3 → q ≠ a4 → q ≠ a5 → q ≠ a6 → q ≠ a7 → q ≠ t0 →
      q ≠ t1 → q ≠ (7 : Fin 32) → q ≠ (28 : Fin 32) → q ≠ (29 : Fin 32) → q ≠ (30 : Fin 32) → q ≠ ra → reg m' q = reg m q) →
      ∀ q : Fin 32, q.val ∈ [2, 3, 4, 8, 9, 18, 19, 20, 21, 22, 23, 24, 25, 26, 27] → reg m' q = reg m q :=
    fun h q hq => h q (by revert hq; revert q; decide) (by revert hq; revert q; decide) (by revert hq; revert q; decide)
      (by revert hq; revert q; decide) (by revert hq; revert q; decide) (by revert hq; revert q; decide)
      (by revert hq; revert q; decide) (by revert hq; revert q; decide) (by revert hq; revert q; decide)
      (by revert hq; revert q; decide) (by revert hq; revert q; decide) (by revert hq; revert q; decide)
      (by revert hq; revert q; decide) (by revert hq; revert q; decide) (by revert hq; revert q; decide)
  -- spill y_is_odd and from_repr's choice, then copy the table down
  obtain ⟨n1, c1, u1⟩ := s.block dqF1 C.self dqF1_end (by
    simp only [BlockOk, BInstr.ok, BInstr.run, dqF1]; simp +decide only [upd, ↓reduceIte, true_and, and_true]
    rw [rsp]; exact ⟨⟨al 0x10 (by decide) (by decide), F.sepHi (by decide) (by decide) (by decide)⟩,
      al 0x14 (by decide) (by decide), F.sepHi (by decide) (by decide) (by decide)⟩)
  have r1 : ∀ q, reg n1 q = (runBlock dqF1 (M, reg n)).2 q := fun q => by rw [u1.regs]
  obtain ⟨M1, hM1⟩ : ∃ M1, memStore32 (memStore32 M (S + BitVec.ofNat 32 0x10) (reg n (21 : Fin 32)))
      (S + BitVec.ofNat 32 0x14) (reg n (20 : Fin 32)) = M1 := ⟨_, rfl⟩
  have m1 : n1.mem = M1 := by
    rw [u1.mem, ← hM1]; simp +decide only [runBlock, BInstr.run, dqF1, upd, ↓reduceIte]; rw [rsp]; rfl
  have h1 : ∀ x, Sep (S + BitVec.ofNat 32 0x10) 8 x 1 → M1 x = M x := fun x hx => by
    rw [← hM1, memStore32_get_sep (by have := hx.sub (c := 4) (l := 4) (by decide); rwa [add_ofNat_assoc] at this),
      memStore32_get_sep (by have := hx.sub (c := 0) (l := 4) (by decide); rwa [add_ofNat_zero] at this)]
  have C1 : DqCode M1 := C.hi fun x hx => h1 x (F.hiOut (by decide) hx)
  have D1 : DqData M1 := D.of F fun x hx => h1 x (inFrame (by decide) hx)
  have g1 : ∀ q, q ≠ a0 → q ≠ a1 → q ≠ a2 → reg n1 q = reg n q := fun q h0 h1 h2 => by
    rw [r1, runBlock_reg _ _ _ q hz (by simp only [dqF1]; revert h0 h1 h2; revert q; decide)]
  have sp1 : reg n1 sp = S := by rw [g1 sp (by decide) (by decide) (by decide)]; exact rsp
  obtain ⟨n2, c2, u2, fr2, k2⟩ := dq_memcpy (dst := S + BitVec.ofNat 32 0x2FC) (src := S + BitVec.ofNat 32 0x62C)
    (S := S) (N := 0x300) (⟨u1.pc, m1, fun _ => rfl⟩ : St M1 DP n1 0x27A (reg n1)) C1 dp_at_27a dp_at_27e
    (by decide) (by decide) (by rw [r1, runBlock_reg _ _ _ sp hz (by decide)]; exact rsp)
    (by rw [r1]; simp +decide only [runBlock, BInstr.run, dqF1, upd, ↓reduceIte]; rw [rsp]; rfl)
    (by rw [r1]; simp +decide only [runBlock, BInstr.run, dqF1, upd, ↓reduceIte]; rw [rsp]; rfl)
    (by rw [r1]; simp +decide only [runBlock, BInstr.run, dqF1, upd, ↓reduceIte]; (try rw [hz]); try rfl)
    ⟨C1.body, F.sepHi (by decide) (by decide) (by decide), hFC, F.mcN (by decide), F.mcN (by decide),
      sepS S (.inl (by decide)) (by decide) (by decide), fA, fW, by rw [F.at _ (by decide)]; omega,
      by rw [F.at _ (by decide)]; omega⟩
  have fr2' : ∀ x, Sep (S + 0xFFFFFFF0) 16 x 1 → Sep (S + BitVec.ofNat 32 0x2FC) 0x300 x 1 → n2.mem x = M1 x :=
    fun x a b => by rw [fr2 x a, copyBytes_sep b (Nat.le_refl _)]
  have C2 := C1.hi fun x hx => fr2' x (lo16 x hx) (F.hiOut (by decide) hx)
  have D2 : DqData n2.mem := D1.of F fun x hx => fr2' x (below16 hx) (inFrame (by decide) hx)
  have k2' := kc k2
  -- copy the exponent
  obtain ⟨n3, c3, u3⟩ := u2.block dqF2 C2.self dqF2_end ⟨trivial, trivial, trivial, trivial⟩
  have r3 : ∀ q, reg n3 q = (runBlock dqF2 (n2.mem, reg n2)).2 q := fun q => by rw [u3.regs]
  have sp2 : reg n2 sp = S := by rw [k2' sp (by decide)]; exact sp1
  obtain ⟨n4, c4, u4, fr4, k4⟩ := dq_memcpy (dst := S + BitVec.ofNat 32 0x5FC) (src := EXPA) (S := S) (N := 48)
    (⟨u3.pc, u3.mem, fun _ => rfl⟩ : St n2.mem DP n3 0x28C (reg n3)) C2 dp_at_28c dp_at_290 (by decide) (by decide)
    (by rw [r3, runBlock_reg _ _ _ sp u2.zero (by decide)]; exact sp2)
    (by rw [r3]; simp +decide only [runBlock, BInstr.run, dqF2, upd, ↓reduceIte]; rw [sp2]; rfl)
    (by rw [r3]; simp +decide only [runBlock, BInstr.run, dqF2, upd, ↓reduceIte]; rw [k2' 22 (by decide),
        g1 22 (by decide) (by decide) (by decide), r22]; exact BitVec.zero_add _)
    (by rw [r3]; simp +decide only [runBlock, BInstr.run, dqF2, upd, ↓reduceIte]; (try rw [u2.zero]); try rfl)
    ⟨C2.body, F.sepHi (by decide) (by decide) (by decide), hFC, F.mcN (by decide),
      (F.lowData (c := 16) (by decide) rfl (by decide) (by decide)).symm, F.bufData (by decide) (by decide) (by decide),
      fA, fW, by rw [F.at _ (by decide)]; omega, by decide⟩
  have fr4' : ∀ x, Sep (S + 0xFFFFFFF0) 16 x 1 → Sep (S + BitVec.ofNat 32 0x5FC) 48 x 1 → n4.mem x = n2.mem x :=
    fun x a b => by rw [fr4 x a, copyBytes_sep b (Nat.le_refl _)]
  have C4 := C2.hi fun x hx => fr4' x (lo16 x hx) (F.hiOut (by decide) hx)
  have D4 : DqData n4.mem := D2.of F fun x hx => fr4' x (below16 hx) (inFrame (by decide) hx)
  have k4' := kc k4
  -- the exponent's shape: 12 limbs, a top window of two bits; then z = 1
  obtain ⟨n5, c5, u5⟩ := u4.block dqF3 C4.self dqF3_end ⟨trivial, trivial, trivial, trivial, trivial, trivial, trivial,
    trivial, trivial, trivial, trivial, trivial, trivial⟩
  have r5 : ∀ q, reg n5 q = (runBlock dqF3 (n4.mem, reg n4)).2 q := fun q => by rw [u5.regs]
  have g3 : ∀ q : Fin 32, q.val ∈ [2, 3, 4, 8, 9, 18, 19, 20, 21, 22, 23, 24, 25, 26, 27] → reg n3 q = reg n2 q := fun q hq => by
    rw [r3, runBlock_reg _ _ _ q u2.zero (by simp only [dqF2]; revert hq; revert q; decide)]
  have k14 : ∀ q : Fin 32, q.val ∈ [2, 3, 4, 8, 9, 18, 19, 20, 21, 22, 23, 24, 25, 26, 27] → reg n4 q = reg n q := fun q hq => by
    rw [k4' q hq, g3 q hq, k2' q hq, g1 q (by revert hq; revert q; decide) (by revert hq; revert q; decide)
      (by revert hq; revert q; decide)]
  have sp4 : reg n4 sp = S := by rw [k14 sp (by decide)]; exact rsp
  obtain ⟨n6, c6, u6, fr6, k6⟩ := dq_memcpy (dst := S + BitVec.ofNat 32 0x95C) (src := PARAMS + 0x30) (S := S) (N := 48)
    (⟨u5.pc, u5.mem, fun _ => rfl⟩ : St n4.mem DP n5 0x2BC (reg n5)) C4 dp_at_2bc dp_at_2c0 (by decide) (by decide)
    (by rw [r5, runBlock_reg _ _ _ sp u4.zero (by decide)]; exact sp4)
    (by rw [r5]; simp +decide only [runBlock, BInstr.run, dqF3, upd, ↓reduceIte]; rw [sp4, spo]; rfl)
    (by rw [r5]; simp +decide only [runBlock, BInstr.run, dqF3, upd, ↓reduceIte]; rw [k14 24 (by decide), r24]
        exact BitVec.zero_add _)
    (by rw [r5]; simp +decide only [runBlock, BInstr.run, dqF3, upd, ↓reduceIte]; (try rw [u4.zero]); try rfl)
    ⟨C4.body, F.sepHi (by decide) (by decide) (by decide), hFC, F.mcN (by decide),
      (F.lowData (c := 16) (by decide) rfl (by decide) (by decide)).symm, F.bufData (by decide) (by decide) (by decide),
      fA, fW, by rw [F.at _ (by decide)]; omega, by decide⟩
  have fr6' : ∀ x, Sep (S + 0xFFFFFFF0) 16 x 1 → Sep (S + BitVec.ofNat 32 0x95C) 48 x 1 → n6.mem x = n4.mem x :=
    fun x a b => by rw [fr6 x a, copyBytes_sep b (Nat.le_refl _)]
  have C6 := C4.hi fun x hx => fr6' x (lo16 x hx) (F.hiOut (by decide) hx)
  have D6 : DqData n6.mem := D4.of F fun x hx => fr6' x (below16 hx) (inFrame (by decide) hx)
  have k6' := kc k6
  have e5 : ∀ q : Fin 32, q.val ∈ [8, 9, 18] → reg n6 q = (runBlock dqF3 (n4.mem, reg n4)).2 q := fun q hq => by
    rw [k6' q (by revert hq; revert q; decide), r5]
  have v8 : reg n6 (8 : Fin 32) = 7 := by
    rw [e5 8 (by decide)]; simp +decide only [runBlock, BInstr.run, dqF3, upd, ↓reduceIte]
    rw [k14 18 (by decide), r18]; decide
  have v9 : reg n6 (9 : Fin 32) = 11 := by
    rw [e5 9 (by decide)]; simp +decide only [runBlock, BInstr.run, dqF3, upd, ↓reduceIte]
    rw [k14 18 (by decide), r18]; decide
  have v18 : reg n6 (18 : Fin 32) = 3 := by
    rw [e5 18 (by decide)]; simp +decide only [runBlock, BInstr.run, dqF3, upd, ↓reduceIte]
    rw [k14 18 (by decide), r18]; decide
  have sp6 : reg n6 sp = S := by rw [k6' sp (by decide), r5, runBlock_reg _ _ _ sp u4.zero (by decide)]; exact sp4
  -- spill the counters and point the squarings at their buffers
  obtain ⟨n7, c7, u7⟩ := u6.block dqF4 C6.self dqF4_end (by
    simp only [BlockOk, BInstr.ok, BInstr.run, dqF4]; simp +decide only [upd, ↓reduceIte, true_and, and_true]
    rw [sp6]
    exact ⟨⟨al 0x34 (by decide) (by decide), F.sepHi (by decide) (by decide) (by decide)⟩,
      ⟨al 0x30 (by decide) (by decide), F.sepHi (by decide) (by decide) (by decide)⟩,
      ⟨al 0x1C (by decide) (by decide), F.sepHi (by decide) (by decide) (by decide)⟩,
      al 0x24 (by decide) (by decide), F.sepHi (by decide) (by decide) (by decide)⟩)
  obtain ⟨M7, hM7⟩ : ∃ M7, memStore32 (memStore32 (memStore32 (memStore32 n6.mem (S + BitVec.ofNat 32 0x34) 11)
      (S + BitVec.ofNat 32 0x30) 7) (S + BitVec.ofNat 32 0x1C) 8) (S + BitVec.ofNat 32 0x24) 3 = M7 := ⟨_, rfl⟩
  have m7 : n7.mem = M7 := by
    rw [u7.mem, ← hM7]; simp +decide only [runBlock, BInstr.run, dqF4, upd, ↓reduceIte]; rw [sp6, v9, v8, v18]; rfl
  have r7 : ∀ q, reg n7 q = (runBlock dqF4 (n6.mem, reg n6)).2 q := fun q => by rw [u7.regs]
  have t7 : St M7 DP n7 0x2F4 (reg n7) := ⟨u7.pc, m7, fun _ => rfl⟩
  have e79 : reg n7 (9 : Fin 32) = BitVec.ofNat 32 (11 + 1) := by
    rw [r7]; simp +decide only [runBlock, BInstr.run, dqF4, upd, ↓reduceIte]; rw [v9]; rfl
  have h7 : ∀ x, Sep (S + BitVec.ofNat 32 0x1C) 0x1C x 1 → M7 x = n6.mem x := fun x hx => by
    rw [← hM7, memStore32_get_sep (by have := hx.sub (c := 8) (l := 4) (by decide); rwa [add_ofNat_assoc] at this),
      memStore32_get_sep (by have := hx.sub (c := 0) (l := 4) (by decide); rwa [add_ofNat_zero] at this),
      memStore32_get_sep (by have := hx.sub (c := 0x14) (l := 4) (by decide); rwa [add_ofNat_assoc] at this),
      memStore32_get_sep (by have := hx.sub (c := 0x18) (l := 4) (by decide); rwa [add_ofNat_assoc] at this)]
  have C7 : DqCode M7 := C6.hi fun x hx => h7 x (F.hiOut (by decide) hx)
  obtain ⟨n8, d8, u8⟩ := t7.notTaken C7.self 0x2F8 dp_at_2f4 (by decide) (by
    show (reg n7 (9 : Fin 32) == reg n7 x0) = false; rw [e79, t7.zero]; rfl)
  -- memory: a word of the frame this stage does not write
  have wM : ∀ d, d + 4 ≤ 0xA50 → (d + 4 ≤ 0x10 ∨ 0x40 ≤ d) → (d + 4 ≤ 0x2FC ∨ 0x62C ≤ d) → (d + 4 ≤ 0x95C ∨ 0x98C ≤ d) →
      memLoad32 M7 (S + BitVec.ofNat 32 d) = memLoad32 M (S + BitVec.ofNat 32 d) := fun d hd h1d h2d h3d =>
    memLoad32_congr fun q hq => by
      rw [add_ofNat_assoc]
      rw [h7 _ (sepS S (by rcases h1d with h | h; exact .inr (by omega); exact .inl (by omega)) (by decide) (by omega)),
        fr6' _ (l16b _ (by omega)) (sepS S (by rcases h3d with h | h; exact .inr (by omega); exact .inl (by omega))
          (by decide) (by omega)),
        fr4' _ (l16b _ (by omega)) (sepS S (by rcases h2d with h | h; exact .inr (by omega); exact .inl (by omega))
          (by decide) (by omega)),
        fr2' _ (l16b _ (by omega)) (sepS S (by rcases h2d with h | h; exact .inr (by omega); exact .inl (by omega))
          (by decide) (by omega)),
        h1 _ (sepS S (by rcases h1d with h | h; exact .inr (by omega); exact .inl (by omega)) (by decide) (by omega))]
  have D7 : DqData M7 := D6.of F fun x hx => h7 x (inFrame (by decide) hx)
  have l16 : ∀ d, d + 4 ≤ 0xA50 → Sep (S + 0xFFFFFFF0) 16 (S + BitVec.ofNat 32 d) 4 := fun d hd =>
    sep_of_le (by rw [hb16, F.at d (by omega)]; omega) (by rw [F.at d (by omega)]; omega)
  have bN0 : memLoad32 M7 (S + BitVec.ofNat 32 0x134) = 0xFFFFFFFF := by
    rw [wM 0x134 (by decide) (.inr (by decide)) (.inl (by decide)) (.inl (by decide))]; exact hN0
  have bN : accV M7 (S + BitVec.ofNat 32 0x134) 12 = p384 := by
    rw [← hN]; exact accV_congr2 12 fun i hi => by
      rw [add_ofNat_assoc, wM _ (by omega) (.inr (by omega)) (.inl (by omega)) (.inl (by omega))]
  have bpw : ∀ k, k < 16 → accV M7 (S + BitVec.ofNat 32 (0x2FC + 48 * k)) 12 = mpow A k := fun k hk => by
    rw [← hT k hk]
    refine accV_congr2 12 fun i hi => ?_
    rw [add_ofNat_assoc, add_ofNat_assoc]
    have e1 : memLoad32 M7 (S + BitVec.ofNat 32 (0x2FC + 48 * k + 4 * i)) =
        memLoad32 n2.mem (S + BitVec.ofNat 32 (0x2FC + 48 * k + 4 * i)) := memLoad32_congr fun q hq => by
      rw [add_ofNat_assoc]
      rw [h7 _ (sepS S (.inl (by omega)) (by decide) (by omega)),
        fr6' _ (l16b _ (by omega)) (sepS S (.inr (by omega)) (by decide) (by omega)),
        fr4' _ (l16b _ (by omega)) (sepS S (.inr (by omega)) (by decide) (by omega))]
    have e2 : memLoad32 n2.mem (S + BitVec.ofNat 32 (0x2FC + 48 * k + 4 * i)) =
        memLoad32 M1 (S + BitVec.ofNat 32 (0x62C + 48 * k + 4 * i)) := by
      rw [load_frame fr2 (l16 _ (by omega)), show 0x2FC + 48 * k + 4 * i = 0x2FC + (48 * k + 4 * i) by omega,
        ← add_ofNat_assoc S 0x2FC, cp_word (by omega) (by decide), add_ofNat_assoc,
        show 0x62C + (48 * k + 4 * i) = 0x62C + 48 * k + 4 * i by omega]
    rw [e1, e2]
    exact memLoad32_congr fun q hq => by
      rw [add_ofNat_assoc]; exact h1 _ (sepS S (.inl (by omega)) (by decide) (by omega))
  have bex : ∀ j, j < 12 → memLoad32 M7 (S + BitVec.ofNat 32 (0x5FC + 4 * j)) = expLimb j := fun j hj => by
    have e1 : memLoad32 M7 (S + BitVec.ofNat 32 (0x5FC + 4 * j)) = memLoad32 n4.mem (S + BitVec.ofNat 32 (0x5FC + 4 * j)) :=
      memLoad32_congr fun q hq => by
        rw [add_ofNat_assoc]
        rw [h7 _ (sepS S (.inl (by omega)) (by decide) (by omega)),
          fr6' _ (l16b _ (by omega)) (sepS S (.inr (by omega)) (by decide) (by omega))]
    rw [e1, load_frame fr4 (l16 _ (by omega)), ← add_ofNat_assoc S 0x5FC, cp_word (by omega) (by decide),
      show (4 * j) = 0 + 4 * j by omega, D2.ex j hj]
  have B7 : DqBase M7 S A := ⟨bN0, bN, bpw, bex,
    by rw [← hM7, slot_word (by decide) (by decide) (.inr (by decide)), memLoad32_store32_same],
    by rw [← hM7, slot_word (by decide) (by decide) (.inl (by decide)), slot_word (by decide) (by decide) (.inl (by decide)),
      slot_word (by decide) (by decide) (.inl (by decide)), memLoad32_store32_same],
    by rw [← hM7, slot_word (by decide) (by decide) (.inl (by decide)), slot_word (by decide) (by decide) (.inl (by decide)),
      memLoad32_store32_same],
    by rw [← hM7, memLoad32_store32_same]⟩
  have k6r : ∀ q : Fin 32, q.val ∈ [2, 3, 4, 20, 24, 25, 27] → reg n6 q = reg n q := fun q hq => by
    rw [k6' q (by revert hq; revert q; decide), r5, runBlock_reg _ _ _ q u4.zero (by simp only [dqF3]; revert hq; revert q; decide),
      k14 q (by revert hq; revert q; decide)]
  have g7 : ∀ q : Fin 32, q.val ∈ [2, 3, 4, 20, 24, 25, 27] → reg n8 q = reg n6 q := fun q hq => by
    rw [u8.regs, r7, runBlock_reg _ _ _ q u6.zero (by simp only [dqF4]; revert hq; revert q; decide)]
  have v7 : ∀ q, reg n8 q = (runBlock dqF4 (n6.mem, reg n6)).2 q := fun q => by rw [u8.regs, r7]
  refine ⟨n8, c1.trans (c2.trans (c3.trans (c4.trans (c5.trans (c6.trans (c7.trans (.single d8))))))),
    ⟨u8.pc, rfl, fun _ => rfl⟩, by rw [u8.mem]; exact C7, by rw [u8.mem]; exact D7, by rw [u8.mem]; exact B7,
    ⟨by rw [g7 sp (by decide), k6r sp (by decide)]; exact rsp, by rw [g7 25 (by decide), k6r 25 (by decide)]; exact r25,
      by rw [v7]; simp +decide only [runBlock, BInstr.run, dqF4, upd, ↓reduceIte]; (try rw [u6.zero]); try rfl,
      by rw [v7]; simp +decide only [runBlock, BInstr.run, dqF4, upd, ↓reduceIte]; rw [sp6, spo]; rfl,
      by rw [v7]; simp +decide only [runBlock, BInstr.run, dqF4, upd, ↓reduceIte]; (try rw [u6.zero]); try rfl,
      by rw [v7]; simp +decide only [runBlock, BInstr.run, dqF4, upd, ↓reduceIte]; rw [sp6]; rfl,
      by rw [v7]; simp +decide only [runBlock, BInstr.run, dqF4, upd, ↓reduceIte]; rw [sp6, spo]; rfl,
      by rw [v7]; simp +decide only [runBlock, BInstr.run, dqF4, upd, ↓reduceIte]; rw [sp6, spo]; rfl⟩,
    by rw [u8.regs, e79], ?_, ?_, ?_, fun x h16 s10 s1C h2FC h95C => ?_,
    fun q hq => by rw [g7 q (by revert hq; revert q; decide), k6r q (by revert hq; revert q; decide)]⟩
  · rw [u8.mem, show 4 * (8 * 11 + 8) = 4 * 96 from rfl, exp_top]
    show accV M7 (S + BitVec.ofNat 32 0x95C) 12 = p3one
    rw [← D4.one]
    refine accV_congr2 12 fun i hi => ?_
    have z1 : memLoad32 M7 (S + BitVec.ofNat 32 0x95C + BitVec.ofNat 32 (4 * i)) =
        memLoad32 n6.mem (S + BitVec.ofNat 32 0x95C + BitVec.ofNat 32 (4 * i)) := memLoad32_congr fun q hq => by
      rw [add_ofNat_assoc, add_ofNat_assoc]; exact h7 _ (sepS S (.inl (by omega)) (by decide) (by omega))
    have hs : Sep (S + 0xFFFFFFF0) 16 (S + BitVec.ofNat 32 0x95C + BitVec.ofNat 32 (4 * i)) 4 := by
      rw [add_ofNat_assoc]; exact l16 _ (by omega)
    rw [z1, load_frame fr6 hs, cp_word (by omega) (by decide)]; rfl
  · have wS : memLoad32 M7 (S + BitVec.ofNat 32 0x10) = memLoad32 M1 (S + BitVec.ofNat 32 0x10) :=
      memLoad32_congr fun q hq => by
        rw [add_ofNat_assoc]
        rw [h7 _ (sepS S (.inr (by omega)) (by decide) (by omega)),
          fr6' _ (l16b _ (by omega)) (sepS S (.inr (by omega)) (by decide) (by omega)),
          fr4' _ (l16b _ (by omega)) (sepS S (.inr (by omega)) (by decide) (by omega)),
          fr2' _ (l16b _ (by omega)) (sepS S (.inr (by omega)) (by decide) (by omega))]
    rw [u8.mem, wS, ← hM1, slot_word (by decide) (by decide) (.inr (by decide)), memLoad32_store32_same]
  · have wS : memLoad32 M7 (S + BitVec.ofNat 32 0x14) = memLoad32 M1 (S + BitVec.ofNat 32 0x14) :=
      memLoad32_congr fun q hq => by
        rw [add_ofNat_assoc]
        rw [h7 _ (sepS S (.inr (by omega)) (by decide) (by omega)),
          fr6' _ (l16b _ (by omega)) (sepS S (.inr (by omega)) (by decide) (by omega)),
          fr4' _ (l16b _ (by omega)) (sepS S (.inr (by omega)) (by decide) (by omega)),
          fr2' _ (l16b _ (by omega)) (sepS S (.inr (by omega)) (by decide) (by omega))]
    rw [u8.mem, wS, ← hM1, memLoad32_store32_same]
  · have s5FC : Sep (S + BitVec.ofNat 32 0x5FC) 48 x 1 := by
      have := h2FC.sub (c := 0x300) (l := 48) (by decide); rwa [add_ofNat_assoc] at this
    have s2FC : Sep (S + BitVec.ofNat 32 0x2FC) 0x300 x 1 := by
      have := h2FC.sub (c := 0) (l := 0x300) (by decide); rwa [add_ofNat_zero] at this
    rw [u8.mem, h7 x s1C, fr6' x h16 h95C, fr4' x h16 s5FC, fr2' x h16 s2FC, h1 x s10]

/-! ## From the entry to the end of the exponentiation -/

theorem accV_keep {M M' : Word → BitVec 8} {S : Word} {c : Nat}
    (h : ∀ q, q < 48 → M' (S + BitVec.ofNat 32 (c + q)) = M (S + BitVec.ofNat 32 (c + q))) :
    accV M' (S + BitVec.ofNat 32 c) 12 = accV M (S + BitVec.ofNat 32 c) 12 :=
  accV_congr2 12 fun i hi => memLoad32_congr fun q hq => by
    rw [add_ofNat_assoc, add_ofNat_assoc]; exact h _ (by omega)

theorem ld_keep {M M' : Word → BitVec 8} {S : Word} {c : Nat}
    (h : ∀ q, q < 4 → M' (S + BitVec.ofNat 32 (c + q)) = M (S + BitVec.ofNat 32 (c + q))) :
    memLoad32 M' (S + BitVec.ofNat 32 c) = memLoad32 M (S + BitVec.ofNat 32 c) :=
  memLoad32_congr fun q hq => by rw [add_ofNat_assoc]; exact h q hq

/-- A frame offset is apart from a stack region below the frame. -/
theorem DqFrame.lowB {S : Word} (F : DqFrame S) {B : Word} {k : Nat} (hB : B.toNat = S.toNat - k) (hk : k ≤ 0x1A0)
    {d : Nat} (hd : d + 1 ≤ 0xA50) : Sep B k (S + BitVec.ofNat 32 d) 1 :=
  sep_of_le (by have := F.lo; rw [hB, F.at d (by omega)]; omega) (by have := F.hi; rw [F.at d (by omega)]; omega)

theorem XOk.lt {x : Nat} {ok : Word} {X : Nat} (h : XOk x ok X) : X < p384 := by
  by_cases hx : x < p384
  · rw [(h.1 hx).2]; exact Nat.mod_lt _ p384_pos
  · rw [(h.2 (by omega)).2]; exact p384_pos

set_option maxRecDepth 100000 in
set_option maxHeartbeats 64000000 in
/-- **From the entry to the end of the exponentiation**: `decompress` decodes
`x`, computes `α = x³ + ax + b`, and leaves `α^((p + 1) / 4)` in Montgomery
form at `S + 0x95C`. -/
theorem dq_toLoop {M : Word → BitVec 8} {n : Machine} {S inp : Word} (C : DqCode M) (D : DqData M) (F : DqFrame S)
    (s : St M DP n 0 (reg n)) (rsp : reg n sp = S + 0xA50) (ra1 : reg n a1 = inp)
    (sI : Sep inp 48 (S + 0xFFFFFE60) 0xBF0) :
    ∃ n', Steps n n' ∧ St n'.mem DP n' 0x5A0 (reg n') ∧ DqCode n'.mem ∧ DqData n'.mem ∧
      XOk (beNat (memBytes M inp 48)) (memLoad32 n'.mem (S + BitVec.ofNat 32 0x14)) (accV n'.mem (S + BitVec.ofNat 32 0xA4) 12) ∧
      accV n'.mem (S + BitVec.ofNat 32 0x104) 12 = dqAlpha (accV n'.mem (S + BitVec.ofNat 32 0xA4) 12) ∧
      accV n'.mem (S + BitVec.ofNat 32 0x95C) 12 = mpow (dqAlpha (accV n'.mem (S + BitVec.ofNat 32 0xA4) 12)) sqrtExp ∧
      memLoad32 n'.mem (S + BitVec.ofNat 32 0x10) = reg n a2 ∧ memLoad32 n'.mem (S + BitVec.ofNat 32 0x18) = reg n a0 ∧
      (∀ k, k < 13 → memLoad32 n'.mem (S + BitVec.ofNat 32 (0xA4C - 4 * k)) = reg n (savedReg k)) ∧
      DqRegs n' S ∧ reg n' (3 : Fin 32) = reg n (3 : Fin 32) ∧ reg n' (4 : Fin 32) = reg n (4 : Fin 32) ∧
      ∀ x, Sep (S + 0xFFFFFE60) 0xBF0 x 1 → n'.mem x = M x := by
  have hSl := F.lo; have hSh := F.hi; have hSa := F.al
  have hb16 : (S + 0xFFFFFFF0).toNat = S.toNat - 16 := F.below 16 (by decide) (by decide)
  have hbF : (S + 0xFFFFFF10).toNat = S.toNat - 0xF0 := F.below 0xF0 (by decide) (by decide)
  have hb1A : (S + 0xFFFFFE60).toNat = S.toNat - 0x1A0 := F.below 0x1A0 (by decide) (by decide)
  have sq : ∀ c l d, c + l ≤ 0xA50 → d + 1 ≤ 0xA50 → (c + l ≤ d ∨ d + 1 ≤ c) →
      Sep (S + BitVec.ofNat 32 c) l (S + BitVec.ofNat 32 d) 1 := fun c l d h1 h2 h3 => sepS S h3 (by omega) (by omega)
  have inFrame : ∀ {c l : Nat} {x : Word}, c + l ≤ 0xA50 → Sep (S + 0xFFFFFE60) 0xBF0 x 1 →
      Sep (S + BitVec.ofNat 32 c) l x 1 := fun {c l x} h hx => by
    have := hx.sub (c := 0x1A0 + c) (l := l) (by omega)
    rwa [BitVec.add_assoc, show (0xFFFFFE60 : Word) + BitVec.ofNat 32 (0x1A0 + c) = BitVec.ofNat 32 c by
      apply BitVec.eq_of_toNat_eq
      rw [BitVec.toNat_add, BitVec.toNat_ofNat, BitVec.toNat_ofNat, show (0xFFFFFE60 : Word).toNat = 0xFFFFFE60 from rfl]
      omega] at this
  have lowIn : ∀ {k : Nat} {B : Word} {x : Word}, B.toNat = S.toNat - k → 0 < k → k ≤ 0x1A0 →
      Sep (S + 0xFFFFFE60) 0xBF0 x 1 → Sep B k x 1 := fun {k B x} hB hk hk' hx => by
    have := hx.sub (c := 0x1A0 - k) (l := k) (by omega)
    rwa [show S + 0xFFFFFE60 + BitVec.ofNat 32 (0x1A0 - k) = B by
      apply BitVec.eq_of_toNat_eq; rw [BitVec.toNat_add, BitVec.toNat_ofNat, hb1A, hB]; omega] at this
  -- decode x
  obtain ⟨n1, c1, u1, C1, D1, sv1, xo1, fr1, sp1, e21, e19, e25, g31, g41⟩ := dq_stA C D F s rsp ra1 sI
  have hX1 := xo1.lt
  -- α
  obtain ⟨n2, c2, u2, C2, D2, hα2, fr2, k2⟩ := dq_stB C1 D1 F u1 sp1 hX1
  have eX2 : accV n2.mem (S + BitVec.ofNat 32 0xA4) 12 = accV n1.mem (S + BitVec.ofNat 32 0xA4) 12 :=
    accV_keep fun q hq => fr2 _ (F.lowB hbF (by decide) (by omega)) (sq _ _ _ (by decide) (by omega) (.inr (by omega)))
      (sq _ _ _ (by decide) (by omega) (.inr (by omega))) (sq _ _ _ (by decide) (by omega) (.inr (by omega)))
  have sp2 : reg n2 sp = S := by rw [k2 sp rfl]; exact sp1
  -- the constants
  obtain ⟨n3, c3, u3, C3, D3, hN03, hN3, hαc3, e324, e318, e322, fr3, k3⟩ := dq_stC C2 D2 F u2 sp2
  have eα3 : accV n3.mem (S + BitVec.ofNat 32 0x104) 12 = accV n2.mem (S + BitVec.ofNat 32 0x104) 12 :=
    accV_keep fun q hq => fr3 _ (F.lowB hb16 (by decide) (by omega)) (sq _ _ _ (by decide) (by omega) (.inr (by omega)))
      (sq _ _ _ (by decide) (by omega) (.inr (by omega))) (sq _ _ _ (by decide) (by omega) (.inr (by omega)))
  have eX3 : accV n3.mem (S + BitVec.ofNat 32 0xA4) 12 = accV n1.mem (S + BitVec.ofNat 32 0xA4) 12 := by
    rw [← eX2]
    exact accV_keep fun q hq => fr3 _ (F.lowB hb16 (by decide) (by omega)) (sq _ _ _ (by decide) (by omega) (.inr (by omega)))
      (sq _ _ _ (by decide) (by omega) (.inr (by omega))) (sq _ _ _ (by decide) (by omega) (.inr (by omega)))
  have sp3 : reg n3 sp = S := by rw [k3 sp (by decide)]; exact sp2
  have hA3 : accV n3.mem (S + BitVec.ofNat 32 0x104) 12 < p384 := by rw [eα3, hα2]; exact dqAlpha_lt _
  -- start the table
  obtain ⟨n4, c4, u4, C4, D4, hT4, s184, e419, e424, fr4, k4⟩ := dq_stD C3 D3 F u3 sp3 e324 hA3
  have keep4 : ∀ c, c + 48 ≤ 0xA50 → (c + 48 ≤ 0x18 ∨ 0x1C ≤ c) → (c + 48 ≤ 0x2FC ∨ 0x95C ≤ c) →
      accV n4.mem (S + BitVec.ofNat 32 c) 12 = accV n3.mem (S + BitVec.ofNat 32 c) 12 := fun c h1 h2 h3 =>
    accV_keep fun q hq => fr4 _ (F.lowB hb16 (by decide) (by omega))
      (sq _ _ _ (by decide) (by omega) (by rcases h2 with h | h; exact .inr (by omega); exact .inl (by omega)))
      (sq _ _ _ (by decide) (by omega) (by rcases h3 with h | h; exact .inr (by omega); exact .inl (by omega)))
  have sp4 : reg n4 sp = S := by rw [k4 sp (by decide)]; exact sp3
  have hN04 : memLoad32 n4.mem (S + BitVec.ofNat 32 0x134) = 0xFFFFFFFF := by
    rw [← hN03]; exact ld_keep fun q hq => fr4 _ (F.lowB hb16 (by decide) (by omega))
      (sq _ _ _ (by decide) (by omega) (.inl (by omega))) (sq _ _ _ (by decide) (by omega) (.inr (by omega)))
  have hN4 : accV n4.mem (S + BitVec.ofNat 32 0x134) 12 = p384 := by
    rw [keep4 0x134 (by decide) (.inr (by decide)) (.inl (by decide)), hN3]
  have hAv4 : accV n4.mem (S + BitVec.ofNat 32 0x29C) 12 = accV n3.mem (S + BitVec.ofNat 32 0x104) 12 := by
    rw [keep4 0x29C (by decide) (.inr (by decide)) (.inl (by decide)), hαc3, eα3]
  -- the table loop
  obtain ⟨n5, d5, u5⟩ := u4.aluImm C4.self dp_at_230 (off' := 0x232) (by decide)
  obtain ⟨n6, d6, u6⟩ := u5.self.notTaken C4.self 0x234 dp_at_232 (by decide) (by
    show (reg n5 (8 : Fin 32) == reg n5 x0) = false
    rw [u5.regs]; simp +decide only [upd, ↓reduceIte]; rw [u4.zero]; rfl)
  have g6 : ∀ q, q ≠ (8 : Fin 32) → reg n6 q = reg n4 q := fun q h => by rw [u6.regs, u5.regs, updz u4.zero h]
  have e68 : reg n6 (8 : Fin 32) = BitVec.ofNat 32 (14 - 0) := by
    rw [u6.regs, u5.regs]; simp +decide only [upd, ↓reduceIte]; rw [u4.zero]; rfl
  obtain ⟨n7, c7, u7, C7, hT7, fr7, k7⟩ := dq_tbl F hA3 13 0 (by decide) C4 ⟨u6.pc, u6.mem, fun _ => rfl⟩
    (by rw [g6 sp (by decide)]; exact sp4) (by rw [g6 19 (by decide), e419]) e68 hN04 hN4 hAv4 hT4
  have keep7 : ∀ c, c + 48 ≤ 0xA50 → (c + 48 ≤ 0x68C ∨ 0x92C ≤ c) → (c + 48 ≤ 0x9EC ∨ 0xA1C ≤ c) →
      accV n7.mem (S + BitVec.ofNat 32 c) 12 = accV n4.mem (S + BitVec.ofNat 32 c) 12 := fun c h1 h2 h3 => by
    exact accV_keep fun q hq => fr7 _ (F.lowB hbF (by decide) (by omega))
      (sq _ _ _ (by decide) (by omega) (by rcases h3 with h | h; exact .inr (by omega); exact .inl (by omega)))
      (sq _ _ _ (by decide) (by omega) (by rcases h2 with h | h; exact .inr (by omega); exact .inl (by omega)))
  have ld7 : ∀ d, d + 4 ≤ 0xA50 → (d + 4 ≤ 0x68C ∨ 0x92C ≤ d) → (d + 4 ≤ 0x9EC ∨ 0xA1C ≤ d) →
      memLoad32 n7.mem (S + BitVec.ofNat 32 d) = memLoad32 n4.mem (S + BitVec.ofNat 32 d) := fun d h1 h2 h3 => by
    exact ld_keep fun q hq => fr7 _ (F.lowB hbF (by decide) (by omega))
      (sq _ _ _ (by decide) (by omega) (by rcases h3 with h | h; exact .inr (by omega); exact .inl (by omega)))
      (sq _ _ _ (by decide) (by omega) (by rcases h2 with h | h; exact .inr (by omega); exact .inl (by omega)))
  have k67 : ∀ q : Fin 32, q.val ∈ [2, 3, 4, 18, 20, 21, 22, 23, 24, 25, 26, 27] → reg n7 q = reg n4 q := fun q hq => by
    rw [k7 q hq, g6 q (by revert hq; revert q; decide)]
  have kk3 : ∀ q : Fin 32, q.val ∈ [2, 3, 4, 19, 20, 21, 25] → reg n3 q = reg n1 q := fun q hq => by
    rw [k3 q hq, k2 q (by revert hq; revert q; decide)]
  have D7 : DqData n7.mem := D4.of F fun x hx => fr7 x (lowIn hbF (by decide) (by decide) hx) (inFrame (by decide) hx)
    (inFrame (by decide) hx)
  -- set up the exponentiation
  obtain ⟨n8, c8, u8, C8, D8, B8, R8, e89, hz8, s108, s148, fr8, k8⟩ := dq_stF C7 D7 F u7
    (by rw [k67 sp (by decide)]; exact sp4) (by rw [k67 18 (by decide), k4 18 (by decide), e318])
    (by rw [k67 22 (by decide), k4 22 (by decide), e322]) (by rw [k67 24 (by decide), e424])
    (by rw [k67 25 (by decide), k4 25 (by decide), kk3 25 (by decide), e25]) hT7
    (by rw [ld7 0x134 (by decide) (.inl (by decide)) (.inl (by decide)), hN04])
    (by rw [keep7 0x134 (by decide) (.inl (by decide)) (.inl (by decide)), hN4])
  have hb10 : ∀ c, c + 48 ≤ 0xA50 → (c + 48 ≤ 0x10 ∨ 0x18 ≤ c) → (c + 48 ≤ 0x1C ∨ 0x38 ≤ c) → (c + 48 ≤ 0x2FC ∨ 0x62C ≤ c) →
      (c + 48 ≤ 0x95C ∨ 0x98C ≤ c) → accV n8.mem (S + BitVec.ofNat 32 c) 12 = accV n7.mem (S + BitVec.ofNat 32 c) 12 :=
    fun c h1 h2 h3 h4 h5 => accV_keep fun q hq => fr8 _ (F.lowB hb16 (by decide) (by omega))
      (sq _ _ _ (by decide) (by omega) (by rcases h2 with h | h; exact .inr (by omega); exact .inl (by omega)))
      (sq _ _ _ (by decide) (by omega) (by rcases h3 with h | h; exact .inr (by omega); exact .inl (by omega)))
      (sq _ _ _ (by decide) (by omega) (by rcases h4 with h | h; exact .inr (by omega); exact .inl (by omega)))
      (sq _ _ _ (by decide) (by omega) (by rcases h5 with h | h; exact .inr (by omega); exact .inl (by omega)))
  -- the exponentiation
  obtain ⟨n9, c9, u9, C9, B9, fr9, R9, hz9, g39, g49⟩ := dq_limbs F 11 (by decide) C8 B8 R8 u8 e89 hz8
  have hbL : ∀ c, c + 48 ≤ 0xA50 → (c + 48 ≤ 0x20 ∨ 0x40 ≤ c) → (c + 48 ≤ 0x62C ∨ 0x65C ≤ c) → (c + 48 ≤ 0x95C ∨ 0xA1C ≤ c) →
      accV n9.mem (S + BitVec.ofNat 32 c) 12 = accV n8.mem (S + BitVec.ofNat 32 c) 12 :=
    fun c h1 h2 h3 h4 => accV_keep fun q hq => fr9 _ (F.lowB hbF (by decide) (by omega))
      (sq _ _ _ (by decide) (by omega) (by rcases h2 with h | h; exact .inr (by omega); exact .inl (by omega)))
      (sq _ _ _ (by decide) (by omega) (by rcases h3 with h | h; exact .inr (by omega); exact .inl (by omega)))
      (sq _ _ _ (by decide) (by omega) (by rcases h4 with h | h; exact .inr (by omega); exact .inl (by omega)))
  have ldL : ∀ d, d + 4 ≤ 0xA50 → (d + 4 ≤ 0x20 ∨ 0x40 ≤ d) → (d + 4 ≤ 0x62C ∨ 0x65C ≤ d) → (d + 4 ≤ 0x95C ∨ 0xA1C ≤ d) →
      memLoad32 n9.mem (S + BitVec.ofNat 32 d) = memLoad32 n8.mem (S + BitVec.ofNat 32 d) :=
    fun d h1 h2 h3 h4 => ld_keep fun q hq => fr9 _ (F.lowB hbF (by decide) (by omega))
      (sq _ _ _ (by decide) (by omega) (by rcases h2 with h | h; exact .inr (by omega); exact .inl (by omega)))
      (sq _ _ _ (by decide) (by omega) (by rcases h3 with h | h; exact .inr (by omega); exact .inl (by omega)))
      (sq _ _ _ (by decide) (by omega) (by rcases h4 with h | h; exact .inr (by omega); exact .inl (by omega)))
  -- x and α, back to where they were written
  have eX9 : accV n9.mem (S + BitVec.ofNat 32 0xA4) 12 = accV n1.mem (S + BitVec.ofNat 32 0xA4) 12 := by
    rw [hbL 0xA4 (by decide) (.inr (by decide)) (.inl (by decide)) (.inl (by decide)),
      hb10 0xA4 (by decide) (.inr (by decide)) (.inr (by decide)) (.inl (by decide)) (.inl (by decide)),
      keep7 0xA4 (by decide) (.inl (by decide)) (.inl (by decide)),
      keep4 0xA4 (by decide) (.inr (by decide)) (.inl (by decide)), eX3]
  have eα9 : accV n9.mem (S + BitVec.ofNat 32 0x104) 12 = accV n3.mem (S + BitVec.ofNat 32 0x104) 12 := by
    rw [hbL 0x104 (by decide) (.inr (by decide)) (.inl (by decide)) (.inl (by decide)),
      hb10 0x104 (by decide) (.inr (by decide)) (.inr (by decide)) (.inl (by decide)) (.inl (by decide)),
      keep7 0x104 (by decide) (.inl (by decide)) (.inl (by decide)),
      keep4 0x104 (by decide) (.inr (by decide)) (.inl (by decide))]
  have hAlpha : accV n3.mem (S + BitVec.ofNat 32 0x104) 12 = dqAlpha (accV n9.mem (S + BitVec.ofNat 32 0xA4) 12) := by
    rw [eα3, hα2, eX9]
  have D9 : DqData n9.mem := D8.of F fun x hx => fr9 x (lowIn hbF (by decide) (by decide) hx) (inFrame (by decide) hx)
    (inFrame (by decide) hx) (inFrame (by decide) hx)
  -- a word of the frame below S + 0x20, or of the saves, through each stage
  have w8 : ∀ d, d + 4 ≤ 0xA50 → (d + 4 ≤ 0x10 ∨ 0x18 ≤ d) → (d + 4 ≤ 0x1C ∨ 0x38 ≤ d) → (d + 4 ≤ 0x2FC ∨ 0x62C ≤ d) →
      (d + 4 ≤ 0x95C ∨ 0x98C ≤ d) → memLoad32 n8.mem (S + BitVec.ofNat 32 d) = memLoad32 n7.mem (S + BitVec.ofNat 32 d) :=
    fun d h1 h2 h3 h4 h5 => ld_keep fun q hq => fr8 _ (F.lowB hb16 (by decide) (by omega))
      (sq _ _ _ (by decide) (by omega) (by rcases h2 with h | h; exact .inr (by omega); exact .inl (by omega)))
      (sq _ _ _ (by decide) (by omega) (by rcases h3 with h | h; exact .inr (by omega); exact .inl (by omega)))
      (sq _ _ _ (by decide) (by omega) (by rcases h4 with h | h; exact .inr (by omega); exact .inl (by omega)))
      (sq _ _ _ (by decide) (by omega) (by rcases h5 with h | h; exact .inr (by omega); exact .inl (by omega)))
  have w4 : ∀ d, d + 4 ≤ 0xA50 → (d + 4 ≤ 0x18 ∨ 0x1C ≤ d) → (d + 4 ≤ 0x2FC ∨ 0x95C ≤ d) →
      memLoad32 n4.mem (S + BitVec.ofNat 32 d) = memLoad32 n3.mem (S + BitVec.ofNat 32 d) :=
    fun d h1 h2 h3 => ld_keep fun q hq => fr4 _ (F.lowB hb16 (by decide) (by omega))
      (sq _ _ _ (by decide) (by omega) (by rcases h2 with h | h; exact .inr (by omega); exact .inl (by omega)))
      (sq _ _ _ (by decide) (by omega) (by rcases h3 with h | h; exact .inr (by omega); exact .inl (by omega)))
  have wS : ∀ k, k < 13 → memLoad32 n3.mem (S + BitVec.ofNat 32 (0xA4C - 4 * k)) =
      memLoad32 n1.mem (S + BitVec.ofNat 32 (0xA4C - 4 * k)) := fun k hk => by
    rw [ld_keep fun q hq => fr3 _ (F.lowB hb16 (by decide) (by omega)) (sq _ _ _ (by decide) (by omega) (.inl (by omega)))
      (sq _ _ _ (by decide) (by omega) (.inl (by omega))) (sq _ _ _ (by decide) (by omega) (.inl (by omega)))]
    exact ld_keep fun q hq => fr2 _ (F.lowB hbF (by decide) (by omega)) (sq _ _ _ (by decide) (by omega) (.inl (by omega)))
      (sq _ _ _ (by decide) (by omega) (.inl (by omega))) (sq _ _ _ (by decide) (by omega) (.inl (by omega)))
  refine ⟨n9, c1.trans (c2.trans (c3.trans (c4.trans (.cons d5 (.cons d6 (c7.trans (c8.trans c9))))))), u9, C9, D9,
    ?_, by rw [eα9, hAlpha], by rw [hz9, hAlpha], ?_, ?_, fun k hk => ?_, R9, ?_, ?_, fun x hx => ?_⟩
  · rw [eX9, ldL 0x14 (by decide) (.inl (by decide)) (.inl (by decide)) (.inl (by decide)), s148, k67 20 (by decide),
      k4 20 (by decide), kk3 20 (by decide)]
    exact xo1
  · rw [ldL 0x10 (by decide) (.inl (by decide)) (.inl (by decide)) (.inl (by decide)), s108, k67 21 (by decide),
      k4 21 (by decide), kk3 21 (by decide), e21]
  · rw [ldL 0x18 (by decide) (.inl (by decide)) (.inl (by decide)) (.inl (by decide)),
      w8 0x18 (by decide) (.inr (by decide)) (.inl (by decide)) (.inl (by decide)) (.inl (by decide)),
      ld7 0x18 (by decide) (.inl (by decide)) (.inl (by decide)), s184, kk3 19 (by decide), e19]
  · rw [ldL _ (by omega) (.inr (by omega)) (.inr (by omega)) (.inr (by omega)),
      w8 _ (by omega) (.inr (by omega)) (.inr (by omega)) (.inr (by omega)) (.inr (by omega)),
      ld7 _ (by omega) (.inr (by omega)) (.inr (by omega)), w4 _ (by omega) (.inr (by omega)) (.inr (by omega)), wS k hk]
    exact sv1 k hk
  · rw [g39, k8 3 (by decide), k67 3 (by decide), k4 3 (by decide), kk3 3 (by decide), g31]
  · rw [g49, k8 4 (by decide), k67 4 (by decide), k4 4 (by decide), kk3 4 (by decide), g41]
  · rw [fr9 x (lowIn hbF (by decide) (by decide) hx) (inFrame (by decide) hx) (inFrame (by decide) hx) (inFrame (by decide) hx),
      fr8 x (lowIn hb16 (by decide) (by decide) hx) (inFrame (by decide) hx) (inFrame (by decide) hx) (inFrame (by decide) hx)
        (inFrame (by decide) hx),
      fr7 x (lowIn hbF (by decide) (by decide) hx) (inFrame (by decide) hx) (inFrame (by decide) hx),
      fr4 x (lowIn hb16 (by decide) (by decide) hx) (inFrame (by decide) hx) (inFrame (by decide) hx),
      fr3 x (lowIn hb16 (by decide) (by decide) hx) (inFrame (by decide) hx) (inFrame (by decide) hx) (inFrame (by decide) hx),
      fr2 x (lowIn hbF (by decide) (by decide) hx) (inFrame (by decide) hx) (inFrame (by decide) hx) (inFrame (by decide) hx),
      fr1 x (lowIn hb1A (by decide) (by decide) hx) (inFrame (by decide) hx) (inFrame (by decide) hx)]

end C3.RV32.Dq
