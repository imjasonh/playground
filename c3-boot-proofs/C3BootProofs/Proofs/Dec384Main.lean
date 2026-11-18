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

end C3.RV32.Dq
