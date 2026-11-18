import C3BootProofs.Proofs.Dec256Pre

/-!
# P-256 point decompression

`<primeorder::affine::AffinePoint<NistP256> as DecompressPoint>::decompress`
from its entry to the limb loop: the prologue, decoding `x`, `α = x³ + ax + b`,
and the exponentiation's setup.
-/

namespace C3.RV32.Gd

open C3.Image C3.RV32.Dq C3.RV32.P3 C3.RV32.P2 C3.RV32.Fs C3.RV32.Gs

set_option maxRecDepth 20000

def gdA1 : List BInstr :=
  [.aluImm .add sp sp 0xFFFFF8F0, .aluImm .add a3 sp 0x700, .sw a3 ra 0xC, .sw a3 (8 : Fin 32) 0x8,
   .sw a3 (9 : Fin 32) 0x4, .sw a3 (18 : Fin 32) 0x0, .aluImm .add a3 sp 0x680, .sw a3 (19 : Fin 32) 0x7C,
   .sw a3 (20 : Fin 32) 0x78, .sw a3 (21 : Fin 32) 0x74, .sw a3 (22 : Fin 32) 0x70, .sw a3 (23 : Fin 32) 0x6C,
   .sw a3 (24 : Fin 32) 0x68, .sw a3 (25 : Fin 32) 0x64, .sw a3 (26 : Fin 32) 0x60, .sw a3 (27 : Fin 32) 0x5C,
   .alu .add (27 : Fin 32) x0 a2, .alu .add (25 : Fin 32) x0 a0, .aluImm .add a0 sp 0x40]
def gdA2 : List BInstr := [.aluImm .add a0 sp 0x64, .aluImm .add a2 x0 0x20, .aluImm .add a1 x0 0x0]
def gdA3 : List BInstr :=
  [.lbu (26 : Fin 32) sp 0x60, .aluImm .add a0 sp 0x84, .aluImm .add a1 sp 0x64, .aluImm .add a2 sp 0x40,
   .alu .add a3 x0 (26 : Fin 32)]

theorem gdA1_end : blockEnd p256DecompressCode 0 gdA1 = some 0x42 := by decide
theorem gdA2_end : blockEnd p256DecompressCode 0x4A gdA2 = some 0x52 := by decide
theorem gdA3_end : blockEnd p256DecompressCode 0x5A gdA3 = some 0x66 := by decide

/-- The prologue's saves, in order. -/
def gdSaves (M : Word → BitVec 8) (S : Word) (n : Machine) : Word → BitVec 8 :=
  memStore32 (memStore32 (memStore32 (memStore32 (memStore32 (memStore32 (memStore32 (memStore32 (memStore32 (memStore32 (memStore32 (memStore32 (memStore32 (M) (S + BitVec.ofNat 32 0x70c) (reg n ra)) (S + BitVec.ofNat 32 0x708) (reg n (8 : Fin 32))) (S + BitVec.ofNat 32 0x704) (reg n (9 : Fin 32))) (S + BitVec.ofNat 32 0x700) (reg n (18 : Fin 32))) (S + BitVec.ofNat 32 0x6fc) (reg n (19 : Fin 32))) (S + BitVec.ofNat 32 0x6f8) (reg n (20 : Fin 32))) (S + BitVec.ofNat 32 0x6f4) (reg n (21 : Fin 32))) (S + BitVec.ofNat 32 0x6f0) (reg n (22 : Fin 32))) (S + BitVec.ofNat 32 0x6ec) (reg n (23 : Fin 32))) (S + BitVec.ofNat 32 0x6e8) (reg n (24 : Fin 32))) (S + BitVec.ofNat 32 0x6e4) (reg n (25 : Fin 32))) (S + BitVec.ofNat 32 0x6e0) (reg n (26 : Fin 32))) (S + BitVec.ofNat 32 0x6dc) (reg n (27 : Fin 32))

set_option maxRecDepth 100000 in
set_option maxHeartbeats 16000000 in
/-- **The prologue**, from the entry to `from_repr`'s call at 0x42: save `ra`
and `s0..s11` at the top of the frame, and open the frame at `S`. -/
theorem gd_pro {M : Word → BitVec 8} {n : Machine} {S : Word} (C : GdCode M) (F : Fr S 0x710)
    (s : St M GD n 0 (reg n)) (rsp : reg n sp = S + 0x710) :
    ∃ n', Steps n n' ∧ St (gdSaves M S n) GD n' 0x42 (reg n') ∧
      reg n' sp = S ∧ reg n' (27 : Fin 32) = reg n a2 ∧ reg n' (25 : Fin 32) = reg n a0 ∧
      reg n' a0 = S + BitVec.ofNat 32 0x40 ∧ ∀ q, q.val ∈ [3, 4, 11] → reg n' q = reg n q := by
  have hz := s.zero
  have hSl := F.lo; have hSh := F.hi; have hSa := F.al
  have hA : aluEval .add (aluEval .add (S + 0x710) 0xFFFFF8F0) 0x700 = S + BitVec.ofNat 32 0x700 := by
    show S + 0x710 + 0xFFFFF8F0 + 0x700 = S + BitVec.ofNat 32 0x700
    rw [BitVec.add_assoc, BitVec.add_assoc]; rfl
  have hB : aluEval .add (aluEval .add (S + 0x710) 0xFFFFF8F0) 0x680 = S + BitVec.ofNat 32 0x680 := by
    show S + 0x710 + 0xFFFFF8F0 + 0x680 = S + BitVec.ofNat 32 0x680
    rw [BitVec.add_assoc, BitVec.add_assoc]; rfl
  have alB : ∀ (c : Nat) (k : Word), c + k.toNat + 4 ≤ 0x710 → (c + k.toNat) % 4 = 0 →
      (S + BitVec.ofNat 32 c + k).toNat % 4 = 0 := fun c k h1 h2 => by
    rw [frame_lit k (by omega), F.at _ (by omega)]; omega
  have sepB : ∀ (c : Nat) (k : Word), c + k.toNat + 4 ≤ 0x710 →
      Sep (S + BitVec.ofNat 32 c + k) 4 GD p256DecompressCode.length := fun c k h1 => by
    rw [frame_lit k (by omega)]; exact F.sepHi (by omega) (by decide) (by decide)
  obtain ⟨n1, c1, u1⟩ := s.block gdA1 C.self gdA1_end (by
    simp only [BlockOk, BInstr.ok, BInstr.run, gdA1]; simp +decide only [upd, ↓reduceIte, true_and, and_true]
    rw [rsp, hA, hB]
    exact ⟨⟨alB 0x700 0xC (by decide) (by decide), sepB 0x700 0xC (by decide)⟩,
      ⟨alB 0x700 0x8 (by decide) (by decide), sepB 0x700 0x8 (by decide)⟩,
      ⟨alB 0x700 0x4 (by decide) (by decide), sepB 0x700 0x4 (by decide)⟩,
      ⟨alB 0x700 0x0 (by decide) (by decide), sepB 0x700 0x0 (by decide)⟩,
      ⟨alB 0x680 0x7C (by decide) (by decide), sepB 0x680 0x7C (by decide)⟩,
      ⟨alB 0x680 0x78 (by decide) (by decide), sepB 0x680 0x78 (by decide)⟩,
      ⟨alB 0x680 0x74 (by decide) (by decide), sepB 0x680 0x74 (by decide)⟩,
      ⟨alB 0x680 0x70 (by decide) (by decide), sepB 0x680 0x70 (by decide)⟩,
      ⟨alB 0x680 0x6C (by decide) (by decide), sepB 0x680 0x6C (by decide)⟩,
      ⟨alB 0x680 0x68 (by decide) (by decide), sepB 0x680 0x68 (by decide)⟩,
      ⟨alB 0x680 0x64 (by decide) (by decide), sepB 0x680 0x64 (by decide)⟩,
      ⟨alB 0x680 0x60 (by decide) (by decide), sepB 0x680 0x60 (by decide)⟩,
      ⟨alB 0x680 0x5C (by decide) (by decide), sepB 0x680 0x5C (by decide)⟩⟩)
  have m1 : n1.mem = gdSaves M S n := by
    rw [u1.mem]; simp only [runBlock, BInstr.run, gdA1]; simp +decide only [upd, ↓reduceIte]
    rw [rsp, hA, hB]
    simp (disch := decide) only [frame_lit]
    rfl
  refine ⟨n1, c1, ⟨u1.pc, m1, fun _ => rfl⟩, ?_, ?_, ?_, ?_, fun q hq => ?_⟩
  · rw [u1.regs]; simp +decide only [runBlock, BInstr.run, gdA1, upd, ↓reduceIte]; rw [rsp]
    show S + 0x710 + 0xFFFFF8F0 = S
    rw [BitVec.add_assoc]; exact BitVec.add_zero S
  · rw [u1.regs]; simp +decide only [runBlock, BInstr.run, gdA1, upd, ↓reduceIte]; exact BitVec.zero_add _
  · rw [u1.regs]; simp +decide only [runBlock, BInstr.run, gdA1, upd, ↓reduceIte]; exact BitVec.zero_add _
  · rw [u1.regs]; simp +decide only [runBlock, BInstr.run, gdA1, upd, ↓reduceIte]; rw [rsp]
    show S + 0x710 + 0xFFFFF8F0 + 0x40 = S + BitVec.ofNat 32 0x40
    rw [BitVec.add_assoc, BitVec.add_assoc]; rfl
  · rw [u1.regs, runBlock_reg _ _ _ q hz (by simp only [gdA1]; revert hq; revert q; decide)]

theorem gdSaves_read {M : Word → BitVec 8} {S : Word} {n : Machine} :
    ∀ k, k < 13 → memLoad32 (gdSaves M S n) (S + BitVec.ofNat 32 (0x70C - 4 * k)) = reg n (savedReg k) := by
  intro k hk
  match k, hk with
  | 0, _ => unfold gdSaves; rw [ld_st_frame (by decide) (by decide) (by decide) (by decide), ite_eq_right (by decide), ld_st_frame (by decide) (by decide) (by decide) (by decide), ite_eq_right (by decide), ld_st_frame (by decide) (by decide) (by decide) (by decide), ite_eq_right (by decide), ld_st_frame (by decide) (by decide) (by decide) (by decide), ite_eq_right (by decide), ld_st_frame (by decide) (by decide) (by decide) (by decide), ite_eq_right (by decide), ld_st_frame (by decide) (by decide) (by decide) (by decide), ite_eq_right (by decide), ld_st_frame (by decide) (by decide) (by decide) (by decide), ite_eq_right (by decide), ld_st_frame (by decide) (by decide) (by decide) (by decide), ite_eq_right (by decide), ld_st_frame (by decide) (by decide) (by decide) (by decide), ite_eq_right (by decide), ld_st_frame (by decide) (by decide) (by decide) (by decide), ite_eq_right (by decide), ld_st_frame (by decide) (by decide) (by decide) (by decide), ite_eq_right (by decide), ld_st_frame (by decide) (by decide) (by decide) (by decide), ite_eq_right (by decide), ld_st_frame (by decide) (by decide) (by decide) (by decide), ite_eq_left (by decide)]; rfl
  | 1, _ => unfold gdSaves; rw [ld_st_frame (by decide) (by decide) (by decide) (by decide), ite_eq_right (by decide), ld_st_frame (by decide) (by decide) (by decide) (by decide), ite_eq_right (by decide), ld_st_frame (by decide) (by decide) (by decide) (by decide), ite_eq_right (by decide), ld_st_frame (by decide) (by decide) (by decide) (by decide), ite_eq_right (by decide), ld_st_frame (by decide) (by decide) (by decide) (by decide), ite_eq_right (by decide), ld_st_frame (by decide) (by decide) (by decide) (by decide), ite_eq_right (by decide), ld_st_frame (by decide) (by decide) (by decide) (by decide), ite_eq_right (by decide), ld_st_frame (by decide) (by decide) (by decide) (by decide), ite_eq_right (by decide), ld_st_frame (by decide) (by decide) (by decide) (by decide), ite_eq_right (by decide), ld_st_frame (by decide) (by decide) (by decide) (by decide), ite_eq_right (by decide), ld_st_frame (by decide) (by decide) (by decide) (by decide), ite_eq_right (by decide), ld_st_frame (by decide) (by decide) (by decide) (by decide), ite_eq_left (by decide)]; rfl
  | 2, _ => unfold gdSaves; rw [ld_st_frame (by decide) (by decide) (by decide) (by decide), ite_eq_right (by decide), ld_st_frame (by decide) (by decide) (by decide) (by decide), ite_eq_right (by decide), ld_st_frame (by decide) (by decide) (by decide) (by decide), ite_eq_right (by decide), ld_st_frame (by decide) (by decide) (by decide) (by decide), ite_eq_right (by decide), ld_st_frame (by decide) (by decide) (by decide) (by decide), ite_eq_right (by decide), ld_st_frame (by decide) (by decide) (by decide) (by decide), ite_eq_right (by decide), ld_st_frame (by decide) (by decide) (by decide) (by decide), ite_eq_right (by decide), ld_st_frame (by decide) (by decide) (by decide) (by decide), ite_eq_right (by decide), ld_st_frame (by decide) (by decide) (by decide) (by decide), ite_eq_right (by decide), ld_st_frame (by decide) (by decide) (by decide) (by decide), ite_eq_right (by decide), ld_st_frame (by decide) (by decide) (by decide) (by decide), ite_eq_left (by decide)]; rfl
  | 3, _ => unfold gdSaves; rw [ld_st_frame (by decide) (by decide) (by decide) (by decide), ite_eq_right (by decide), ld_st_frame (by decide) (by decide) (by decide) (by decide), ite_eq_right (by decide), ld_st_frame (by decide) (by decide) (by decide) (by decide), ite_eq_right (by decide), ld_st_frame (by decide) (by decide) (by decide) (by decide), ite_eq_right (by decide), ld_st_frame (by decide) (by decide) (by decide) (by decide), ite_eq_right (by decide), ld_st_frame (by decide) (by decide) (by decide) (by decide), ite_eq_right (by decide), ld_st_frame (by decide) (by decide) (by decide) (by decide), ite_eq_right (by decide), ld_st_frame (by decide) (by decide) (by decide) (by decide), ite_eq_right (by decide), ld_st_frame (by decide) (by decide) (by decide) (by decide), ite_eq_right (by decide), ld_st_frame (by decide) (by decide) (by decide) (by decide), ite_eq_left (by decide)]; rfl
  | 4, _ => unfold gdSaves; rw [ld_st_frame (by decide) (by decide) (by decide) (by decide), ite_eq_right (by decide), ld_st_frame (by decide) (by decide) (by decide) (by decide), ite_eq_right (by decide), ld_st_frame (by decide) (by decide) (by decide) (by decide), ite_eq_right (by decide), ld_st_frame (by decide) (by decide) (by decide) (by decide), ite_eq_right (by decide), ld_st_frame (by decide) (by decide) (by decide) (by decide), ite_eq_right (by decide), ld_st_frame (by decide) (by decide) (by decide) (by decide), ite_eq_right (by decide), ld_st_frame (by decide) (by decide) (by decide) (by decide), ite_eq_right (by decide), ld_st_frame (by decide) (by decide) (by decide) (by decide), ite_eq_right (by decide), ld_st_frame (by decide) (by decide) (by decide) (by decide), ite_eq_left (by decide)]; rfl
  | 5, _ => unfold gdSaves; rw [ld_st_frame (by decide) (by decide) (by decide) (by decide), ite_eq_right (by decide), ld_st_frame (by decide) (by decide) (by decide) (by decide), ite_eq_right (by decide), ld_st_frame (by decide) (by decide) (by decide) (by decide), ite_eq_right (by decide), ld_st_frame (by decide) (by decide) (by decide) (by decide), ite_eq_right (by decide), ld_st_frame (by decide) (by decide) (by decide) (by decide), ite_eq_right (by decide), ld_st_frame (by decide) (by decide) (by decide) (by decide), ite_eq_right (by decide), ld_st_frame (by decide) (by decide) (by decide) (by decide), ite_eq_right (by decide), ld_st_frame (by decide) (by decide) (by decide) (by decide), ite_eq_left (by decide)]; rfl
  | 6, _ => unfold gdSaves; rw [ld_st_frame (by decide) (by decide) (by decide) (by decide), ite_eq_right (by decide), ld_st_frame (by decide) (by decide) (by decide) (by decide), ite_eq_right (by decide), ld_st_frame (by decide) (by decide) (by decide) (by decide), ite_eq_right (by decide), ld_st_frame (by decide) (by decide) (by decide) (by decide), ite_eq_right (by decide), ld_st_frame (by decide) (by decide) (by decide) (by decide), ite_eq_right (by decide), ld_st_frame (by decide) (by decide) (by decide) (by decide), ite_eq_right (by decide), ld_st_frame (by decide) (by decide) (by decide) (by decide), ite_eq_left (by decide)]; rfl
  | 7, _ => unfold gdSaves; rw [ld_st_frame (by decide) (by decide) (by decide) (by decide), ite_eq_right (by decide), ld_st_frame (by decide) (by decide) (by decide) (by decide), ite_eq_right (by decide), ld_st_frame (by decide) (by decide) (by decide) (by decide), ite_eq_right (by decide), ld_st_frame (by decide) (by decide) (by decide) (by decide), ite_eq_right (by decide), ld_st_frame (by decide) (by decide) (by decide) (by decide), ite_eq_right (by decide), ld_st_frame (by decide) (by decide) (by decide) (by decide), ite_eq_left (by decide)]; rfl
  | 8, _ => unfold gdSaves; rw [ld_st_frame (by decide) (by decide) (by decide) (by decide), ite_eq_right (by decide), ld_st_frame (by decide) (by decide) (by decide) (by decide), ite_eq_right (by decide), ld_st_frame (by decide) (by decide) (by decide) (by decide), ite_eq_right (by decide), ld_st_frame (by decide) (by decide) (by decide) (by decide), ite_eq_right (by decide), ld_st_frame (by decide) (by decide) (by decide) (by decide), ite_eq_left (by decide)]; rfl
  | 9, _ => unfold gdSaves; rw [ld_st_frame (by decide) (by decide) (by decide) (by decide), ite_eq_right (by decide), ld_st_frame (by decide) (by decide) (by decide) (by decide), ite_eq_right (by decide), ld_st_frame (by decide) (by decide) (by decide) (by decide), ite_eq_right (by decide), ld_st_frame (by decide) (by decide) (by decide) (by decide), ite_eq_left (by decide)]; rfl
  | 10, _ => unfold gdSaves; rw [ld_st_frame (by decide) (by decide) (by decide) (by decide), ite_eq_right (by decide), ld_st_frame (by decide) (by decide) (by decide) (by decide), ite_eq_right (by decide), ld_st_frame (by decide) (by decide) (by decide) (by decide), ite_eq_left (by decide)]; rfl
  | 11, _ => unfold gdSaves; rw [ld_st_frame (by decide) (by decide) (by decide) (by decide), ite_eq_right (by decide), ld_st_frame (by decide) (by decide) (by decide) (by decide), ite_eq_left (by decide)]; rfl
  | 12, _ => unfold gdSaves; rw [ld_st_frame (by decide) (by decide) (by decide) (by decide), ite_eq_left (by decide)]; rfl

theorem gdSaves_out {M : Word → BitVec 8} {S : Word} {n : Machine} {x : Word}
    (h : Sep (S + BitVec.ofNat 32 0x6DC) 0x34 x 1) : gdSaves M S n x = M x := by
  have hs : ∀ c, 0x6DC ≤ c → c + 4 ≤ 0x710 → Sep (S + BitVec.ofNat 32 c) 4 x 1 := fun c h1 h2 => by
    have := h.sub (c := c - 0x6DC) (l := 4) (by omega)
    rwa [add_ofNat_assoc, show 0x6DC + (c - 0x6DC) = c by omega] at this
  unfold gdSaves
  rw [memStore32_get_sep (hs 0x6dc (by decide) (by decide))]
  rw [memStore32_get_sep (hs 0x6e0 (by decide) (by decide))]
  rw [memStore32_get_sep (hs 0x6e4 (by decide) (by decide))]
  rw [memStore32_get_sep (hs 0x6e8 (by decide) (by decide))]
  rw [memStore32_get_sep (hs 0x6ec (by decide) (by decide))]
  rw [memStore32_get_sep (hs 0x6f0 (by decide) (by decide))]
  rw [memStore32_get_sep (hs 0x6f4 (by decide) (by decide))]
  rw [memStore32_get_sep (hs 0x6f8 (by decide) (by decide))]
  rw [memStore32_get_sep (hs 0x6fc (by decide) (by decide))]
  rw [memStore32_get_sep (hs 0x700 (by decide) (by decide))]
  rw [memStore32_get_sep (hs 0x704 (by decide) (by decide))]
  rw [memStore32_get_sep (hs 0x708 (by decide) (by decide))]
  rw [memStore32_get_sep (hs 0x70c (by decide) (by decide))]

/-- What `decompress` leaves after `from_repr`: `s4` holds whether the input
`x` is below `p`, and `S + 0x84` holds `x` in Montgomery form, or zero. -/
def XOk2 (x : Nat) (ok : Word) (X : Nat) : Prop :=
  (x < p256 → ok = 1 ∧ X = x * 2 ^ 256 % p256) ∧ (p256 ≤ x → ok = 0 ∧ X = 0)

set_option maxRecDepth 100000 in
set_option maxHeartbeats 16000000 in
/-- **Decoding `x`**, from the entry to 0x6E: the prologue, `from_repr`, and
the conditional select of the result or zero into `S + 0x84`. -/
theorem gd_stA {M : Word → BitVec 8} {n : Machine} {S inp : Word} (C : GdCode M) (D : GdData M) (F : Fr S 0x710)
    (s : St M GD n 0 (reg n)) (rsp : reg n sp = S + 0x710) (ra1 : reg n a1 = inp)
    (sI : Sep inp 32 (S + 0xFFFFFE60) 0x8B0) :
    ∃ n', Steps n n' ∧ St n'.mem GD n' 0x6E (reg n') ∧ GdCode n'.mem ∧ GdData n'.mem ∧
      (∀ k, k < 13 → memLoad32 n'.mem (S + BitVec.ofNat 32 (0x70C - 4 * k)) = reg n (savedReg k)) ∧
      XOk2 (beNat (memBytes M inp 32)) (reg n' (26 : Fin 32)) (accV n'.mem (S + BitVec.ofNat 32 0x84) 8) ∧
      (∀ x, Sep (S + 0xFFFFFEC0) 0x140 x 1 → Sep (S + BitVec.ofNat 32 0x40) 0x64 x 1 →
        Sep (S + BitVec.ofNat 32 0x6DC) 0x34 x 1 → n'.mem x = M x) ∧
      reg n' sp = S ∧ reg n' (27 : Fin 32) = reg n a2 ∧ reg n' (25 : Fin 32) = reg n a0 ∧
      reg n' (3 : Fin 32) = reg n (3 : Fin 32) ∧ reg n' (4 : Fin 32) = reg n (4 : Fin 32) := by
  have hSl := F.lo; have hSh := F.hi; have hSa := F.al
  obtain ⟨n1, c1, u1, sp1, e27, e25, e10, k1⟩ := gd_pro C F s rsp
  have hsv : ∀ x, Sep (S + BitVec.ofNat 32 0x6DC) 0x34 x 1 → gdSaves M S n x = M x := fun x h => gdSaves_out h
  have hihi : ∀ x : Word, 0x40000000 ≤ x.toNat → gdSaves M S n x = M x := fun x hx =>
    hsv x (F.hiOut (by decide) hx)
  have C1 := C.hi hihi
  have dS : ∀ x, Sep (S + 0xFFFFFE60) 0x8B0 x 1 → gdSaves M S n x = M x := fun x hx => by
    exact (hsv x) (by
      have := hx.sub (c := 0x1A0 + 0x6DC) (l := 0x34) (by decide)
      rwa [BitVec.add_assoc, show (0xFFFFFE60 : Word) + BitVec.ofNat 32 (0x1A0 + 0x6DC) = BitVec.ofNat 32 0x6DC from rfl]
        at this)
  have D1 := D.of F dS
  have hin : memBytes (gdSaves M S n) inp 32 = memBytes M inp 32 :=
    memBytes_congr fun i hi => dS _ (sI.symm.subR (c := i) (l := 1) (by omega))
  -- from_repr
  obtain ⟨n2, c2, u2, ok2, bad2, fr2, sp2, k2⟩ := c2_frp (out := S + BitVec.ofNat 32 0x40) (inp := inp) u1 C1.self C1.K
    D1.D F gd_at_42 gd_at_46 (by decide) (by decide) sp1 e10 (by rw [k1 11 (by decide)]; exact ra1) (co := 0x40) (by decide) rfl
    (sI.subR (c := 0x60) (l := 0x140) (by decide) |> fun h => by
      rwa [show S + 0xFFFFFE60 + BitVec.ofNat 32 0x60 = S + 0xFFFFFEC0 by rw [BitVec.add_assoc]; rfl] at h)
  rw [hin] at ok2 bad2
  have hbF : (S + 0xFFFFFEC0).toNat = S.toNat - 0x140 := F.below 0x140 (by decide) (by decide)
  have h2hi : ∀ x : Word, 0x40000000 ≤ x.toNat → n2.mem x = M x := fun x hx => by
    rw [fr2 x (sep_of_le (by rw [hbF]; omega) (by have := x.isLt; omega)) (F.hiOut (c := 0x40) (n := 33) (by decide) hx),
      hihi x hx]
  have C2 := C.hi h2hi
  have D2 : GdData n2.mem := D1.of F fun x hx => fr2 x (hx.sub (c := 0x60) (l := 0x140) (by decide) |> fun h => by
    rwa [show S + 0xFFFFFE60 + BitVec.ofNat 32 0x60 = S + 0xFFFFFEC0 by rw [BitVec.add_assoc]; rfl] at h) (by
      have := hx.sub (c := 0x1A0 + 0x40) (l := 33) (by decide)
      rwa [BitVec.add_assoc, show (0xFFFFFE60 : Word) + BitVec.ofNat 32 (0x1A0 + 0x40) = BitVec.ofNat 32 0x40 from rfl] at this)
  -- zero the other operand
  obtain ⟨n3, c3, u3⟩ := u2.block gdA2 C2.self gdA2_end ⟨trivial, trivial, trivial, trivial⟩
  have r3 : ∀ q, reg n3 q = (runBlock gdA2 (n2.mem, reg n2)).2 q := fun q => by rw [u3.regs]
  obtain ⟨n4, c4, u4, mem4, k4⟩ := c_memset (dst := S + BitVec.ofNat 32 0x64) (b := 0) (N := 32)
    (⟨u3.pc, u3.mem, fun _ => rfl⟩ : St n2.mem GD n3 0x52 (reg n3)) C2.self C2.K.K gd_at_52 gd_at_56 (by decide) (by decide)
    (by rw [r3]; simp +decide only [runBlock, BInstr.run, gdA2, upd, ↓reduceIte]; rw [sp2]; rfl)
    (by rw [r3]; simp +decide only [runBlock, BInstr.run, gdA2, upd, ↓reduceIte]; (try rw [u2.zero]); try rfl)
    (by rw [r3]; simp +decide only [runBlock, BInstr.run, gdA2, upd, ↓reduceIte]; (try rw [u2.zero]); try rfl)
    (by rw [F.at _ (by decide)]; omega) (F.sepHi (by decide) (by decide) (by decide))
  have h4 : ∀ x, Sep (S + BitVec.ofNat 32 0x64) 32 x 1 → n4.mem x = n2.mem x := fun x hx => by
    rw [mem4, fillBytes_sep hx (Nat.le_refl _)]
  have C4 := C2.hi fun x hx => h4 x (F.hiOut (by decide) hx)
  have k4' : ∀ q, q ≠ a0 → q ≠ a1 → q ≠ a2 → q ≠ a3 → q ≠ a4 → q ≠ a5 → q ≠ a6 → q ≠ ra → reg n4 q = reg n2 q :=
    fun q h0 h1 h2 h3 h4 h5 h6 hr => by
      rw [k4 q h0 h2 h3 h4 h5 h6 hr, r3, runBlock_reg _ _ _ q u2.zero (by simp only [gdA2]; revert h0 h1 h2; revert q; decide)]
  have sp4 : reg n4 sp = S := by
    rw [k4' sp (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)]; exact sp2
  -- the select
  have a70 : n4.mem (S + BitVec.ofNat 32 0x40 + 0x20) = n2.mem (S + BitVec.ofNat 32 0x40 + 0x20) :=
    h4 _ (sepS S (c := 0x64) (n := 32) (d := 0x60) (k := 1) (.inr (by decide)) (by decide) (by decide) |> fun h => by
      rwa [show S + BitVec.ofNat 32 0x60 = S + BitVec.ofNat 32 0x40 + 0x20 from by rw [BitVec.add_assoc]; rfl] at h)
  obtain ⟨n5, c5, u5⟩ := u4.block gdA3 C4.self gdA3_end ⟨trivial, trivial, trivial, trivial, trivial, trivial⟩
  have r5 : ∀ q, reg n5 q = (runBlock gdA3 (n4.mem, reg n4)).2 q := fun q => by rw [u5.regs]
  have e20 : reg n5 (26 : Fin 32) = (n2.mem (S + BitVec.ofNat 32 0x40 + 0x20)).zeroExtend 32 := by
    rw [r5]; simp +decide only [runBlock, BInstr.run, gdA3, upd, ↓reduceIte]; rw [sp4, ← a70]
    rw [show S + BitVec.ofNat 32 0x40 + 0x20 = S + 0x60 from by rw [BitVec.add_assoc]; rfl]
  have hc01 : (n2.mem (S + BitVec.ofNat 32 0x40 + 0x20)).zeroExtend 32 = (0 : Word) ∨
      (n2.mem (S + BitVec.ofNat 32 0x40 + 0x20)).zeroExtend 32 = (1 : Word) := by
    by_cases hx : beNat (memBytes M inp 32) < p256
    · rw [(ok2 hx).1]; exact .inr rfl
    · rw [(bad2 (by omega)).1]; exact .inl rfl
  obtain ⟨n6, c6, u6, vals6, fr6, sp6, k6⟩ := c2_csel (out := S + BitVec.ofNat 32 0x84) (a := S + BitVec.ofNat 32 0x64)
    (b := S + BitVec.ofNat 32 0x40) (c := (n2.mem (S + BitVec.ofNat 32 0x40 + 0x20)).zeroExtend 32)
    (⟨u5.pc, u5.mem, fun _ => rfl⟩ : St n4.mem GD n5 0x66 (reg n5)) C4.self C4.K F gd_at_66 gd_at_6a (by decide) (by decide)
    (by rw [r5, runBlock_reg _ _ _ sp u4.zero (by decide)]; exact sp4)
    (by rw [r5]; simp +decide only [runBlock, BInstr.run, gdA3, upd, ↓reduceIte]; rw [sp4]; rfl)
    (by rw [r5]; simp +decide only [runBlock, BInstr.run, gdA3, upd, ↓reduceIte]; rw [sp4]; rfl)
    (by rw [r5]; simp +decide only [runBlock, BInstr.run, gdA3, upd, ↓reduceIte]; rw [sp4]; rfl)
    (by rw [r5]; simp +decide only [runBlock, BInstr.run, gdA3, upd, ↓reduceIte]; rw [sp4]
        show aluEval .add 0 ((n4.mem (S + 0x60)).zeroExtend 32) = _
        rw [show (S + 0x60 : Word) = S + BitVec.ofNat 32 0x40 + 0x20 from by rw [BitVec.add_assoc]; rfl, a70]
        exact BitVec.zero_add _)
    hc01 (co := 0x84) (ca := 0x64) (cb := 0x40) (by decide) (by decide) (by decide) rfl rfl rfl (by decide)
  have hb60 : (S + 0xFFFFFFB0).toNat = S.toNat - 0x50 := F.below 0x50 (by decide) (by decide)
  have h6hi : ∀ x : Word, 0x40000000 ≤ x.toNat → n6.mem x = M x := fun x hx => by
    rw [fr6 x (sep_of_le (by rw [hb60]; omega) (by have := x.isLt; omega)) (F.hiOut (c := 0x84) (n := 32) (by decide) hx),
      h4 x (F.hiOut (by decide) hx), h2hi x hx]
  -- the whole frame of this stage
  have frame : ∀ x, Sep (S + 0xFFFFFEC0) 0x140 x 1 → Sep (S + BitVec.ofNat 32 0x40) 0x64 x 1 →
      Sep (S + BitVec.ofNat 32 0x6DC) 0x34 x 1 → n6.mem x = M x := by
    intro x hF h40 hA
    have h60 : Sep (S + 0xFFFFFFB0) 0x50 x 1 := by
      have := hF.sub (c := 0xF0) (l := 0x50) (by decide)
      rwa [show S + 0xFFFFFEC0 + BitVec.ofNat 32 0xF0 = S + 0xFFFFFFB0 by rw [BitVec.add_assoc]; rfl] at this
    have hA4 : Sep (S + BitVec.ofNat 32 0x84) 32 x 1 := by
      have := h40.sub (c := 0x44) (l := 32) (by decide); rwa [add_ofNat_assoc] at this
    have h74 : Sep (S + BitVec.ofNat 32 0x64) 32 x 1 := by
      have := h40.sub (c := 0x24) (l := 32) (by decide); rwa [add_ofNat_assoc] at this
    have h4049 : Sep (S + BitVec.ofNat 32 0x40) 33 x 1 := by
      have := h40.sub (c := 0) (l := 33) (by decide); rwa [add_ofNat_zero] at this
    rw [fr6 x h60 hA4, h4 x h74, fr2 x hF h4049, hsv x hA]
  have D6 : GdData n6.mem := D.of F fun x hx => frame x (hx.sub (c := 0x60) (l := 0x140) (by decide) |> fun h => by
      rwa [show S + 0xFFFFFE60 + BitVec.ofNat 32 0x60 = S + 0xFFFFFEC0 by rw [BitVec.add_assoc]; rfl] at h)
    (by have := hx.sub (c := 0x1A0 + 0x40) (l := 0x64) (by decide)
        rwa [BitVec.add_assoc, show (0xFFFFFE60 : Word) + BitVec.ofNat 32 (0x1A0 + 0x40) = BitVec.ofNat 32 0x40 from rfl]
          at this)
    (by have := hx.sub (c := 0x1A0 + 0x6DC) (l := 0x34) (by decide)
        rwa [BitVec.add_assoc, show (0xFFFFFE60 : Word) + BitVec.ofNat 32 (0x1A0 + 0x6DC) = BitVec.ofNat 32 0x6DC from rfl]
          at this)
  have e620 : reg n6 (26 : Fin 32) = (n2.mem (S + BitVec.ofNat 32 0x40 + 0x20)).zeroExtend 32 := by
    rw [k6 26 (by decide), e20]
  refine ⟨n6, c1.trans (c2.trans (c3.trans (c4.trans (c5.trans c6)))), u6, C.hi h6hi, D6, fun k hk => ?_, ⟨fun hx => ?_,
    fun hx => ?_⟩, frame, sp6, ?_, ?_, ?_, ?_⟩
  · rw [← gdSaves_read k hk]
    refine memLoad32_congr fun q hq => ?_
    rw [add_ofNat_assoc]
    have e1 : n6.mem (S + BitVec.ofNat 32 (0x70C - 4 * k + q)) = n4.mem (S + BitVec.ofNat 32 (0x70C - 4 * k + q)) :=
      fr6 _ (sep_of_le (by rw [hb60, F.at _ (by omega)]; omega) (by rw [F.at _ (by omega)]; omega))
        (sepS S (.inl (by omega)) (by decide) (by omega))
    rw [e1, h4 _ (sepS S (.inl (by omega)) (by decide) (by omega)),
      fr2 _ (sep_of_le (by rw [hbF, F.at _ (by omega)]; omega) (by rw [F.at _ (by omega)]; omega))
        (sepS S (.inl (by omega)) (by decide) (by omega))]
  · obtain ⟨o1, olt, ocg⟩ := ok2 hx
    have hc1 : (n2.mem (S + BitVec.ofNat 32 0x40 + 0x20)).zeroExtend 32 = (1 : Word) := by rw [o1]; rfl
    refine ⟨by rw [e620, hc1], ?_⟩
    have eA : accV n6.mem (S + BitVec.ofNat 32 0x84) 8 = accV n2.mem (S + BitVec.ofNat 32 0x40) 8 :=
      accV_congr2 8 fun i hi => by
        rw [vals6 i hi, ite_eq_left hc1]
        exact memLoad32_congr fun q hq => by
          rw [add_ofNat_assoc, add_ofNat_assoc]
          exact h4 _ (sepS S (.inr (by omega)) (by decide) (by omega))
    rw [eA]
    exact frp2_val olt ocg
  · obtain ⟨o0, _⟩ := bad2 (by omega)
    have hc0 : (n2.mem (S + BitVec.ofNat 32 0x40 + 0x20)).zeroExtend 32 = (0 : Word) := by rw [o0]; rfl
    refine ⟨by rw [e620, hc0], ?_⟩
    exact accV_zero 8 fun i hi => by
      rw [vals6 i hi, ite_eq_right (by rw [hc0]; decide), mem4]
      exact fill_word0 (by omega) (by decide)
  · rw [k6 27 (by decide), r5, runBlock_reg _ _ _ 27 u4.zero (by decide), k4' 27 (by decide) (by decide) (by decide)
      (by decide) (by decide) (by decide) (by decide) (by decide), k2 27 (by decide), e27]
  · rw [k6 25 (by decide), r5, runBlock_reg _ _ _ 25 u4.zero (by decide), k4' 25 (by decide) (by decide) (by decide)
      (by decide) (by decide) (by decide) (by decide) (by decide), k2 25 (by decide), e25]
  · rw [k6 3 (by decide), r5, runBlock_reg _ _ _ 3 u4.zero (by decide), k4' 3 (by decide) (by decide) (by decide)
      (by decide) (by decide) (by decide) (by decide) (by decide), k2 3 (by decide), k1 3 (by decide)]
  · rw [k6 4 (by decide), r5, runBlock_reg _ _ _ 4 u4.zero (by decide), k4' 4 (by decide) (by decide) (by decide)
      (by decide) (by decide) (by decide) (by decide) (by decide), k2 4 (by decide), k1 4 (by decide)]


/-! ## `α = x³ + ax + b` -/

def gdB1 : List BInstr := [.aluImm .add a0 sp 0x43C, .aluImm .add a1 sp 0x84, .aluImm .add a2 sp 0x84, .aluImm .add (8 : Fin 32) sp 0x43C]
def gdB2 : List BInstr := [.aluImm .add a0 sp 0x21C, .aluImm .add a1 sp 0x43C, .aluImm .add a2 sp 0x84]
def gdB3 : List BInstr := [.lui a1 0x3FCC4000, .aluImm .add a1 a1 0x2C8, .aluImm .add a0 sp 0x43C, .aluImm .add a2 sp 0x84]
def gdB4 : List BInstr := [.aluImm .add a0 sp 0x1DC, .aluImm .add a1 sp 0x21C, .aluImm .add a2 sp 0x43C]
def gdB5 : List BInstr := [.lui a2 0x3FCC4000, .aluImm .add a2 a2 0x368, .aluImm .add a0 sp 0xC4, .aluImm .add a1 sp 0x1DC]

theorem gdB1_end : blockEnd p256DecompressCode 0x6E gdB1 = some 0x7A := by decide
theorem gdB2_end : blockEnd p256DecompressCode 0x82 gdB2 = some 0x8A := by decide
theorem gdB3_end : blockEnd p256DecompressCode 0x92 gdB3 = some 0xA0 := by decide
theorem gdB4_end : blockEnd p256DecompressCode 0xA8 gdB4 = some 0xB0 := by decide
theorem gdB5_end : blockEnd p256DecompressCode 0xB8 gdB5 = some 0xC4 := by decide

set_option maxRecDepth 100000 in
set_option maxHeartbeats 64000000 in
/-- **`α = x³ + ax + b`**, from 0x6E to 0xCC: three Montgomery products and
two sums, into `S + 0xC4`. -/
theorem gd_stB {M : Word → BitVec 8} {n : Machine} {S : Word} {X : Nat} (C : GdCode M) (D : GdData M) (F : Fr S 0x710)
    (s : St M GD n 0x6E (reg n)) (rsp : reg n sp = S) (hX : accV M (S + BitVec.ofNat 32 0x84) 8 = X) (hXp : X < p256) :
    ∃ n', Steps n n' ∧ St n'.mem GD n' 0xCC (reg n') ∧ GdCode n'.mem ∧ GdData n'.mem ∧
      accV n'.mem (S + BitVec.ofNat 32 0xC4) 8 = gsAlpha X ∧
      (∀ x, Sep (S + 0xFFFFFED0) 0x130 x 1 → Sep (S + BitVec.ofNat 32 0xC4) 0x20 x 1 →
        Sep (S + BitVec.ofNat 32 0x1DC) 0x60 x 1 → Sep (S + BitVec.ofNat 32 0x43C) 0x20 x 1 → n'.mem x = M x) ∧
      reg n' sp = S ∧ ∀ q : Fin 32, q.val ∈ [3, 4, 9, 18, 19, 20, 21, 22, 23, 24, 25, 26, 27] → reg n' q = reg n q := by
  have hz := s.zero
  have hSl := F.lo; have hSh := F.hi; have hSa := F.al
  have hbF : (S + 0xFFFFFED0).toNat = S.toNat - 0x130 := F.below 0x130 (by decide) (by decide)
  have hbA : (S + 0xFFFFFF4C).toNat = S.toNat - 0xB4 := F.below 0xB4 (by decide) (by decide)
  have sF : ∀ c, c + 32 ≤ 0x710 → Sep (S + BitVec.ofNat 32 c) 32 (S + 0xFFFFFED0) 0x130 := fun c h =>
    (sep_of_le (by rw [hbF, F.at c (by omega)]; omega) (by rw [F.at c (by omega)]; omega)).symm
  have sA : ∀ c, c + 32 ≤ 0x710 → Sep (S + BitVec.ofNat 32 c) 32 (S + 0xFFFFFF4C) 0xB4 := fun c h =>
    (sep_of_le (by rw [hbA, F.at c (by omega)]; omega) (by rw [F.at c (by omega)]; omega)).symm
  have al : ∀ c, c + 4 ≤ 0x710 → c % 4 = 0 → (S + BitVec.ofNat 32 c).toNat % 4 = 0 := fun c h1 h2 => by
    rw [F.at c (by omega)]; omega
  have hiF : ∀ x : Word, 0x40000000 ≤ x.toNat → Sep (S + 0xFFFFFED0) 0x130 x 1 := fun x hx =>
    sep_of_le (by rw [hbF]; omega) (by have := x.isLt; omega)
  have hiA : ∀ x : Word, 0x40000000 ≤ x.toNat → Sep (S + 0xFFFFFF4C) 0xB4 x 1 := fun x hx =>
    sep_of_le (by rw [hbA]; omega) (by have := x.isLt; omega)
  have keepF : ∀ {Mx My : Word → BitVec 8} {c : Nat}, (∀ x, Sep (S + 0xFFFFFED0) 0x130 x 1 →
      Sep (S + BitVec.ofNat 32 c) 32 x 1 → My x = Mx x) → ∀ d, d + 32 ≤ 0x710 → c + 32 ≤ 0x710 →
      (c + 32 ≤ d ∨ d + 32 ≤ c) → accV My (S + BitVec.ofNat 32 d) 8 = accV Mx (S + BitVec.ofNat 32 d) 8 :=
    fun {Mx My c} h d hd hc hcd => accV_congr2 8 fun i hi => memLoad32_congr fun q hq => by
      rw [add_ofNat_assoc, add_ofNat_assoc]
      exact h _ (sep_of_le (by rw [hbF, F.at _ (by omega)]; omega) (by rw [F.at _ (by omega)]; omega))
        (sepS S (by rcases hcd with h | h; exact .inl (by omega); exact .inr (by omega)) (by omega) (by omega))
  have keepA : ∀ {Mx My : Word → BitVec 8} {c : Nat}, (∀ x, Sep (S + 0xFFFFFF4C) 0xB4 x 1 →
      Sep (S + BitVec.ofNat 32 c) 32 x 1 → My x = Mx x) → (∀ x, Sep (S + 0xFFFFFED0) 0x130 x 1 →
      Sep (S + BitVec.ofNat 32 c) 32 x 1 → My x = Mx x) := fun h x hF hc => h x (by
        have := hF.sub (c := 0x7C) (l := 0xB4) (by decide)
        rwa [show S + 0xFFFFFED0 + BitVec.ofNat 32 0x7C = S + 0xFFFFFF4C by rw [BitVec.add_assoc]; rfl] at this) hc
  have dOf : ∀ {Mx My : Word → BitVec 8} {c : Nat}, c + 32 ≤ 0x710 → GdData Mx → (∀ x, Sep (S + 0xFFFFFED0) 0x130 x 1 →
      Sep (S + BitVec.ofNat 32 c) 32 x 1 → My x = Mx x) → GdData My := fun {Mx My c} hc Dx h => Dx.of F fun x hx => h x (by
        have := hx.sub (c := 0x1A0 - 0x130) (l := 0x130) (by decide)
        rwa [BitVec.add_assoc, show (0xFFFFFE60 : Word) + BitVec.ofNat 32 (0x1A0 - 0x130) = 0xFFFFFED0 from rfl] at this)
      (fr_inFrame (by omega) hx)
  have kf : ∀ {m m' : Machine}, (∀ q, q ≠ a0 → q ≠ a1 → q ≠ a2 → q ≠ a3 → q ≠ a4 → q ≠ a5 → q ≠ a6 → q ≠ a7 → q ≠ t0 →
      q ≠ t1 → q ≠ (7 : Fin 32) → q ≠ (28 : Fin 32) → q ≠ (29 : Fin 32) → q ≠ (30 : Fin 32) → q ≠ (31 : Fin 32) → q ≠ ra →
      reg m' q = reg m q) → ∀ q : Fin 32, q.val ∈ [2, 3, 4, 8, 9, 18, 19, 20, 21, 22, 23, 24, 25, 26, 27] → reg m' q = reg m q :=
    fun h q hq => h q (by revert hq; revert q; decide) (by revert hq; revert q; decide) (by revert hq; revert q; decide) (by revert hq; revert q; decide) (by revert hq; revert q; decide) (by revert hq; revert q; decide) (by revert hq; revert q; decide) (by revert hq; revert q; decide) (by revert hq; revert q; decide) (by revert hq; revert q; decide) (by revert hq; revert q; decide) (by revert hq; revert q; decide) (by revert hq; revert q; decide) (by revert hq; revert q; decide) (by revert hq; revert q; decide) (by revert hq; revert q; decide)
  -- x²
  obtain ⟨n1, c1, u1⟩ := s.block gdB1 C.self gdB1_end ⟨trivial, trivial, trivial, trivial, trivial⟩
  have r1 : ∀ q, reg n1 q = (runBlock gdB1 (M, reg n)).2 q := fun q => by rw [u1.regs]
  obtain ⟨n2, c2, u2, v2, fr2, sp2, k2⟩ := c2_fmul (out := S + BitVec.ofNat 32 0x43C) (xp := S + BitVec.ofNat 32 0x84)
    (yp := S + BitVec.ofNat 32 0x84) (⟨u1.pc, u1.mem, fun _ => rfl⟩ : St M GD n1 0x7A (reg n1)) C.self C.K F gd_at_7a
    gd_at_7e (by decide) (by decide) (by rw [r1, runBlock_reg _ _ _ sp hz (by decide)]; exact rsp)
    (by rw [r1]; simp +decide only [runBlock, BInstr.run, gdB1, upd, ↓reduceIte]; rw [rsp]; rfl)
    (by rw [r1]; simp +decide only [runBlock, BInstr.run, gdB1, upd, ↓reduceIte]; rw [rsp]; rfl)
    (by rw [r1]; simp +decide only [runBlock, BInstr.run, gdB1, upd, ↓reduceIte]; rw [rsp]; rfl)
    (co := 0x43C) (by decide) rfl (by decide) (sF _ (by decide)) (al _ (by decide) (by decide)) (sF _ (by decide))
    (al _ (by decide) (by decide)) (by rw [hX]; exact hXp) (by rw [hX]; exact hXp)
  rw [hX] at v2
  have C2 := C.hi fun x hx => fr2 x (hiF x hx) (F.hiOut (by decide) hx)
  have D2 : GdData n2.mem := dOf (by decide) D fr2
  have kk2 : ∀ q : Fin 32, q.val ∈ [3, 4, 9, 18, 19, 20, 21, 22, 23, 24, 25, 26, 27] → reg n2 q = reg n q := fun q hq => by
    rw [kf k2 q (by revert hq; revert q; decide), r1, runBlock_reg _ _ _ q hz (by simp only [gdB1]; revert hq; revert q; decide)]
  have eX2 : accV n2.mem (S + BitVec.ofNat 32 0x84) 8 = X := by
    rw [keepF fr2 0x84 (by decide) (by decide) (.inr (by decide)), hX]
  -- x³
  obtain ⟨n3, c3, u3⟩ := u2.block gdB2 C2.self gdB2_end ⟨trivial, trivial, trivial, trivial⟩
  have r3 : ∀ q, reg n3 q = (runBlock gdB2 (n2.mem, reg n2)).2 q := fun q => by rw [u3.regs]
  obtain ⟨n4, c4, u4, v4, fr4, sp4, k4⟩ := c2_fmul (out := S + BitVec.ofNat 32 0x21C) (xp := S + BitVec.ofNat 32 0x43C)
    (yp := S + BitVec.ofNat 32 0x84) (⟨u3.pc, u3.mem, fun _ => rfl⟩ : St n2.mem GD n3 0x8A (reg n3)) C2.self C2.K F
    gd_at_8a gd_at_8e (by decide) (by decide) (by rw [r3, runBlock_reg _ _ _ sp u2.zero (by decide)]; exact sp2)
    (by rw [r3]; simp +decide only [runBlock, BInstr.run, gdB2, upd, ↓reduceIte]; rw [sp2]; rfl)
    (by rw [r3]; simp +decide only [runBlock, BInstr.run, gdB2, upd, ↓reduceIte]; rw [sp2]; rfl)
    (by rw [r3]; simp +decide only [runBlock, BInstr.run, gdB2, upd, ↓reduceIte]; rw [sp2]; rfl)
    (co := 0x21C) (by decide) rfl (by decide) (sF _ (by decide)) (al _ (by decide) (by decide)) (sF _ (by decide))
    (al _ (by decide) (by decide)) (by rw [v2]; exact p2fm_lt _ _) (by rw [eX2]; exact hXp)
  rw [v2, eX2] at v4
  have C4 := C2.hi fun x hx => fr4 x (hiF x hx) (F.hiOut (by decide) hx)
  have D4 : GdData n4.mem := dOf (by decide) D2 fr4
  have kk4 : ∀ q : Fin 32, q.val ∈ [3, 4, 9, 18, 19, 20, 21, 22, 23, 24, 25, 26, 27] → reg n4 q = reg n q := fun q hq => by
    rw [kf k4 q (by revert hq; revert q; decide), r3, runBlock_reg _ _ _ q u2.zero (by simp only [gdB2]; revert hq; revert q; decide),
      kk2 q hq]
  have eX4 : accV n4.mem (S + BitVec.ofNat 32 0x84) 8 = X := by
    rw [keepF fr4 0x84 (by decide) (by decide) (.inr (by decide)), eX2]
  -- ax
  obtain ⟨n5, c5, u5⟩ := u4.block gdB3 C4.self gdB3_end ⟨trivial, trivial, trivial, trivial, trivial⟩
  have r5 : ∀ q, reg n5 q = (runBlock gdB3 (n4.mem, reg n4)).2 q := fun q => by rw [u5.regs]
  have hAv : accV n4.mem P2A 8 = p2A := by
    rw [show P2A = P2A + BitVec.ofNat 32 0 from (add_ofNat_zero _).symm, code_accV D4.D.ca 0 8 (by decide), p2A_val]
  obtain ⟨n6, c6, u6, v6, fr6, sp6, k6⟩ := c2_fmul (out := S + BitVec.ofNat 32 0x43C) (xp := P2A)
    (yp := S + BitVec.ofNat 32 0x84) (⟨u5.pc, u5.mem, fun _ => rfl⟩ : St n4.mem GD n5 0xA0 (reg n5)) C4.self C4.K F
    gd_at_a0 gd_at_a4 (by decide) (by decide) (by rw [r5, runBlock_reg _ _ _ sp u4.zero (by decide)]; exact sp4)
    (by rw [r5]; simp +decide only [runBlock, BInstr.run, gdB3, upd, ↓reduceIte]; rw [sp4]; rfl)
    (by rw [r5]; simp +decide only [runBlock, BInstr.run, gdB3, upd, ↓reduceIte]; try rfl)
    (by rw [r5]; simp +decide only [runBlock, BInstr.run, gdB3, upd, ↓reduceIte]; rw [sp4]; rfl)
    (co := 0x43C) (by decide) rfl (by decide) (F.lowData (c := 0x130) (by decide) rfl (by decide) (by decide)).symm
    (by decide) (sF _ (by decide)) (al _ (by decide) (by decide)) (by rw [hAv]; unfold p2A p256; decide)
    (by rw [eX4]; exact hXp)
  rw [hAv, eX4] at v6
  have C6 := C4.hi fun x hx => fr6 x (hiF x hx) (F.hiOut (by decide) hx)
  have D6 : GdData n6.mem := dOf (by decide) D4 fr6
  have kk6 : ∀ q : Fin 32, q.val ∈ [3, 4, 9, 18, 19, 20, 21, 22, 23, 24, 25, 26, 27] → reg n6 q = reg n q := fun q hq => by
    rw [kf k6 q (by revert hq; revert q; decide), r5, runBlock_reg _ _ _ q u4.zero (by simp only [gdB3]; revert hq; revert q; decide),
      kk4 q hq]
  have e6x3 : accV n6.mem (S + BitVec.ofNat 32 0x21C) 8 = p2fm (p2fm X X) X := by
    rw [keepF fr6 0x21C (by decide) (by decide) (.inr (by decide)), v4]
  -- x³ + ax
  obtain ⟨n7, c7, u7⟩ := u6.block gdB4 C6.self gdB4_end ⟨trivial, trivial, trivial, trivial⟩
  have r7 : ∀ q, reg n7 q = (runBlock gdB4 (n6.mem, reg n6)).2 q := fun q => by rw [u7.regs]
  obtain ⟨n8, c8, u8, v8, fr8, sp8, k8⟩ := c2_fadd (out := S + BitVec.ofNat 32 0x1DC) (lp := S + BitVec.ofNat 32 0x21C)
    (rp := S + BitVec.ofNat 32 0x43C) (⟨u7.pc, u7.mem, fun _ => rfl⟩ : St n6.mem GD n7 0xB0 (reg n7)) C6.self C6.K F
    gd_at_b0 gd_at_b4 (by decide) (by decide) (by rw [r7, runBlock_reg _ _ _ sp u6.zero (by decide)]; exact sp6)
    (by rw [r7]; simp +decide only [runBlock, BInstr.run, gdB4, upd, ↓reduceIte]; rw [sp6]; rfl)
    (by rw [r7]; simp +decide only [runBlock, BInstr.run, gdB4, upd, ↓reduceIte]; rw [sp6]; rfl)
    (by rw [r7]; simp +decide only [runBlock, BInstr.run, gdB4, upd, ↓reduceIte]; rw [sp6]; rfl)
    (co := 0x1DC) (by decide) rfl (by decide) (sA _ (by decide)) (al _ (by decide) (by decide)) (sA _ (by decide))
    (al _ (by decide) (by decide))
  rw [e6x3, v6] at v8
  have fr8' := keepA fr8
  have C8 := C6.hi fun x hx => fr8 x (hiA x hx) (F.hiOut (by decide) hx)
  have D8 : GdData n8.mem := dOf (by decide) D6 fr8'
  have kk8 : ∀ q : Fin 32, q.val ∈ [3, 4, 9, 18, 19, 20, 21, 22, 23, 24, 25, 26, 27] → reg n8 q = reg n q := fun q hq => by
    rw [kf k8 q (by revert hq; revert q; decide), r7, runBlock_reg _ _ _ q u6.zero (by simp only [gdB4]; revert hq; revert q; decide),
      kk6 q hq]
  -- + b
  obtain ⟨n9, c9, u9⟩ := u8.block gdB5 C8.self gdB5_end ⟨trivial, trivial, trivial, trivial, trivial⟩
  have r9 : ∀ q, reg n9 q = (runBlock gdB5 (n8.mem, reg n8)).2 q := fun q => by rw [u9.regs]
  have hBv : accV n8.mem P2B 8 = p2B := by
    rw [show P2B = P2B + BitVec.ofNat 32 0 from (add_ofNat_zero _).symm, code_accV D8.D.cb 0 8 (by decide), p2B_val]
  obtain ⟨n10, c10, u10, v10, fr10, sp10, k10⟩ := c2_fadd (out := S + BitVec.ofNat 32 0xC4)
    (lp := S + BitVec.ofNat 32 0x1DC) (rp := P2B) (⟨u9.pc, u9.mem, fun _ => rfl⟩ : St n8.mem GD n9 0xC4 (reg n9))
    C8.self C8.K F gd_at_c4 gd_at_c8 (by decide) (by decide)
    (by rw [r9, runBlock_reg _ _ _ sp u8.zero (by decide)]; exact sp8)
    (by rw [r9]; simp +decide only [runBlock, BInstr.run, gdB5, upd, ↓reduceIte]; rw [sp8]; rfl)
    (by rw [r9]; simp +decide only [runBlock, BInstr.run, gdB5, upd, ↓reduceIte]; rw [sp8]; rfl)
    (by rw [r9]; simp +decide only [runBlock, BInstr.run, gdB5, upd, ↓reduceIte]; try rfl)
    (co := 0xC4) (by decide) rfl (by decide) (sA _ (by decide)) (al _ (by decide) (by decide))
    (F.lowData (c := 0xB4) (by decide) rfl (by decide) (by decide)).symm (by decide)
  rw [hBv, v8] at v10
  have fr10' := keepA fr10
  refine ⟨n10, c1.trans (c2.trans (c3.trans (c4.trans (c5.trans (c6.trans (c7.trans (c8.trans (c9.trans c10)))))))),
    u10, C8.hi fun x hx => fr10 x (hiA x hx) (F.hiOut (by decide) hx), dOf (by decide) D8 fr10', v10,
    fun x hF hC4 h1DC h43C => ?_, sp10, fun q hq => ?_⟩
  · have h1 : Sep (S + BitVec.ofNat 32 0x1DC) 32 x 1 := by
      have := h1DC.sub (c := 0) (l := 32) (by decide); rwa [add_ofNat_zero] at this
    have h2 : Sep (S + BitVec.ofNat 32 0x21C) 32 x 1 := by
      have := h1DC.sub (c := 0x40) (l := 32) (by decide); rwa [add_ofNat_assoc] at this
    rw [fr10' x hF hC4, fr8' x hF h1, fr6 x hF h43C, fr4 x hF h2, fr2 x hF h43C]
  · rw [kf k10 q (by revert hq; revert q; decide), r9, runBlock_reg _ _ _ q u8.zero (by simp only [gdB5]; revert hq; revert q; decide),
      kk8 q hq]

/-! ## Copying the constants -/

def gdC1 : List BInstr :=
  [.aluImm .add a0 sp 0xE4, .lui (24 : Fin 32) 0x3FCC5000, .aluImm .add (24 : Fin 32) (24 : Fin 32) 0xFFFFFB38,
   .aluImm .add a2 x0 0x6C, .alu .add a1 x0 (24 : Fin 32)]
def gdC2 : List BInstr :=
  [.aluImm .add (9 : Fin 32) x0 0x100, .alu .sub (18 : Fin 32) (9 : Fin 32) (8 : Fin 32), .aluImm .add a0 sp 0x1DC,
   .aluImm .add a1 sp 0xC4, .aluImm .add a2 x0 0x20]
def gdC3 : List BInstr :=
  [.aluImm .add a0 sp 0x1FC, .lui (22 : Fin 32) 0x3FCC5000, .aluImm .add (22 : Fin 32) (22 : Fin 32) 0xFFFFFBCC,
   .aluImm .add a2 x0 0x20, .alu .add a1 x0 (22 : Fin 32)]

theorem gdC1_end : blockEnd p256DecompressCode 0xCC gdC1 = some 0xDC := by decide
theorem gdC2_end : blockEnd p256DecompressCode 0x144 gdC2 = some 0x154 := by decide
theorem gdC3_end : blockEnd p256DecompressCode 0x15C gdC3 = some 0x16C := by decide

set_option maxRecDepth 100000 in
set_option maxHeartbeats 16000000 in
/-- **Copying the constants**, from 0xCC to 0x196: the parameters to
`S + 0xE4`, `α` to `S + 0x1DC`, and the exponent to `S + 0x1FC`; the
exponent's bit width 254 to `s2`. -/
theorem gd_stC {M : Word → BitVec 8} {n : Machine} {S : Word} (C : GdCode M) (D : GdData M) (F : Fr S 0x710)
    (s : St M GD n 0xCC (reg n)) (rsp : reg n sp = S) :
    ∃ n', Steps n n' ∧ St n'.mem GD n' 0x196 (reg n') ∧ GdCode n'.mem ∧ GdData n'.mem ∧
      memLoad32 n'.mem (S + BitVec.ofNat 32 0xE4) = 0xFFFFFFFF ∧ accV n'.mem (S + BitVec.ofNat 32 0xE4) 8 = p256 ∧
      accV n'.mem (S + BitVec.ofNat 32 0x1DC) 8 = accV M (S + BitVec.ofNat 32 0xC4) 8 ∧
      reg n' (24 : Fin 32) = P2N ∧ reg n' (18 : Fin 32) = 0xFE ∧ reg n' (22 : Fin 32) = EXP2 ∧
      (∀ x, Sep (S + 0xFFFFFFF0) 16 x 1 → Sep (S + BitVec.ofNat 32 0xE4) 0x6C x 1 →
        Sep (S + BitVec.ofNat 32 0x1DC) 0x40 x 1 → Sep (S + BitVec.ofNat 32 0x43C) 4 x 1 → n'.mem x = M x) ∧
      ∀ q : Fin 32, q.val ∈ [2, 3, 4, 19, 20, 21, 25, 26, 27] → reg n' q = reg n q := by
  have hz := s.zero
  have hSl := F.lo; have hSh := F.hi; have hSa := F.al
  obtain ⟨fA, fW, hFC⟩ := F.mc
  have hb16 : (S + 0xFFFFFFF0).toNat = S.toNat - 16 := F.below 16 (by decide) (by decide)
  have lo16 : ∀ x : Word, 0x40000000 ≤ x.toNat → Sep (S + 0xFFFFFFF0) 16 x 1 := fun x hx =>
    sep_of_le (by rw [hb16]; omega) (by have := x.isLt; omega)
  have l16 : ∀ d, d + 4 ≤ 0x710 → Sep (S + 0xFFFFFFF0) 16 (S + BitVec.ofNat 32 d) 4 := fun d hd =>
    sep_of_le (by rw [hb16, F.at d (by omega)]; omega) (by rw [F.at d (by omega)]; omega)
  have l16b : ∀ d, d + 1 ≤ 0x710 → Sep (S + 0xFFFFFFF0) 16 (S + BitVec.ofNat 32 d) 1 := fun d hd =>
    sep_of_le (by rw [hb16, F.at d (by omega)]; omega) (by rw [F.at d (by omega)]; omega)
  have inFrame : ∀ {c l : Nat} {x : Word}, c + l ≤ 0x710 → Sep (S + 0xFFFFFE60) 0x8B0 x 1 →
      Sep (S + BitVec.ofNat 32 c) l x 1 := fun {c l x} h hx => by
    have := hx.sub (c := 0x1A0 + c) (l := l) (by omega)
    rwa [BitVec.add_assoc, show (0xFFFFFE60 : Word) + BitVec.ofNat 32 (0x1A0 + c) = BitVec.ofNat 32 c by
      apply BitVec.eq_of_toNat_eq
      rw [BitVec.toNat_add, BitVec.toNat_ofNat, BitVec.toNat_ofNat, show (0xFFFFFE60 : Word).toNat = 0xFFFFFE60 from rfl]
      omega] at this
  have below16 : ∀ {x : Word}, Sep (S + 0xFFFFFE60) 0x8B0 x 1 → Sep (S + 0xFFFFFFF0) 16 x 1 := fun {x} hx => by
    have := hx.sub (c := 0x190) (l := 16) (by decide)
    rwa [show S + 0xFFFFFE60 + BitVec.ofNat 32 0x190 = S + 0xFFFFFFF0 by rw [BitVec.add_assoc]; rfl] at this
  -- the parameters
  obtain ⟨n1, c1, u1⟩ := s.block gdC1 C.self gdC1_end ⟨trivial, trivial, trivial, trivial, trivial, trivial⟩
  have r1 : ∀ q, reg n1 q = (runBlock gdC1 (M, reg n)).2 q := fun q => by rw [u1.regs]
  have e24 : reg n1 (24 : Fin 32) = P2N := by
    rw [r1]; simp +decide only [runBlock, BInstr.run, gdC1, upd, ↓reduceIte]; try rfl
  obtain ⟨n2, c2, u2, fr2, k2⟩ := c_memcpy (dst := S + BitVec.ofNat 32 0xE4) (src := P2N) (S := S) (N := 0x6C)
    (⟨u1.pc, u1.mem, fun _ => rfl⟩ : St M GD n1 0xDC (reg n1)) C.self C.K.K gd_at_dc gd_at_e0 (by decide) (by decide)
    (by rw [r1, runBlock_reg _ _ _ sp hz (by decide)]; exact rsp)
    (by rw [r1]; simp +decide only [runBlock, BInstr.run, gdC1, upd, ↓reduceIte]; rw [rsp]; rfl)
    (by rw [r1]; simp +decide only [runBlock, BInstr.run, gdC1, upd, ↓reduceIte]; try rfl)
    (by rw [r1]; simp +decide only [runBlock, BInstr.run, gdC1, upd, ↓reduceIte]; (try rw [hz]); try rfl)
    ⟨C.K.K.body, F.sepHi (by decide) (by decide) (by decide), hFC, F.mcN (by decide),
      (F.lowData (c := 16) (by decide) rfl (by decide) (by decide)).symm, F.bufData (by decide) (by decide) (by decide),
      fA, fW, by rw [F.at _ (by decide)]; omega, by decide⟩
  have fr2' : ∀ x, Sep (S + 0xFFFFFFF0) 16 x 1 → Sep (S + BitVec.ofNat 32 0xE4) 0x6C x 1 → n2.mem x = M x :=
    fun x a b => by rw [fr2 x a, copyBytes_sep b (Nat.le_refl _)]
  have C2 := C.hi fun x hx => fr2' x (lo16 x hx) (F.hiOut (by decide) hx)
  have D2 : GdData n2.mem := D.of F fun x hx => fr2' x (below16 hx) (inFrame (by decide) hx)
  have hP : ∀ i, i < 8 → memLoad32 n2.mem (S + BitVec.ofNat 32 0xE4 + BitVec.ofNat 32 (4 * i)) =
      memLoad32 M (P2N + BitVec.ofNat 32 (4 * i)) := fun i hi => by
    rw [load_frame fr2 (by rw [add_ofNat_assoc]; exact l16 _ (by omega)), cp_word (by omega) (by decide)]
  have kk2 : ∀ q : Fin 32, q.val ∈ [2, 3, 4, 8, 9, 18, 19, 20, 21, 22, 23, 25, 26, 27] → reg n2 q = reg n q := fun q hq => by
    rw [k2 q (by revert hq; revert q; decide) (by revert hq; revert q; decide) (by revert hq; revert q; decide)
      (by revert hq; revert q; decide) (by revert hq; revert q; decide) (by revert hq; revert q; decide)
      (by revert hq; revert q; decide) (by revert hq; revert q; decide) (by revert hq; revert q; decide)
      (by revert hq; revert q; decide) (by revert hq; revert q; decide) (by revert hq; revert q; decide)
      (by revert hq; revert q; decide) (by revert hq; revert q; decide) (by revert hq; revert q; decide)]
    rw [r1, runBlock_reg _ _ _ q hz (by simp only [gdC1]; revert hq; revert q; decide)]
  have e224 : reg n2 (24 : Fin 32) = P2N := by
    rw [k2 24 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
      (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide), e24]
  -- the bit width
  obtain ⟨n3, c3, u3, C3, fr3, e38, k3⟩ := gd_lz C2 F u2 (by rw [kk2 sp (by decide)]; exact rsp)
  have k3' : ∀ q : Fin 32, q.val ∈ [2, 3, 4, 9, 18, 19, 20, 21, 22, 23, 25, 26, 27] → reg n3 q = reg n q := fun q hq => by
    rw [k3 q (by revert hq; revert q; decide) (by revert hq; revert q; decide) (by revert hq; revert q; decide)
      (by revert hq; revert q; decide) (by revert hq; revert q; decide) (by revert hq; revert q; decide),
      kk2 q (by revert hq; revert q; decide)]
  have D3 : GdData n3.mem := D2.of F fun x hx => fr3 x (inFrame (by decide) hx)
  have e324 : reg n3 (24 : Fin 32) = P2N := by
    rw [k3 24 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide), e224]
  -- copy α
  obtain ⟨n4, c4, u4⟩ := u3.block gdC2 C3.self gdC2_end ⟨trivial, trivial, trivial, trivial, trivial, trivial⟩
  have r4 : ∀ q, reg n4 q = (runBlock gdC2 (n3.mem, reg n3)).2 q := fun q => by rw [u4.regs]
  have sp3 : reg n3 sp = S := by rw [k3' sp (by decide)]; exact rsp
  obtain ⟨n5, c5, u5, fr5, k5⟩ := c_memcpy (dst := S + BitVec.ofNat 32 0x1DC) (src := S + BitVec.ofNat 32 0xC4)
    (S := S) (N := 32) (⟨u4.pc, u4.mem, fun _ => rfl⟩ : St n3.mem GD n4 0x154 (reg n4)) C3.self C3.K.K gd_at_154 gd_at_158
    (by decide) (by decide) (by rw [r4, runBlock_reg _ _ _ sp u3.zero (by decide)]; exact sp3)
    (by rw [r4]; simp +decide only [runBlock, BInstr.run, gdC2, upd, ↓reduceIte]; rw [sp3]; rfl)
    (by rw [r4]; simp +decide only [runBlock, BInstr.run, gdC2, upd, ↓reduceIte]; rw [sp3]; rfl)
    (by rw [r4]; simp +decide only [runBlock, BInstr.run, gdC2, upd, ↓reduceIte]; (try rw [u3.zero]); try rfl)
    ⟨C3.K.K.body, F.sepHi (by decide) (by decide) (by decide), hFC, F.mcN (by decide), F.mcN (by decide),
      sepS S (.inr (by decide)) (by decide) (by decide), fA, fW, by rw [F.at _ (by decide)]; omega,
      by rw [F.at _ (by decide)]; omega⟩
  have fr5' : ∀ x, Sep (S + 0xFFFFFFF0) 16 x 1 → Sep (S + BitVec.ofNat 32 0x1DC) 32 x 1 → n5.mem x = n3.mem x :=
    fun x a b => by rw [fr5 x a, copyBytes_sep b (Nat.le_refl _)]
  have C5 := C3.hi fun x hx => fr5' x (lo16 x hx) (F.hiOut (by decide) hx)
  have D5 : GdData n5.mem := D3.of F fun x hx => fr5' x (below16 hx) (inFrame (by decide) hx)
  have hA : accV n5.mem (S + BitVec.ofNat 32 0x1DC) 8 = accV n3.mem (S + BitVec.ofNat 32 0xC4) 8 :=
    accV_congr2 8 fun i hi => by
      rw [load_frame fr5 (by rw [add_ofNat_assoc]; exact l16 _ (by omega)), cp_word (by omega) (by decide)]
  have k5' : ∀ q : Fin 32, q.val ∈ [2, 3, 4, 8, 19, 20, 21, 22, 23, 24, 25, 26, 27] → reg n5 q = reg n3 q := fun q hq => by
    rw [k5 q (by revert hq; revert q; decide) (by revert hq; revert q; decide) (by revert hq; revert q; decide)
      (by revert hq; revert q; decide) (by revert hq; revert q; decide) (by revert hq; revert q; decide)
      (by revert hq; revert q; decide) (by revert hq; revert q; decide) (by revert hq; revert q; decide)
      (by revert hq; revert q; decide) (by revert hq; revert q; decide) (by revert hq; revert q; decide)
      (by revert hq; revert q; decide) (by revert hq; revert q; decide) (by revert hq; revert q; decide), r4,
      runBlock_reg _ _ _ q u3.zero (by simp only [gdC2]; revert hq; revert q; decide)]
  have e518 : reg n5 (18 : Fin 32) = 0xFE := by
    rw [k5 18 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
      (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide), r4]
    simp +decide only [runBlock, BInstr.run, gdC2, upd, ↓reduceIte]; rw [e38, u3.zero]; rfl
  have e59 : reg n5 (9 : Fin 32) = 0x100 := by
    rw [k5 9 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
      (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide), r4]
    simp +decide only [runBlock, BInstr.run, gdC2, upd, ↓reduceIte]; (try rw [u3.zero]); try rfl
  -- copy the exponent
  obtain ⟨n6, c6, u6⟩ := u5.block gdC3 C5.self gdC3_end ⟨trivial, trivial, trivial, trivial, trivial, trivial⟩
  have r6 : ∀ q, reg n6 q = (runBlock gdC3 (n5.mem, reg n5)).2 q := fun q => by rw [u6.regs]
  have sp5 : reg n5 sp = S := by rw [k5' sp (by decide)]; exact sp3
  obtain ⟨n7, c7, u7, fr7, k7⟩ := c_memcpy (dst := S + BitVec.ofNat 32 0x1FC) (src := EXP2) (S := S) (N := 32)
    (⟨u6.pc, u6.mem, fun _ => rfl⟩ : St n5.mem GD n6 0x16C (reg n6)) C5.self C5.K.K gd_at_16c gd_at_170 (by decide) (by decide)
    (by rw [r6, runBlock_reg _ _ _ sp u5.zero (by decide)]; exact sp5)
    (by rw [r6]; simp +decide only [runBlock, BInstr.run, gdC3, upd, ↓reduceIte]; rw [sp5]; rfl)
    (by rw [r6]; simp +decide only [runBlock, BInstr.run, gdC3, upd, ↓reduceIte]; try rfl)
    (by rw [r6]; simp +decide only [runBlock, BInstr.run, gdC3, upd, ↓reduceIte]; (try rw [u5.zero]); try rfl)
    ⟨C5.K.K.body, F.sepHi (by decide) (by decide) (by decide), hFC, F.mcN (by decide),
      (F.lowData (c := 16) (by decide) rfl (by decide) (by decide)).symm, F.bufData (by decide) (by decide) (by decide),
      fA, fW, by rw [F.at _ (by decide)]; omega, by decide⟩
  have fr7' : ∀ x, Sep (S + 0xFFFFFFF0) 16 x 1 → Sep (S + BitVec.ofNat 32 0x1FC) 32 x 1 → n7.mem x = n5.mem x :=
    fun x a b => by rw [fr7 x a, copyBytes_sep b (Nat.le_refl _)]
  have C7 := C5.hi fun x hx => fr7' x (lo16 x hx) (F.hiOut (by decide) hx)
  have D7 : GdData n7.mem := D5.of F fun x hx => fr7' x (below16 hx) (inFrame (by decide) hx)
  have k7' : ∀ q : Fin 32, q.val ∈ [2, 3, 4, 8, 9, 18, 19, 20, 21, 23, 24, 25, 26, 27] → reg n7 q = reg n5 q := fun q hq => by
    rw [k7 q (by revert hq; revert q; decide) (by revert hq; revert q; decide) (by revert hq; revert q; decide)
      (by revert hq; revert q; decide) (by revert hq; revert q; decide) (by revert hq; revert q; decide)
      (by revert hq; revert q; decide) (by revert hq; revert q; decide) (by revert hq; revert q; decide)
      (by revert hq; revert q; decide) (by revert hq; revert q; decide) (by revert hq; revert q; decide)
      (by revert hq; revert q; decide) (by revert hq; revert q; decide) (by revert hq; revert q; decide), r6,
      runBlock_reg _ _ _ q u5.zero (by simp only [gdC3]; revert hq; revert q; decide)]
  -- the two tests the constant exponent passes
  obtain ⟨n8, d8, u8⟩ := u7.taken C7.self 0x17C gd_at_174 (by decide) (by
    show branchTaken .bltu (reg n7 (18 : Fin 32)) (reg n7 (9 : Fin 32)) = true
    rw [k7' 18 (by decide), k7' 9 (by decide), e518, e59]; decide)
  obtain ⟨n9, d9, u9⟩ := u8.self.aluImm C7.self gd_at_17c (off' := 0x180) (by decide)
  obtain ⟨n10, d10, u10⟩ := u9.self.taken C7.self 0x196 gd_at_180 (by decide) (by
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
    rw [show memLoad32 n7.mem (S + BitVec.ofNat 32 0xE4) = memLoad32 n2.mem (S + BitVec.ofNat 32 0xE4) from
      memLoad32_congr fun q hq => by
        rw [add_ofNat_assoc]
        rw [fr7' _ (l16b _ (by omega))
          (sepS S (.inr (by omega)) (by decide) (by omega)),
          fr5' _ (l16b _ (by omega))
          (sepS S (.inr (by omega)) (by decide) (by omega)),
          fr3 _ (sepS S (.inr (by omega)) (by decide) (by omega))], this]
    exact D.D.N0
  · rw [u10.mem, show p256 = accV M P2N 8 from D.D.N.symm]
    refine accV_congr2 8 fun i hi => ?_
    rw [← hP i hi]
    refine memLoad32_congr fun q hq => ?_
    rw [add_ofNat_assoc, add_ofNat_assoc]
    rw [fr7' _ (l16b _ (by omega))
        (sepS S (.inr (by omega)) (by decide) (by omega)),
      fr5' _ (l16b _ (by omega))
        (sepS S (.inr (by omega)) (by decide) (by omega)),
      fr3 _ (sepS S (.inr (by omega)) (by decide) (by omega))]
  · rw [u10.mem]
    have e7 : accV n7.mem (S + BitVec.ofNat 32 0x1DC) 8 = accV n5.mem (S + BitVec.ofNat 32 0x1DC) 8 :=
      accV_congr2 8 fun i hi => memLoad32_congr fun q hq => by
        rw [add_ofNat_assoc, add_ofNat_assoc]
        exact fr7' _ (l16b _ (by omega))
          (sepS S (.inr (by omega)) (by decide) (by omega))
    rw [e7, hA]
    exact accV_congr2 8 fun i hi => memLoad32_congr fun q hq => by
      rw [add_ofNat_assoc, add_ofNat_assoc]
      rw [fr3 _ (sepS S (.inr (by omega)) (by decide) (by omega)),
        fr2' _ (l16b _ (by omega))
          (sepS S (.inr (by omega)) (by decide) (by omega))]
  · rw [g10 22 (by decide), k7 22 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
      (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide), r6]
    simp +decide only [runBlock, BInstr.run, gdC3, upd, ↓reduceIte]; try rfl
  · have h29C48 : Sep (S + BitVec.ofNat 32 0x1DC) 32 x 1 := by
      have := h29C.sub (c := 0) (l := 32) (by decide); rwa [add_ofNat_zero] at this
    have h2CC : Sep (S + BitVec.ofNat 32 0x1FC) 32 x 1 := by
      have := h29C.sub (c := 0x20) (l := 32) (by decide); rwa [add_ofNat_assoc] at this
    rw [u10.mem, fr7' x h16 h2CC, fr5' x h16 h29C48, fr3 x h62C, fr2' x h16 h134]
  · rw [g10 q (by revert hq; revert q; decide), k7' q (by revert hq; revert q; decide), k5' q (by revert hq; revert q; decide),
      k3' q (by revert hq; revert q; decide)]


/-! ## Starting the table -/

def gdE0 : List BInstr := [.aluImm .add (8 : Fin 32) sp 0x21C, .aluImm .add (9 : Fin 32) x0 0x10]
def gdE1 : List BInstr :=
  [.aluImm .add a0 sp 0x43C, .aluImm .add a1 sp 0x21C, .aluImm .add a2 x0 0x200, .aluImm .add (9 : Fin 32) sp 0x43C]
def gdE2 : List BInstr := [.aluImm .add a0 sp 0x63C, .aluImm .add a2 x0 0x20, .aluImm .add a1 x0 0x0]
def gdE3 : List BInstr := [.aluImm .add a0 sp 0x21C, .aluImm .add a1 sp 0x43C, .aluImm .add a2 x0 0x220]
def gdE4 : List BInstr :=
  [.aluImm .add (19 : Fin 32) sp 0x45C, .aluImm .add (8 : Fin 32) x0 0x10, .aluImm .add (24 : Fin 32) (24 : Fin 32) 0x20]
def gdE5 : List BInstr := [.aluImm .add a1 sp 0xC4, .aluImm .add a2 x0 0x20, .alu .add a0 x0 (19 : Fin 32)]

theorem gdE0_end : blockEnd p256DecompressCode 0x196 gdE0 = some 0x19A := by decide
theorem gdE1_end : blockEnd p256DecompressCode 0x1B4 gdE1 = some 0x1C2 := by decide
theorem gdE2_end : blockEnd p256DecompressCode 0x1CA gdE2 = some 0x1D4 := by decide
theorem gdE3_end : blockEnd p256DecompressCode 0x1DC gdE3 = some 0x1E6 := by decide
theorem gdE4_end : blockEnd p256DecompressCode 0x1EE gdE4 = some 0x1F8 := by decide
theorem gdE5_end : blockEnd p256DecompressCode 0x212 gdE5 = some 0x21A := by decide

theorem P2Data.one {M : Word → BitVec 8} (D : P2Data M) : accV M (P2N + 0x20) 8 = p2one := by
  rw [show P2N + 0x20 = P2N + BitVec.ofNat 32 0x20 from rfl, code_accV D.params 0x20 8 (by decide)]
  unfold p2one p256; decide

set_option maxRecDepth 100000 in
set_option maxHeartbeats 16000000 in
/-- **Starting the table**, from 0x196 to the table loop at 0x226: entry 0
of the table at `S + 0x43C` is 1 and entry 1 is `α`, in Montgomery form. -/
theorem gd_stD {M : Word → BitVec 8} {n : Machine} {S : Word} (C : GdCode M) (D : GdData M) (F : Fr S 0x710)
    (s : St M GD n 0x196 (reg n)) (rsp : reg n sp = S) (r24 : reg n (24 : Fin 32) = P2N)
    (hA : accV M (S + BitVec.ofNat 32 0xC4) 8 < p256) :
    ∃ n', Steps n n' ∧ St n'.mem GD n' 0x226 (reg n') ∧ GdCode n'.mem ∧ GdData n'.mem ∧
      (∀ j, j ≤ 1 → accV n'.mem (S + BitVec.ofNat 32 (0x43C + 32 * j)) 8 = mpow2 (accV M (S + BitVec.ofNat 32 0xC4) 8) j) ∧
      reg n' (19 : Fin 32) = S + BitVec.ofNat 32 0x45C ∧ reg n' (8 : Fin 32) = 0xE ∧ reg n' (24 : Fin 32) = P2N + 0x20 ∧
      (∀ x, Sep (S + 0xFFFFFFF0) 16 x 1 → Sep (S + BitVec.ofNat 32 0x21C) 0x440 x 1 → n'.mem x = M x) ∧
      ∀ q : Fin 32, q.val ∈ [2, 3, 4, 18, 20, 21, 22, 23, 25, 26, 27] → reg n' q = reg n q := by
  have hz := s.zero
  have hSl := F.lo; have hSh := F.hi; have hSa := F.al
  obtain ⟨fA, fW, hFC⟩ := F.mc
  have hb16 : (S + 0xFFFFFFF0).toNat = S.toNat - 16 := F.below 16 (by decide) (by decide)
  have lo16 : ∀ x : Word, 0x40000000 ≤ x.toNat → Sep (S + 0xFFFFFFF0) 16 x 1 := fun x hx =>
    sep_of_le (by rw [hb16]; omega) (by have := x.isLt; omega)
  have l16b : ∀ d, d + 1 ≤ 0x710 → Sep (S + 0xFFFFFFF0) 16 (S + BitVec.ofNat 32 d) 1 := fun d hd =>
    sep_of_le (by rw [hb16, F.at d (by omega)]; omega) (by rw [F.at d (by omega)]; omega)
  have inFrame : ∀ {c l : Nat} {x : Word}, c + l ≤ 0x710 → Sep (S + 0xFFFFFE60) 0x8B0 x 1 →
      Sep (S + BitVec.ofNat 32 c) l x 1 := fun {c l x} h hx => by
    have := hx.sub (c := 0x1A0 + c) (l := l) (by omega)
    rwa [BitVec.add_assoc, show (0xFFFFFE60 : Word) + BitVec.ofNat 32 (0x1A0 + c) = BitVec.ofNat 32 c by
      apply BitVec.eq_of_toNat_eq
      rw [BitVec.toNat_add, BitVec.toNat_ofNat, BitVec.toNat_ofNat, show (0xFFFFFE60 : Word).toNat = 0xFFFFFE60 from rfl]
      omega] at this
  have below16 : ∀ {x : Word}, Sep (S + 0xFFFFFE60) 0x8B0 x 1 → Sep (S + 0xFFFFFFF0) 16 x 1 := fun {x} hx => by
    have := hx.sub (c := 0x190) (l := 16) (by decide)
    rwa [show S + 0xFFFFFE60 + BitVec.ofNat 32 0x190 = S + 0xFFFFFFF0 by rw [BitVec.add_assoc]; rfl] at this
  -- zero the powers
  obtain ⟨n1, c1, u1⟩ := s.block gdE0 C.self gdE0_end ⟨trivial, trivial, trivial⟩
  have r1 : ∀ q, reg n1 q = (runBlock gdE0 (M, reg n)).2 q := fun q => by rw [u1.regs]
  have v1 : St M GD n1 0x19A (reg n1) := ⟨u1.pc, u1.mem, fun _ => rfl⟩
  obtain ⟨n2, d2, u2⟩ := v1.notTaken C.self 0x19C gd_at_19a (by decide) (by
    show (reg n1 (9 : Fin 32) == reg n1 x0) = false
    rw [r1]; simp +decide only [runBlock, BInstr.run, gdE0, upd, ↓reduceIte]; rw [v1.zero]; rfl)
  obtain ⟨n3, c3, u3, C3, fr3, k3⟩ := gd_zero16 F 15 0 (by decide) C u2.self
    (by rw [u2.regs, r1]; simp +decide only [runBlock, BInstr.run, gdE0, upd, ↓reduceIte]; rw [rsp]; rfl)
    (by rw [u2.regs, r1]; simp +decide only [runBlock, BInstr.run, gdE0, upd, ↓reduceIte]; (try rw [hz]); try rfl)
  have k3' : ∀ q : Fin 32, q.val ∈ [2, 3, 4, 18, 19, 20, 21, 22, 23, 24, 25, 26, 27] → reg n3 q = reg n q := fun q hq => by
    rw [k3 q (by revert hq; revert q; decide) (by revert hq; revert q; decide) (by revert hq; revert q; decide)
      (by revert hq; revert q; decide) (by revert hq; revert q; decide) (by revert hq; revert q; decide)
      (by revert hq; revert q; decide) (by revert hq; revert q; decide) (by revert hq; revert q; decide)
      (by revert hq; revert q; decide), u2.regs, r1, runBlock_reg _ _ _ q hz (by simp only [gdE0]; revert hq; revert q; decide)]
  have D3 : GdData n3.mem := D.of F fun x hx => fr3 x (inFrame (by decide) hx)
  have sp3 : reg n3 sp = S := by rw [k3' sp (by decide)]; exact rsp
  -- copy the zeros up
  obtain ⟨n4, c4, u4⟩ := u3.block gdE1 C3.self gdE1_end ⟨trivial, trivial, trivial, trivial, trivial⟩
  have r4 : ∀ q, reg n4 q = (runBlock gdE1 (n3.mem, reg n3)).2 q := fun q => by rw [u4.regs]
  have C4 := C3
  have D4 := D3
  obtain ⟨n5, c5, u5, fr5, k5⟩ := c_memcpy (dst := S + BitVec.ofNat 32 0x43C) (src := S + BitVec.ofNat 32 0x21C)
    (S := S) (N := 0x200) (⟨u4.pc, u4.mem, fun _ => rfl⟩ : St n3.mem GD n4 0x1C2 (reg n4)) C4.self C4.K.K gd_at_1c2 gd_at_1c6
    (by decide) (by decide) (by rw [r4, runBlock_reg _ _ _ sp u3.zero (by decide)]; exact sp3)
    (by rw [r4]; simp +decide only [runBlock, BInstr.run, gdE1, upd, ↓reduceIte]; rw [sp3]; rfl)
    (by rw [r4]; simp +decide only [runBlock, BInstr.run, gdE1, upd, ↓reduceIte]; rw [sp3]; rfl)
    (by rw [r4]; simp +decide only [runBlock, BInstr.run, gdE1, upd, ↓reduceIte]; (try rw [u3.zero]); try rfl)
    ⟨C4.K.K.body, F.sepHi (by decide) (by decide) (by decide), hFC, F.mcN (by decide), F.mcN (by decide),
      sepS S (.inr (by decide)) (by decide) (by decide), fA, fW, by rw [F.at _ (by decide)]; omega,
      by rw [F.at _ (by decide)]; omega⟩
  have fr5' : ∀ x, Sep (S + 0xFFFFFFF0) 16 x 1 → Sep (S + BitVec.ofNat 32 0x43C) 0x200 x 1 → n5.mem x = n3.mem x :=
    fun x a b => by rw [fr5 x a, copyBytes_sep b (Nat.le_refl _)]
  have C5 := C4.hi fun x hx => fr5' x (lo16 x hx) (F.hiOut (by decide) hx)
  have D5 : GdData n5.mem := D4.of F fun x hx => fr5' x (below16 hx) (inFrame (by decide) hx)
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
    rw [r4, runBlock_reg _ _ _ q u3.zero (by simp only [gdE1]; revert hq; revert q; decide)]
  have sp5 : reg n5 sp = S := by rw [k5' sp (by decide), g4 sp (by decide)]; exact sp3
  have e59 : reg n5 (9 : Fin 32) = S + BitVec.ofNat 32 0x43C := by
    rw [k5' 9 (by decide), r4]; simp +decide only [runBlock, BInstr.run, gdE1, upd, ↓reduceIte]; rw [sp3]; rfl
  -- clear the slot above the table, and copy everything down
  obtain ⟨n6, c6, u6⟩ := u5.block gdE2 C5.self gdE2_end ⟨trivial, trivial, trivial, trivial⟩
  have r6 : ∀ q, reg n6 q = (runBlock gdE2 (n5.mem, reg n5)).2 q := fun q => by rw [u6.regs]
  obtain ⟨n7, c7, u7, mem7, k7⟩ := c_memset (dst := S + BitVec.ofNat 32 0x63C) (b := 0) (N := 32)
    (⟨u6.pc, u6.mem, fun _ => rfl⟩ : St n5.mem GD n6 0x1D4 (reg n6)) C5.self C5.K.K gd_at_1d4 gd_at_1d8 (by decide) (by decide)
    (by rw [r6]; simp +decide only [runBlock, BInstr.run, gdE2, upd, ↓reduceIte]; rw [sp5]; rfl)
    (by rw [r6]; simp +decide only [runBlock, BInstr.run, gdE2, upd, ↓reduceIte]; (try rw [u5.zero]); try rfl)
    (by rw [r6]; simp +decide only [runBlock, BInstr.run, gdE2, upd, ↓reduceIte]; (try rw [u5.zero]); try rfl)
    (by rw [F.at _ (by decide)]; omega) (F.sepHi (by decide) (by decide) (by decide))
  have h7 : ∀ x, Sep (S + BitVec.ofNat 32 0x63C) 32 x 1 → n7.mem x = n5.mem x := fun x hx => by
    rw [mem7, fillBytes_sep hx (Nat.le_refl _)]
  have C7 := C5.hi fun x hx => h7 x (F.hiOut (by decide) hx)
  have D7 : GdData n7.mem := D5.of F fun x hx => h7 x (inFrame (by decide) hx)
  have k7' : ∀ q : Fin 32, q.val ∈ [2, 3, 4, 8, 9, 18, 19, 20, 21, 22, 23, 24, 25, 26, 27] → reg n7 q = reg n5 q := fun q hq => by
    rw [k7 q (by revert hq; revert q; decide) (by revert hq; revert q; decide) (by revert hq; revert q; decide)
      (by revert hq; revert q; decide) (by revert hq; revert q; decide) (by revert hq; revert q; decide)
      (by revert hq; revert q; decide), r6, runBlock_reg _ _ _ q u5.zero (by simp only [gdE2]; revert hq; revert q; decide)]
  obtain ⟨n8, c8, u8⟩ := u7.block gdE3 C7.self gdE3_end ⟨trivial, trivial, trivial, trivial⟩
  have r8 : ∀ q, reg n8 q = (runBlock gdE3 (n7.mem, reg n7)).2 q := fun q => by rw [u8.regs]
  have sp7 : reg n7 sp = S := by rw [k7' sp (by decide)]; exact sp5
  obtain ⟨n9, c9, u9, fr9, k9⟩ := c_memcpy (dst := S + BitVec.ofNat 32 0x21C) (src := S + BitVec.ofNat 32 0x43C)
    (S := S) (N := 0x220) (⟨u8.pc, u8.mem, fun _ => rfl⟩ : St n7.mem GD n8 0x1E6 (reg n8)) C7.self C7.K.K gd_at_1e6 gd_at_1ea
    (by decide) (by decide) (by rw [r8, runBlock_reg _ _ _ sp u7.zero (by decide)]; exact sp7)
    (by rw [r8]; simp +decide only [runBlock, BInstr.run, gdE3, upd, ↓reduceIte]; rw [sp7]; rfl)
    (by rw [r8]; simp +decide only [runBlock, BInstr.run, gdE3, upd, ↓reduceIte]; rw [sp7]; rfl)
    (by rw [r8]; simp +decide only [runBlock, BInstr.run, gdE3, upd, ↓reduceIte]; (try rw [u7.zero]); try rfl)
    ⟨C7.K.K.body, F.sepHi (by decide) (by decide) (by decide), hFC, F.mcN (by decide), F.mcN (by decide),
      sepS S (.inl (by decide)) (by decide) (by decide), fA, fW, by rw [F.at _ (by decide)]; omega,
      by rw [F.at _ (by decide)]; omega⟩
  have fr9' : ∀ x, Sep (S + 0xFFFFFFF0) 16 x 1 → Sep (S + BitVec.ofNat 32 0x21C) 0x220 x 1 → n9.mem x = n7.mem x :=
    fun x a b => by rw [fr9 x a, copyBytes_sep b (Nat.le_refl _)]
  have C9 := C7.hi fun x hx => fr9' x (lo16 x hx) (F.hiOut (by decide) hx)
  have D9 : GdData n9.mem := D7.of F fun x hx => fr9' x (below16 hx) (inFrame (by decide) hx)
  have k9' := kc k9
  have g8 : ∀ q : Fin 32, q.val ∈ [2, 3, 4, 8, 9, 18, 19, 20, 21, 22, 23, 24, 25, 26, 27] → reg n8 q = reg n7 q := fun q hq => by
    rw [r8, runBlock_reg _ _ _ q u7.zero (by simp only [gdE3]; revert hq; revert q; decide)]
  have k79 : ∀ q : Fin 32, q.val ∈ [2, 3, 4, 8, 9, 18, 19, 20, 21, 22, 23, 24, 25, 26, 27] → reg n9 q = reg n5 q :=
    fun q hq => by rw [k9' q hq, g8 q hq, k7' q hq]
  -- the ones
  obtain ⟨n10, c10, u10⟩ := u9.block gdE4 C9.self gdE4_end ⟨trivial, trivial, trivial, trivial⟩
  have r10 : ∀ q, reg n10 q = (runBlock gdE4 (n9.mem, reg n9)).2 q := fun q => by rw [u10.regs]
  have t10 : St n9.mem GD n10 0x1F8 (reg n10) := ⟨u10.pc, u10.mem, fun _ => rfl⟩
  obtain ⟨n11, d11, u11⟩ := t10.notTaken C9.self 0x1FA gd_at_1f8 (by decide) (by
    show (reg n10 (8 : Fin 32) == reg n10 x0) = false
    rw [r10]; simp +decide only [runBlock, BInstr.run, gdE4, upd, ↓reduceIte]; rw [t10.zero]; (try rw [u9.zero]); rfl)
  have e1024 : reg n10 (24 : Fin 32) = P2N + 0x20 := by
    rw [r10]; simp +decide only [runBlock, BInstr.run, gdE4, upd, ↓reduceIte]
    rw [k79 24 (by decide), k5' 24 (by decide), g4 24 (by decide), k3' 24 (by decide), r24]; rfl
  have hOF : Sep (S + 0xFFFFFFF0) 16 (P2N + 0x20) 32 := F.lowData (c := 16) (by decide) rfl (by decide) (by decide)
  have hOT : Sep (S + BitVec.ofNat 32 0x43C) 0x200 (P2N + 0x20) 32 := F.bufData (by decide) (by decide) (by decide)
  obtain ⟨n12, c12, u12, C12, hT12, fr12, k12⟩ := gd_ones16 F hOF hOT (by decide) 15 0 (by decide) C9 u11.self
    (by rw [u11.regs, r10, runBlock_reg _ _ _ sp u9.zero (by decide), k79 sp (by decide)]; exact sp5)
    (by rw [u11.regs, r10, runBlock_reg _ _ _ 9 u9.zero (by decide), k79 9 (by decide), e59])
    (by rw [u11.regs, r10]; simp +decide only [runBlock, BInstr.run, gdE4, upd, ↓reduceIte]; (try rw [u9.zero]); try rfl)
    (by rw [u11.regs, e1024])
  have k12' : ∀ q : Fin 32, q.val ∈ [2, 3, 4, 18, 19, 20, 21, 22, 23, 24, 25, 26, 27] → reg n12 q = reg n10 q := fun q hq => by
    rw [k12 q (by revert hq; revert q; decide) (by revert hq; revert q; decide) (by revert hq; revert q; decide)
      (by revert hq; revert q; decide) (by revert hq; revert q; decide) (by revert hq; revert q; decide)
      (by revert hq; revert q; decide) (by revert hq; revert q; decide) (by revert hq; revert q; decide)
      (by revert hq; revert q; decide) (by revert hq; revert q; decide) (by revert hq; revert q; decide)
      (by revert hq; revert q; decide) (by revert hq; revert q; decide) (by revert hq; revert q; decide)
      (by revert hq; revert q; decide) (by revert hq; revert q; decide), u11.regs]
  have e1019 : reg n10 (19 : Fin 32) = S + BitVec.ofNat 32 0x45C := by
    rw [r10]; simp +decide only [runBlock, BInstr.run, gdE4, upd, ↓reduceIte]; rw [k79 sp (by decide), sp5]; rfl
  have g10 : ∀ q : Fin 32, q.val ∈ [2, 3, 4, 18, 20, 21, 22, 23, 25, 26, 27] → reg n10 q = reg n9 q := fun q hq => by
    rw [r10, runBlock_reg _ _ _ q u9.zero (by simp only [gdE4]; revert hq; revert q; decide)]
  have fr12' : ∀ x, Sep (S + 0xFFFFFFF0) 16 x 1 → Sep (S + BitVec.ofNat 32 0x43C) 0x200 x 1 → n12.mem x = n9.mem x := by
    intro x a b; exact fr12 x a (by rwa [show 0x43C + 32 * 0 = 0x43C from rfl, show 32 * (16 - 0) = 0x200 from rfl])
  have D12 : GdData n12.mem := D9.of F fun x hx => fr12' x (below16 hx) (inFrame (by decide) hx)
  -- α to entry 1
  obtain ⟨n13, c13, u13⟩ := u12.block gdE5 C12.self gdE5_end ⟨trivial, trivial, trivial, trivial⟩
  have r13 : ∀ q, reg n13 q = (runBlock gdE5 (n12.mem, reg n12)).2 q := fun q => by rw [u13.regs]
  have sp12 : reg n12 sp = S := by rw [k12' sp (by decide), g10 sp (by decide), k79 sp (by decide)]; exact sp5
  have e1219 : reg n12 (19 : Fin 32) = S + BitVec.ofNat 32 0x45C := by rw [k12' 19 (by decide), e1019]
  obtain ⟨n14, c14, u14, fr14, k14⟩ := c_memcpy (dst := S + BitVec.ofNat 32 0x45C) (src := S + BitVec.ofNat 32 0xC4)
    (S := S) (N := 32) (⟨u13.pc, u13.mem, fun _ => rfl⟩ : St n12.mem GD n13 0x21A (reg n13)) C12.self C12.K.K gd_at_21a gd_at_21e
    (by decide) (by decide) (by rw [r13, runBlock_reg _ _ _ sp u12.zero (by decide)]; exact sp12)
    (by rw [r13]; simp +decide only [runBlock, BInstr.run, gdE5, upd, ↓reduceIte]; rw [e1219]
        exact BitVec.zero_add _)
    (by rw [r13]; simp +decide only [runBlock, BInstr.run, gdE5, upd, ↓reduceIte]; rw [sp12]; rfl)
    (by rw [r13]; simp +decide only [runBlock, BInstr.run, gdE5, upd, ↓reduceIte]; (try rw [u12.zero]); try rfl)
    ⟨C12.K.K.body, F.sepHi (by decide) (by decide) (by decide), hFC, F.mcN (by decide), F.mcN (by decide),
      sepS S (.inr (by decide)) (by decide) (by decide), fA, fW, by rw [F.at _ (by decide)]; omega,
      by rw [F.at _ (by decide)]; omega⟩
  have fr14' : ∀ x, Sep (S + 0xFFFFFFF0) 16 x 1 → Sep (S + BitVec.ofNat 32 0x45C) 32 x 1 → n14.mem x = n12.mem x :=
    fun x a b => by rw [fr14 x a, copyBytes_sep b (Nat.le_refl _)]
  have k14' := kc k14
  have g13 : ∀ q : Fin 32, q.val ∈ [2, 3, 4, 8, 9, 18, 19, 20, 21, 22, 23, 24, 25, 26, 27] → reg n13 q = reg n12 q := fun q hq => by
    rw [r13, runBlock_reg _ _ _ q u12.zero (by simp only [gdE5]; revert hq; revert q; decide)]
  -- the frame, through each step
  have frame : ∀ x, Sep (S + 0xFFFFFFF0) 16 x 1 → Sep (S + BitVec.ofNat 32 0x21C) 0x440 x 1 → n14.mem x = M x := by
    intro x h16 h2FC
    have s62C : Sep (S + BitVec.ofNat 32 0x43C) 0x200 x 1 := by
      have := h2FC.sub (c := 0x220) (l := 0x200) (by decide); rwa [add_ofNat_assoc] at this
    have s65C : Sep (S + BitVec.ofNat 32 0x45C) 32 x 1 := by
      have := h2FC.sub (c := 0x240) (l := 32) (by decide); rwa [add_ofNat_assoc] at this
    have s2FC : Sep (S + BitVec.ofNat 32 0x21C) 0x220 x 1 := by
      have := h2FC.sub (c := 0) (l := 0x220) (by decide); rwa [add_ofNat_zero] at this
    have s2FC3 : Sep (S + BitVec.ofNat 32 0x21C) 0x200 x 1 := by
      have := h2FC.sub (c := 0) (l := 0x200) (by decide); rwa [add_ofNat_zero] at this
    have s92C : Sep (S + BitVec.ofNat 32 0x63C) 32 x 1 := by
      have := h2FC.sub (c := 0x420) (l := 32) (by decide); rwa [add_ofNat_assoc] at this
    rw [fr14' x h16 s65C, fr12' x h16 s62C, fr9' x h16 s2FC, h7 x s92C, fr5' x h16 s62C, fr3 x s2FC3]
  have hAv : accV n12.mem (S + BitVec.ofNat 32 0xC4) 8 = accV M (S + BitVec.ofNat 32 0xC4) 8 := by
    rw [← show accV n14.mem (S + BitVec.ofNat 32 0xC4) 8 = accV n12.mem (S + BitVec.ofNat 32 0xC4) 8 from
      accV_congr2 8 fun i hi => memLoad32_congr fun q hq => by
        rw [add_ofNat_assoc, add_ofNat_assoc]
        exact fr14' _ (l16b _ (by omega)) (sepS S (.inr (by omega)) (by decide) (by omega))]
    exact accV_congr2 8 fun i hi => memLoad32_congr fun q hq => by
      rw [add_ofNat_assoc, add_ofNat_assoc]
      exact frame _ (l16b _ (by omega)) (sepS S (.inr (by omega)) (by decide) (by omega))
  have C14 := C12.hi fun x hx => fr14' x (lo16 x hx) (F.hiOut (by decide) hx)
  obtain ⟨n15, d15, u15⟩ := u14.aluImm C14.self gd_at_222 (off' := 0x224) (by decide)
  obtain ⟨n16, d16, u16⟩ := u15.self.notTaken C14.self 0x226 gd_at_224 (by decide) (by
    show (reg n15 (8 : Fin 32) == reg n15 x0) = false
    rw [u15.regs]; simp +decide only [upd, ↓reduceIte]; rw [u15.self.zero]; rfl)
  have g16 : ∀ q, q ≠ (8 : Fin 32) → reg n16 q = reg n14 q := fun q h => by
    rw [u16.regs, u15.regs, updz u14.zero h]
  have m16 : n16.mem = n14.mem := by rw [u16.mem]
  refine ⟨n16, c1.trans (.cons d2 (c3.trans (c4.trans (c5.trans (c6.trans (c7.trans (c8.trans (c9.trans (c10.trans
    (.cons d11 (c12.trans (c13.trans (c14.trans (.cons d15 (.single d16))))))))))))))), ⟨u16.pc, by rw [m16], fun _ => rfl⟩,
    by rw [m16]; exact C14,
    by rw [m16]; exact D12.of F fun x hx => fr14' x (below16 hx) (inFrame (by decide) hx), fun j hj => ?_, ?_,
    by rw [u16.regs, u15.regs]; simp +decide only [upd, ↓reduceIte]; rw [u14.zero]; rfl, ?_,
    by rw [m16]; exact frame, fun q hq => ?_⟩
  · rw [m16]
    rcases Nat.le_one_iff_eq_zero_or_eq_one.mp hj with rfl | rfl
    · show accV n14.mem (S + BitVec.ofNat 32 (0x43C + 32 * 0)) 8 = p2one
      rw [show 0x43C + 32 * 0 = 0x43C from rfl]
      rw [show accV n14.mem (S + BitVec.ofNat 32 0x43C) 8 = accV n12.mem (S + BitVec.ofNat 32 0x43C) 8 from
        accV_congr2 8 fun i hi => memLoad32_congr fun q hq => by
          rw [add_ofNat_assoc, add_ofNat_assoc]
          exact fr14' _ (l16b _ (by omega)) (sepS S (.inr (by omega)) (by decide) (by omega))]
      rw [show S + BitVec.ofNat 32 0x43C = S + BitVec.ofNat 32 (0x43C + 32 * 0) from rfl, hT12 0 (Nat.le_refl 0) (by decide)]
      exact P2Data.one D9.D
    · rw [mpow2_one _ hA, ← hAv]
      refine cp_accV8 (by decide) (by decide) fun i hi => ?_
      have hs : Sep (S + 0xFFFFFFF0) 16 (S + BitVec.ofNat 32 (0x45C + 4 * i)) 4 :=
        sep_of_le (by rw [hb16, F.at _ (by omega)]; omega) (by rw [F.at _ (by omega)]; omega)
      rw [show 0x43C + 32 * 1 + 4 * i = 0x45C + 4 * i by omega, load_frame fr14 hs, ← add_ofNat_assoc S 0x45C,
        cp_word (by omega) (by decide), add_ofNat_assoc]
  · rw [g16 19 (by decide), k14' 19 (by decide), g13 19 (by decide), e1219]
  · rw [g16 24 (by decide), k14' 24 (by decide), g13 24 (by decide), k12' 24 (by decide), e1024]
  · rw [g16 q (by revert hq; revert q; decide), k14' q (by revert hq; revert q; decide), g13 q (by revert hq; revert q; decide), k12' q (by revert hq; revert q; decide),
      g10 q hq, k79 q (by revert hq; revert q; decide), k5' q (by revert hq; revert q; decide),
      g4 q (by revert hq; revert q; decide), k3' q (by revert hq; revert q; decide)]


/-! ## Setting up the exponentiation -/

def gdF1 : List BInstr :=
  [.sw sp (27 : Fin 32) 0x10, .sw sp (26 : Fin 32) 0x14, .sw sp (25 : Fin 32) 0x18, .aluImm .add a0 sp 0x21C,
   .aluImm .add a1 sp 0x43C, .aluImm .add a2 x0 0x200]
def gdF2 : List BInstr := [.aluImm .add a2 x0 0x20, .aluImm .add a0 sp 0x41C, .alu .add a1 x0 (22 : Fin 32)]
def gdF3 : List BInstr :=
  [.aluImm .add (18 : Fin 32) (18 : Fin 32) 0xFFFFFFFF, .aluImm .srl (9 : Fin 32) (18 : Fin 32) 0x5,
   .aluImm .and a0 (18 : Fin 32) 0x3, .aluImm .add a1 x0 0x2, .aluImm .sll (18 : Fin 32) (18 : Fin 32) 0x1B,
   .alu .sll a0 a1 a0, .aluImm .srl (8 : Fin 32) (18 : Fin 32) 0x1D, .aluImm .add (18 : Fin 32) a0 0xFFFFFFFF,
   .aluImm .add a0 sp 0x65C, .aluImm .add a2 x0 0x20, .alu .add a1 x0 (24 : Fin 32)]
def gdF4 : List BInstr :=
  [.sw sp (9 : Fin 32) 0x34, .aluImm .add (9 : Fin 32) (9 : Fin 32) 0x1, .sw sp (8 : Fin 32) 0x30,
   .aluImm .add (8 : Fin 32) (8 : Fin 32) 0x1, .sw sp (8 : Fin 32) 0x1C, .aluImm .and a0 (18 : Fin 32) 0xF, .sw sp a0 0x24,
   .aluImm .add (19 : Fin 32) sp 0x6A0, .aluImm .add (25 : Fin 32) sp 0x680, .aluImm .add (21 : Fin 32) sp 0xE8,
   .aluImm .add (18 : Fin 32) sp 0x69C, .aluImm .add (27 : Fin 32) x0 0x8, .aluImm .add (22 : Fin 32) x0 0xFFFFFFFF]

theorem gdF1_end : blockEnd p256DecompressCode 0x256 gdF1 = some 0x266 := by decide
theorem gdF2_end : blockEnd p256DecompressCode 0x26E gdF2 = some 0x278 := by decide
theorem gdF3_end : blockEnd p256DecompressCode 0x280 gdF3 = some 0x2A4 := by decide
theorem gdF4_end : blockEnd p256DecompressCode 0x2AC gdF4 = some 0x2D0 := by decide

set_option exponentiation.threshold 600 in
theorem exp_words2 : ∀ j, j < 8 → wordAt p256SqrtExpData 0 j = expLimb2 j := by unfold expLimb2 sqrtExp2 p256; decide

theorem GdData.exw {M : Word → BitVec 8} (D : GdData M) (j : Nat) (hj : j < 8) :
    memLoad32 M (EXP2 + BitVec.ofNat 32 (0 + 4 * j)) = expLimb2 j := by
  rw [code_word D.ex 0 j (by have : p256SqrtExpData.length = 32 := rfl; omega), exp_words2 j hj]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 16000000 in
/-- **Setting up the exponentiation**, from 0x256 to the limb loop at 0x2D4:
spill `s9..s11`, copy the table to `S + 0x21C` and the exponent to
`S + 0x41C`, set `z` to 1, and spill the loop's counters. -/
theorem gd_stF {M : Word → BitVec 8} {n : Machine} {S : Word} {A : Nat} (C : GdCode M) (D : GdData M)
    (F : Fr S 0x710) (s : St M GD n 0x256 (reg n)) (rsp : reg n sp = S) (r18 : reg n (18 : Fin 32) = 0xFE)
    (r22 : reg n (22 : Fin 32) = EXP2) (r24 : reg n (24 : Fin 32) = P2N + 0x20)
    (hT : ∀ j, j < 16 → accV M (S + BitVec.ofNat 32 (0x43C + 32 * j)) 8 = mpow2 A j)
    (hN0 : memLoad32 M (S + BitVec.ofNat 32 0xE4) = 0xFFFFFFFF) (hN : accV M (S + BitVec.ofNat 32 0xE4) 8 = p256) :
    ∃ n', Steps n n' ∧ St n'.mem GD n' 0x2D4 (reg n') ∧ GdCode n'.mem ∧ GdData n'.mem ∧ GdBase n'.mem S A ∧
      GdRegs n' S ∧ reg n' (9 : Fin 32) = BitVec.ofNat 32 (7 + 1) ∧
      accV n'.mem (S + BitVec.ofNat 32 0x65C) 8 = mpow2 A (sqrtExp2 / 2 ^ (4 * (8 * 7 + 8))) ∧
      memLoad32 n'.mem (S + BitVec.ofNat 32 0x10) = reg n (27 : Fin 32) ∧
      memLoad32 n'.mem (S + BitVec.ofNat 32 0x14) = reg n (26 : Fin 32) ∧
      memLoad32 n'.mem (S + BitVec.ofNat 32 0x18) = reg n (25 : Fin 32) ∧
      (∀ x, Sep (S + 0xFFFFFFF0) 16 x 1 → Sep (S + BitVec.ofNat 32 0x10) 12 x 1 → Sep (S + BitVec.ofNat 32 0x1C) 0x1C x 1 →
        Sep (S + BitVec.ofNat 32 0x21C) 0x220 x 1 → Sep (S + BitVec.ofNat 32 0x65C) 32 x 1 → n'.mem x = M x) ∧
      ∀ q : Fin 32, q.val ∈ [3, 4, 20, 24, 26] → reg n' q = reg n q := by
  have hz := s.zero
  have hSl := F.lo; have hSh := F.hi; have hSa := F.al
  obtain ⟨fA, fW, hFC⟩ := F.mc
  have hb16 : (S + 0xFFFFFFF0).toNat = S.toNat - 16 := F.below 16 (by decide) (by decide)
  have lo16 : ∀ x : Word, 0x40000000 ≤ x.toNat → Sep (S + 0xFFFFFFF0) 16 x 1 := fun x hx =>
    sep_of_le (by rw [hb16]; omega) (by have := x.isLt; omega)
  have l16b : ∀ d, d + 1 ≤ 0x710 → Sep (S + 0xFFFFFFF0) 16 (S + BitVec.ofNat 32 d) 1 := fun d hd =>
    sep_of_le (by rw [hb16, F.at d (by omega)]; omega) (by rw [F.at d (by omega)]; omega)
  have inFrame : ∀ {c l : Nat} {x : Word}, c + l ≤ 0x710 → Sep (S + 0xFFFFFE60) 0x8B0 x 1 →
      Sep (S + BitVec.ofNat 32 c) l x 1 := fun {c l x} h hx => by
    have := hx.sub (c := 0x1A0 + c) (l := l) (by omega)
    rwa [BitVec.add_assoc, show (0xFFFFFE60 : Word) + BitVec.ofNat 32 (0x1A0 + c) = BitVec.ofNat 32 c by
      apply BitVec.eq_of_toNat_eq
      rw [BitVec.toNat_add, BitVec.toNat_ofNat, BitVec.toNat_ofNat, show (0xFFFFFE60 : Word).toNat = 0xFFFFFE60 from rfl]
      omega] at this
  have below16 : ∀ {x : Word}, Sep (S + 0xFFFFFE60) 0x8B0 x 1 → Sep (S + 0xFFFFFFF0) 16 x 1 := fun {x} hx => by
    have := hx.sub (c := 0x190) (l := 16) (by decide)
    rwa [show S + 0xFFFFFE60 + BitVec.ofNat 32 0x190 = S + 0xFFFFFFF0 by rw [BitVec.add_assoc]; rfl] at this
  have al : ∀ c, c + 4 ≤ 0x710 → c % 4 = 0 → (S + BitVec.ofNat 32 c).toNat % 4 = 0 := fun c h1 h2 => by
    rw [F.at c (by omega)]; omega
  have kc : ∀ {m m' : Machine}, (∀ q, q ≠ a0 → q ≠ a1 → q ≠ a2 → q ≠ a3 → q ≠ a4 → q ≠ a5 → q ≠ a6 → q ≠ a7 → q ≠ t0 →
      q ≠ t1 → q ≠ (7 : Fin 32) → q ≠ (28 : Fin 32) → q ≠ (29 : Fin 32) → q ≠ (30 : Fin 32) → q ≠ ra → reg m' q = reg m q) →
      ∀ q : Fin 32, q.val ∈ [2, 3, 4, 8, 9, 18, 19, 20, 21, 22, 23, 24, 25, 26, 27] → reg m' q = reg m q :=
    fun h q hq => h q (by revert hq; revert q; decide) (by revert hq; revert q; decide) (by revert hq; revert q; decide)
      (by revert hq; revert q; decide) (by revert hq; revert q; decide) (by revert hq; revert q; decide)
      (by revert hq; revert q; decide) (by revert hq; revert q; decide) (by revert hq; revert q; decide)
      (by revert hq; revert q; decide) (by revert hq; revert q; decide) (by revert hq; revert q; decide)
      (by revert hq; revert q; decide) (by revert hq; revert q; decide) (by revert hq; revert q; decide)
  -- spill out, from_repr's choice, and y_is_odd, then copy the table down
  obtain ⟨n1, c1, u1⟩ := s.block gdF1 C.self gdF1_end (by
    simp only [BlockOk, BInstr.ok, BInstr.run, gdF1]; simp +decide only [and_true]
    rw [rsp]; exact ⟨⟨al 0x10 (by decide) (by decide), F.sepHi (by decide) (by decide) (by decide)⟩,
      ⟨al 0x14 (by decide) (by decide), F.sepHi (by decide) (by decide) (by decide)⟩,
      al 0x18 (by decide) (by decide), F.sepHi (by decide) (by decide) (by decide)⟩)
  have r1 : ∀ q, reg n1 q = (runBlock gdF1 (M, reg n)).2 q := fun q => by rw [u1.regs]
  obtain ⟨M1, hM1⟩ : ∃ M1, memStore32 (memStore32 (memStore32 M (S + BitVec.ofNat 32 0x10) (reg n (27 : Fin 32)))
      (S + BitVec.ofNat 32 0x14) (reg n (26 : Fin 32))) (S + BitVec.ofNat 32 0x18) (reg n (25 : Fin 32)) = M1 := ⟨_, rfl⟩
  have m1 : n1.mem = M1 := by
    rw [u1.mem, ← hM1]; simp +decide only [runBlock, BInstr.run, gdF1, upd, ↓reduceIte]; rw [rsp]; rfl
  have h1 : ∀ x, Sep (S + BitVec.ofNat 32 0x10) 12 x 1 → M1 x = M x := fun x hx => by
    rw [← hM1, memStore32_get_sep (by have := hx.sub (c := 8) (l := 4) (by decide); rwa [add_ofNat_assoc] at this),
      memStore32_get_sep (by have := hx.sub (c := 4) (l := 4) (by decide); rwa [add_ofNat_assoc] at this),
      memStore32_get_sep (by have := hx.sub (c := 0) (l := 4) (by decide); rwa [add_ofNat_zero] at this)]
  have C1 : GdCode M1 := C.hi fun x hx => h1 x (F.hiOut (by decide) hx)
  have D1 : GdData M1 := D.of F fun x hx => h1 x (inFrame (by decide) hx)
  have g1 : ∀ q, q ≠ a0 → q ≠ a1 → q ≠ a2 → reg n1 q = reg n q := fun q h0 h1 h2 => by
    rw [r1, runBlock_reg _ _ _ q hz (by simp only [gdF1]; revert h0 h1 h2; revert q; decide)]
  have sp1 : reg n1 sp = S := by rw [g1 sp (by decide) (by decide) (by decide)]; exact rsp
  obtain ⟨n2, c2, u2, fr2, k2⟩ := c_memcpy (dst := S + BitVec.ofNat 32 0x21C) (src := S + BitVec.ofNat 32 0x43C)
    (S := S) (N := 0x200) (⟨u1.pc, m1, fun _ => rfl⟩ : St M1 GD n1 0x266 (reg n1)) C1.self C1.K.K gd_at_266 gd_at_26a
    (by decide) (by decide) (by rw [r1, runBlock_reg _ _ _ sp hz (by decide)]; exact rsp)
    (by rw [r1]; simp +decide only [runBlock, BInstr.run, gdF1, upd, ↓reduceIte]; rw [rsp]; rfl)
    (by rw [r1]; simp +decide only [runBlock, BInstr.run, gdF1, upd, ↓reduceIte]; rw [rsp]; rfl)
    (by rw [r1]; simp +decide only [runBlock, BInstr.run, gdF1, upd, ↓reduceIte]; (try rw [hz]); try rfl)
    ⟨C1.K.K.body, F.sepHi (by decide) (by decide) (by decide), hFC, F.mcN (by decide), F.mcN (by decide),
      sepS S (.inl (by decide)) (by decide) (by decide), fA, fW, by rw [F.at _ (by decide)]; omega,
      by rw [F.at _ (by decide)]; omega⟩
  have fr2' : ∀ x, Sep (S + 0xFFFFFFF0) 16 x 1 → Sep (S + BitVec.ofNat 32 0x21C) 0x200 x 1 → n2.mem x = M1 x :=
    fun x a b => by rw [fr2 x a, copyBytes_sep b (Nat.le_refl _)]
  have C2 := C1.hi fun x hx => fr2' x (lo16 x hx) (F.hiOut (by decide) hx)
  have D2 : GdData n2.mem := D1.of F fun x hx => fr2' x (below16 hx) (inFrame (by decide) hx)
  have k2' := kc k2
  -- copy the exponent
  obtain ⟨n3, c3, u3⟩ := u2.block gdF2 C2.self gdF2_end ⟨trivial, trivial, trivial, trivial⟩
  have r3 : ∀ q, reg n3 q = (runBlock gdF2 (n2.mem, reg n2)).2 q := fun q => by rw [u3.regs]
  have sp2 : reg n2 sp = S := by rw [k2' sp (by decide)]; exact sp1
  obtain ⟨n4, c4, u4, fr4, k4⟩ := c_memcpy (dst := S + BitVec.ofNat 32 0x41C) (src := EXP2) (S := S) (N := 32)
    (⟨u3.pc, u3.mem, fun _ => rfl⟩ : St n2.mem GD n3 0x278 (reg n3)) C2.self C2.K.K gd_at_278 gd_at_27c (by decide) (by decide)
    (by rw [r3, runBlock_reg _ _ _ sp u2.zero (by decide)]; exact sp2)
    (by rw [r3]; simp +decide only [runBlock, BInstr.run, gdF2, upd, ↓reduceIte]; rw [sp2]; rfl)
    (by rw [r3]; simp +decide only [runBlock, BInstr.run, gdF2, upd, ↓reduceIte]; rw [k2' 22 (by decide),
        g1 22 (by decide) (by decide) (by decide), r22]; exact BitVec.zero_add _)
    (by rw [r3]; simp +decide only [runBlock, BInstr.run, gdF2, upd, ↓reduceIte]; (try rw [u2.zero]); try rfl)
    ⟨C2.K.K.body, F.sepHi (by decide) (by decide) (by decide), hFC, F.mcN (by decide),
      (F.lowData (c := 16) (by decide) rfl (by decide) (by decide)).symm, F.bufData (by decide) (by decide) (by decide),
      fA, fW, by rw [F.at _ (by decide)]; omega, by decide⟩
  have fr4' : ∀ x, Sep (S + 0xFFFFFFF0) 16 x 1 → Sep (S + BitVec.ofNat 32 0x41C) 32 x 1 → n4.mem x = n2.mem x :=
    fun x a b => by rw [fr4 x a, copyBytes_sep b (Nat.le_refl _)]
  have C4 := C2.hi fun x hx => fr4' x (lo16 x hx) (F.hiOut (by decide) hx)
  have D4 : GdData n4.mem := D2.of F fun x hx => fr4' x (below16 hx) (inFrame (by decide) hx)
  have k4' := kc k4
  -- the exponent's shape: 8 limbs, a top window of two bits; then z = 1
  obtain ⟨n5, c5, u5⟩ := u4.block gdF3 C4.self gdF3_end ⟨trivial, trivial, trivial, trivial, trivial, trivial, trivial,
    trivial, trivial, trivial, trivial, trivial⟩
  have r5 : ∀ q, reg n5 q = (runBlock gdF3 (n4.mem, reg n4)).2 q := fun q => by rw [u5.regs]
  have g3 : ∀ q : Fin 32, q.val ∈ [2, 3, 4, 8, 9, 18, 19, 20, 21, 22, 23, 24, 25, 26, 27] → reg n3 q = reg n2 q := fun q hq => by
    rw [r3, runBlock_reg _ _ _ q u2.zero (by simp only [gdF2]; revert hq; revert q; decide)]
  have k14 : ∀ q : Fin 32, q.val ∈ [2, 3, 4, 8, 9, 18, 19, 20, 21, 22, 23, 24, 25, 26, 27] → reg n4 q = reg n q := fun q hq => by
    rw [k4' q hq, g3 q hq, k2' q hq, g1 q (by revert hq; revert q; decide) (by revert hq; revert q; decide)
      (by revert hq; revert q; decide)]
  have sp4 : reg n4 sp = S := by rw [k14 sp (by decide)]; exact rsp
  obtain ⟨n6, c6, u6, fr6, k6⟩ := c_memcpy (dst := S + BitVec.ofNat 32 0x65C) (src := P2N + 0x20) (S := S) (N := 32)
    (⟨u5.pc, u5.mem, fun _ => rfl⟩ : St n4.mem GD n5 0x2A4 (reg n5)) C4.self C4.K.K gd_at_2a4 gd_at_2a8 (by decide) (by decide)
    (by rw [r5, runBlock_reg _ _ _ sp u4.zero (by decide)]; exact sp4)
    (by rw [r5]; simp +decide only [runBlock, BInstr.run, gdF3, upd, ↓reduceIte]; rw [sp4]; rfl)
    (by rw [r5]; simp +decide only [runBlock, BInstr.run, gdF3, upd, ↓reduceIte]; rw [k14 24 (by decide), r24]
        exact BitVec.zero_add _)
    (by rw [r5]; simp +decide only [runBlock, BInstr.run, gdF3, upd, ↓reduceIte]; (try rw [u4.zero]); try rfl)
    ⟨C4.K.K.body, F.sepHi (by decide) (by decide) (by decide), hFC, F.mcN (by decide),
      (F.lowData (c := 16) (by decide) rfl (by decide) (by decide)).symm, F.bufData (by decide) (by decide) (by decide),
      fA, fW, by rw [F.at _ (by decide)]; omega, by decide⟩
  have fr6' : ∀ x, Sep (S + 0xFFFFFFF0) 16 x 1 → Sep (S + BitVec.ofNat 32 0x65C) 32 x 1 → n6.mem x = n4.mem x :=
    fun x a b => by rw [fr6 x a, copyBytes_sep b (Nat.le_refl _)]
  have C6 := C4.hi fun x hx => fr6' x (lo16 x hx) (F.hiOut (by decide) hx)
  have D6 : GdData n6.mem := D4.of F fun x hx => fr6' x (below16 hx) (inFrame (by decide) hx)
  have k6' := kc k6
  have e5 : ∀ q : Fin 32, q.val ∈ [8, 9, 18] → reg n6 q = (runBlock gdF3 (n4.mem, reg n4)).2 q := fun q hq => by
    rw [k6' q (by revert hq; revert q; decide), r5]
  have v8 : reg n6 (8 : Fin 32) = 7 := by
    rw [e5 8 (by decide)]; simp +decide only [runBlock, BInstr.run, gdF3, upd, ↓reduceIte]
    rw [k14 18 (by decide), r18]; decide
  have v9 : reg n6 (9 : Fin 32) = 7 := by
    rw [e5 9 (by decide)]; simp +decide only [runBlock, BInstr.run, gdF3, upd, ↓reduceIte]
    rw [k14 18 (by decide), r18]; decide
  have v18 : reg n6 (18 : Fin 32) = 3 := by
    rw [e5 18 (by decide)]; simp +decide only [runBlock, BInstr.run, gdF3, upd, ↓reduceIte]
    rw [k14 18 (by decide), r18]; decide
  have sp6 : reg n6 sp = S := by rw [k6' sp (by decide), r5, runBlock_reg _ _ _ sp u4.zero (by decide)]; exact sp4
  -- spill the counters and point the squarings at their buffers
  obtain ⟨n7, c7, u7⟩ := u6.block gdF4 C6.self gdF4_end (by
    simp only [BlockOk, BInstr.ok, BInstr.run, gdF4]; simp +decide only [upd, ↓reduceIte, true_and, and_true]
    rw [sp6]
    exact ⟨⟨al 0x34 (by decide) (by decide), F.sepHi (by decide) (by decide) (by decide)⟩,
      ⟨al 0x30 (by decide) (by decide), F.sepHi (by decide) (by decide) (by decide)⟩,
      ⟨al 0x1C (by decide) (by decide), F.sepHi (by decide) (by decide) (by decide)⟩,
      al 0x24 (by decide) (by decide), F.sepHi (by decide) (by decide) (by decide)⟩)
  obtain ⟨M7, hM7⟩ : ∃ M7, memStore32 (memStore32 (memStore32 (memStore32 n6.mem (S + BitVec.ofNat 32 0x34) 7)
      (S + BitVec.ofNat 32 0x30) 7) (S + BitVec.ofNat 32 0x1C) 8) (S + BitVec.ofNat 32 0x24) 3 = M7 := ⟨_, rfl⟩
  have m7 : n7.mem = M7 := by
    rw [u7.mem, ← hM7]; simp +decide only [runBlock, BInstr.run, gdF4, upd, ↓reduceIte]; rw [sp6, v9, v8, v18]; rfl
  have r7 : ∀ q, reg n7 q = (runBlock gdF4 (n6.mem, reg n6)).2 q := fun q => by rw [u7.regs]
  have t7 : St M7 GD n7 0x2D0 (reg n7) := ⟨u7.pc, m7, fun _ => rfl⟩
  have e79 : reg n7 (9 : Fin 32) = BitVec.ofNat 32 (7 + 1) := by
    rw [r7]; simp +decide only [runBlock, BInstr.run, gdF4, upd, ↓reduceIte]; rw [v9]; rfl
  have h7 : ∀ x, Sep (S + BitVec.ofNat 32 0x1C) 0x1C x 1 → M7 x = n6.mem x := fun x hx => by
    rw [← hM7, memStore32_get_sep (by have := hx.sub (c := 8) (l := 4) (by decide); rwa [add_ofNat_assoc] at this),
      memStore32_get_sep (by have := hx.sub (c := 0) (l := 4) (by decide); rwa [add_ofNat_zero] at this),
      memStore32_get_sep (by have := hx.sub (c := 0x14) (l := 4) (by decide); rwa [add_ofNat_assoc] at this),
      memStore32_get_sep (by have := hx.sub (c := 0x18) (l := 4) (by decide); rwa [add_ofNat_assoc] at this)]
  have C7 : GdCode M7 := C6.hi fun x hx => h7 x (F.hiOut (by decide) hx)
  obtain ⟨n8, d8, u8⟩ := t7.notTaken C7.self 0x2D4 gd_at_2d0 (by decide) (by
    show (reg n7 (9 : Fin 32) == reg n7 x0) = false; rw [e79, t7.zero]; rfl)
  -- memory: a word of the frame this stage does not write
  have wM : ∀ d, d + 4 ≤ 0x710 → (d + 4 ≤ 0x10 ∨ 0x38 ≤ d) → (d + 4 ≤ 0x21C ∨ 0x43C ≤ d) → (d + 4 ≤ 0x65C ∨ 0x67C ≤ d) →
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
  have D7 : GdData M7 := D6.of F fun x hx => h7 x (inFrame (by decide) hx)
  have l16 : ∀ d, d + 4 ≤ 0x710 → Sep (S + 0xFFFFFFF0) 16 (S + BitVec.ofNat 32 d) 4 := fun d hd =>
    sep_of_le (by rw [hb16, F.at d (by omega)]; omega) (by rw [F.at d (by omega)]; omega)
  have bN0 : memLoad32 M7 (S + BitVec.ofNat 32 0xE4) = 0xFFFFFFFF := by
    rw [wM 0xE4 (by decide) (.inr (by decide)) (.inl (by decide)) (.inl (by decide))]; exact hN0
  have bN : accV M7 (S + BitVec.ofNat 32 0xE4) 8 = p256 := by
    rw [← hN]; exact accV_congr2 8 fun i hi => by
      rw [add_ofNat_assoc, wM _ (by omega) (.inr (by omega)) (.inl (by omega)) (.inl (by omega))]
  have bpw : ∀ k, k < 16 → accV M7 (S + BitVec.ofNat 32 (0x21C + 32 * k)) 8 = mpow2 A k := fun k hk => by
    rw [← hT k hk]
    refine accV_congr2 8 fun i hi => ?_
    rw [add_ofNat_assoc, add_ofNat_assoc]
    have e1 : memLoad32 M7 (S + BitVec.ofNat 32 (0x21C + 32 * k + 4 * i)) =
        memLoad32 n2.mem (S + BitVec.ofNat 32 (0x21C + 32 * k + 4 * i)) := memLoad32_congr fun q hq => by
      rw [add_ofNat_assoc]
      rw [h7 _ (sepS S (.inl (by omega)) (by decide) (by omega)),
        fr6' _ (l16b _ (by omega)) (sepS S (.inr (by omega)) (by decide) (by omega)),
        fr4' _ (l16b _ (by omega)) (sepS S (.inr (by omega)) (by decide) (by omega))]
    have e2 : memLoad32 n2.mem (S + BitVec.ofNat 32 (0x21C + 32 * k + 4 * i)) =
        memLoad32 M1 (S + BitVec.ofNat 32 (0x43C + 32 * k + 4 * i)) := by
      rw [load_frame fr2 (l16 _ (by omega)), show 0x21C + 32 * k + 4 * i = 0x21C + (32 * k + 4 * i) by omega,
        ← add_ofNat_assoc S 0x21C, cp_word (by omega) (by decide), add_ofNat_assoc,
        show 0x43C + (32 * k + 4 * i) = 0x43C + 32 * k + 4 * i by omega]
    rw [e1, e2]
    exact memLoad32_congr fun q hq => by
      rw [add_ofNat_assoc]; exact h1 _ (sepS S (.inl (by omega)) (by decide) (by omega))
  have bex : ∀ j, j < 8 → memLoad32 M7 (S + BitVec.ofNat 32 (0x41C + 4 * j)) = expLimb2 j := fun j hj => by
    have e1 : memLoad32 M7 (S + BitVec.ofNat 32 (0x41C + 4 * j)) = memLoad32 n4.mem (S + BitVec.ofNat 32 (0x41C + 4 * j)) :=
      memLoad32_congr fun q hq => by
        rw [add_ofNat_assoc]
        rw [h7 _ (sepS S (.inl (by omega)) (by decide) (by omega)),
          fr6' _ (l16b _ (by omega)) (sepS S (.inr (by omega)) (by decide) (by omega))]
    rw [e1, load_frame fr4 (l16 _ (by omega)), ← add_ofNat_assoc S 0x41C, cp_word (by omega) (by decide),
      show (4 * j) = 0 + 4 * j by omega, D2.exw j hj]
  have B7 : GdBase M7 S A := ⟨bN0, bN, bpw, bex,
    by rw [← hM7, slot_word8 (by decide) (by decide) (.inr (by decide)), memLoad32_store32_same],
    by rw [← hM7, slot_word8 (by decide) (by decide) (.inl (by decide)), slot_word8 (by decide) (by decide) (.inl (by decide)),
      slot_word8 (by decide) (by decide) (.inl (by decide)), memLoad32_store32_same],
    by rw [← hM7, slot_word8 (by decide) (by decide) (.inl (by decide)), slot_word8 (by decide) (by decide) (.inl (by decide)),
      memLoad32_store32_same],
    by rw [← hM7, memLoad32_store32_same]⟩
  have k6r : ∀ q : Fin 32, q.val ∈ [2, 3, 4, 20, 24, 26] → reg n6 q = reg n q := fun q hq => by
    rw [k6' q (by revert hq; revert q; decide), r5, runBlock_reg _ _ _ q u4.zero (by simp only [gdF3]; revert hq; revert q; decide),
      k14 q (by revert hq; revert q; decide)]
  have g7 : ∀ q : Fin 32, q.val ∈ [2, 3, 4, 20, 24, 26] → reg n8 q = reg n6 q := fun q hq => by
    rw [u8.regs, r7, runBlock_reg _ _ _ q u6.zero (by simp only [gdF4]; revert hq; revert q; decide)]
  have v7 : ∀ q, reg n8 q = (runBlock gdF4 (n6.mem, reg n6)).2 q := fun q => by rw [u8.regs, r7]
  refine ⟨n8, c1.trans (c2.trans (c3.trans (c4.trans (c5.trans (c6.trans (c7.trans (.single d8))))))),
    ⟨u8.pc, rfl, fun _ => rfl⟩, by rw [u8.mem]; exact C7, by rw [u8.mem]; exact D7, by rw [u8.mem]; exact B7,
    ⟨by rw [g7 sp (by decide), k6r sp (by decide)]; exact rsp,
      by rw [v7]; simp +decide only [runBlock, BInstr.run, gdF4, upd, ↓reduceIte]; (try rw [u6.zero]); try rfl,
      by rw [v7]; simp +decide only [runBlock, BInstr.run, gdF4, upd, ↓reduceIte]; rw [sp6]; rfl,
      by rw [v7]; simp +decide only [runBlock, BInstr.run, gdF4, upd, ↓reduceIte]; (try rw [u6.zero]); try rfl,
      by rw [v7]; simp +decide only [runBlock, BInstr.run, gdF4, upd, ↓reduceIte]; rw [sp6]; rfl,
      by rw [v7]; simp +decide only [runBlock, BInstr.run, gdF4, upd, ↓reduceIte]; rw [sp6]; rfl,
      by rw [v7]; simp +decide only [runBlock, BInstr.run, gdF4, upd, ↓reduceIte]; rw [sp6]; rfl⟩,
    by rw [u8.regs, e79], ?_, ?_, ?_, ?_, fun x h16 s10 s1C h2FC h95C => ?_,
    fun q hq => by rw [g7 q (by revert hq; revert q; decide), k6r q (by revert hq; revert q; decide)]⟩
  · rw [u8.mem, show 4 * (8 * 7 + 8) = 4 * 64 from rfl, exp_top2]
    show accV M7 (S + BitVec.ofNat 32 0x65C) 8 = p2one
    rw [← P2Data.one D4.D]
    refine accV_congr2 8 fun i hi => ?_
    have z1 : memLoad32 M7 (S + BitVec.ofNat 32 0x65C + BitVec.ofNat 32 (4 * i)) =
        memLoad32 n6.mem (S + BitVec.ofNat 32 0x65C + BitVec.ofNat 32 (4 * i)) := memLoad32_congr fun q hq => by
      rw [add_ofNat_assoc, add_ofNat_assoc]; exact h7 _ (sepS S (.inl (by omega)) (by decide) (by omega))
    have hs : Sep (S + 0xFFFFFFF0) 16 (S + BitVec.ofNat 32 0x65C + BitVec.ofNat 32 (4 * i)) 4 := by
      rw [add_ofNat_assoc]; exact l16 _ (by omega)
    rw [z1, load_frame fr6 hs, cp_word (by omega) (by decide)]
  · have wS : ∀ d, 0x10 ≤ d → d + 4 ≤ 0x1C → memLoad32 M7 (S + BitVec.ofNat 32 d) = memLoad32 M1 (S + BitVec.ofNat 32 d) :=
      fun d h1d h2d => memLoad32_congr fun q hq => by
        rw [add_ofNat_assoc]
        rw [h7 _ (sepS S (.inr (by omega)) (by decide) (by omega)),
          fr6' _ (l16b _ (by omega)) (sepS S (.inr (by omega)) (by decide) (by omega)),
          fr4' _ (l16b _ (by omega)) (sepS S (.inr (by omega)) (by decide) (by omega)),
          fr2' _ (l16b _ (by omega)) (sepS S (.inr (by omega)) (by decide) (by omega))]
    rw [u8.mem, wS 0x10 (by decide) (by decide), ← hM1, slot_word8 (by decide) (by decide) (.inr (by decide)),
      slot_word8 (by decide) (by decide) (.inr (by decide)), memLoad32_store32_same]
  · rw [u8.mem, show memLoad32 M7 (S + BitVec.ofNat 32 0x14) = memLoad32 M1 (S + BitVec.ofNat 32 0x14) from
      memLoad32_congr fun q hq => by
        rw [add_ofNat_assoc]
        rw [h7 _ (sepS S (.inr (by omega)) (by decide) (by omega)),
          fr6' _ (l16b _ (by omega)) (sepS S (.inr (by omega)) (by decide) (by omega)),
          fr4' _ (l16b _ (by omega)) (sepS S (.inr (by omega)) (by decide) (by omega)),
          fr2' _ (l16b _ (by omega)) (sepS S (.inr (by omega)) (by decide) (by omega))],
      ← hM1, slot_word8 (by decide) (by decide) (.inr (by decide)), memLoad32_store32_same]
  · rw [u8.mem, show memLoad32 M7 (S + BitVec.ofNat 32 0x18) = memLoad32 M1 (S + BitVec.ofNat 32 0x18) from
      memLoad32_congr fun q hq => by
        rw [add_ofNat_assoc]
        rw [h7 _ (sepS S (.inr (by omega)) (by decide) (by omega)),
          fr6' _ (l16b _ (by omega)) (sepS S (.inr (by omega)) (by decide) (by omega)),
          fr4' _ (l16b _ (by omega)) (sepS S (.inr (by omega)) (by decide) (by omega)),
          fr2' _ (l16b _ (by omega)) (sepS S (.inr (by omega)) (by decide) (by omega))],
      ← hM1, memLoad32_store32_same]
  · have s5FC : Sep (S + BitVec.ofNat 32 0x41C) 32 x 1 := by
      have := h2FC.sub (c := 0x200) (l := 32) (by decide); rwa [add_ofNat_assoc] at this
    have s2FC : Sep (S + BitVec.ofNat 32 0x21C) 0x200 x 1 := by
      have := h2FC.sub (c := 0) (l := 0x200) (by decide); rwa [add_ofNat_zero] at this
    rw [u8.mem, h7 x s1C, fr6' x h16 h95C, fr4' x h16 s5FC, fr2' x h16 s2FC, h1 x s10]


end C3.RV32.Gd
