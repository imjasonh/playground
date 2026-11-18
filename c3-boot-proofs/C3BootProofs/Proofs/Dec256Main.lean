import C3BootProofs.Proofs.Dec256Pre

/-!
# P-256 point decompression

`<primeorder::affine::AffinePoint<NistP256> as DecompressPoint>::decompress`
from its entry to the limb loop: the prologue, decoding `x`, `α = x³ + ax + b`,
and the exponentiation's setup.
-/

namespace C3.RV32.Gd

open C3.Image C3.RV32.Dq C3.RV32.P3 C3.RV32.P2 C3.RV32.Gs

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


end C3.RV32.Gd
