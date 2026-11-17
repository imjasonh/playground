import C3BootProofs.Proofs.Ed25519VerifyP4b

/-!
# `ed25519_verify`, offsets 0x12CE to 0x1356: the digest as 16 words

The function copies the 64-byte digest from `F + 0x9F0` to `F + 0x7B0` and
on to `F + 0x8F0`, clears `F + 0x9F0`, and reads the copy at `F + 0x8F0` as
16 little-endian words into `F + 0x9F0`. The loop at offset 0x132A is the
loop at offset 0x150 with `s0` and `s1` swapped and twice the words.
-/

namespace C3.RV32

open C3.Image

section
variable {M0 Ms : Word → BitVec 8} {F pk sig msg : Word} {len : Nat} {r0 : Fin 32 → Word}

def evB133c : List BInstr :=
  [.lbu a3 a5 0, .aluImm .add a5 a5 1, .alu .sll a3 a3 (8 : Fin 32), .aluImm .add (8 : Fin 32) (8 : Fin 32) 8,
   .alu .or a4 a4 a3]

theorem evB133c_end : blockEnd ed25519VerifyCode 0x133C evB133c = some 0x134A :=
  blockEnd_cons' ev_at_133c rfl (blockEnd_cons' ev_at_1340 rfl (blockEnd_cons' ev_at_1342 rfl
    (blockEnd_cons' ev_at_1346 rfl (blockEnd_cons' ev_at_1348 rfl rfl))))

set_option maxRecDepth 20000 in
set_option maxHeartbeats 8000000 in
/-- The inner loop at offset 0x1336: `a4` gains the bytes at `b` from `j`
to 4, little-endian. -/
theorem ev_inner16 (C : EvCtx M0 F pk sig msg len) {M : Word → BitVec 8} {b : Word} :
    ∀ k j {n : Machine}, j + k = 4 → EvSt M0 Ms F r0 M n 0x1336 → reg n 8 = BitVec.ofNat 32 (8 * j) →
      reg n a5 = b + BitVec.ofNat 32 j → (reg n a4).toNat = leAcc M b j →
      ∃ n', Steps n n' ∧ EvSt M0 Ms F r0 M n' 0x134C ∧ (reg n' a4).toNat = leAcc M b 4 ∧
        ∀ q : Fin 32, q ≠ a3 → q ≠ a4 → q ≠ a5 → q ≠ (8 : Fin 32) → reg n' q = reg n q
  | 0, j, n, hk, D, h8, ha5, ha4 => by
    obtain rfl : j = 4 := by omega
    obtain ⟨n1, c1, D1, hr1⟩ := D.block C (off' := 0x133A) [.aluImm .add a3 (8 : Fin 32) 0xFFFFFFE0]
      (bEnd1 ev_at_1336 rfl) ⟨trivial, trivial⟩ rfl
      (fun q hq => by rcases hq with rfl | rfl | rfl <;> simp +decide only [runBlock, BInstr.run, upd, ↓reduceIte])
    obtain ⟨n2, d2, u2⟩ := D1.st.taken (D1.code C) 0x134C ev_at_133a (by decide)
      (by rw [hr1]; simp +decide only [runBlock, BInstr.run, upd, ↓reduceIte]; rw [h8, D1.st.zero]; decide)
    refine ⟨n2, c1.trans (.single d2), D1.jmp u2, by rw [u2.regs, hr1]; simpa +decide only [runBlock, BInstr.run, upd,
      ↓reduceIte] using ha4, fun q h3 h4 h5 h8' => ?_⟩
    by_cases h0 : q.val = 0
    · rw [show q = 0 from Fin.ext h0, u2.regs, D1.st.zero, D.st.zero]
    · rw [u2.regs, hr1]; simp only [runBlock, BInstr.run, upd, h0, h3, ↓reduceIte]
  | k + 1, j, n, hk, D, h8, ha5, ha4 => by
    have hj : j < 4 := by omega
    obtain ⟨n1, c1, D1, hr1⟩ := D.block C (off' := 0x133A) [.aluImm .add a3 (8 : Fin 32) 0xFFFFFFE0]
      (bEnd1 ev_at_1336 rfl) ⟨trivial, trivial⟩ rfl
      (fun q hq => by rcases hq with rfl | rfl | rfl <;> simp +decide only [runBlock, BInstr.run, upd, ↓reduceIte])
    obtain ⟨n2, d2, u2⟩ := D1.st.notTaken (D1.code C) 0x133C ev_at_133a (by decide)
      (by rw [hr1]; simp +decide only [runBlock, BInstr.run, upd, ↓reduceIte]; rw [h8, D1.st.zero]; exact beq_inner j hj)
    have D2 := D1.jmp u2
    obtain ⟨n3, c3, D3, hr3⟩ := D2.block C evB133c evB133c_end
      ⟨trivial, trivial, trivial, trivial, trivial, trivial⟩ rfl
      (fun q hq => by rcases hq with rfl | rfl | rfl <;> simp +decide only [evB133c, runBlock, BInstr.run, upd, ↓reduceIte])
    obtain ⟨n4, d4, u4⟩ := D3.st.jump (D3.code C) ev_at_134a (off' := 0x1336) (by decide) (by rw [D3.st.pc]; decide)
    have D4 := D3.jmp u4
    have R1 : ∀ q : Fin 32, q ≠ a3 → reg n2 q = reg n q := fun q h => by
      by_cases h0 : q.val = 0
      · rw [show q = 0 from Fin.ext h0, D2.st.zero, D.st.zero]
      · rw [u2.regs, hr1]; simp only [runBlock, BInstr.run, upd, h0, h, ↓reduceIte]
    have hsh : (BitVec.ofNat 32 (8 * j)).toNat % 32 = 8 * j := by
      rw [BitVec.toNat_ofNat]; omega
    obtain ⟨n', c', D', ha4', kp'⟩ := ev_inner16 C k (j + 1) (by omega) D4
      (by rw [u4.regs, hr3]; simp +decide only [evB133c, runBlock, BInstr.run, upd, ↓reduceIte]
          rw [R1 _ (by decide), h8, show (8 : Word) = BitVec.ofNat 32 8 from rfl]
          exact (BitVec.ofNat_add_ofNat ..).trans (congrArg _ (by omega)))
      (by rw [u4.regs, hr3]; simp +decide only [evB133c, runBlock, BInstr.run, upd, ↓reduceIte]
          rw [R1 _ (by decide), ha5, show (1 : Word) = BitVec.ofNat 32 1 from rfl]; exact add_ofNat_assoc ..)
      (by
        rw [u4.regs, hr3]; simp +decide only [evB133c, runBlock, BInstr.run, upd, ↓reduceIte]
        rw [R1 _ (by decide), R1 _ (by decide), R1 _ (by decide), ha5, h8, add_lit_zero, leAcc]
        have hb := (M (b + BitVec.ofNat 32 j)).isLt
        have hl := leAcc_lt M b j
        have e : aluEval .or (reg n a4) (aluEval .sll ((M (b + BitVec.ofNat 32 j)).zeroExtend 32)
            (BitVec.ofNat 32 (8 * j))) = reg n a4 ||| (M (b + BitVec.ofNat 32 j)).zeroExtend 32 <<< (8 * j) := by
          simp only [aluEval]; rw [hsh]
        rw [e, or_shl _ _ (by rw [ha4, Nat.pow_mul]; exact hl) (by
            rw [BitVec.toNat_setWidth, Nat.mod_eq_of_lt (by omega), Nat.pow_mul]
            have : (M (b + BitVec.ofNat 32 j)).toNat * 256 ^ j ≤ 255 * 256 ^ 3 :=
              Nat.mul_le_mul (by omega) (Nat.pow_le_pow_right (by decide) (by omega))
            show (M (b + BitVec.ofNat 32 j)).toNat * 256 ^ j < 2 ^ 32; omega),
          ha4, BitVec.toNat_setWidth, Nat.mod_eq_of_lt (by omega), Nat.pow_mul])
    refine ⟨n', c1.trans (.cons d2 (c3.trans (.cons d4 c'))), D', ha4', fun q h3 h4 h5 h8' => ?_⟩
    rw [kp' q h3 h4 h5 h8', u4.regs, hr3]
    by_cases h0 : q.val = 0
    · rw [show q = 0 from Fin.ext h0]; simp +decide only [evB133c, runBlock, BInstr.run, upd, ↓reduceIte]
      exact D.st.zero.symm
    · simp only [evB133c, runBlock, BInstr.run, upd, h0, h3, h4, h5, h8', ↓reduceIte]; exact R1 q h3

/-- What the 16-word loop keeps at the head of iteration `i`, from the
memory `Mb` before it. -/
structure Words16Inv (F : Word) (Mb M : Word → BitVec 8) (i : Nat) : Prop where
  hW : ∀ t, t < i → memLoad32 M (F + BitVec.ofNat 32 (0x9F0 + 4 * t)) =
    BitVec.ofNat 32 (leAcc Mb (F + BitVec.ofNat 32 (0x8F0 + 4 * t)) 4)
  hZ : ∀ j, 4 * i ≤ j → j < 64 → M (F + BitVec.ofNat 32 (0x9F0 + j)) = 0
  hK : ∀ c, c < 0x16A0 → (c < 0x9F0 ∨ 0xA30 ≤ c) → M (F + BitVec.ofNat 32 c) = Mb (F + BitVec.ofNat 32 c)

def evB132a : List BInstr :=
  [.aluImm .add (8 : Fin 32) x0 0, .aluImm .sll a2 a0 2, .alu .add a2 a2 (18 : Fin 32), .lw a4 a2 0,
   .alu .add a5 x0 (9 : Fin 32)]

theorem evB132a_end : blockEnd ed25519VerifyCode 0x132A evB132a = some 0x1336 :=
  blockEnd_cons' ev_at_132a rfl (blockEnd_cons' ev_at_132c rfl (blockEnd_cons' ev_at_1330 rfl
    (blockEnd_cons' ev_at_1332 rfl (blockEnd_cons' ev_at_1334 rfl rfl))))

theorem evSll16 (i : Nat) (G : Word) :
    aluEval .add (aluEval .sll (BitVec.ofNat 32 i) 2) G = G + BitVec.ofNat 32 (4 * i) := by
  have e : aluEval .sll (BitVec.ofNat 32 i) 2 = BitVec.ofNat 32 (4 * i) := by
    apply BitVec.eq_of_toNat_eq
    show (BitVec.ofNat 32 i <<< ((2 : Word).toNat % 32)).toNat = _
    rw [BitVec.toNat_shiftLeft, BitVec.toNat_ofNat, BitVec.toNat_ofNat, show (2 : Word).toNat % 32 = 2 from rfl,
      Nat.shiftLeft_eq]; omega
  rw [e]; exact BitVec.add_comm _ _

set_option maxRecDepth 20000 in
set_option maxHeartbeats 16000000 in
/-- One iteration of the 16-word loop from offset 0x132A: word `i` from the
four bytes at `F + 0x8F0 + 4i`. -/
theorem ev_outer16 (C : EvCtx M0 F pk sig msg len) {Mb M : Word → BitVec 8} {n : Machine} {i : Nat} (hi : i < 16)
    (D : EvSt M0 Ms F r0 M n 0x132A) (W : Words16Inv F Mb M i) (ha0 : reg n a0 = BitVec.ofNat 32 i)
    (ha1 : reg n a1 = 0x10) (h9 : reg n 9 = F + BitVec.ofNat 32 (0x8F0 + 4 * i))
    (h18 : reg n 18 = F + BitVec.ofNat 32 0x9F0) :
    ∃ n' M', Steps n n' ∧ Words16Inv F Mb M' (i + 1) ∧ reg n' a0 = BitVec.ofNat 32 (i + 1) ∧ reg n' a1 = 0x10 ∧
      reg n' 9 = F + BitVec.ofNat 32 (0x8F0 + 4 * (i + 1)) ∧ reg n' 18 = F + BitVec.ofNat 32 0x9F0 ∧
      (∀ q : Fin 32, q.val ∈ evKeep → q ≠ 8 → q ≠ 9 → reg n' q = reg n q) ∧
      (i + 1 < 16 → EvSt M0 Ms F r0 M' n' 0x132A) ∧ (i + 1 = 16 → EvSt M0 Ms F r0 M' n' 0x1356) := by
  have ea2 : aluEval .add (aluEval .sll (reg n a0) 2) (reg n 18) = F + BitVec.ofNat 32 (0x9F0 + 4 * i) := by
    rw [ha0, h18, evSll16, add_ofNat_assoc]
  obtain ⟨n1, c1, D1, hr1⟩ := D.block C evB132a evB132a_end
    ⟨trivial, trivial, trivial, by
      show (aluEval .add (aluEval .sll (reg n a0) 2) (reg n 18) + 0).toNat % 4 = 0
      rw [ea2, add_lit_zero]; exact C.al (by omega), trivial, trivial⟩ rfl
    (fun q hq => by rcases hq with rfl | rfl | rfl <;> simp +decide only [evB132a, runBlock, BInstr.run, upd, ↓reduceIte])
  have va2 : reg n1 a2 = F + BitVec.ofNat 32 (0x9F0 + 4 * i) := by
    rw [hr1]; simp +decide only [evB132a, runBlock, BInstr.run, upd, ↓reduceIte]; exact ea2
  have va4 : reg n1 a4 = 0 := by
    rw [hr1]; simp +decide only [evB132a, runBlock, BInstr.run, upd, ↓reduceIte]
    rw [ea2, add_lit_zero]
    exact ld_zero fun j hj => by
      rw [add_ofNat_assoc, show 0x9F0 + 4 * i + j = 0x9F0 + (4 * i + j) by omega]; exact W.hZ _ (by omega) (by omega)
  obtain ⟨n2, c2, D2, ha42, kp2⟩ := ev_inner16 C (b := F + BitVec.ofNat 32 (0x8F0 + 4 * i)) 4 0 rfl D1
    (by rw [hr1]; simp +decide only [evB132a, runBlock, BInstr.run, upd, ↓reduceIte]; rfl)
    (by rw [hr1]; simp +decide only [evB132a, runBlock, BInstr.run, upd, ↓reduceIte]
        rw [h9, add_ofNat_zero]; exact BitVec.zero_add _)
    (by rw [va4]; rfl)
  have k2 : ∀ q : Fin 32, q ≠ a2 → q ≠ a3 → q ≠ a4 → q ≠ a5 → q ≠ (8 : Fin 32) → reg n2 q = reg n q := by
    intro q h2 h3 h4 h5 h8
    rw [kp2 q h3 h4 h5 h8, hr1]
    by_cases h0 : q.val = 0
    · rw [show q = 0 from Fin.ext h0]; simp +decide only [evB132a, runBlock, BInstr.run, upd, ↓reduceIte]
      exact D.st.zero.symm
    · simp only [evB132a, runBlock, BInstr.run, upd, h0, h2, h4, h5, h8, ↓reduceIte]
  have va2' : reg n2 a2 = F + BitVec.ofNat 32 (0x9F0 + 4 * i) := by
    rw [kp2 _ (by decide) (by decide) (by decide) (by decide), va2]
  obtain ⟨n3, c3, D3, hr3⟩ := D2.block C (off' := 0x134E) [.aluImm .add a0 a0 1] (bEnd1 ev_at_134c rfl)
    ⟨trivial, trivial⟩ rfl
    (fun q hq => by rcases hq with rfl | rfl | rfl <;> simp +decide only [runBlock, BInstr.run, upd, ↓reduceIte])
  have r3 : ∀ q : Fin 32, q ≠ a0 → reg n3 q = reg n2 q := fun q hq => by
    rw [hr3]; simp only [runBlock, BInstr.run]; exact upd_ne' hq D2.st.zero
  have hc := D3.code C
  obtain ⟨n4, d4, u4⟩ := D3.st.sw hc ev_at_134e (off' := 0x1350) (by decide)
    (by rw [r3 _ (by decide), va2', add_lit_zero]; exact C.al (by omega))
  rw [r3 _ (by decide), va2', add_lit_zero, r3 _ (by decide)] at u4
  have D4 := D3.store C (d := 0x9F0 + 4 * i) (k := 4) u4.self (by rw [u4.regs, D3.hsp]) (by rw [u4.regs])
    (by rw [u4.regs]) (by omega) (fun x hx => st32_frame hx)
  obtain ⟨n5, c5, D5, hr5⟩ := D4.block C (off' := 0x1352) [.aluImm .add (9 : Fin 32) (9 : Fin 32) 4]
    (bEnd1 ev_at_1350 rfl) ⟨trivial, trivial⟩ rfl
    (fun q hq => by rcases hq with rfl | rfl | rfl <;> simp +decide only [runBlock, BInstr.run, upd, ↓reduceIte])
  have r5 : ∀ q : Fin 32, q ≠ (9 : Fin 32) → reg n5 q = reg n3 q := fun q hq => by
    rw [hr5, ← u4.regs q]; simp only [runBlock, BInstr.run]; exact upd_ne' hq D4.st.zero
  have va0 : reg n5 a0 = BitVec.ofNat 32 (i + 1) := by
    rw [r5 _ (by decide), hr3]; simp +decide only [runBlock, BInstr.run, upd, ↓reduceIte]
    rw [k2 _ (by decide) (by decide) (by decide) (by decide) (by decide), ha0]
    show BitVec.ofNat 32 i + BitVec.ofNat 32 1 = BitVec.ofNat 32 (i + 1); rw [BitVec.ofNat_add_ofNat]
  have va1 : reg n5 a1 = 0x10 := by
    rw [r5 _ (by decide), r3 _ (by decide), k2 _ (by decide) (by decide) (by decide) (by decide) (by decide), ha1]
  have hb : ∀ u, u < 4 → M (F + BitVec.ofNat 32 (0x8F0 + 4 * i) + BitVec.ofNat 32 u) =
      Mb (F + BitVec.ofNat 32 (0x8F0 + 4 * i) + BitVec.ofNat 32 u) := fun u hu => by
    rw [add_ofNat_assoc]; exact W.hK _ (by omega) (by omega)
  have hv : reg n2 a4 = BitVec.ofNat 32 (leAcc Mb (F + BitVec.ofNat 32 (0x8F0 + 4 * i)) 4) := by
    apply BitVec.eq_of_toNat_eq
    rw [ha42, BitVec.toNat_ofNat, leAcc_congr 4 hb, Nat.mod_eq_of_lt (leAcc_lt _ _ 4)]
  rw [hv] at D4 D5
  have W' : Words16Inv F Mb (memStore32 M (F + BitVec.ofNat 32 (0x9F0 + 4 * i))
      (BitVec.ofNat 32 (leAcc Mb (F + BitVec.ofNat 32 (0x8F0 + 4 * i)) 4))) (i + 1) :=
    ⟨fun t ht => by
      by_cases e : t = i
      · subst e; exact memLoad32_store32_same _ _ _
      · rw [memLoad32_store32_sep (C.offs (by omega) (by omega) (by omega))]; exact W.hW t (by omega),
     fun j h1 h2 => by rw [st32_frame (C.offs (by omega) (by omega) (by omega))]; exact W.hZ j (by omega) h2,
     fun c h1 h2 => by rw [st32_frame (C.offs (by omega) (by omega) (by omega))]; exact W.hK c h1 h2⟩
  have v9 : reg n5 9 = F + BitVec.ofNat 32 (0x8F0 + 4 * (i + 1)) := by
    rw [hr5]; simp +decide only [runBlock, BInstr.run, upd, ↓reduceIte]
    rw [u4.regs, r3 _ (by decide), k2 _ (by decide) (by decide) (by decide) (by decide) (by decide), h9]
    exact add_sp F (a := 0x8F0 + 4 * i) (b := 4) (c := 0x8F0 + 4 * (i + 1)) (by omega)
  have v18 : reg n5 18 = F + BitVec.ofNat 32 0x9F0 := by
    rw [r5 _ (by decide), r3 _ (by decide), k2 _ (by decide) (by decide) (by decide) (by decide) (by decide), h18]
  have kq : ∀ q : Fin 32, q.val ∈ evKeep → q ≠ 8 → q ≠ 9 → reg n5 q = reg n q := fun q hq h8 h9 => by
    rw [r5 q h9, r3 q (by revert hq; revert q; decide),
      k2 q (by revert hq; revert q; decide) (by revert hq; revert q; decide) (by revert hq; revert q; decide)
        (by revert hq; revert q; decide) h8]
  have hc5 := D5.code C
  have hne : (BitVec.ofNat 32 (i + 1)).toNat = i + 1 := by rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega)]
  rcases Nat.lt_or_ge (i + 1) 16 with hl | hl
  · obtain ⟨n6, d6, u6⟩ := D5.st.taken hc5 0x132A ev_at_1352 (by decide) (by
      rw [va0, va1]
      show (BitVec.ofNat 32 (i + 1) != 0x10) = true
      exact bne_iff_ne.mpr fun e => by have := congrArg BitVec.toNat e; rw [hne] at this; exact absurd this (by
        show i + 1 ≠ 16; omega))
    exact ⟨n6, _, c1.trans (c2.trans (c3.trans (.cons d4 (c5.trans (.single d6))))), W',
      by rw [u6.regs, va0], by rw [u6.regs, va1], by rw [u6.regs, v9], by rw [u6.regs, v18],
      fun q hq h8 h9 => by rw [u6.regs, kq q hq h8 h9], fun _ => D5.jmp u6, fun h => absurd h (by omega)⟩
  · have e16 : i + 1 = 16 := by omega
    obtain ⟨n6, d6, u6⟩ := D5.st.notTaken hc5 0x1356 ev_at_1352 (by decide) (by
      rw [va0, va1, e16]; rfl)
    exact ⟨n6, _, c1.trans (c2.trans (c3.trans (.cons d4 (c5.trans (.single d6))))), W',
      by rw [u6.regs, va0], by rw [u6.regs, va1], by rw [u6.regs, v9], by rw [u6.regs, v18],
      fun q hq h8 h9 => by rw [u6.regs, kq q hq h8 h9], fun h => absurd h (by omega), fun _ => D5.jmp u6⟩

/-- The 16-word loop from the head of iteration `i` to offset 0x1356. -/
theorem ev_loop16 (C : EvCtx M0 F pk sig msg len) {Mb : Word → BitVec 8} :
    ∀ k i {M : Word → BitVec 8} {n : Machine}, i + k = 16 → i < 16 → EvSt M0 Ms F r0 M n 0x132A →
      Words16Inv F Mb M i → reg n a0 = BitVec.ofNat 32 i → reg n a1 = 0x10 →
      reg n 9 = F + BitVec.ofNat 32 (0x8F0 + 4 * i) → reg n 18 = F + BitVec.ofNat 32 0x9F0 →
      ∃ n' M', Steps n n' ∧ EvSt M0 Ms F r0 M' n' 0x1356 ∧ Words16Inv F Mb M' 16 ∧
        ∀ q : Fin 32, q.val ∈ evKeep → q ≠ 8 → q ≠ 9 → reg n' q = reg n q
  | 0, i, _, _, hk, hi, _, _, _, _, _, _ => absurd hk (by omega)
  | k + 1, i, M, n, hk, hi, D, W, ha0, ha1, h9, h18 => by
    obtain ⟨n1, M1, c1, W1, ha01, ha11, h91, h181, kq1, T1, F1⟩ := ev_outer16 C hi D W ha0 ha1 h9 h18
    rcases Nat.lt_or_ge (i + 1) 16 with hl | hl
    · obtain ⟨n', M', c', D', W', kq'⟩ := ev_loop16 C k (i + 1) (by omega) hl (T1 hl) W1 ha01 ha11 h91 h181
      exact ⟨n', M', c1.trans c', D', W', fun q hq h8 h9 => by rw [kq' q hq h8 h9, kq1 q hq h8 h9]⟩
    · obtain e16 : i + 1 = 16 := by omega
      exact ⟨n1, M1, c1, F1 e16, by rw [← e16]; exact W1, kq1⟩

set_option maxRecDepth 20000 in
set_option maxHeartbeats 8000000 in
/-- From offset 0x1324: the 64 bytes at `F + 0x8F0` as 16 little-endian
words at `F + 0x9F0`, which must hold zeros. -/
theorem ev_words16 (C : EvCtx M0 F pk sig msg len) {M : Word → BitVec 8} {n : Machine} (D : EvSt M0 Ms F r0 M n 0x1324)
    (h9 : reg n 9 = F + BitVec.ofNat 32 0x8F0) (h18 : reg n 18 = F + BitVec.ofNat 32 0x9F0)
    (hz : ∀ j, j < 64 → M (F + BitVec.ofNat 32 (0x9F0 + j)) = 0) :
    ∃ n' M', Steps n n' ∧ EvSt M0 Ms F r0 M' n' 0x1356 ∧
      (∀ t, t < 16 → memLoad32 M' (F + BitVec.ofNat 32 (0x9F0 + 4 * t)) =
        BitVec.ofNat 32 (leAcc M (F + BitVec.ofNat 32 (0x8F0 + 4 * t)) 4)) ∧
      (∀ c, c < 0x16A0 → (c < 0x9F0 ∨ 0xA30 ≤ c) → M' (F + BitVec.ofNat 32 c) = M (F + BitVec.ofNat 32 c)) ∧
      ∀ q : Fin 32, q.val ∈ evKeep → q ≠ 8 → q ≠ 9 → reg n' q = reg n q := by
  obtain ⟨n1, c1, D1, hr1⟩ := D.block C (off' := 0x1328) [.aluImm .add a0 x0 0, .aluImm .add a1 x0 0x10]
    (blockEnd_cons' ev_at_1324 rfl (blockEnd_cons' ev_at_1326 rfl rfl)) ⟨trivial, trivial, trivial⟩ rfl
    (fun q hq => by rcases hq with rfl | rfl | rfl <;> simp +decide only [runBlock, BInstr.run, upd, ↓reduceIte])
  obtain ⟨n2, d2, u2⟩ := D1.st.notTaken (D1.code C) 0x132A ev_at_1328 (by decide)
    (by rw [D1.st.zero, hr1]; simp +decide only [runBlock, BInstr.run, upd, ↓reduceIte]; try decide)
  have R : ∀ q : Fin 32, q ≠ a0 → q ≠ a1 → reg n2 q = reg n q := fun q h0 h1 => by
    rw [u2.regs, hr1]
    by_cases hz0 : q.val = 0
    · rw [show q = 0 from Fin.ext hz0]; simp +decide only [runBlock, BInstr.run, upd, ↓reduceIte]
      exact D.st.zero.symm
    · simp only [runBlock, BInstr.run, upd, hz0, h0, h1, ↓reduceIte]
  obtain ⟨n', M', c', D', W', kq'⟩ := ev_loop16 C (Mb := M) 16 0 rfl (by decide) (D1.jmp u2)
    ⟨fun t ht => absurd ht (by omega), fun j _ h2 => hz j h2, fun _ _ _ => rfl⟩
    (by rw [u2.regs, hr1]; simp +decide only [runBlock, BInstr.run, upd, ↓reduceIte]; try rfl)
    (by rw [u2.regs, hr1]; simp +decide only [runBlock, BInstr.run, upd, ↓reduceIte]; try rfl)
    (by rw [R _ (by decide) (by decide), h9])
    (by rw [R _ (by decide) (by decide), h18])
  exact ⟨n', M', c1.trans (.cons d2 c'), D', W'.hW, W'.hK, fun q hq h8 h9 => by
    rw [kq' q hq h8 h9, R q (by revert hq; revert q; decide) (by revert hq; revert q; decide)]⟩

theorem leAcc_copy {M M' : Word → BitVec 8} {b b' : Word} :
    ∀ j, (∀ u, u < j → M (b + BitVec.ofNat 32 u) = M' (b' + BitVec.ofNat 32 u)) → leAcc M b j = leAcc M' b' j
  | 0, _ => rfl
  | j + 1, h => by
    simp only [leAcc]; rw [leAcc_copy j fun u hu => h u (by omega), h j (by omega)]

theorem fb_in {M : Word → BitVec 8} {dst : Word} {v : BitVec 8} {N j : Nat} (hj : j < N) (hN : N < 2 ^ 32) :
    fillBytes M dst v N (dst + BitVec.ofNat 32 j) = v := by
  unfold fillBytes
  rw [add_sub_toNat _ (by omega), ite_eq_left hj]

set_option maxRecDepth 20000 in
set_option maxHeartbeats 16000000 in
/-- From offset 0x12CE: the digest at `F + 0x9F0` copied to `F + 0x7B0` and
`F + 0x8F0`, and read back as 16 little-endian words at `F + 0x9F0`. -/
theorem ev_dw (C : EvCtx M0 F pk sig msg len) {M : Word → BitVec 8} {n : Machine} (D : EvSt M0 Ms F r0 M n 0x12CE) :
    ∃ n' M', Steps n n' ∧ EvSt M0 Ms F r0 M' n' 0x1356 ∧
      (∀ q : Fin 32, q.val ∈ evKeep → q ≠ 8 → q ≠ 9 → q ≠ 18 → reg n' q = reg n q) ∧
      (∀ t, t < 16 → memLoad32 M' (F + BitVec.ofNat 32 (0x9F0 + 4 * t)) =
        BitVec.ofNat 32 (leAcc M (F + BitVec.ofNat 32 (0x9F0 + 4 * t)) 4)) ∧
      memBytes M' (F + BitVec.ofNat 32 0x7B0) 64 = memBytes M (F + BitVec.ofNat 32 0x9F0) 64 ∧
      memBytes M' (F + BitVec.ofNat 32 0x8F0) 64 = memBytes M (F + BitVec.ofNat 32 0x9F0) 64 ∧
      ∀ c, c < 0x16A0 → (c < 0x7B0 ∨ (0x7F0 ≤ c ∧ c < 0x8F0) ∨ 0xA30 ≤ c) →
        M' (F + BitVec.ofNat 32 c) = M (F + BitVec.ofNat 32 c) := by
  obtain ⟨n1, c1, D1, hr1⟩ := D.block C (off' := 0x12E6)
    [.aluImm .add a0 sp 0x7B0, .aluImm .add a1 sp 0x7FF, .aluImm .add a1 a1 0x1F1, .aluImm .add a2 x0 0x40,
      .aluImm .add (18 : Fin 32) sp 0x7FF, .aluImm .add (18 : Fin 32) (18 : Fin 32) 0x1F1]
    (blockEnd_cons' ev_at_12ce rfl (blockEnd_cons' ev_at_12d2 rfl (blockEnd_cons' ev_at_12d6 rfl
      (blockEnd_cons' ev_at_12da rfl (blockEnd_cons' ev_at_12de rfl (blockEnd_cons' ev_at_12e2 rfl rfl))))))
    ⟨trivial, trivial, trivial, trivial, trivial, trivial, trivial⟩ rfl
    (fun q hq => by rcases hq with rfl | rfl | rfl <;> simp +decide only [runBlock, BInstr.run, upd, ↓reduceIte])
  have v18 : reg n1 18 = F + BitVec.ofNat 32 0x9F0 := by
    rw [hr1]; simp +decide only [runBlock, BInstr.run, upd, ↓reduceIte]
    rw [D.hsp, show aluEval .add F 0x7FF = F + BitVec.ofNat 32 0x7FF from rfl]; exact add_sp F rfl
  obtain ⟨n2, c2, D2, k2, fz2⟩ := D1.memcpy C (d := 0x7B0) (s := F + BitVec.ofNat 32 0x9F0) (N := 0x40)
    ev_at_12e6 ev_at_12ea (by decide) (by decide)
    (by rw [hr1]; simp +decide only [runBlock, BInstr.run, upd, ↓reduceIte]; rw [D.hsp]; rfl)
    (by rw [hr1]; simp +decide only [runBlock, BInstr.run, upd, ↓reduceIte]
        rw [D.hsp, show aluEval .add F 0x7FF = F + BitVec.ofNat 32 0x7FF from rfl]; exact add_sp F rfl)
    (by rw [hr1]; simp +decide only [runBlock, BInstr.run, upd, ↓reduceIte]; try rfl)
    (by decide) (C.zF (by decide)).symm (C.offs (by decide) (by decide) (by decide))
    (by rw [C.fN (by decide)]; have := C.hhi; omega)
  obtain ⟨n3, c3, D3, hr3⟩ := D2.block C (off' := 0x1306)
    [.aluImm .add a0 sp 0x7FF, .aluImm .add a0 a0 0xF1, .aluImm .add a1 sp 0x7B0, .aluImm .add a2 x0 0x40,
      .aluImm .add (9 : Fin 32) sp 0x7FF, .aluImm .add (9 : Fin 32) (9 : Fin 32) 0xF1]
    (blockEnd_cons' ev_at_12ee rfl (blockEnd_cons' ev_at_12f2 rfl (blockEnd_cons' ev_at_12f6 rfl
      (blockEnd_cons' ev_at_12fa rfl (blockEnd_cons' ev_at_12fe rfl (blockEnd_cons' ev_at_1302 rfl rfl))))))
    ⟨trivial, trivial, trivial, trivial, trivial, trivial, trivial⟩ rfl
    (fun q hq => by rcases hq with rfl | rfl | rfl <;> simp +decide only [runBlock, BInstr.run, upd, ↓reduceIte])
  have v9 : reg n3 9 = F + BitVec.ofNat 32 0x8F0 := by
    rw [hr3]; simp +decide only [runBlock, BInstr.run, upd, ↓reduceIte]
    rw [D2.hsp, show aluEval .add F 0x7FF = F + BitVec.ofNat 32 0x7FF from rfl]; exact add_sp F rfl
  obtain ⟨n4, c4, D4, k4, fz4⟩ := D3.memcpy C (d := 0x8F0) (s := F + BitVec.ofNat 32 0x7B0) (N := 0x40)
    ev_at_1306 ev_at_130a (by decide) (by decide)
    (by rw [hr3]; simp +decide only [runBlock, BInstr.run, upd, ↓reduceIte]
        rw [D2.hsp, show aluEval .add F 0x7FF = F + BitVec.ofNat 32 0x7FF from rfl]; exact add_sp F rfl)
    (by rw [hr3]; simp +decide only [runBlock, BInstr.run, upd, ↓reduceIte]; rw [D2.hsp]; rfl)
    (by rw [hr3]; simp +decide only [runBlock, BInstr.run, upd, ↓reduceIte]; try rfl)
    (by decide) (C.zF (by decide)).symm (C.offs (by decide) (by decide) (by decide))
    (by rw [C.fN (by decide)]; have := C.hhi; omega)
  obtain ⟨n5, c5, D5, hr5⟩ := D4.block C (off' := 0x131C)
    [.aluImm .add a0 sp 0x7FF, .aluImm .add a0 a0 0x1F1, .aluImm .add a2 x0 0x40, .aluImm .add a1 x0 0x0]
    (blockEnd_cons' ev_at_130e rfl (blockEnd_cons' ev_at_1312 rfl (blockEnd_cons' ev_at_1316 rfl
      (blockEnd_cons' ev_at_131a rfl rfl)))) ⟨trivial, trivial, trivial, trivial, trivial⟩ rfl
    (fun q hq => by rcases hq with rfl | rfl | rfl <;> simp +decide only [runBlock, BInstr.run, upd, ↓reduceIte])
  obtain ⟨n6, c6, D6, k6⟩ := D5.memset C (d := 0x9F0) (b := 0) (N := 0x40) ev_at_131c ev_at_1320 (by decide)
    (by decide)
    (by rw [hr5]; simp +decide only [runBlock, BInstr.run, upd, ↓reduceIte]
        rw [D4.hsp, show aluEval .add F 0x7FF = F + BitVec.ofNat 32 0x7FF from rfl]; exact add_sp F rfl)
    (by rw [hr5]; simp +decide only [runBlock, BInstr.run, upd, ↓reduceIte]; (try rw [D4.st.zero]); try rfl)
    (by rw [hr5]; simp +decide only [runBlock, BInstr.run, upd, ↓reduceIte]; (try rw [D4.st.zero]); try rfl)
    (by decide)
  have kk6 : ∀ q : Fin 32, q.val ∈ evKeep → reg n6 q = reg n5 q := fun q hq => by
    rw [k6 q hq]
  have r5 : ∀ q : Fin 32, q.val ∈ evKeep → q ≠ 9 → q ≠ 18 → reg n5 q = reg n q := fun q hq h9 h18 => by
    rw [hr5, evb_reg q D4.st.zero (by revert hq; revert q; decide), k4 q hq, hr3,
      evb_reg q D2.st.zero (by revert h9; revert hq; revert q; decide), k2 q hq, hr1,
      evb_reg q D.st.zero (by revert h18; revert hq; revert q; decide)]
  -- the copies
  have b4 : ∀ j, j < 64 → n4.mem (F + BitVec.ofNat 32 (0x8F0 + j)) = M (F + BitVec.ofNat 32 (0x9F0 + j)) := fun j hj => by
    rw [cp_at C fz4 (by decide) hj, add_ofNat_assoc, cp_at C fz2 (by decide) hj, add_ofNat_assoc]
  have b2 : ∀ j, j < 64 → n4.mem (F + BitVec.ofNat 32 (0x7B0 + j)) = M (F + BitVec.ofNat 32 (0x9F0 + j)) := fun j hj => by
    rw [cp_out C fz4 (by decide) (by omega) (Or.inl (by omega)), cp_at C fz2 (by decide) hj, add_ofNat_assoc]
  have f4 : ∀ c, c < 0x16A0 → (c < 0x7B0 ∨ (0x7F0 ≤ c ∧ c < 0x8F0) ∨ 0x930 ≤ c) →
      n4.mem (F + BitVec.ofNat 32 c) = M (F + BitVec.ofNat 32 c) := fun c hc hh => by
    rcases hh with hh | hh | hh <;>
      rw [cp_out C fz4 (by decide) hc (by omega), cp_out C fz2 (by decide) hc (by omega)]
  obtain ⟨n7, M7, c7, D7, hw7, fr7, kq7⟩ := ev_words16 C D6
    (by rw [kk6 9 (by decide), hr5, evb_reg 9 D4.st.zero (by decide), k4 9 (by decide), v9])
    (by rw [kk6 18 (by decide), hr5, evb_reg 18 D4.st.zero (by decide), k4 18 (by decide), hr3,
      evb_reg 18 D2.st.zero (by decide), k2 18 (by decide), v18])
    (fun j hj => by rw [← add_ofNat_assoc, fb_in hj (by decide)]; rfl)
  refine ⟨n7, M7, c1.trans (c2.trans (c3.trans (c4.trans (c5.trans (c6.trans c7))))), D7,
    fun q hq h8 h9 h18 => by rw [kq7 q hq h8 h9, kk6 q hq, r5 q hq h9 h18], fun t ht => ?_, ?_, ?_, fun c hc hh => ?_⟩
  · rw [hw7 t ht, leAcc_copy (M' := M) (b' := F + BitVec.ofNat 32 (0x9F0 + 4 * t)) 4 fun u hu => by
      rw [add_ofNat_assoc, add_ofNat_assoc, fb_out C (by decide) (by omega) (Or.inl (by omega)),
        show 0x8F0 + 4 * t + u = 0x8F0 + (4 * t + u) by omega, b4 _ (by omega),
        show 0x9F0 + (4 * t + u) = 0x9F0 + 4 * t + u by omega]]
  · unfold memBytes
    exact List.map_congr_left fun j hj => by
      have := List.mem_range.mp hj
      rw [add_ofNat_assoc, add_ofNat_assoc, fr7 _ (by omega) (Or.inl (by omega)),
        fb_out C (by decide) (by omega) (Or.inl (by omega)), b2 j this]
  · unfold memBytes
    exact List.map_congr_left fun j hj => by
      have := List.mem_range.mp hj
      rw [add_ofNat_assoc, add_ofNat_assoc, fr7 _ (by omega) (Or.inl (by omega)),
        fb_out C (by decide) (by omega) (Or.inl (by omega)), b4 j this]
  · rcases hh with hh | hh | hh
    · rw [fr7 c hc (Or.inl (by omega)), fb_out C (by decide) hc (Or.inl (by omega)), f4 c hc (Or.inl hh)]
    · rw [fr7 c hc (Or.inl (by omega)), fb_out C (by decide) hc (Or.inl (by omega)), f4 c hc (Or.inr (Or.inl hh))]
    · rw [fr7 c hc (Or.inr hh), fb_out C (by decide) hc (Or.inr (by omega)), f4 c hc (Or.inr (Or.inr (by omega)))]

end

end C3.RV32


