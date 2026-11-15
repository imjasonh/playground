import C3BootProofs.Proofs.DerPositive
import C3BootProofs.Proofs.ZipNext

/-!
# `der::scalar::<48>`, as compiled

`der::scalar::<48>` reads a positive `INTEGER` through the proved
`Der::positive_integer`, drops one leading 0x00 byte, and fails with
`OutOfRange` when more than 48 bytes are left. Otherwise it zeroes a 48-byte
array in its frame with `memset`, copies the magnitude to the array's end a
byte at a time through the proved `Zip::next`, and copies the array to its
`Result<[u8; 48], Error>` with `memcpy`.
-/

namespace C3.RV32

open C3.Image

section
set_option maxRecDepth 20000
theorem ds_at_0 : fetchRel derScalar48Code 0x0 = some (.aluImm .add sp sp 0xFFFFFF90, 2) := by decide
theorem ds_at_2 : fetchRel derScalar48Code 0x2 = some (.store .sw sp ra 0x6C, 2) := by decide
theorem ds_at_4 : fetchRel derScalar48Code 0x4 = some (.store .sw sp (8 : Fin 32) 0x68, 2) := by decide
theorem ds_at_6 : fetchRel derScalar48Code 0x6 = some (.store .sw sp (9 : Fin 32) 0x64, 2) := by decide
theorem ds_at_8 : fetchRel derScalar48Code 0x8 = some (.store .sw sp (18 : Fin 32) 0x60, 2) := by decide
theorem ds_at_a : fetchRel derScalar48Code 0xA = some (.store .sw sp (19 : Fin 32) 0x5C, 2) := by decide
theorem ds_at_c : fetchRel derScalar48Code 0xC = some (.store .sw sp (20 : Fin 32) 0x58, 2) := by decide
theorem ds_at_e : fetchRel derScalar48Code 0xE = some (.alu .add (18 : Fin 32) x0 a0, 2) := by decide
theorem ds_at_10 : fetchRel derScalar48Code 0x10 = some (.aluImm .add a0 sp 0xC, 2) := by decide
theorem ds_at_12 : fetchRel derScalar48Code 0x12 = some (.auipc ra 0x0, 4) := by decide
theorem ds_at_16 : fetchRel derScalar48Code 0x16 = some (.jalr ra ra 0xFFFFFD00, 4) := by decide
theorem ds_at_1a : fetchRel derScalar48Code 0x1A = some (.load .lw (9 : Fin 32) sp 0xC, 2) := by decide
theorem ds_at_1c : fetchRel derScalar48Code 0x1C = some (.branch .beq (9 : Fin 32) x0 0x1E, 2) := by decide
theorem ds_at_1e : fetchRel derScalar48Code 0x1E = some (.load .lw a0 sp 0x10, 2) := by decide
theorem ds_at_20 : fetchRel derScalar48Code 0x20 = some (.branch .beq a0 x0 0x20, 2) := by decide
theorem ds_at_22 : fetchRel derScalar48Code 0x22 = some (.load .lbu a1 (9 : Fin 32) 0x0, 4) := by decide
theorem ds_at_26 : fetchRel derScalar48Code 0x26 = some (.aluImm .sltu a1 a1 0x1, 4) := by decide
theorem ds_at_2a : fetchRel derScalar48Code 0x2A = some (.alu .sub (8 : Fin 32) a0 a1, 4) := by decide
theorem ds_at_2e : fetchRel derScalar48Code 0x2E = some (.aluImm .add a0 x0 0x31, 4) := by decide
theorem ds_at_32 : fetchRel derScalar48Code 0x32 = some (.branch .bgeu (8 : Fin 32) a0 0x6E, 4) := by decide
theorem ds_at_36 : fetchRel derScalar48Code 0x36 = some (.alu .add (9 : Fin 32) (9 : Fin 32) a1, 2) := by decide
theorem ds_at_38 : fetchRel derScalar48Code 0x38 = some (.jal x0 0xA, 2) := by decide
theorem ds_at_3a : fetchRel derScalar48Code 0x3A = some (.load .lbu a0 sp 0x10, 4) := by decide
theorem ds_at_3e : fetchRel derScalar48Code 0x3E = some (.jal x0 0x64, 2) := by decide
theorem ds_at_40 : fetchRel derScalar48Code 0x40 = some (.aluImm .add (8 : Fin 32) x0 0x0, 2) := by decide
theorem ds_at_42 : fetchRel derScalar48Code 0x42 = some (.aluImm .add a0 x0 0x30, 4) := by decide
theorem ds_at_46 : fetchRel derScalar48Code 0x46 = some (.alu .sub (19 : Fin 32) a0 (8 : Fin 32), 4) := by decide
theorem ds_at_4a : fetchRel derScalar48Code 0x4A = some (.aluImm .add a0 sp 0xC, 2) := by decide
theorem ds_at_4c : fetchRel derScalar48Code 0x4C = some (.aluImm .add a2 x0 0x30, 4) := by decide
theorem ds_at_50 : fetchRel derScalar48Code 0x50 = some (.aluImm .add a1 x0 0x0, 2) := by decide
theorem ds_at_52 : fetchRel derScalar48Code 0x52 = some (.aluImm .add (20 : Fin 32) sp 0xC, 4) := by decide
theorem ds_at_56 : fetchRel derScalar48Code 0x56 = some (.auipc ra 0xC000, 4) := by decide
theorem ds_at_5a : fetchRel derScalar48Code 0x5A = some (.jalr ra ra 0x510, 4) := by decide
theorem ds_at_5e : fetchRel derScalar48Code 0x5E = some (.aluImm .add a0 sp 0x3C, 2) := by decide
theorem ds_at_60 : fetchRel derScalar48Code 0x60 = some (.alu .add a1 (9 : Fin 32) (8 : Fin 32), 4) := by decide
theorem ds_at_64 : fetchRel derScalar48Code 0x64 = some (.store .sw sp (20 : Fin 32) 0x3C, 2) := by decide
theorem ds_at_66 : fetchRel derScalar48Code 0x66 = some (.store .sw sp a0 0x40, 2) := by decide
theorem ds_at_68 : fetchRel derScalar48Code 0x68 = some (.store .sw sp (19 : Fin 32) 0x44, 2) := by decide
theorem ds_at_6a : fetchRel derScalar48Code 0x6A = some (.store .sw sp (9 : Fin 32) 0x48, 2) := by decide
theorem ds_at_6c : fetchRel derScalar48Code 0x6C = some (.store .sw sp a1 0x4C, 2) := by decide
theorem ds_at_6e : fetchRel derScalar48Code 0x6E = some (.store .sw sp x0 0x50, 2) := by decide
theorem ds_at_70 : fetchRel derScalar48Code 0x70 = some (.store .sw sp (8 : Fin 32) 0x54, 2) := by decide
theorem ds_at_72 : fetchRel derScalar48Code 0x72 = some (.aluImm .add a0 sp 0x3C, 2) := by decide
theorem ds_at_74 : fetchRel derScalar48Code 0x74 = some (.auipc ra 0x0, 4) := by decide
theorem ds_at_78 : fetchRel derScalar48Code 0x78 = some (.jalr ra ra 0xFFFFFCEE, 4) := by decide
theorem ds_at_7c : fetchRel derScalar48Code 0x7C = some (.branch .beq a0 x0 0xC, 2) := by decide
theorem ds_at_7e : fetchRel derScalar48Code 0x7E = some (.load .lbu a1 a1 0x0, 4) := by decide
theorem ds_at_82 : fetchRel derScalar48Code 0x82 = some (.store .sb a0 a1 0x0, 4) := by decide
theorem ds_at_86 : fetchRel derScalar48Code 0x86 = some (.jal x0 0xFFFFFFEC, 2) := by decide
theorem ds_at_88 : fetchRel derScalar48Code 0x88 = some (.aluImm .add a0 (18 : Fin 32) 0x1, 4) := by decide
theorem ds_at_8c : fetchRel derScalar48Code 0x8C = some (.aluImm .add a1 sp 0xC, 2) := by decide
theorem ds_at_8e : fetchRel derScalar48Code 0x8E = some (.aluImm .add a2 x0 0x30, 4) := by decide
theorem ds_at_92 : fetchRel derScalar48Code 0x92 = some (.auipc ra 0xC000, 4) := by decide
theorem ds_at_96 : fetchRel derScalar48Code 0x96 = some (.jalr ra ra 0x53C, 4) := by decide
theorem ds_at_9a : fetchRel derScalar48Code 0x9A = some (.store .sb (18 : Fin 32) x0 0x0, 4) := by decide
theorem ds_at_9e : fetchRel derScalar48Code 0x9E = some (.jal x0 0xE, 2) := by decide
theorem ds_at_a0 : fetchRel derScalar48Code 0xA0 = some (.aluImm .add a0 x0 0x5, 2) := by decide
theorem ds_at_a2 : fetchRel derScalar48Code 0xA2 = some (.aluImm .add a1 x0 0x1, 2) := by decide
theorem ds_at_a4 : fetchRel derScalar48Code 0xA4 = some (.store .sb (18 : Fin 32) a1 0x0, 4) := by decide
theorem ds_at_a8 : fetchRel derScalar48Code 0xA8 = some (.store .sb (18 : Fin 32) a0 0x1, 4) := by decide
theorem ds_at_ac : fetchRel derScalar48Code 0xAC = some (.load .lw ra sp 0x6C, 2) := by decide
theorem ds_at_ae : fetchRel derScalar48Code 0xAE = some (.load .lw (8 : Fin 32) sp 0x68, 2) := by decide
theorem ds_at_b0 : fetchRel derScalar48Code 0xB0 = some (.load .lw (9 : Fin 32) sp 0x64, 2) := by decide
theorem ds_at_b2 : fetchRel derScalar48Code 0xB2 = some (.load .lw (18 : Fin 32) sp 0x60, 2) := by decide
theorem ds_at_b4 : fetchRel derScalar48Code 0xB4 = some (.load .lw (19 : Fin 32) sp 0x5C, 2) := by decide
theorem ds_at_b6 : fetchRel derScalar48Code 0xB6 = some (.load .lw (20 : Fin 32) sp 0x58, 2) := by decide
theorem ds_at_b8 : fetchRel derScalar48Code 0xB8 = some (.aluImm .add sp sp 0x70, 2) := by decide
theorem ds_at_ba : fetchRel derScalar48Code 0xBA = some (.jalr x0 ra 0x0, 2) := by decide
end

/-- The frame after `i` passes of the copy loop: the zip's index at
`F + 0x50` is `i`, and the first `i` bytes of the magnitude at `src` are in
the array at `F + 0xC`, from offset `pad`. -/
def dsMem (Mz : Word → BitVec 8) (F src : Word) (pad i : Nat) : Word → BitVec 8 :=
  copyBytes (memStore32 Mz (F + 0x50) (BitVec.ofNat 32 i)) (F + 0xC + BitVec.ofNat 32 pad) src i

theorem cb_store32 {M : Word → BitVec 8} {D src a v x : Word} {k n : Nat} (hk : k ≤ n)
    (hD : Sep a 4 D n) (hS : Sep a 4 src n) :
    memStore32 (copyBytes M D src k) a v x = copyBytes (memStore32 M a v) D src k x := by
  by_cases hx : (x - D).toNat < k
  · have hxD : Sep a 4 x 1 := by rw [← off_of D x]; exact hD.subR (c := (x - D).toNat) (l := 1) (by omega)
    have hsx : Sep a 4 (src + (x - D)) 1 := by
      rw [← ofNat_toNat_self (x - D)]; exact hS.subR (c := (x - D).toNat) (l := 1) (by omega)
    rw [memStore32_get_sep hxD]
    unfold copyBytes
    rw [ite_eq_left hx, ite_eq_left hx, memStore32_get_sep hsx]
  · have h1 : copyBytes M D src k x = M x := by unfold copyBytes; rw [ite_eq_right hx]
    rw [memStore32_pt (v := v) (a := a) h1]
    unfold copyBytes
    rw [ite_eq_right hx]

theorem ds_ult {i s : Nat} (hi : i < 2 ^ 32) (hs : s < 2 ^ 32) :
    (BitVec.ofNat 32 i).ult (BitVec.ofNat 32 s) = decide (i < s) := by
  simp only [BitVec.ult, BitVec.toNat_ofNat, Nat.mod_eq_of_lt hi, Nat.mod_eq_of_lt hs]

set_option maxRecDepth 20000 in
set_option maxHeartbeats 8000000 in
/-- **The copy loop of `der::scalar::<48>`**, from its head at 0x72 with `i`
bytes copied: each pass calls `Zip::next` and stores the byte it returns. -/
theorem ds_loop {P F src : Word} {Mz : Word → BitVec 8} {s pad : Nat} (hP : P.toNat % 2 = 0) (hpad : pad + s = 48)
    (hFa : F.toNat % 4 = 0) (hFw : F.toNat + 0x70 ≤ 2 ^ 32) (hsw : src.toNat + s ≤ 2 ^ 32)
    (hc : CodeIn Mz P derScalar48Code) (hz : CodeIn Mz (P + 0xFFFFFD62) zipSkipNextCode)
    (sFC : Sep F 0x70 P derScalar48Code.length) (sFZ : Sep F 0x70 (P + 0xFFFFFD62) zipSkipNextCode.length)
    (sSF : Sep src s F 0x70)
    (z0 : memLoad32 Mz (F + 0x3C) = F + 0xC) (z8 : memLoad32 Mz (F + 0x44) = BitVec.ofNat 32 pad)
    (zC : memLoad32 Mz (F + 0x48) = src) (z18 : memLoad32 Mz (F + 0x54) = BitVec.ofNat 32 s) :
    ∀ k i, i + k = s → ∀ {n : Machine}, St (dsMem Mz F src pad i) P n 0x72 (reg n) → reg n sp = F →
      ∃ n', Steps n n' ∧ St (dsMem Mz F src pad s) P n' 0x88 (reg n') ∧
        ∀ q, q.val ∉ [1, 10, 11, 12, 13, 14, 15] → reg n' q = reg n q := by
  have hs48 : s ≤ 48 := by omega
  have eI : F + 0x3C + 0x14 = F + 0x50 := by rw [BitVec.add_assoc]; rfl
  have eZ8 : F + 0x3C + 8 = F + 0x44 := by rw [BitVec.add_assoc]; rfl
  have eZC : F + 0x3C + 0xC = F + 0x48 := by rw [BitVec.add_assoc]; rfl
  have eZ18 : F + 0x3C + 0x18 = F + 0x54 := by rw [BitVec.add_assoc]; rfl
  have eD : F + 0xC + BitVec.ofNat 32 pad = F + BitVec.ofNat 32 (0xC + pad) := by
    rw [show (0xC : Word) = BitVec.ofNat 32 0xC from rfl, add_ofNat_assoc]
  -- the array's copied part is apart from the zip's words
  have sDw : ∀ c, 0x3C ≤ c → c + 4 ≤ 0x70 → Sep (F + 0xC + BitVec.ofNat 32 pad) s (F + BitVec.ofNat 32 c) 4 :=
    fun c h1 h2 => by rw [eD]; exact sep_offsets F (.inl (by omega)) (by omega) (by omega)
  have sIS : Sep (F + 0x50) 4 src s := (sSF.subR (c := 0x50) (l := 4) (by decide)).symm
  have sID : Sep (F + 0x50) 4 (F + 0xC + BitVec.ofNat 32 pad) s := (sDw 0x50 (by decide) (by decide)).symm
  have ldZ : ∀ i c, i ≤ s → 0x3C ≤ c → c + 4 ≤ 0x70 → (c + 4 ≤ 0x50 ∨ 0x54 ≤ c) →
      memLoad32 (dsMem Mz F src pad i) (F + BitVec.ofNat 32 c) = memLoad32 Mz (F + BitVec.ofNat 32 c) :=
    fun i c hi h1 h2 h3 => by
      unfold dsMem
      rw [memLoad32_congr fun j hj => copyBytes_sep ((sDw c h1 h2).subR (c := j) (l := 1) (by omega)) hi,
        memLoad32_store32_sep (by
          rw [show (0x50 : Word) = BitVec.ofNat 32 0x50 from rfl]
          rcases h3 with h3 | h3
          · exact sep_offsets F (c := 0x50) (n := 4) (d := c) (k := 4) (.inr (by omega)) (by omega) (by omega)
          · exact sep_offsets F (c := 0x50) (n := 4) (d := c) (k := 4) (.inl (by omega)) (by omega) (by omega))]
  have ldI : ∀ i, i ≤ s → memLoad32 (dsMem Mz F src pad i) (F + 0x50) = BitVec.ofNat 32 i := fun i hi => by
    unfold dsMem
    rw [memLoad32_congr fun j hj => copyBytes_sep (sID.symm.subR (c := j) (l := 1) (by omega)) hi,
      memLoad32_store32_same]
  have codeD : ∀ {b : Word} {code : List Nat} (i : Nat), i ≤ s → CodeIn Mz b code → Sep F 0x70 b code.length →
      CodeIn (dsMem Mz F src pad i) b code := fun i hi hcb hs => by
    unfold dsMem
    exact CodeIn.copyBytes (CodeIn.store32 hcb (hs.sub (c := 0x50) (l := 4) (by decide)))
      ((by rw [eD]; exact hs.sub (c := 0xC + pad) (l := s) (by omega)) : Sep _ s _ _) hi
  intro k
  induction k with
  | zero =>
    intro i hi n st rsp
    have his : i = s := by omega
    subst his
    have hc0 := codeD i (Nat.le_refl _) hc sFC
    have hz0 := codeD i (Nat.le_refl _) hz sFZ
    obtain ⟨n1, d1, u1⟩ := st.aluImm hc0 ds_at_72 (off' := 0x74) (by decide)
    obtain ⟨n2, c2, pc2, mem2, regs2⟩ := u1.self.callRa hc0 ds_at_74 ds_at_78 (cb := P + 0xFFFFFD62)
      (by rw [BitVec.add_assoc, BitVec.add_assoc]; rfl) (even_at P hP 0xFFFFFD62 (by decide))
    have r2 := PEnv.reg1 regs2 u1.self.zero
    have a02 : reg n2 a0 = F + 0x3C := by
      rw [r2 a0 (by decide), u1.regs]; simp +decide only [upd_app, ↓reduceIte]; rw [rsp]; rfl
    obtain ⟨n3, c3, pc3, hif, k3⟩ := zipSkipNext_correct n2 (by rw [mem2]; exact hz0) pc2 a02
      (aligned_add hFa (k := 0x3C) (by decide)) (by rw [eI]; exact sFZ.sub (c := 0x50) (l := 4) (by decide))
      (by rw [regs2]; simp +decide [upd]) (even_clear _ (even_at P hP (0x74 + 8) (by decide)))
    rw [mem2, eI, eZ18, ldI i (Nat.le_refl _), show F + 0x54 = F + BitVec.ofNat 32 0x54 from rfl,
      ldZ i 0x54 (Nat.le_refl _) (by decide) (by decide) (.inr (by decide)), ← show F + 0x54 = F + BitVec.ofNat 32 0x54 from rfl,
      z18, ds_ult (by omega) (by omega), decide_eq_false (Nat.lt_irrefl _)] at hif
    simp only [Bool.false_eq_true, ↓reduceIte] at hif
    obtain ⟨mem3, a03⟩ := hif
    have u3 : St (dsMem Mz F src pad i) P n3 0x7C (reg n3) := ⟨by rw [pc3], mem3, fun _ => rfl⟩
    obtain ⟨n4, d4, u4⟩ := u3.taken hc0 0x88 ds_at_7c (by decide) (by rw [a03, u3.zero]; rfl)
    refine ⟨n4, .cons d1 (c2.trans (c3.trans (.single d4))), u4.self, fun q hq => ?_⟩
    have h : ∀ r : Fin 32, r.val ∈ [1, 10, 11, 12, 13, 14, 15] → q ≠ r := fun r hr e => by subst e; exact hq hr
    rw [u4.regs, k3 q (fun hm => hq (List.mem_cons_of_mem _ hm)), r2 q (h ra (by decide)), u1.regs,
      updz st.zero (h a0 (by decide))]
  | succ k ih =>
    intro i hi n st rsp
    have his : i < s := by omega
    have hc0 := codeD i (by omega) hc sFC
    have hz0 := codeD i (by omega) hz sFZ
    obtain ⟨n1, d1, u1⟩ := st.aluImm hc0 ds_at_72 (off' := 0x74) (by decide)
    obtain ⟨n2, c2, pc2, mem2, regs2⟩ := u1.self.callRa hc0 ds_at_74 ds_at_78 (cb := P + 0xFFFFFD62)
      (by rw [BitVec.add_assoc, BitVec.add_assoc]; rfl) (even_at P hP 0xFFFFFD62 (by decide))
    have r2 := PEnv.reg1 regs2 u1.self.zero
    have a02 : reg n2 a0 = F + 0x3C := by
      rw [r2 a0 (by decide), u1.regs]; simp +decide only [upd_app, ↓reduceIte]; rw [rsp]; rfl
    obtain ⟨n3, c3, pc3, hif, k3⟩ := zipSkipNext_correct n2 (by rw [mem2]; exact hz0) pc2 a02
      (aligned_add hFa (k := 0x3C) (by decide)) (by rw [eI]; exact sFZ.sub (c := 0x50) (l := 4) (by decide))
      (by rw [regs2]; simp +decide [upd]) (even_clear _ (even_at P hP (0x74 + 8) (by decide)))
    have l0 : memLoad32 (dsMem Mz F src pad i) (F + 0x3C) = F + 0xC := by
      rw [show F + 0x3C = F + BitVec.ofNat 32 0x3C from rfl,
        ldZ i 0x3C (by omega) (by decide) (by decide) (.inl (by decide))]; exact z0
    have l8 : memLoad32 (dsMem Mz F src pad i) (F + 0x44) = BitVec.ofNat 32 pad := by
      rw [show F + 0x44 = F + BitVec.ofNat 32 0x44 from rfl,
        ldZ i 0x44 (by omega) (by decide) (by decide) (.inl (by decide))]; exact z8
    have lC : memLoad32 (dsMem Mz F src pad i) (F + 0x48) = src := by
      rw [show F + 0x48 = F + BitVec.ofNat 32 0x48 from rfl,
        ldZ i 0x48 (by omega) (by decide) (by decide) (.inl (by decide))]; exact zC
    have l18 : memLoad32 (dsMem Mz F src pad i) (F + 0x54) = BitVec.ofNat 32 s := by
      rw [show F + 0x54 = F + BitVec.ofNat 32 0x54 from rfl,
        ldZ i 0x54 (by omega) (by decide) (by decide) (.inr (by decide))]; exact z18
    rw [mem2, eI, eZ18, eZ8, eZC, ldI i (by omega), l18, l0, l8, lC, ds_ult (by omega) (by omega),
      decide_eq_true his] at hif
    simp only [↓reduceIte] at hif
    obtain ⟨mem3, a03, a13⟩ := hif
    have hAi : F + 0xC + BitVec.ofNat 32 i + BitVec.ofNat 32 pad = F + 0xC + BitVec.ofNat 32 pad + BitVec.ofNat 32 i := by
      rw [BitVec.add_assoc, BitVec.add_comm (BitVec.ofNat 32 i), ← BitVec.add_assoc]
    have hDi : F + 0xC + BitVec.ofNat 32 pad + BitVec.ofNat 32 i = F + BitVec.ofNat 32 (0xC + pad + i) := by
      rw [show (0xC : Word) = BitVec.ofNat 32 0xC from rfl, add_ofNat_assoc, add_ofNat_assoc, Nat.add_assoc]
    have hne : F + 0xC + BitVec.ofNat 32 pad + BitVec.ofNat 32 i ≠ 0 := fun h => by
      rw [hDi] at h
      have := congrArg BitVec.toNat h
      rw [BitVec.toNat_add, ofNat_tn (by omega), Nat.mod_eq_of_lt (by omega)] at this
      change _ = 0 at this; omega
    have hc3 : CodeIn (memStore32 (dsMem Mz F src pad i) (F + 0x50) (BitVec.ofNat 32 i + 1)) P derScalar48Code :=
      CodeIn.store32 hc0 (sFC.sub (c := 0x50) (l := 4) (by decide))
    have u3 : St (memStore32 (dsMem Mz F src pad i) (F + 0x50) (BitVec.ofNat 32 i + 1)) P n3 0x7C (reg n3) :=
      ⟨by rw [pc3], mem3, fun _ => rfl⟩
    obtain ⟨n4, d4, u4⟩ := u3.notTaken hc3 0x7E ds_at_7c (by decide) (by
      rw [a03, u3.zero, hAi]; exact beq_false_of_ne hne)
    obtain ⟨n5, d5, u5⟩ := u4.self.lbu hc3 ds_at_7e (off' := 0x82) (by decide)
    have hsi : src + BitVec.ofNat 32 i = BitVec.ofNat 32 i + src + 0 := by
      rw [add_lit_zero]; exact BitVec.add_comm _ _
    have sSi : Sep (F + 0x50) 4 (src + BitVec.ofNat 32 i) 1 := sIS.subR (c := i) (l := 1) (by omega)
    have sDsi : Sep (F + 0xC + BitVec.ofNat 32 pad) s (src + BitVec.ofNat 32 i) 1 := by
      rw [eD]; exact ((sSF.subR (c := 0xC + pad) (l := s) (by omega)).symm.subR (c := i) (l := 1) (by omega))
    have vb : (memStore32 (dsMem Mz F src pad i) (F + 0x50) (BitVec.ofNat 32 i + 1)) (BitVec.ofNat 32 i + src + 0) =
        Mz (src + BitVec.ofNat 32 i) := by
      rw [← hsi, memStore32_get_sep sSi]
      unfold dsMem
      rw [copyBytes_sep sDsi (by omega), memStore32_get_sep sSi]
    obtain ⟨n6, d6, u6⟩ := u5.self.sb hc3 ds_at_82 (off' := 0x86) (by decide)
    have hmem : memStore8 (memStore32 (dsMem Mz F src pad i) (F + 0x50) (BitVec.ofNat 32 i + 1))
        (reg n5 a0 + 0) ((reg n5 a1).extractLsb' 0 8) = dsMem Mz F src pad (i + 1) := by
      have e0 : reg n5 a0 = reg n3 a0 := by rw [u5.regs, upd_ne' (by decide) u4.self.zero, u4.regs]
      have e1 : (reg n5 a1).extractLsb' 0 8 = Mz (src + BitVec.ofNat 32 i) := by
        rw [u5.regs]; simp +decide only [upd_app, ↓reduceIte]; rw [u4.regs, a13, vb, tlv_zext]
      rw [e0, e1, a03, add_lit_zero, hAi]
      unfold dsMem
      have eS : memStore32 (copyBytes (memStore32 Mz (F + 0x50) (BitVec.ofNat 32 i)) (F + 0xC + BitVec.ofNat 32 pad)
          src i) (F + 0x50) (BitVec.ofNat 32 i + 1) = copyBytes (memStore32 Mz (F + 0x50) (BitVec.ofNat 32 (i + 1)))
          (F + 0xC + BitVec.ofNat 32 pad) src i := by
        funext x
        rw [cb_store32 (n := s) (by omega) sID sIS]
        unfold copyBytes
        split
        · rw [memStore32_overwrite, ofNat_succ]
        · rw [memStore32_overwrite, ofNat_succ]
      rw [eS, show Mz (src + BitVec.ofNat 32 i) = memStore32 Mz (F + 0x50) (BitVec.ofNat 32 (i + 1)) (src + BitVec.ofNat 32 i)
        from (memStore32_get_sep sSi).symm, copyBytes_succ (by omega)]
    rw [hmem] at u6
    have hc6 := codeD (i + 1) (by omega) hc sFC
    obtain ⟨n7, d7, u7⟩ := u6.jump hc6 ds_at_86 (off' := 0x72) (by decide) (by
      rw [u6.pc, show P + BitVec.ofNat 32 0x86 + 0xFFFFFFEC = P + BitVec.ofNat 32 0x72 by rw [BitVec.add_assoc]; rfl]
      exact even_bit0 (even_at P hP 0x72 (by decide)))
    have k7 : ∀ q, q.val ∉ [1, 10, 11, 12, 13, 14, 15] → reg n7 q = reg n q := fun q hq => by
      have h : ∀ r : Fin 32, r.val ∈ [1, 10, 11, 12, 13, 14, 15] → q ≠ r := fun r hr e => by subst e; exact hq hr
      rw [u7.regs, u5.regs, upd_ne' (h a1 (by decide)) u4.self.zero, u4.regs,
        k3 q (fun hm => hq (List.mem_cons_of_mem _ hm)), r2 q (h ra (by decide)), u1.regs,
        updz st.zero (h a0 (by decide))]
    obtain ⟨n', c', u', k'⟩ := ih (i + 1) (by omega) u7.self (by rw [k7 sp (by decide), rsp])
    exact ⟨n', .cons d1 (c2.trans (c3.trans (.cons d4 (.cons d5 (.cons d6 (.cons d7 c')))))), u',
      fun q hq => by rw [k' q hq, k7 q hq]⟩

end C3.RV32
