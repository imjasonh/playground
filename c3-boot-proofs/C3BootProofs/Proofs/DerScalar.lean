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

theorem memStore32_self (M : Word → BitVec 8) (a : Word) : memStore32 M a (memLoad32 M a) = M := by
  funext x
  unfold memStore32 memStore8
  have b0 := load_byte M a 0 (by decide)
  rw [add_ofNat_zero] at b0
  by_cases h3 : x = a + 3
  · rw [ite_eq_left h3, h3]; exact load_byte M a 3 (by decide)
  rw [ite_eq_right h3]
  by_cases h2 : x = a + 2
  · rw [ite_eq_left h2, h2]; exact load_byte M a 2 (by decide)
  rw [ite_eq_right h2]
  by_cases h1 : x = a + 1
  · rw [ite_eq_left h1, h1]; exact load_byte M a 1 (by decide)
  rw [ite_eq_right h1]
  by_cases h0 : x = a
  · rw [ite_eq_left h0, h0]; exact b0
  rw [ite_eq_right h0]

theorem fillWords_byte0 {M : Word → BitVec 8} {dst : Word} {k j : Nat} (hj : j < 4 * k)
    (hw : dst.toNat + 4 * k ≤ 2 ^ 32) : fillWords M dst 0 k (dst + BitVec.ofNat 32 j) = 0 := by
  have hb := load_byte (fillWords M dst 0 k) (dst + BitVec.ofNat 32 (4 * (j / 4))) (j % 4) (Nat.mod_lt _ (by decide))
  rw [fillWords_load k (j / 4) (by omega) hw, add_ofNat_assoc, show 4 * (j / 4) + j % 4 = j by omega] at hb
  rw [← hb]
  have h4 : j % 4 < 4 := Nat.mod_lt _ (by decide)
  generalize j % 4 = b at h4
  rcases (show b = 0 ∨ b = 1 ∨ b = 2 ∨ b = 3 by omega) with rfl | rfl | rfl | rfl <;> decide

/-- `der::scalar::<N>`'s result for the unread bytes `L` starting at `rp`,
given `Der::element`'s result `r` for tag 2: the error byte, or the `N`-byte
big-endian value of the positive integer's magnitude, left-padded with
zeros. More than `N` magnitude bytes is `OutOfRange`, 5. -/
def derScalarOf (N : Nat) (L : Bytes) (rp : Word) (r : Except DerError DerTlv) : Except (BitVec 8) Bytes :=
  match r, derPosIntOf L rp r with
  | .ok t, .ok _ =>
    if N < (if (t.content L).head? = some 0 then (t.content L).drop 1 else t.content L).length then .error 5
    else .ok (List.replicate (N - (if (t.content L).head? = some 0 then (t.content L).drop 1 else t.content L).length) 0 ++
      (if (t.content L).head? = some 0 then (t.content L).drop 1 else t.content L))
  | _, .error e => .error (derErrByte e)
  | .error e, .ok _ => .error (derErrByte e)

/-- Where `der::scalar::<48>` runs: its code and its callees', the 0xA0
bytes of stack below `sp0`, the 49-byte result at `out`, the reader at `d`,
and the reader's unread bytes, apart from what each must not touch. -/
structure DSEnv (M : Word → BitVec 8) (P sp0 out d : Word) : Prop where
  hP : P.toNat % 2 = 0
  cod : CodeIn M P derScalar48Code
  pint : CodeIn M (P + 0xFFFFFD12) derPositiveIntegerCode
  int : CodeIn M (P + 0xFFFFFD12 + 0x72) derIntegerCode
  elem : CodeIn M (P + 0xFFFFFD12 + 0x72 + 0x5E) derElementCode
  tlv : CodeIn M (P + 0xFFFFFD12 + 0x72 + 0x5E + 0x26) derTlvCode
  zip : CodeIn M (P + 0xFFFFFD62) zipSkipNextCode
  mset : CodeIn M (P + 0xC566) memsetCode
  mcs : CodeIn M (P + 0xC5CE) memcpyStubCode
  mcb : CodeIn M (P + 0xC5D6) memcpyBodyCode
  hsp : sp0.toNat % 4 = 0
  hS : 0xA0 ≤ sp0.toNat
  hd : d.toNat % 4 = 0
  how : out.toNat + 49 < 2 ^ 32
  sGC : Sep (sp0 + 0xFFFFFF60) 0xA0 P derScalar48Code.length
  sGP : Sep (sp0 + 0xFFFFFF60) 0xA0 (P + 0xFFFFFD12) derPositiveIntegerCode.length
  sGI : Sep (sp0 + 0xFFFFFF60) 0xA0 (P + 0xFFFFFD12 + 0x72) derIntegerCode.length
  sGE : Sep (sp0 + 0xFFFFFF60) 0xA0 (P + 0xFFFFFD12 + 0x72 + 0x5E) derElementCode.length
  sGT : Sep (sp0 + 0xFFFFFF60) 0xA0 (P + 0xFFFFFD12 + 0x72 + 0x5E + 0x26) derTlvCode.length
  sGZ : Sep (sp0 + 0xFFFFFF60) 0xA0 (P + 0xFFFFFD62) zipSkipNextCode.length
  sGM : Sep (sp0 + 0xFFFFFF60) 0xA0 (P + 0xC566) memsetCode.length
  sGS : Sep (sp0 + 0xFFFFFF60) 0xA0 (P + 0xC5CE) memcpyStubCode.length
  sGB : Sep (sp0 + 0xFFFFFF60) 0xA0 (P + 0xC5D6) memcpyBodyCode.length
  sOC : Sep out 49 P derScalar48Code.length
  sOB : Sep out 49 (P + 0xC5D6) memcpyBodyCode.length
  sOG : Sep out 49 (sp0 + 0xFFFFFF60) 0xA0
  sDS : Sep (d + 8) 8 P derScalar48Code.length
  sDZ : Sep (d + 8) 8 (P + 0xFFFFFD62) zipSkipNextCode.length
  sDM : Sep (d + 8) 8 (P + 0xC566) memsetCode.length
  sDU : Sep (d + 8) 8 (P + 0xC5CE) memcpyStubCode.length
  sDB : Sep (d + 8) 8 (P + 0xC5D6) memcpyBodyCode.length
  sDC : Sep (d + 8) 8 (P + 0xFFFFFD12) derPositiveIntegerCode.length
  sDI : Sep (d + 8) 8 (P + 0xFFFFFD12 + 0x72) derIntegerCode.length
  sDT : Sep (d + 8) 8 (P + 0xFFFFFD12 + 0x72 + 0x5E + 0x26) derTlvCode.length
  sDG : Sep (d + 8) 8 (sp0 + 0xFFFFFF60) 0xA0
  sRG : Sep (memLoad32 M (d + 8)) (memLoad32 M (d + 0xC)).toNat (sp0 + 0xFFFFFF60) 0xA0
  sDR : Sep (d + 8) 8 (memLoad32 M (d + 8)) (memLoad32 M (d + 0xC)).toNat
  hrp : 0 < (memLoad32 M (d + 8)).toNat
  hrw : (memLoad32 M (d + 8)).toNat + (memLoad32 M (d + 0xC)).toNat < 2 ^ 32

theorem ds_sltu1 : ∀ b : BitVec 8,
    aluEval .sltu (b.zeroExtend 32) 1 = BitVec.ofNat 32 (if b.toNat = 0 then 1 else 0) := by decide

theorem ds_bgeu {k : Nat} (hk : k < 2 ^ 32) :
    branchTaken .bgeu (BitVec.ofNat 32 k) (aluEval .add 0 0x31) = decide (49 ≤ k) := by
  show (!(BitVec.ofNat 32 k).ult 0x31) = _
  simp only [BitVec.ult, BitVec.toNat_ofNat, Nat.mod_eq_of_lt hk, show (0x31 : Word).toNat = 49 from rfl]
  by_cases h : 49 ≤ k
  · rw [decide_eq_true h, decide_eq_false (by omega)]; rfl
  · rw [decide_eq_false h, decide_eq_true (by omega)]; rfl

abbrev dsPs : List (Fin 32 × Word) :=
  [(ra, 0x6C), ((8 : Fin 32), 0x68), ((9 : Fin 32), 0x64), ((18 : Fin 32), 0x60), ((19 : Fin 32), 0x5C),
   ((20 : Fin 32), 0x58)]

section
set_option maxRecDepth 20000
theorem dsSave_end : blockEnd derScalar48Code 2 (saveBlock dsPs) = some 0xE := by decide
theorem dsRestore_end : blockEnd derScalar48Code 0xAC (restoreBlock dsPs) = some 0xB8 := by decide
end

set_option maxRecDepth 20000 in
set_option maxHeartbeats 32000000 in
/-- **The compiled `der::scalar::<48>`**: with the reader at `d`, whose
unread bytes start at `rp` and number `rl`, it stores `derScalarOf 48` of
those bytes in its `Result<[u8; 48], Error>` at `out`: a zero tag and the 48
bytes, or a tag of 1 and the error byte. It moves the reader past the
element when `Der::element` reads one. -/
theorem derScalar48_correct (m : Machine) {P sp0 out d retAddr : Word} (env : DSEnv m.mem P sp0 out d)
    (hpc : m.pc = P) (hsp : reg m sp = sp0) (ha0 : reg m a0 = out) (ha1 : reg m a1 = d)
    (hra : reg m ra = retAddr) (hret : retAddr &&& ~~~1 = retAddr) :
    ∃ m', Steps m m' ∧ m'.pc = retAddr ∧ reg m' sp = sp0 ∧
      (∀ q, q.val ∈ [1, 3, 4, 8, 9, 18, 19, 20, 21, 22, 23, 24, 25, 26, 27] → reg m' q = reg m q) ∧
      match derScalarOf 48 (memBytes m.mem (memLoad32 m.mem (d + 8)) (memLoad32 m.mem (d + 0xC)).toNat)
          (memLoad32 m.mem (d + 8))
          (derElement 2 (memBytes m.mem (memLoad32 m.mem (d + 8)) (memLoad32 m.mem (d + 0xC)).toNat)) with
      | .ok bs => m'.mem out = 0 ∧
          (∀ j, j < 48 → m'.mem (out + BitVec.ofNat 32 (1 + j)) = BitVec.ofNat 8 (bs.getD j 0)) ∧
          ∀ x, Sep (sp0 + 0xFFFFFF60) 0xA0 x 1 → Sep out 49 x 1 →
            m'.mem x = derAdvance m.mem d (memLoad32 m.mem (d + 8)) (memLoad32 m.mem (d + 0xC))
              (derElement 2 (memBytes m.mem (memLoad32 m.mem (d + 8)) (memLoad32 m.mem (d + 0xC)).toNat)) x
      | .error b => m'.mem out = 1 ∧ m'.mem (out + 1) = b ∧
          ∀ x, Sep (sp0 + 0xFFFFFF60) 0xA0 x 1 → Sep out 2 x 1 →
            m'.mem x = derAdvance m.mem d (memLoad32 m.mem (d + 8)) (memLoad32 m.mem (d + 0xC))
              (derElement 2 (memBytes m.mem (memLoad32 m.mem (d + 8)) (memLoad32 m.mem (d + 0xC)).toNat)) x := by
  have hrp0 := env.hrp; have hrw := env.hrw; have sRG := env.sRG; have sDR := env.sDR
  generalize hRP : memLoad32 m.mem (d + 8) = rp at hrp0 hrw sRG sDR ⊢
  generalize hRL : memLoad32 m.mem (d + 0xC) = rl at hrw sRG sDR ⊢
  obtain ⟨G, hG⟩ : ∃ G, sp0 + 0xFFFFFF60 = G := ⟨_, rfl⟩
  obtain ⟨F, hF⟩ : ∃ F, sp0 + 0xFFFFFF90 = F := ⟨_, rfl⟩
  have sGC := env.sGC; have sGP := env.sGP; have sGI := env.sGI; have sGE := env.sGE; have sGT := env.sGT
  have sGZ := env.sGZ; have sGM := env.sGM; have sGS := env.sGS; have sGB := env.sGB; have sOG := env.sOG
  have sDG := env.sDG
  rw [hG] at sGC sGP sGI sGE sGT sGZ sGM sGS sGB sOG sDG sRG ⊢
  have hGF : G + 0x30 = F := by rw [← hG, ← hF, BitVec.add_assoc]; rfl
  have hGa : G.toNat % 4 = 0 := by rw [← hG]; exact aligned_add env.hsp (k := 0xFFFFFF60) (by decide)
  have hFa : F.toNat % 4 = 0 := by rw [← hGF]; exact aligned_add hGa (k := 0x30) (by decide)
  have hGw : G.toNat + 0xA0 = sp0.toNat := by
    rw [← hG, BitVec.toNat_add, show (0xFFFFFF60 : Word).toNat = 4294967136 from rfl]
    have := sp0.isLt; have := env.hS; omega
  have hFn : F.toNat = G.toNat + 0x30 := by
    rw [← hGF, BitVec.toNat_add, show (0x30 : Word).toNat = 0x30 from rfl]; omega
  have eS : F + 0x70 = sp0 := by rw [← hF, BitVec.add_assoc]; exact BitVec.add_zero sp0
  have eFk : ∀ k, F + BitVec.ofNat 32 k = G + BitVec.ofNat 32 (0x30 + k) := fun k => by
    rw [← hGF, show (0x30 : Word) = BitVec.ofNat 32 0x30 from rfl, add_ofNat_assoc]
  have inF : ∀ {b : Word} {l : Nat}, Sep G 0xA0 b l → Sep F 0x70 b l := fun h => by
    rw [← hGF]; exact h.sub (c := 0x30) (l := 0x70) (by decide)
  have inP : ∀ {b : Word} {l : Nat}, Sep G 0xA0 b l → Sep G 0x30 b l := fun h =>
    (h.sub (c := 0) (l := 0x30) (by decide)) |> fun h' => by rwa [add_ofNat_zero] at h'
  have cIn : ∀ {M' : Word → BitVec 8} {b : Word} {code' : List Nat}, CodeIn m.mem b code' →
      Sep G 0xA0 b code'.length → (∀ x, Sep G 0xA0 x 1 → M' x = m.mem x) → CodeIn M' b code' :=
    fun hc hs hM i hi => by rw [hM _ (hs.subR (c := i) (l := 1) (by omega))]; exact hc i hi
  have s0 : St m.mem P m 0 (reg m) := ⟨by rw [hpc]; simp, rfl, fun _ => rfl⟩
  have hz := s0.zero
  obtain ⟨m1, d1, u1⟩ := s0.aluImm env.cod ds_at_0 (off' := 2) (by decide)
  have sp1 : upd (reg m) sp (aluEval .add (reg m sp) 0xFFFFFF90) sp = F := by
    simp +decide only [upd_app, ↓reduceIte]; rw [ev_add, hsp, hF]
  obtain ⟨m2, c2, u2⟩ := St.block (saveBlock dsPs) u1 env.cod dsSave_end (saveBlock_ok _ dsPs _ fun p hp => by
    rw [sp1]
    simp only [dsPs, List.mem_cons, List.mem_nil_iff, or_false] at hp
    rcases hp with rfl | rfl | rfl | rfl | rfl | rfl <;>
      exact ⟨aligned_add hFa (by decide), (inF sGC).sub (by decide)⟩)
  simp only [saveBlock_run] at u2
  rw [sp1] at u2
  obtain ⟨Msv, hMsv⟩ : ∃ Msv, saveMem m.mem F (upd (reg m) sp (aluEval .add (reg m sp) 0xFFFFFF90)) dsPs = Msv :=
    ⟨_, rfl⟩
  rw [hMsv] at u2
  have frSv : ∀ x, Sep G 0xA0 x 1 → Msv x = m.mem x := fun x hx => by
    rw [← hMsv]
    exact saveMem_outside dsPs fun p hp => by
      simp only [dsPs, List.mem_cons, List.mem_nil_iff, or_false] at hp
      rcases hp with rfl | rfl | rfl | rfl | rfl | rfl <;> exact (inF hx).sub (by decide)
  -- the bytes below the slots keep their entry values
  have frLo : ∀ k, k < 0x58 → Msv (F + BitVec.ofNat 32 k) = m.mem (F + BitVec.ofNat 32 k) := fun k hk => by
    rw [← hMsv]
    exact saveMem_outside dsPs fun p hp => by
      simp only [dsPs, List.mem_cons, List.mem_nil_iff, or_false] at hp
      rcases hp with rfl | rfl | rfl | rfl | rfl | rfl <;>
        exact sep_offsets F (.inr (by simp; omega)) (by simp) (by omega)
  have hslv : ∀ r o, (r, o) ∈ dsPs → memLoad32 Msv (F + o) = reg m r := fun r o h => by
    rw [← hMsv]
    simp only [dsPs, List.mem_cons, List.mem_nil_iff, or_false, Prod.mk.injEq] at h
    rcases h with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ <;>
    · simp only [saveMem]
      simp (disch := decide) only [ls_lit, ls_same]
      simp +decide only [upd_app, ↓reduceIte]
  have r2 : ∀ q, q ≠ sp → reg m2 q = reg m q := fun q h => by rw [u2.regs, updz hz h]
  have sp2 : reg m2 sp = F := by rw [u2.regs]; exact sp1
  have hcS : CodeIn Msv P derScalar48Code := cIn env.cod sGC frSv
  obtain ⟨m3, c3, u3⟩ := St.block [.alu .add (18 : Fin 32) x0 a0, .aluImm .add a0 sp 0xC] u2.self hcS (off' := 0x12)
    (by decide) (by simp [BlockOk, BInstr.ok])
  simp only [runBlock, BInstr.run] at u3
  obtain ⟨m4, c4, pc4, mem4, regs4⟩ := u3.callRa hcS ds_at_12 ds_at_16 (cb := P + 0xFFFFFD12)
    (by rw [BitVec.add_assoc, BitVec.add_assoc]; rfl) (even_at P env.hP 0xFFFFFD12 (by decide))
  have r4 := PEnv.reg1 regs4 u3.zero
  have hz18 : upd (reg m2) 18 (aluEval .add (reg m2 x0) (reg m2 a0)) 0 = 0 :=
    (updz (r := 0) u2.self.zero (by decide)).trans u2.self.zero
  have v4 : ∀ q, q ≠ ra → q ≠ a0 → q ≠ 18 → q ≠ sp → reg m4 q = reg m q := fun q hr h0 h8 hs => by
    rw [r4 q hr, updz hz18 h0, updz u2.self.zero h8, r2 q hs]
  have v4a0 : reg m4 a0 = F + 0xC := by
    rw [r4 a0 (by decide)]; simp +decide only [upd_app, ↓reduceIte]; rw [sp2]; rfl
  have v418 : reg m4 18 = out := by
    rw [r4 18 (by decide), updz hz18 (by decide)]
    simp +decide only [upd_app, ↓reduceIte]; rw [r2 a0 (by decide), ha0]; exact zw out
  have v4sp : reg m4 sp = F := by
    rw [r4 sp (by decide), updz hz18 (by decide), updz u2.self.zero (by decide), sp2]
  have v4a1 : reg m4 a1 = d := by rw [v4 a1 (by decide) (by decide) (by decide) (by decide), ha1]
  have eD8 : memLoad32 Msv (d + 8) = rp := by
    rw [← hRP]; exact memLoad32_congr fun j hj => frSv _ (sDG.symm.subR (c := j) (l := 1) (by omega) |>.symm |>
      fun h => h.symm)
  have eDC : memLoad32 Msv (d + 0xC) = rl := by
    rw [← hRL]; exact memLoad32_congr fun j hj => frSv _ (by
      rw [show d + 0xC = d + 8 + BitVec.ofNat 32 4 by rw [BitVec.add_assoc]; rfl, add_ofNat_assoc]
      exact sDG.symm.subR (by omega) |>.symm |> fun h => h.symm)
  have eL : memBytes Msv rp rl.toNat = memBytes m.mem rp rl.toNat :=
    memBytes_congr fun i hi => frSv _ (sRG.symm.subR (c := i) (l := 1) (by omega) |>.symm |> fun h => h.symm)
  have eFG : F + 0xFFFFFFD0 = G := by rw [← hGF, BitVec.add_assoc]; exact BitVec.add_zero G
  have eA : F + 0xC = G + BitVec.ofNat 32 0x3C := by rw [show (0xC : Word) = BitVec.ofNat 32 0xC from rfl, eFk]
  have sAP : ∀ {b : Word} {l : Nat}, Sep G 0xA0 b l → Sep (F + 0xC) 8 b l := fun h => by
    rw [eA]; exact h.sub (c := 0x3C) (l := 8) (by decide)
  have hPI : PIEnv m4.mem (P + 0xFFFFFD12) F (F + 0xC) d := by
    rw [mem4]
    refine ⟨even_at P env.hP 0xFFFFFD12 (by decide), cIn env.pint sGP frSv, cIn env.int sGI frSv,
      cIn env.elem sGE frSv, cIn env.tlv sGT frSv, hFa, by omega, aligned_add hFa (k := 0xC) (by decide), env.hd,
      ?_, ?_, ?_, ?_, sAP sGP, env.sDC, env.sDI, env.sDT, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
    · rw [eFG]; exact inP sGP
    · rw [eFG]; exact inP sGI
    · rw [eFG]; exact inP sGE
    · rw [eFG]; exact inP sGT
    · rw [eFG, eA]
      have := sep_offsets G (c := 0x3C) (n := 8) (d := 0) (k := 0x30) (.inr (by decide)) (by omega) (by omega)
      rwa [add_ofNat_zero] at this
    · rw [eFG]; exact (sDG.subR (c := 0) (l := 0x30) (by decide)) |> fun h => by rwa [add_ofNat_zero] at h
    · rw [eFG, eD8, eDC]; exact (sRG.subR (c := 0) (l := 0x30) (by decide)) |> fun h => by rwa [add_ofNat_zero] at h
    · rw [eD8, eDC]; exact sDR
    · rw [eD8, eDC]; exact (sAP sRG.symm).symm.symm |> fun h => h.symm.symm |> fun h' => (sAP sRG.symm)
    · exact (sAP sDG.symm)
    · rw [eD8]; exact hrp0
    · rw [eD8, eDC]; exact hrw
  obtain ⟨m5, c5, pc5, sp5, k5, f5⟩ := derPositiveInteger_correct m4 hPI pc4 v4sp v4a0 v4a1
    (by rw [regs4]; simp +decide [upd]) (even_clear _ (even_at P env.hP (0x12 + 8) (by decide)))
  rw [mem4, eD8, eDC, eL, eFG] at f5
  generalize hr : derElement 2 (memBytes m.mem rp rl.toNat) = r at f5 ⊢
  generalize hR : derPosIntOf (memBytes m.mem rp rl.toNat) rp r = R at f5
  have memI : ∀ x, Sep G 0xA0 x 1 → m5.mem x = derAdvance m.mem d rp rl r x := fun x hx => by
    have h8 : Sep (F + 0xC) 8 x 1 := sAP hx
    rw [f5 x (inP hx), slice_out R h8]
    exact derAdvance_pt r (frSv x hx)
  -- the frame above `Der::positive_integer`'s result is as the prologue left it
  have frU : ∀ k, 0x14 ≤ k → k < 0x70 → m5.mem (F + BitVec.ofNat 32 k) = Msv (F + BitVec.ofNat 32 k) := fun k h1 h2 => by
    have hp : Sep G 0x30 (F + BitVec.ofNat 32 k) 1 := by
      rw [eFk]
      have := sep_offsets G (c := 0) (n := 0x30) (d := 0x30 + k) (k := 1) (.inl (by omega)) (by omega) (by omega)
      rwa [add_ofNat_zero] at this
    have h8 : Sep (F + 0xC) 8 (F + BitVec.ofNat 32 k) 1 := by
      rw [show (0xC : Word) = BitVec.ofNat 32 0xC from rfl]
      exact sep_offsets F (.inl (by omega)) (by omega) (by omega)
    have hd8 : Sep (d + 8) 8 (F + BitVec.ofNat 32 k) 1 := by rw [eFk]; exact sDG.subR (by omega)
    rw [f5 _ hp, slice_out R h8, derAdvance_outside r hd8]
  have ldA : ∀ o, o + 4 ≤ 8 → memLoad32 m5.mem (F + 0xC + BitVec.ofNat 32 o) =
      memLoad32 (derSliceMem (derAdvance Msv d rp rl r) (F + 0xC) R) (F + 0xC + BitVec.ofNat 32 o) := fun o ho =>
    memLoad32_congr fun j hj => by
      rw [show F + 0xC + BitVec.ofNat 32 o + BitVec.ofNat 32 j = G + BitVec.ofNat 32 (0x3C + (o + j)) by
        rw [add_ofNat_assoc, eA, add_ofNat_assoc]]
      exact f5 _ (by
        have := sep_offsets G (c := 0) (n := 0x30) (d := 0x3C + (o + j)) (k := 1) (.inl (by omega)) (by omega) (by omega)
        rwa [add_ofNat_zero] at this)
  have cIn5 : ∀ {b : Word} {code' : List Nat}, CodeIn m.mem b code' → Sep G 0xA0 b code'.length →
      Sep (d + 8) 8 b code'.length → CodeIn m5.mem b code' := fun hcb hs hd i hi => by
    rw [memI _ (hs.subR (c := i) (l := 1) (by omega)), derAdvance_outside r (hd.subR (c := i) (l := 1) (by omega))]
    exact hcb i hi
  have hc5 := cIn5 env.cod sGC env.sDS
  have u5 : St m5.mem P m5 0x1A (reg m5) := ⟨by rw [pc5], rfl, fun _ => rfl⟩
  have S5 : Steps m m5 := .cons d1 (c2.trans (c3.trans (c4.trans c5)))
  have K5 : ∀ q, q.val ∈ [3, 4, 9, 19, 20, 21, 22, 23, 24, 25, 26, 27] → reg m5 q = reg m q := fun q hq => by
    have ho : oidKeep q = true := by revert hq; revert q; decide
    have h : q ≠ ra ∧ q ≠ a0 ∧ q ≠ 18 ∧ q ≠ sp := by revert hq; revert q; decide
    rw [k5 q ho, v4 q h.1 h.2.1 h.2.2.1 h.2.2.2]
  have s185 : reg m5 18 = out := by rw [k5 18 (by decide), v418]
  have sp5' : reg m5 sp = F := sp5
  have hpsp : ∀ p ∈ dsPs, p.1 ≠ sp := by decide
  -- the epilogue, from 0xAC
  have fin : ∀ {Mx : Word → BitVec 8} {n : Machine}, Steps m5 n → St Mx P n 0xAC (reg n) →
      CodeIn Mx P derScalar48Code →
      (∀ k, 0x58 ≤ k → k < 0x70 → Mx (F + BitVec.ofNat 32 k) = m5.mem (F + BitVec.ofNat 32 k)) → reg n sp = F →
      (∀ q, q.val ∈ [3, 4, 21, 22, 23, 24, 25, 26, 27] → reg n q = reg m q) →
      ∃ n', Steps m n' ∧ n'.pc = retAddr ∧ n'.mem = Mx ∧ reg n' sp = sp0 ∧
        ∀ q, q.val ∈ [1, 3, 4, 8, 9, 18, 19, 20, 21, 22, 23, 24, 25, 26, 27] → reg n' q = reg m q := by
    intro Mx n S st hc hsl rsp kq
    have slotW : ∀ r o, (r, o) ∈ dsPs → memLoad32 Mx (F + o) = reg m r := fun r o h => by
      have ho : 0x58 ≤ o.toNat ∧ o.toNat + 4 ≤ 0x70 := by
        simp only [dsPs, List.mem_cons, List.mem_nil_iff, or_false, Prod.mk.injEq] at h
        rcases h with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ <;> decide
      rw [← hslv r o h]
      apply memLoad32_congr; intro j hj
      rw [← ofNat_toNat_self o, add_ofNat_assoc, hsl _ (by omega) (by omega), frU _ (by omega) (by omega)]
    obtain ⟨n1, c1, u1⟩ := St.block (restoreBlock dsPs) st hc dsRestore_end
      (restoreBlock_ok Mx F dsPs (reg n) rsp hpsp fun q hq => by
        simp only [dsPs, List.mem_cons, List.mem_nil_iff, or_false] at hq
        rcases hq with rfl | rfl | rfl | rfl | rfl | rfl <;> exact aligned_add hFa (by decide))
    simp only [restoreBlock_run Mx F dsPs (reg n) rsp hpsp] at u1
    obtain ⟨n2, d2, u2⟩ := u1.aluImm hc ds_at_b8 (off' := 0xBA) (by decide)
    obtain ⟨n3, d3, pc3, mem3, regs3⟩ := u2.jalr hc ds_at_ba
    have rsp1 : restoreRegs Mx F (reg n) dsPs sp = F := by rw [restoreRegs_sp _ _ _ _ hpsp]; exact rsp
    have rr : ∀ (f : Fin 32 → Word) (ps : List (Fin 32 × Word)) (q : Fin 32), q.val ≠ 0 → (∀ p ∈ ps, p.1 ≠ q) →
        restoreRegs Mx F f ps q = f q := by
      intro f ps q h0
      induction ps generalizing f with
      | nil => intro _; rfl
      | cons p ps ih =>
        intro h
        simp only [restoreRegs]
        rw [ih _ (fun p' hp' => h p' (List.mem_cons_of_mem _ hp')), upd_ne h0 (fun e => h p List.mem_cons_self e.symm)]
    have hreg : ∀ r o, (r, o) ∈ dsPs → restoreRegs Mx F (reg n) dsPs r = reg m r := fun r o hm => by
      simp only [dsPs, List.mem_cons, List.mem_nil_iff, or_false, Prod.mk.injEq] at hm
      rcases hm with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ <;>
      · simp only [restoreRegs]; simp +decide only [upd_app, ↓reduceIte]
        exact slotW _ _ (by decide)
    refine ⟨n3, S5.trans (S.trans (c1.trans (.cons d2 (.single d3)))), ?_, mem3, ?_, fun q hq => ?_⟩
    · rw [pc3]; simp +decide only [upd_app, ↓reduceIte]; rw [hreg ra 0x6C (by decide), hra, add_lit_zero, hret]
    · rw [regs3]; simp +decide only [upd_app, ↓reduceIte]; rw [ev_add, rsp1, eS]
    · rw [regs3]
      have key : ∀ q : Fin 32, q.val ∈ [1, 3, 4, 8, 9, 18, 19, 20, 21, 22, 23, 24, 25, 26, 27] →
          q = ra ∨ q = (8 : Fin 32) ∨ q = (9 : Fin 32) ∨ q = (18 : Fin 32) ∨ q = (19 : Fin 32) ∨
          q = (20 : Fin 32) ∨ (q.val ∈ [3, 4, 21, 22, 23, 24, 25, 26, 27] ∧ q.val ≠ 0 ∧ q ≠ sp ∧
            (∀ p ∈ dsPs, p.1 ≠ q)) := by decide
      rcases key q hq with rfl | rfl | rfl | rfl | rfl | rfl | ⟨h1, h0, hs, hps⟩
      · simp +decide only [upd_app, ↓reduceIte]; exact hreg _ 0x6C (by decide)
      · simp +decide only [upd_app, ↓reduceIte]; exact hreg _ 0x68 (by decide)
      · simp +decide only [upd_app, ↓reduceIte]; exact hreg _ 0x64 (by decide)
      · simp +decide only [upd_app, ↓reduceIte]; exact hreg _ 0x60 (by decide)
      · simp +decide only [upd_app, ↓reduceIte]; exact hreg _ 0x5C (by decide)
      · simp +decide only [upd_app, ↓reduceIte]; exact hreg _ 0x58 (by decide)
      · rw [upd_ne h0 hs, rr _ _ q h0 hps]; exact kq q h1
  have outF : ∀ k, k < 0x70 → Sep out 49 (F + BitVec.ofNat 32 k) 1 := fun k hk => by rw [eFk]; exact sOG.subR (by omega)
  have ho1 : (out + 1).toNat = out.toNat + 1 := by
    rw [BitVec.toNat_add, show (1 : Word).toNat = 1 from rfl]; have := env.how; omega
  have hne1 : out ≠ out + 1 := fun h => by have := congrArg BitVec.toNat h; rw [ho1] at this; omega
  -- the error tail, from 0xA2
  have errT : ∀ {n : Machine} {b : BitVec 8}, Steps m5 n → St m5.mem P n 0xA2 (reg n) →
      (reg n a0).extractLsb' 0 8 = b → reg n 18 = out → reg n sp = F →
      (∀ q, q.val ∈ [3, 4, 21, 22, 23, 24, 25, 26, 27] → reg n q = reg m q) →
      ∃ n', Steps m n' ∧ n'.pc = retAddr ∧ reg n' sp = sp0 ∧
        (∀ q, q.val ∈ [1, 3, 4, 8, 9, 18, 19, 20, 21, 22, 23, 24, 25, 26, 27] → reg n' q = reg m q) ∧
        n'.mem out = 1 ∧ n'.mem (out + 1) = b ∧
        ∀ x, Sep G 0xA0 x 1 → Sep out 2 x 1 → n'.mem x = derAdvance m.mem d rp rl r x := by
    intro n b S st hb r18 rsp kq
    obtain ⟨n1, d1, u1⟩ := st.aluImm hc5 ds_at_a2 (off' := 0xA4) (by decide)
    have k1 : ∀ q, q ≠ a1 → reg n1 q = reg n q := fun q h => by rw [u1.regs, upd_ne' h st.zero]
    have v1 : reg n1 a1 = 1 := by rw [u1.regs]; simp +decide only [upd_app, ↓reduceIte]; rw [st.zero]; rfl
    obtain ⟨n2, d2, u2⟩ := u1.self.sb hc5 ds_at_a4 (off' := 0xA8) (by decide)
    rw [k1 18 (by decide), r18, v1, add_lit_zero] at u2
    have hc2 := CodeIn.store8 (v := (1 : Word).extractLsb' 0 8) hc5
      (env.sOC.sub (c := 0) (l := 1) (by decide) |> fun h => by rwa [add_ofNat_zero] at h)
    obtain ⟨n3, d3, u3⟩ := u2.sb hc2 ds_at_a8 (off' := 0xAC) (by decide)
    rw [k1 18 (by decide), k1 a0 (by decide), r18, hb] at u3
    have hc3 := CodeIn.store8 (v := b) hc2 (env.sOC.sub (c := 1) (l := 1) (by decide))
    obtain ⟨n', S', pc', mem', sp', k'⟩ := fin (S.trans (.cons d1 (.cons d2 (.single d3)))) u3.self hc3
      (fun k h1 h2 => by
        rw [memStore8_ne fun e' => outF k (by omega) 1 (by decide) 0 (by decide) (by rw [add_ofNat_zero]; exact e'.symm),
          memStore8_ne fun e' => outF k (by omega) 0 (by decide) 0 (by decide)
            (by rw [add_ofNat_zero, add_ofNat_zero]; exact e'.symm)])
      (by rw [u3.regs, k1 sp (by decide), rsp]) (fun q hq => by
        rw [u3.regs, k1 q (fun e => by subst e; revert hq; decide)]; exact kq q hq)
    refine ⟨n', S', pc', sp', k', ?_, ?_, fun x hx ho => ?_⟩
    · rw [mem', memStore8_ne hne1, memStore8_same]; rfl
    · rw [mem', memStore8_same]
    · rw [mem', memStore8_ne fun e' => ho.point (i := 1) (j := 0) (by decide) (by decide) (by rw [add_ofNat_zero]; exact e'.symm),
        memStore8_ne fun e' => ho.point (i := 0) (j := 0) (by decide) (by decide)
          (by rw [add_ofNat_zero, add_ofNat_zero]; exact e'.symm), memI x hx]
  obtain ⟨n6, d6, u6⟩ := u5.lw hc5 ds_at_1a (off' := 0x1C) (by decide) (by
    rw [sp5']; exact aligned_add hFa (k := 0xC) (by decide))
  have v6 : reg n6 9 = memLoad32 (derSliceMem (derAdvance Msv d rp rl r) (F + 0xC) R) (F + 0xC) := by
    rw [u6.regs]; simp +decide only [upd_app, ↓reduceIte]
    have h0 := ldA 0 (by decide); rw [add_ofNat_zero] at h0
    rw [sp5', h0]
  have r6 : ∀ q, q ≠ 9 → reg n6 q = reg m5 q := fun q h => by rw [u6.regs, upd_ne' h u5.zero]
  cases R with
  | error e =>
    obtain ⟨n7, d7, u7⟩ := u6.self.taken hc5 0x3A ds_at_1c (by decide) (by rw [v6, slice_ld0, u6.self.zero]; rfl)
    obtain ⟨n8, d8, u8⟩ := u7.self.lbu hc5 ds_at_3a (off' := 0x3E) (by decide)
    have v8 : reg n8 a0 = (derErrByte e).zeroExtend 32 := by
      rw [u8.regs]; simp +decide only [upd_app, ↓reduceIte]
      rw [u7.regs, r6 sp (by decide), sp5', show F + 0x10 = F + 0xC + BitVec.ofNat 32 4 by rw [BitVec.add_assoc]; rfl,
        show F + 0xC + BitVec.ofNat 32 4 = G + BitVec.ofNat 32 0x40 by rw [eA, add_ofNat_assoc],
        f5 _ (by
          have := sep_offsets G (c := 0) (n := 0x30) (d := 0x40) (k := 1) (.inl (by omega)) (by omega) (by omega)
          rwa [add_ofNat_zero] at this),
        show G + BitVec.ofNat 32 0x40 = F + 0xC + 4 by rw [eA, BitVec.add_assoc]; rfl, slice_b4]
    obtain ⟨n9, d9, u9⟩ := u8.self.jump hc5 ds_at_3e (off' := 0xA2) (by decide) (by
      rw [u8.self.pc, show P + BitVec.ofNat 32 0x3E + 0x64 = P + BitVec.ofNat 32 0xA2 by rw [BitVec.add_assoc]; rfl]
      exact even_bit0 (even_at P env.hP 0xA2 (by decide)))
    have k9 : ∀ q, q ≠ a0 → q ≠ 9 → reg n9 q = reg m5 q := fun q h0 h9 => by
      rw [u9.regs, u8.regs, upd_ne' h0 u7.self.zero, u7.regs, r6 q h9]
    obtain ⟨n', S', pc', sp', k', o0, o1, fr'⟩ := errT (.cons d6 (.cons d7 (.cons d8 (.single d9)))) u9.self
      (by rw [u9.regs, v8, tlv_zext]) (by rw [k9 18 (by decide) (by decide), s185])
      (by rw [k9 sp (by decide) (by decide), sp5'])
      (fun q hq => by
        rw [k9 q (fun e => by subst e; revert hq; decide) (fun e => by subst e; revert hq; decide)]
        exact K5 q (by revert hq; revert q; decide))
    have hspec : derScalarOf 48 (memBytes m.mem rp rl.toNat) rp r = .error (derErrByte e) := by
      cases r <;> simp only [derScalarOf, hR]
    refine ⟨n', S', pc', sp', k', ?_⟩
    rw [hspec]; exact ⟨o0, o1, fr'⟩
  | ok pl =>
    obtain ⟨p, l⟩ := pl
    cases r with
    | error e => exact absurd hR (by simp only [derPosIntOf, derIntOf]; intro h; cases h)
    | ok t =>
    have hR0 := hR
    have hb : t.header + t.len ≤ rl.toNat := by have := derElement_bound hr; rwa [memBytes_length] at this
    cases hI : derIntOf (memBytes m.mem rp rl.toNat) rp (.ok t) with
    | error e => simp only [derPosIntOf, hI] at hR; cases hR
    | ok pl' =>
    simp only [derPosIntOf, hI] at hR
    by_cases hcond : (t.len = 1 ∧ (memBytes m.mem rp rl.toNat).getD t.header 0 = 0) ∨
        0x80 ≤ (memBytes m.mem rp rl.toNat).getD t.header 0
    · rw [ite_eq_left hcond] at hR; cases hR
    rw [ite_eq_right hcond] at hR
    simp only [Except.ok.injEq] at hR
    subst hR
    have hI0 := hI
    simp only [derIntOf] at hI
    by_cases h0 : t.len = 0
    · rw [ite_eq_left h0] at hI; cases hI
    rw [ite_eq_right h0] at hI
    by_cases hm : 2 ≤ t.len ∧ (((memBytes m.mem rp rl.toNat).getD t.header 0 = 0 ∧
        (memBytes m.mem rp rl.toNat).getD (t.header + 1) 0 < 0x80) ∨ ((memBytes m.mem rp rl.toNat).getD t.header 0 = 0xFF ∧
        0x80 ≤ (memBytes m.mem rp rl.toNat).getD (t.header + 1) 0))
    · rw [ite_eq_left hm] at hI; cases hI
    rw [ite_eq_right hm] at hI
    clear hm
    simp only [Except.ok.injEq, Prod.mk.injEq] at hI
    obtain ⟨rfl, rfl⟩ := hI
    have hcp : (rp + BitVec.ofNat 32 t.header).toNat = rp.toNat + t.header := by
      rw [BitVec.toNat_add, ofNat_tn (by omega)]; exact Nat.mod_eq_of_lt (by omega)
    have hp0 : rp + BitVec.ofNat 32 t.header ≠ 0 := fun h => by
      have := congrArg BitVec.toNat h; rw [hcp] at this; change _ = 0 at this; omega
    have hl0 : BitVec.ofNat 32 t.len ≠ 0 := fun h => by
      have := congrArg BitVec.toNat h; rw [ofNat_tn (by omega)] at this; exact h0 this
    have hbyte : m5.mem (rp + BitVec.ofNat 32 t.header) = m.mem (rp + BitVec.ofNat 32 t.header) := by
      rw [memI _ (sRG.sub (c := t.header) (l := 1) (by omega)).symm,
        derAdvance_outside (.ok t) (sDR.subR (c := t.header) (l := 1) (by omega))]
    have hL : (m.mem (rp + BitVec.ofNat 32 t.header)).toNat = (memBytes m.mem rp rl.toNat).getD t.header 0 :=
      (memBytes_getD (by omega)).symm
    obtain ⟨Bb, hBb⟩ : ∃ Bb, m.mem (rp + BitVec.ofNat 32 t.header) = Bb := ⟨_, rfl⟩
    rw [hBb] at hbyte hL
    rw [← hL] at hcond
    have v6' : reg n6 9 = rp + BitVec.ofNat 32 t.header := by rw [v6, slice_ld0]
    obtain ⟨n7, d7, u7⟩ := u6.self.notTaken hc5 0x1E ds_at_1c (by decide) (by
      rw [v6', u6.self.zero]; exact beq_false_of_ne hp0)
    obtain ⟨n8, d8, u8⟩ := u7.self.lw hc5 ds_at_1e (off' := 0x20) (by decide) (by
      rw [u7.regs, r6 sp (by decide), sp5']; exact aligned_add hFa (k := 0x10) (by decide))
    have v8 : reg n8 a0 = BitVec.ofNat 32 t.len := by
      rw [u8.regs]; simp +decide only [upd_app, ↓reduceIte]
      rw [u7.regs, r6 sp (by decide), sp5', show F + 0x10 = F + 0xC + BitVec.ofNat 32 4 by rw [BitVec.add_assoc]; rfl,
        ldA 4 (by decide), ← show F + 0xC + 4 = F + 0xC + BitVec.ofNat 32 4 from rfl, slice_ld4]
    have k8 : ∀ q, q ≠ a0 → q ≠ 9 → reg n8 q = reg m5 q := fun q h0' h9 => by
      rw [u8.regs, upd_ne' h0' u7.self.zero, u7.regs, r6 q h9]
    obtain ⟨n9, d9, u9⟩ := u8.self.notTaken hc5 0x22 ds_at_20 (by decide) (by
      rw [v8, u8.self.zero]; exact beq_false_of_ne hl0)
    obtain ⟨n10, d10, u10⟩ := u9.self.lbu hc5 ds_at_22 (off' := 0x26) (by decide)
    have v10 : reg n10 a1 = Bb.zeroExtend 32 := by
      rw [u10.regs]; simp +decide only [upd_app, ↓reduceIte]
      rw [u9.regs, u8.regs, upd_ne' (by decide) u7.self.zero, u7.regs, v6', add_lit_zero, hbyte]
    obtain ⟨n11, d11, u11⟩ := u10.self.aluImm hc5 ds_at_26 (off' := 0x2A) (by decide)
    obtain ⟨zN, hzN⟩ : ∃ zN, (if Bb.toNat = 0 then 1 else 0) = zN := ⟨_, rfl⟩
    have hz1 : zN ≤ 1 := by rw [← hzN]; split <;> omega
    have v11 : reg n11 a1 = BitVec.ofNat 32 zN := by
      rw [u11.regs]; simp +decide only [upd_app, ↓reduceIte]; rw [v10, ds_sltu1, hzN]
    obtain ⟨n12, d12, u12⟩ := u11.self.alu hc5 ds_at_2a (off' := 0x2E) (by decide)
    have v12 : reg n12 8 = BitVec.ofNat 32 (t.len - zN) := by
      rw [u12.regs]; simp +decide only [upd_app, ↓reduceIte]
      rw [u11.regs, upd_ne' (by decide) u10.self.zero, u10.regs, upd_ne' (by decide) u9.self.zero, u9.regs, v8, v11]
      exact sub_val (by omega) (by omega)
    obtain ⟨n13, d13, u13⟩ := u12.self.aluImm hc5 ds_at_2e (off' := 0x32) (by decide)
    have k13 : ∀ q, q ≠ a0 → q ≠ a1 → q ≠ 8 → q ≠ 9 → reg n13 q = reg m5 q := fun q h0' h1 h8 h9 => by
      rw [u13.regs, upd_ne' h0' u12.self.zero, u12.regs, upd_ne' h8 u11.self.zero, u11.regs, upd_ne' h1 u10.self.zero,
        u10.regs, upd_ne' h1 u9.self.zero, u9.regs, k8 q h0' h9]
    have K13 : ∀ q, q.val ∈ [3, 4, 21, 22, 23, 24, 25, 26, 27] → reg n13 q = reg m q := fun q hq => by
      have h : q ≠ a0 ∧ q ≠ a1 ∧ q ≠ 8 ∧ q ≠ 9 := by revert hq; revert q; decide
      rw [k13 q h.1 h.2.1 h.2.2.1 h.2.2.2]; exact K5 q (by revert hq; revert q; decide)
    have v13s0 : reg n13 8 = BitVec.ofNat 32 (t.len - zN) := by rw [u13.regs, upd_ne' (by decide) u12.self.zero, v12]
    have v13a0 : reg n13 a0 = aluEval .add 0 0x31 := by
      rw [u13.regs]; simp +decide only [upd_app, ↓reduceIte]; rw [u12.self.zero]
    have S13 : Steps m5 n13 := .cons d6 (.cons d7 (.cons d8 (.cons d9 (.cons d10 (.cons d11 (.cons d12 (.single d13)))))))
    -- the content and its magnitude
    have hcont : t.content (memBytes m.mem rp rl.toNat) = memBytes m.mem (rp + BitVec.ofNat 32 t.header) t.len := by
      unfold DerTlv.content; exact memBytes_drop_take hb
    obtain ⟨j, hj⟩ : ∃ j, t.len = j + 1 := ⟨t.len - 1, by omega⟩
    have hmag : (if (t.content (memBytes m.mem rp rl.toNat)).head? = some 0 then
        (t.content (memBytes m.mem rp rl.toNat)).drop 1 else t.content (memBytes m.mem rp rl.toNat)) =
        memBytes m.mem (rp + BitVec.ofNat 32 t.header + BitVec.ofNat 32 zN) (t.len - zN) := by
      rw [hcont, hj, memBytes_succ, hBb]
      by_cases hb0 : Bb.toNat = 0
      · have : zN = 1 := by rw [← hzN, ite_eq_left hb0]
        subst this
        rw [hb0]; rfl
      · have : zN = 0 := by rw [← hzN, ite_eq_right hb0]
        subst this
        rw [ite_eq_right (show ¬ ((Bb.toNat :: memBytes m.mem (rp + BitVec.ofNat 32 t.header + 1) j).head? = some 0)
          from fun h => hb0 (Option.some.inj h)), add_ofNat_zero, Nat.sub_zero, memBytes_succ, hBb]
    have hspec : derScalarOf 48 (memBytes m.mem rp rl.toNat) rp (.ok t) =
        if 48 < t.len - zN then .error 5 else .ok (List.replicate (48 - (t.len - zN)) 0 ++
          memBytes m.mem (rp + BitVec.ofNat 32 t.header + BitVec.ofNat 32 zN) (t.len - zN)) := by
      simp only [derScalarOf, hR0]
      rw [hmag, memBytes_length]
    by_cases hbig : 49 ≤ t.len - zN
    · obtain ⟨n14, d14, u14⟩ := u13.self.taken hc5 0xA0 ds_at_32 (by decide) (by
        rw [v13s0, v13a0, ds_bgeu (by omega)]; exact decide_eq_true hbig)
      obtain ⟨n15, d15, u15⟩ := u14.self.aluImm hc5 ds_at_a0 (off' := 0xA2) (by decide)
      obtain ⟨n', S', pc', sp', k', o0, o1, fr'⟩ := errT (b := 5) (S13.trans (.cons d14 (.single d15))) u15.self
        (by rw [u15.regs]; simp +decide only [upd_app, ↓reduceIte]; rw [u14.self.zero]; rfl)
        (by rw [u15.regs, upd_ne' (by decide) u14.self.zero, u14.regs, k13 18 (by decide) (by decide) (by decide)
          (by decide), s185])
        (by rw [u15.regs, upd_ne' (by decide) u14.self.zero, u14.regs, k13 sp (by decide) (by decide) (by decide)
          (by decide), sp5'])
        (fun q hq => by
          rw [u15.regs, upd_ne' (fun e => by subst e; revert hq; decide) u14.self.zero, u14.regs]; exact K13 q hq)
      refine ⟨n', S', pc', sp', k', ?_⟩
      rw [hspec, ite_eq_left (by omega)]; exact ⟨o0, o1, fr'⟩
    obtain ⟨n14, d14, u14⟩ := u13.self.notTaken hc5 0x36 ds_at_32 (by decide) (by
      rw [v13s0, v13a0, ds_bgeu (by omega)]; exact decide_eq_false hbig)
    obtain ⟨n15, d15, u15⟩ := u14.self.alu hc5 ds_at_36 (off' := 0x38) (by decide)
    obtain ⟨n16, d16, u16⟩ := u15.self.jump hc5 ds_at_38 (off' := 0x42) (by decide) (by
      rw [u15.self.pc, show P + BitVec.ofNat 32 0x38 + 0xA = P + BitVec.ofNat 32 0x42 by rw [BitVec.add_assoc]; rfl]
      exact even_bit0 (even_at P env.hP 0x42 (by decide)))
    obtain ⟨src, hsrc⟩ : ∃ src, rp + BitVec.ofNat 32 t.header + BitVec.ofNat 32 zN = src := ⟨_, rfl⟩
    obtain ⟨sN, hsN⟩ : ∃ sN, t.len - zN = sN := ⟨_, rfl⟩
    rw [hsrc, hsN] at hspec
    rw [hsN] at v13s0 hbig
    have r13_9 : reg n13 9 = rp + BitVec.ofNat 32 t.header := by
      rw [u13.regs, upd_ne' (by decide) u12.self.zero, u12.regs, upd_ne' (by decide) u11.self.zero, u11.regs,
        upd_ne' (by decide) u10.self.zero, u10.regs, upd_ne' (by decide) u9.self.zero, u9.regs, u8.regs,
        upd_ne' (by decide) u7.self.zero, u7.regs, v6']
    have r13_a1 : reg n13 a1 = BitVec.ofNat 32 zN := by
      rw [u13.regs, upd_ne' (by decide) u12.self.zero, u12.regs, upd_ne' (by decide) u11.self.zero, v11]
    have v16s1 : reg n16 9 = src := by
      rw [u16.regs, u15.regs]; simp +decide only [upd_app, ↓reduceIte]
      simp only [u14.regs]; rw [r13_9, r13_a1, ← hsrc]; rfl
    sorry

end C3.RV32
