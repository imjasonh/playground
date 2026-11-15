import C3BootProofs.Proofs.FeToBytes
import C3BootProofs.Proofs.Leaves
import C3BootProofs.Proofs.ShaTools
import C3BootProofs.Proofs.DerTlv

/-!
# `FieldElement2625::is_negative`, as compiled

`is_negative` writes the field element's canonical bytes to its stack with the
proved `to_bytes`, takes the low bit of the first byte, and passes it through
the proved `black_box`.
-/

namespace C3.RV32

open C3.Image

section
set_option maxRecDepth 20000
theorem fin_at_0 : fetchRel feIsNegativeCode 0x0 = some (.aluImm .add sp sp 0xFFFFFFD0, 2) := by decide
theorem fin_at_2 : fetchRel feIsNegativeCode 0x2 = some (.store .sw sp ra 0x2C, 2) := by decide
theorem fin_at_4 : fetchRel feIsNegativeCode 0x4 = some (.alu .add a1 x0 a0, 2) := by decide
theorem fin_at_6 : fetchRel feIsNegativeCode 0x6 = some (.aluImm .add a0 sp 0xC, 2) := by decide
theorem fin_at_8 : fetchRel feIsNegativeCode 0x8 = some (.auipc ra 0xFFFFE000, 4) := by decide
theorem fin_at_c : fetchRel feIsNegativeCode 0xC = some (.jalr ra ra 0x2DE, 4) := by decide
theorem fin_at_10 : fetchRel feIsNegativeCode 0x10 = some (.load .lbu a0 sp 0xC, 4) := by decide
theorem fin_at_14 : fetchRel feIsNegativeCode 0x14 = some (.aluImm .and a0 a0 0x1, 2) := by decide
theorem fin_at_16 : fetchRel feIsNegativeCode 0x16 = some (.load .lw ra sp 0x2C, 2) := by decide
theorem fin_at_18 : fetchRel feIsNegativeCode 0x18 = some (.aluImm .add sp sp 0x30, 2) := by decide
theorem fin_at_1a : fetchRel feIsNegativeCode 0x1A = some (.auipc (6 : Fin 32) 0xFFFFE000, 4) := by decide
theorem fin_at_1e : fetchRel feIsNegativeCode 0x1E = some (.jalr x0 (6 : Fin 32) 0xFFFFF9DE, 4) := by decide
end

/-- The canonical bytes of the field element whose ten limbs are at `fp`. -/
def feBytesOf (M : Word → BitVec 8) (fp : Word) : Bytes :=
  feToBytesOf (feReduceSpec (memLoad32 M fp).toNat
    (memLoad32 M (fp + 0x4)).toNat (memLoad32 M (fp + 0x8)).toNat (memLoad32 M (fp + 0xC)).toNat
    (memLoad32 M (fp + 0x10)).toNat (memLoad32 M (fp + 0x14)).toNat
    (memLoad32 M (fp + 0x18)).toNat (memLoad32 M (fp + 0x1C)).toNat
    (memLoad32 M (fp + 0x20)).toNat (memLoad32 M (fp + 0x24)).toNat)

theorem feBytesOf_congr {M M' : Word → BitVec 8} {fp : Word}
    (h : ∀ i, i < 40 → M' (fp + BitVec.ofNat 32 i) = M (fp + BitVec.ofNat 32 i)) : feBytesOf M' fp = feBytesOf M fp := by
  have w : ∀ k, k < 10 → memLoad32 M' (fp + BitVec.ofNat 32 (4 * k)) = memLoad32 M (fp + BitVec.ofNat 32 (4 * k)) :=
    fun k hk => memLoad32_congr fun j hj => by rw [add_ofNat_assoc]; exact h _ (by omega)
  have w0 : memLoad32 M' fp = memLoad32 M fp := by have := w 0 (by decide); rwa [add_ofNat_zero] at this
  unfold feBytesOf
  rw [w0, show (0x4 : Word) = BitVec.ofNat 32 (4 * 1) from rfl, w 1 (by decide),
    show (0x8 : Word) = BitVec.ofNat 32 (4 * 2) from rfl, w 2 (by decide),
    show (0xC : Word) = BitVec.ofNat 32 (4 * 3) from rfl, w 3 (by decide),
    show (0x10 : Word) = BitVec.ofNat 32 (4 * 4) from rfl, w 4 (by decide),
    show (0x14 : Word) = BitVec.ofNat 32 (4 * 5) from rfl, w 5 (by decide),
    show (0x18 : Word) = BitVec.ofNat 32 (4 * 6) from rfl, w 6 (by decide),
    show (0x1C : Word) = BitVec.ofNat 32 (4 * 7) from rfl, w 7 (by decide),
    show (0x20 : Word) = BitVec.ofNat 32 (4 * 8) from rfl, w 8 (by decide),
    show (0x24 : Word) = BitVec.ofNat 32 (4 * 9) from rfl, w 9 (by decide)]

theorem fin_val : ∀ b : BitVec 8,
    ((aluEval .and (b.zeroExtend 32) 1).extractLsb' 0 8).zeroExtend 32 = BitVec.ofNat 32 (b.toNat % 2) := by decide

/-- Where `is_negative` runs: its code and its callees', the 0xE0 bytes of
stack below `sp0`, and the ten limbs at `fp`. -/
structure FINEnv (M : Word → BitVec 8) (P sp0 fp : Word) : Prop where
  hP : P.toNat % 2 = 0
  cod : CodeIn M P feIsNegativeCode
  tb : CodeIn M (P + 0xFFFFE2E6) feToBytesCode
  red : CodeIn M (P + 0xFFFFE2E6 + 0x210) feReduceCode
  bb : CodeIn M (P + 0xFFFFD9F8) blackBoxU8Code
  hsp : sp0.toNat % 4 = 0
  hS : 0xE0 ≤ sp0.toNat
  hfp : fp.toNat % 4 = 0
  sGC : Sep (sp0 + 0xFFFFFF20) 0xE0 P feIsNegativeCode.length
  sGT : Sep (sp0 + 0xFFFFFF20) 0xE0 (P + 0xFFFFE2E6) feToBytesCode.length
  sGR : Sep (sp0 + 0xFFFFFF20) 0xE0 (P + 0xFFFFE2E6 + 0x210) feReduceCode.length
  sGB : Sep (sp0 + 0xFFFFFF20) 0xE0 (P + 0xFFFFD9F8) blackBoxU8Code.length
  sFG : Sep fp 40 (sp0 + 0xFFFFFF20) 0xE0

set_option maxRecDepth 20000 in
set_option maxHeartbeats 4000000 in
/-- **The compiled `FieldElement2625::is_negative`**: it returns the low bit
of the first canonical byte of the field element at `fp`. -/
theorem feIsNegative_correct (m : Machine) {P sp0 fp retAddr : Word} (env : FINEnv m.mem P sp0 fp)
    (hpc : m.pc = P) (hsp : reg m sp = sp0) (ha0 : reg m a0 = fp)
    (hra : reg m ra = retAddr) (hret : retAddr &&& ~~~1 = retAddr) :
    ∃ m', Steps m m' ∧ m'.pc = retAddr ∧ reg m' sp = sp0 ∧
      reg m' a0 = BitVec.ofNat 32 ((feBytesOf m.mem fp).getD 0 0 % 2) ∧
      (∀ q, q.val ∈ [1, 3, 4, 8, 9, 18, 19, 20, 21, 22, 23, 24, 25, 26, 27] → reg m' q = reg m q) ∧
      ∀ x, Sep (sp0 + 0xFFFFFF20) 0xE0 x 1 → m'.mem x = m.mem x := by
  obtain ⟨G, hG⟩ : ∃ G, sp0 + 0xFFFFFF20 = G := ⟨_, rfl⟩
  have sGC := env.sGC; have sGT := env.sGT; have sGR := env.sGR; have sGB := env.sGB; have sFG := env.sFG
  rw [hG] at sGC sGT sGR sGB sFG ⊢
  obtain ⟨F, hF⟩ : ∃ F, sp0 + 0xFFFFFFD0 = F := ⟨_, rfl⟩
  have hGa : G.toNat % 4 = 0 := by rw [← hG]; exact aligned_add env.hsp (k := 0xFFFFFF20) (by decide)
  have hGw : G.toNat + 0xE0 = sp0.toNat := by
    rw [← hG, BitVec.toNat_add, show (0xFFFFFF20 : Word).toNat = 4294967072 from rfl]
    have := sp0.isLt; have := env.hS; omega
  have eGF : G + BitVec.ofNat 32 0xB0 = F := by rw [← hG, ← hF, BitVec.add_assoc]; rfl
  have hFa : F.toNat % 4 = 0 := by rw [← eGF]; exact aligned_add hGa (k := 0xB0) (by decide)
  have hFn : F.toNat = G.toNat + 0xB0 := by rw [← eGF, BitVec.toNat_add, BitVec.toNat_ofNat]; omega
  have eS : F + 0x30 = sp0 := by rw [← hF, BitVec.add_assoc]; exact BitVec.add_zero sp0
  have eW : F + 0x2C = G + BitVec.ofNat 32 0xDC := by rw [← eGF, BitVec.add_assoc]; rfl
  have eB : F + 0xC = G + BitVec.ofNat 32 0xBC := by rw [← eGF, BitVec.add_assoc]; rfl
  have eR : F + 0xFFFFFF50 = G + BitVec.ofNat 32 0 := by rw [← eGF, BitVec.add_assoc]; rfl
  have eT : sp0 + 0xFFFFFFFF = G + BitVec.ofNat 32 0xDF := by rw [← hG, BitVec.add_assoc]; rfl
  have gw : G.toNat + 0xE0 ≤ 2 ^ 32 := by have := sp0.isLt; omega
  have offs : ∀ {c n d k : Nat}, c + n ≤ d ∨ d + k ≤ c → c + n ≤ 0xE0 → d + k ≤ 0xE0 →
      Sep (G + BitVec.ofNat 32 c) n (G + BitVec.ofNat 32 d) k :=
    fun h h1 h2 => sep_offsets G h (by omega) (by omega)
  have cIn : ∀ {M' : Word → BitVec 8} {b : Word} {code' : List Nat}, CodeIn m.mem b code' →
      Sep G 0xE0 b code'.length → (∀ y, Sep G 0xE0 y 1 → M' y = m.mem y) → CodeIn M' b code' :=
    fun hc hs hM i hi => by rw [hM _ (hs.subR (c := i) (l := 1) (by omega))]; exact hc i hi
  have inR : ∀ {b : Word} {l : Nat}, Sep G 0xE0 b l → Sep (F + 0xFFFFFF50) 0xB0 b l := fun h => by
    rw [eR]; exact h.sub (c := 0) (l := 0xB0) (by decide)
  have s0 : St m.mem P m 0 (reg m) := ⟨by rw [hpc]; simp, rfl, fun _ => rfl⟩
  have hz := s0.zero
  obtain ⟨n1, d1, u1⟩ := s0.aluImm env.cod fin_at_0 (off' := 2) (by decide)
  obtain ⟨n2, d2, u2⟩ := u1.sw env.cod fin_at_2 (off' := 4) (by decide) (by
    simp +decide only [upd_app, ↓reduceIte]; rw [ev_add, hsp, hF]; exact aligned_add hFa (k := 0x2C) (by decide))
  simp +decide only [upd_app, ↓reduceIte] at u2
  rw [ev_add, hsp, hF, eW, hra] at u2
  obtain ⟨Ms, hMs⟩ : ∃ Ms, memStore32 m.mem (G + BitVec.ofNat 32 0xDC) retAddr = Ms := ⟨_, rfl⟩
  have frS : ∀ x, Sep G 0xE0 x 1 → Ms x = m.mem x := fun x hx => by
    rw [← hMs]; exact memStore32_get_sep (hx.sub (c := 0xDC) (l := 4) (by decide))
  rw [hMs] at u2
  have hc2 := cIn env.cod sGC frS
  obtain ⟨n3, c3, u3⟩ := St.block [.alu .add a1 x0 a0, .aluImm .add a0 sp 0xC] u2.self hc2 (off' := 0x8) (by decide)
    (by simp [BlockOk, BInstr.ok])
  simp only [runBlock, BInstr.run] at u3
  have k2 : ∀ q, q ≠ sp → reg n2 q = reg m q := fun q h => by rw [u2.regs, updz hz h]
  have sp2 : reg n2 sp = F := by rw [u2.regs]; simp +decide only [upd_app, ↓reduceIte]
  obtain ⟨n4, c4, pc4, mem4, regs4⟩ := u3.self.callRa hc2 fin_at_8 fin_at_c (cb := P + 0xFFFFE2E6)
    (by rw [BitVec.add_assoc, BitVec.add_assoc]; rfl) (even_at P env.hP 0xFFFFE2E6 (by decide))
  have r4 := PEnv.reg1 regs4 u3.self.zero
  have sp4 : reg n4 sp = F := by
    rw [r4 sp (by decide), u3.regs, upd_ne (by decide) (by decide), upd_ne (by decide) (by decide), sp2]
  have tenv : TBEnv n4.mem (P + 0xFFFFE2E6) F (F + 0xC) fp := by
    rw [mem4]
    exact ⟨even_at P env.hP 0xFFFFE2E6 (by decide), cIn env.tb sGT frS, cIn env.red sGR frS, hFa, by omega, env.hfp,
      inR sGT, inR sGR, by rw [eB]; exact sGT.sub (c := 0xBC) (l := 32) (by decide),
      by rw [eB, eR]; exact offs (.inr (by decide)) (by decide) (by decide),
      by rw [eR]; exact sFG.subR (c := 0) (l := 0xB0) (by decide)⟩
  obtain ⟨n5, c5, pc5, sp5, k5, b5, f5⟩ := feToBytes_correct n4 tenv pc4 sp4
    (by rw [r4 a0 (by decide), u3.regs]; simp +decide only [upd_app, ↓reduceIte]; rw [sp2]; rfl)
    (by rw [r4 a1 (by decide), u3.regs]; simp +decide only [upd_app, ↓reduceIte]; rw [u2.self.zero, k2 a0 (by decide),
          ha0]; exact zw fp)
    (by rw [regs4]; simp +decide only [upd_app, ↓reduceIte]) (even_clear _ (even_at P env.hP (0x8 + 8) (by decide)))
  rw [mem4] at b5 f5
  have eF : feBytesOf Ms fp = feBytesOf m.mem fp :=
    feBytesOf_congr fun i hi => frS _ (sFG.sub (c := i) (l := 1) (by omega)).symm
  rw [show feToBytesOf _ = feBytesOf Ms fp from rfl, eF] at b5
  have fr5 : ∀ x, Sep G 0xE0 x 1 → n5.mem x = m.mem x := fun x hx => by
    rw [f5 x (inR hx) (by rw [eB]; exact hx.sub (c := 0xBC) (l := 32) (by decide)), frS x hx]
  have hc5 : CodeIn n5.mem P feIsNegativeCode := cIn env.cod sGC fr5
  have u5 : St n5.mem P n5 (0x8 + 8) (reg n5) := ⟨by rw [pc5], rfl, fun _ => rfl⟩
  obtain ⟨n6, c6, u6⟩ := St.block [.lbu a0 sp 0xC, .aluImm .and a0 a0 1] u5 hc5 (off' := 0x16) (by decide)
    (by simp [BlockOk, BInstr.ok])
  simp only [runBlock, BInstr.run] at u6
  obtain ⟨n7, d7, u7⟩ := u6.self.lw hc5 fin_at_16 (off' := 0x18) (by decide) (by
    rw [u6.regs, upd_ne (by decide) (by decide), upd_ne (by decide) (by decide), sp5]
    exact aligned_add hFa (k := 0x2C) (by decide))
  have sp6 : reg n6 sp = F := by rw [u6.regs, upd_ne (by decide) (by decide), upd_ne (by decide) (by decide), sp5]
  have eRa : memLoad32 n5.mem (G + BitVec.ofNat 32 0xDC) = retAddr := by
    rw [memLoad32_congr (M := Ms) (b := G + BitVec.ofNat 32 0xDC) (fun j hj => f5 _ (by
      rw [eR, add_ofNat_assoc]; exact offs (.inl (by omega)) (by decide) (by omega))
      (by rw [eB, add_ofNat_assoc]; exact offs (.inl (by omega)) (by decide) (by omega))), ← hMs]
    exact memLoad32_store32_same _ _ _
  rw [sp6, eW, eRa] at u7
  obtain ⟨n8, d8, u8⟩ := u7.aluImm hc5 fin_at_18 (off' := 0x1A) (by decide)
  obtain ⟨n9, d9, u9⟩ := u8.self.auipc hc5 fin_at_1a (off' := 0x1E) (by decide)
  obtain ⟨n10, d10, pc10, mem10, regs10⟩ := u9.self.jalr hc5 fin_at_1e
  have pc10' : n10.pc = P + 0xFFFFD9F8 := by
    rw [pc10, u9.regs]; simp +decide only [upd, ↓reduceIte]
    rw [show P + BitVec.ofNat 32 0x1A + 0xFFFFE000 + 0xFFFFF9DE = P + 0xFFFFD9F8 by
      rw [BitVec.add_assoc, BitVec.add_assoc]; rfl]
    exact even_clear _ (even_at P env.hP 0xFFFFD9F8 (by decide))
  have k10 : ∀ q, q ≠ t1 → q ≠ sp → q ≠ ra → q ≠ a0 → reg n10 q = reg n5 q := fun q h6 hs hr h0 => by
    rw [regs10, u9.regs, upd_ne' h6 u8.self.zero, u8.regs, upd_ne' hs (upd_zero _ _ _), upd_ne' hr u6.self.zero,
      u6.regs, upd_ne' h0 (upd_zero _ _ _), upd_ne' h0 u5.zero]
  have sp10 : reg n10 sp = sp0 := by
    rw [regs10, u9.regs, upd_ne (by decide) (by decide), u8.regs]; simp +decide only [upd_app, ↓reduceIte]
    rw [sp6, ev_add, eS]
  have ra10 : reg n10 ra = retAddr := by
    rw [regs10, u9.regs, upd_ne (by decide) (by decide), u8.regs, upd_ne (by decide) (by decide)]
    simp +decide only [upd_app, ↓reduceIte]
  have byte0 : n5.mem (F + 0xC) = BitVec.ofNat 8 ((feBytesOf m.mem fp).getD 0 0) := by
    rw [← b5, memBytes_getD (by decide), add_ofNat_zero]; exact (tlv_tag8 _).symm
  have a010 : reg n10 a0 = aluEval .and ((n5.mem (F + 0xC)).zeroExtend 32) 1 := by
    rw [regs10, u9.regs, upd_ne (by decide) (by decide), u8.regs, upd_ne (by decide) (by decide),
      upd_ne (by decide) (by decide), u6.regs]
    simp +decide only [upd_app, ↓reduceIte]
    rw [sp5]
  have mG : ∀ x, Sep G 0xE0 x 1 → n10.mem x = m.mem x := fun x hx => by rw [mem10, fr5 x hx]
  obtain ⟨m', c', pc', a0', k', f'⟩ := blackBoxU8_correct n10 (base := P + 0xFFFFD9F8) (retAddr := retAddr)
    (cIn env.bb sGB mG) pc10' ra10 hret (by rw [sp10, eT]; exact sGB.sub (c := 0xDF) (l := 1) (by decide))
  refine ⟨m', .cons d1 (.cons d2 (c3.trans (c4.trans (c5.trans (c6.trans (.cons d7 (.cons d8 (.cons d9
    (.cons d10 c'))))))))), pc', by rw [k' sp (by decide), sp10], ?_, fun q hq => ?_, fun x hx => ?_⟩
  · rw [a0', a010, fin_val, byte0, BitVec.toNat_ofNat]
    have : (feBytesOf m.mem fp).getD 0 0 % 2 ^ 8 % 2 = (feBytesOf m.mem fp).getD 0 0 % 2 := by omega
    rw [this]
  · have h0 : q ≠ a0 := fun e => by subst e; revert hq; decide
    have h6 : q ≠ t1 := fun e => by subst e; revert hq; decide
    rw [k' q h0]
    by_cases hs : q = sp
    · subst hs; exact absurd hq (by decide)
    by_cases hr : q = ra
    · subst hr; rw [ra10, hra]
    have hk : tbKeep q = true := by revert hq; revert q; decide
    have h1 : q ≠ a1 := fun e => by subst e; revert hq; decide
    rw [k10 q h6 hs hr h0, k5 q hk, r4 q hr, u3.regs, upd_ne' h0 (upd_zero _ _ _), upd_ne' h1 u2.self.zero, k2 q hs]
  · rw [f' x (by rw [sp10, eT]; exact hx.sub (c := 0xDF) (l := 1) (by decide)), mG x hx]

end C3.RV32
