import C3BootProofs.Proofs.TufRoleKeysMetLoop

/-!
# `tufRoleKeysMet`: the prologue and the contract

`RoleKeys::met` from its entry to the loop head at 0x78: the saved
registers, the message and the signatures it reads through `a1`, the
eight zeroed slot numbers at `F + 0x28`, and the count. `rm_wp` joins it to
the loop, and `tufRoleKeysMet_ret_pi` is the function's contract: it halts
only in a panic that a failed inversion bound allows (`rmHI`), or returns.
`tufRoleKeysMet_ret` and `tufRoleKeysMet_correct` weaken it to any panic.
-/

namespace C3.RV32

open C3.Image C3.Json

set_option maxRecDepth 20000

section
variable {M0 : Word → BitVec 8} {s R A MP SP : Word} {ML SL t : Nat} {es : List RkEntry} {g0 : Fin 32 → Word}

/-- `RoleKeys::met` from its entry, with the `RoleKeys` at `R` in `a0` and
in `a1` the address `A` of the message (`MP`, `ML`) and the signatures
(`SP`, `SL`), and its stack the 0x3920 bytes below `sp`. -/
theorem rm_wp (hg0 : g0 a0 = R) (hg1 : g0 a1 = A) (hsp : g0 sp = s + BitVec.ofNat 32 0x3920)
    (hret : g0 ra &&& ~~~1 = g0 ra) (hal : s.toNat % 16 = 0) (hlo : 0x3FC80000 ≤ s.toNat)
    (hhi : s.toNat + 0x3920 ≤ 0x3FCE0000)
    (hds : Sep s 0x3920 (BitVec.ofNat 32 (img% dataWindowAddress)) (img% dataWindowSize))
    (hro : Sep s 0x3920 (BitVec.ofNat 32 (img% roWindowAddress)) (img% roWindowSize))
    (hc : ∀ M : Word → BitVec 8, (∀ x, Sep x 1 s 0x3920 → M x = M0 x) → RmCode M)
    (halR : R.toNat % 4 = 0) (hRw : R.toNat + 0x540 ≤ 0x40000000) (hSR : Sep s 0x3920 R 0x540)
    (hMw : MP.toNat + ML ≤ 0x40000000) (hML : ML < 2 ^ 31) (hSM : Sep s 0x3920 MP ML)
    (hS0 : SP.toNat ≠ 0) (hSw : SP.toNat + SL ≤ 0x40000000) (hSL : SL < 2 ^ 31) (hSS : Sep s 0x3920 SP SL)
    (halA : A.toNat % 4 = 0) (hSA : Sep s 0x3920 A 16) (hA0 : memLoad32 M0 A = MP)
    (hA4 : memLoad32 M0 (A + BitVec.ofNat 32 4) = BitVec.ofNat 32 ML) (hA8 : memLoad32 M0 (A + BitVec.ofNat 32 8) = SP)
    (hAC : memLoad32 M0 (A + BitVec.ofNat 32 12) = BitVec.ofNat 32 SL) (hR : RkAt M0 R t es) (hw : RkWf es) :
    WP tufRoleKeysMetCode TRM
      (rmQ rmHI M0 s g0 (MetSound (memBytes M0 SP SL) (memBytes M0 MP ML) t (es.map nbE))) M0 0 g0 := by
  refine WP.zero fun hz => ?_
  refine WP.aluImm rkm_at_0 ?_; wn
  have esp : aluEval .add (g0 sp) 0xFFFFFE10 = s + BitVec.ofNat 32 0x3730 := by
    rw [hsp, ev_add, BitVec.add_assoc]; rfl
  rw [esp]
  refine WP.aluImm rkm_at_2 ?_; wn
  have ea2 : aluEval .add (s + BitVec.ofNat 32 0x3730) 0x180 = s + BitVec.ofNat 32 0x3730 + 0x180 := by
    rw [ev_add]
  (try rsimp); rw [ea2]
  generalize hF : s + BitVec.ofNat 32 0x3730 = F
  obtain ⟨hO1, hv⟩ := rk_pro M0 (F + 0x180) g0
  have E : RmEnv M0 (rkM1 M0 (F + 0x180) g0) s F R MP SP ML SL g0 :=
    ⟨⟨hF, hal, hlo, hhi, hds, hro, fun M h => (hc M h).a,
      Out.upK (c := 0x38B0) (by rw [← hF, BitVec.add_assoc]; rfl) hO1 (by decide), hv,
      by rw [hsp, ← hF, add_ofNat_assoc], hret, hz, halR, hRw, hSR, hMw, hML, hSM, hS0, hSw, hSL, hSS⟩, hc⟩
  refine WP.sw rkm_at_4 (by (try rsimp); rw [BitVec.add_assoc]; exact E.alF (c := 0x180 + 0x6C) (by decide))
    (by (try rsimp); rw [BitVec.add_assoc]; exact E.cF (c := 0x180 + 0x6C) (by decide)) ?_; wn
  refine WP.sw rkm_at_8 (by (try rsimp); rw [BitVec.add_assoc]; exact E.alF (c := 0x180 + 0x68) (by decide))
    (by (try rsimp); rw [BitVec.add_assoc]; exact E.cF (c := 0x180 + 0x68) (by decide)) ?_; wn
  refine WP.sw rkm_at_a (by (try rsimp); rw [BitVec.add_assoc]; exact E.alF (c := 0x180 + 0x64) (by decide))
    (by (try rsimp); rw [BitVec.add_assoc]; exact E.cF (c := 0x180 + 0x64) (by decide)) ?_; wn
  refine WP.sw rkm_at_c (by (try rsimp); rw [BitVec.add_assoc]; exact E.alF (c := 0x180 + 0x60) (by decide))
    (by (try rsimp); rw [BitVec.add_assoc]; exact E.cF (c := 0x180 + 0x60) (by decide)) ?_; wn
  refine WP.sw rkm_at_10 (by (try rsimp); rw [BitVec.add_assoc]; exact E.alF (c := 0x180 + 0x5C) (by decide))
    (by (try rsimp); rw [BitVec.add_assoc]; exact E.cF (c := 0x180 + 0x5C) (by decide)) ?_; wn
  refine WP.sw rkm_at_14 (by (try rsimp); rw [BitVec.add_assoc]; exact E.alF (c := 0x180 + 0x58) (by decide))
    (by (try rsimp); rw [BitVec.add_assoc]; exact E.cF (c := 0x180 + 0x58) (by decide)) ?_; wn
  refine WP.sw rkm_at_18 (by (try rsimp); rw [BitVec.add_assoc]; exact E.alF (c := 0x180 + 0x54) (by decide))
    (by (try rsimp); rw [BitVec.add_assoc]; exact E.cF (c := 0x180 + 0x54) (by decide)) ?_; wn
  refine WP.sw rkm_at_1c (by (try rsimp); rw [BitVec.add_assoc]; exact E.alF (c := 0x180 + 0x50) (by decide))
    (by (try rsimp); rw [BitVec.add_assoc]; exact E.cF (c := 0x180 + 0x50) (by decide)) ?_; wn
  refine WP.sw rkm_at_20 (by (try rsimp); rw [BitVec.add_assoc]; exact E.alF (c := 0x180 + 0x4C) (by decide))
    (by (try rsimp); rw [BitVec.add_assoc]; exact E.cF (c := 0x180 + 0x4C) (by decide)) ?_; wn
  refine WP.sw rkm_at_24 (by (try rsimp); rw [BitVec.add_assoc]; exact E.alF (c := 0x180 + 0x48) (by decide))
    (by (try rsimp); rw [BitVec.add_assoc]; exact E.cF (c := 0x180 + 0x48) (by decide)) ?_; wn
  refine WP.sw rkm_at_28 (by (try rsimp); rw [BitVec.add_assoc]; exact E.alF (c := 0x180 + 0x44) (by decide))
    (by (try rsimp); rw [BitVec.add_assoc]; exact E.cF (c := 0x180 + 0x44) (by decide)) ?_; wn
  refine WP.sw rkm_at_2c (by (try rsimp); rw [BitVec.add_assoc]; exact E.alF (c := 0x180 + 0x40) (by decide))
    (by (try rsimp); rw [BitVec.add_assoc]; exact E.cF (c := 0x180 + 0x40) (by decide)) ?_; wn
  refine WP.sw rkm_at_30 (by (try rsimp); rw [BitVec.add_assoc]; exact E.alF (c := 0x180 + 0x3C) (by decide))
    (by (try rsimp); rw [BitVec.add_assoc]; exact E.cF (c := 0x180 + 0x3C) (by decide)) ?_; wn
  change WP tufRoleKeysMetCode TRM _ (rkM1 M0 (F + 0x180) g0) 0x34 _
  clear hO1 hv
  generalize rkM1 M0 (F + 0x180) g0 = M1 at E
  have hx0 : g0 x0 = 0 := hz
  have hAm : ∀ c, c + 4 ≤ 16 → ∀ Mk, Out M1 Mk s 0x38EC →
      memLoad32 Mk (A + BitVec.ofNat 32 c) = memLoad32 M0 (A + BitVec.ofNat 32 c) :=
    fun c hc Mk hO => memLoad32_congr fun j hj => E.agree hO _ (sep_pt (hSA.subR hc) hj)
  have hRm : ∀ c, c + 4 ≤ 0x540 → ∀ Mk, Out M1 Mk s 0x38EC →
      memLoad32 Mk (R + BitVec.ofNat 32 c) = memLoad32 M0 (R + BitVec.ofNat 32 c) :=
    fun c hc Mk hO => memLoad32_congr fun j hj => E.agree hO _ (sep_pt (E.hSR.subR hc) hj)
  have hA0' : memLoad32 M1 A = MP := by
    have := hAm 0 (by decide) M1 (Out.refl _ _ _); rw [add_ofNat_zero] at this; rw [this, hA0]
  refine WP.alu rkm_at_34 ?_; wn
  (try rw [hx0]); rw [ev0, hg1]
  refine WP.lw rkm_at_36 (by (try rsimp); (try rw [add_lit_zero]); rw [hg1]; exact halA) ?_; wn
  (try rw [add_lit_zero]); rw [hg1, hA0']
  refine rm_sw rkm_at_38 (A := F + BitVec.ofNat 32 0x14) (V := MP) (by (try rsimp); rfl) (by rsimp)
    (E.alF (by decide)) (E.cF (by decide)) ?_; wn
  have hO2a : Out M1 (memStore32 M1 (F + BitVec.ofNat 32 0x14) MP) s 0x38EC := E.st (Out.refl _ _ _) (by decide)
  refine WP.lw rkm_at_3a (by (try rsimp); exact aligned_add halA (k := 4) (by decide)) ?_; wn
  rw [show (4 : Word) = BitVec.ofNat 32 4 from rfl, hAm 4 (by decide) _ hO2a, hA4]
  refine rm_sw rkm_at_3c (A := F + BitVec.ofNat 32 0x10) (V := BitVec.ofNat 32 ML) (by (try rsimp); rfl) (by rsimp)
    (E.alF (by decide)) (E.cF (by decide)) ?_; wn
  have hO2 := E.st (v := BitVec.ofNat 32 ML) (d := 0x10) hO2a (by decide)
  refine WP.alu rkm_at_3e ?_; wn
  (try rw [hx0]); rw [ev0, hg0]
  refine WP.aluImm rkm_at_40 ?_; wn
  refine WP.aluImm rkm_at_42 ?_; wn
  refine WP.aluImm rkm_at_46 ?_; wn
  refine WP.aluImm rkm_at_48 ?_; wn
  have hcm := E.codeA hO2
  refine WP.callMemsetT (tb := TPS_MS) (dst := F + BitVec.ofNat 32 0x28) (b := 0) (n := 0x20) rkm_at_4a
    rkm_at_4e (by decide) (by decide) (by decide) hcm.rk.tps.ms (by (try rsimp); rw [ev_add]; rfl)
    (by (try rsimp); try (rw [hx0]; rfl)) (by (try rsimp); try rfl)
    (by have := E.wF (c := 0x28) (k := 0x20) (by decide); omega)
    (E.lowF (by decide) (by decide) (by decide)) (E.cF (by decide)) fun m2 hm2 => ?_
  have oF : Out (memStore32 (memStore32 M1 (F + BitVec.ofNat 32 0x14) MP) (F + BitVec.ofNat 32 0x10)
      (BitVec.ofNat 32 ML)) m2.mem (F + BitVec.ofNat 32 0x28) 0x20 := fun x hx => by
    rw [hm2]; exact fillBytes_sep hx.symm (Nat.le_refl _)
  have hO3 := hO2.trans (E.outF oF (by decide))
  have h10 : memLoad32 m2.mem (F + BitVec.ofNat 32 0x10) = BitVec.ofNat 32 ML :=
    (oF.load32 (rm_ff F (c := 0x28) (n := 0x20) (d := 0x10) (k := 4) (Or.inr (by decide)) (by decide)
      (by decide))).trans (memLoad32_store32_same _ _ _)
  have h14 : memLoad32 m2.mem (F + BitVec.ofNat 32 0x14) = MP :=
    (oF.load32 (rm_ff F (c := 0x28) (n := 0x20) (d := 0x14) (k := 4) (Or.inr (by decide)) (by decide)
      (by decide))).trans ((rm_ld F (c := 0x10) (d := 0x14) (by decide) (by decide) (by decide)).trans
      (memLoad32_store32_same _ _ _))
  clear hm2 oF
  generalize m2.mem = M3 at hO3 h10 h14
  have hn := hR.2.2.1
  rw [rk_w32] at hn
  refine rm_sw rkm_at_52 (A := F + BitVec.ofNat 32 0x1C) (V := 0) (by (try rsimp); rfl) (by rsimp)
    (E.alF (by decide)) (E.cF (by decide)) ?_; wn
  have hO4 := E.st (v := 0) (d := 0x1C) hO3 (by decide)
  refine WP.aluImm rkm_at_54 ?_; wn
  refine WP.aluImm rkm_at_56 ?_; wn
  refine WP.lw rkm_at_58 (by (try rsimp); exact aligned_add halR (k := 0x538) (by decide)) ?_; wn
  rw [show (0x538 : Word) = BitVec.ofNat 32 0x538 from rfl, hRm 0x538 (by decide) _ hO4, hn]
  refine WP.aluImm rkm_at_5c ?_; wn
  refine WP.lw rkm_at_60 (by (try rsimp); exact aligned_add halA (k := 8) (by decide)) ?_; wn
  refine WP.lw rkm_at_62 (by (try rsimp); exact aligned_add halA (k := 12) (by decide)) ?_; wn
  rw [show (8 : Word) = BitVec.ofNat 32 8 from rfl, show (12 : Word) = BitVec.ofNat 32 12 from rfl,
    hAm 8 (by decide) _ hO4, hA8, hAm 12 (by decide) _ hO4, hAC]
  refine WP.aluImm rkm_at_64 ?_; wn
  refine WP.aluImm rkm_at_68 ?_; wn
  refine rm_sw rkm_at_6c (A := F + BitVec.ofNat 32 0x24) (V := SP) (by (try rsimp); rfl) (by rsimp)
    (E.alF (by decide)) (E.cF (by decide)) ?_; wn
  refine rm_sw rkm_at_6e (A := F + BitVec.ofNat 32 0x20) (V := BitVec.ofNat 32 SL) (by (try rsimp); rfl) (by rsimp)
    (E.alF (by decide)) (E.cF (by decide)) ?_; wn
  refine rm_sw rkm_at_70 (A := F + BitVec.ofNat 32 0x18) (V := 0) (by (try rsimp); rfl) (by rsimp)
    (E.alF (by decide)) (E.cF (by decide)) ?_; wn
  refine WP.aluImm rkm_at_72 ?_; wn
  refine WP.alu rkm_at_74 ?_; wn
  refine rm_sw rkm_at_76 (A := F + BitVec.ofNat 32 0xC) (V := F + BitVec.ofNat 32 0x28) (by (try rsimp); rfl)
    (by rsimp; rw [show aluEval .sll (aluEval .add 0 0) 2 = (0 : Word) by decide, ev_add, ev_add]; exact BitVec.zero_add _) (E.alF (by decide)) (E.cF (by decide)) ?_; wn
  refine rm_loop E hR hw _ [] 0 _ _ rfl ⟨E.st (E.st (E.st (E.st hO4 (by decide)) (by decide)) (by decide)) (by decide),
    ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, by decide, fun m hm => absurd hm (Nat.not_lt_zero m)⟩, rm_snd0, by rsimp, by rsimp; (try exact hz),
    by keepz hz, by rsimp, by rsimp, by rsimp, by rsimp, by rsimp, by rsimp; rw [ev_add]; rfl, by rsimp, by rsimp, by decide,
    Nat.zero_le _⟩
  · rw [rm_ld F (c := 0xC) (d := 0x10) (by decide) (by decide) (by decide), rm_ld F (c := 0x18) (d := 0x10) (by decide) (by decide) (by decide), rm_ld F (c := 0x20) (d := 0x10) (by decide) (by decide) (by decide), rm_ld F (c := 0x24) (d := 0x10) (by decide) (by decide) (by decide), rm_ld F (c := 0x1C) (d := 0x10) (by decide) (by decide) (by decide)]; exact h10
  · rw [rm_ld F (c := 0xC) (d := 0x14) (by decide) (by decide) (by decide), rm_ld F (c := 0x18) (d := 0x14) (by decide) (by decide) (by decide), rm_ld F (c := 0x20) (d := 0x14) (by decide) (by decide) (by decide), rm_ld F (c := 0x24) (d := 0x14) (by decide) (by decide) (by decide), rm_ld F (c := 0x1C) (d := 0x14) (by decide) (by decide) (by decide)]; exact h14
  · rw [rm_ld F (c := 0xC) (d := 0x18) (by decide) (by decide) (by decide)]; exact memLoad32_store32_same _ _ _
  · rw [rm_ld F (c := 0xC) (d := 0x1C) (by decide) (by decide) (by decide), rm_ld F (c := 0x18) (d := 0x1C) (by decide) (by decide) (by decide), rm_ld F (c := 0x20) (d := 0x1C) (by decide) (by decide) (by decide), rm_ld F (c := 0x24) (d := 0x1C) (by decide) (by decide) (by decide)]; exact memLoad32_store32_same _ _ _
  · rw [rm_ld F (c := 0xC) (d := 0x20) (by decide) (by decide) (by decide), rm_ld F (c := 0x18) (d := 0x20) (by decide) (by decide) (by decide)]; exact memLoad32_store32_same _ _ _
  · rw [rm_ld F (c := 0xC) (d := 0x24) (by decide) (by decide) (by decide), rm_ld F (c := 0x18) (d := 0x24) (by decide) (by decide) (by decide), rm_ld F (c := 0x20) (d := 0x24) (by decide) (by decide) (by decide)]; exact memLoad32_store32_same _ _ _
  · exact memLoad32_store32_same _ _ _


/-- **`tufRoleKeysMet_ret` with its panic refined**: `RoleKeys::met` halts
only if an inversion bound fails (`rmHI`), or it returns as
`tufRoleKeysMet_ret` says. `tufRoleKeysMet_correct_pi`, `tufRoleKeysMet_spec_pi`,
and `tufRoleKeysMet_result_pi` refine the others the same way. -/
def TufRoleKeysMetRetPI : Prop :=
  ∀ (m : Machine) {retAddr s R A MP SP : Word} {ML SL t : Nat} {es : List RkEntry}
    (_hpc : m.pc = TRM) (_ha0 : reg m a0 = R) (_ha1 : reg m a1 = A) (_hsp : reg m sp = s + BitVec.ofNat 32 0x3920)
    (_hra : reg m ra = retAddr) (_hret : retAddr &&& ~~~1 = retAddr) (_hal : s.toNat % 16 = 0)
    (_hlo : 0x3FC80000 ≤ s.toNat) (_hhi : s.toNat + 0x3920 ≤ 0x3FCE0000)
    (_hds : Sep s 0x3920 (BitVec.ofNat 32 (img% dataWindowAddress)) (img% dataWindowSize))
    (_hro : Sep s 0x3920 (BitVec.ofNat 32 (img% roWindowAddress)) (img% roWindowSize))
    (_hc : ∀ M : Word → BitVec 8, (∀ x, Sep x 1 s 0x3920 → M x = m.mem x) → RmCode M)
    (_halR : R.toNat % 4 = 0) (_hRw : R.toNat + 0x540 ≤ 0x40000000) (_hSR : Sep s 0x3920 R 0x540)
    (_hMw : MP.toNat + ML ≤ 0x40000000) (_hML : ML < 2 ^ 31) (_hSM : Sep s 0x3920 MP ML)
    (_hS0 : SP.toNat ≠ 0) (_hSw : SP.toNat + SL ≤ 0x40000000) (_hSL : SL < 2 ^ 31) (_hSS : Sep s 0x3920 SP SL)
    (_halA : A.toNat % 4 = 0) (_hSA : Sep s 0x3920 A 16) (_hA0 : memLoad32 m.mem A = MP)
    (_hA4 : memLoad32 m.mem (A + BitVec.ofNat 32 4) = BitVec.ofNat 32 ML)
    (_hA8 : memLoad32 m.mem (A + BitVec.ofNat 32 8) = SP)
    (_hAC : memLoad32 m.mem (A + BitVec.ofNat 32 12) = BitVec.ofNat 32 SL) (_hR : RkAt m.mem R t es) (_hw : RkWf es),
    ∃ m', Steps m m' ∧
        (rmHI m'.pc m'.mem (reg m') ∨
          (m'.pc = retAddr ∧ (∀ x, Sep x 1 s 0x3920 → m'.mem x = m.mem x) ∧ (∀ r, r ∉ jClob → reg m' r = reg m r) ∧
            (reg m' a0 = 0 → reg m' a1 ≠ 0 →
              MetSound (memBytes m.mem SP SL) (memBytes m.mem MP ML) t (es.map nbE)) ∧
            (reg m' a0 = 0 ∨ reg m' a0 = 1) ∧ (reg m' a0 ≠ 0 → (reg m' a1 &&& 0xFF).toNat < 0x27)))

/-- **`RoleKeys::met`**, from its entry, with the `RoleKeys` at `R` in `a0`
holding the threshold `t` and the listed keys `es`, and in `a1` the
address `A` of the 16 bytes that give the message (`ML` bytes at `MP`)
and the signatures array (`SL` bytes at `SP`). Its stack is the 0x3920
bytes below `sp`, and the code and the constants that it and its callees
read lie outside the stack. It halts in a panic, and then some inversion
bound fails, or it returns to `ra` with memory outside the stack as
before and every register outside `jClob` as before. When it returns
`Ok(true)`, at least `t` distinct listed keys have a key ID whose first
signature in the array checks over the message. It returns 0 (`Ok`) or 1
(`Err`) in `a0`, and in an `Err` the low byte of `a1` is an error code
below 0x27. -/
theorem tufRoleKeysMet_ret_pi : TufRoleKeysMetRetPI := by
  intro m retAddr s R A MP SP ML SL t es hpc ha0 ha1 hsp hra hret hal hlo hhi hds hro hc halR hRw hSR hMw hML hSM
    hS0 hSw hSL hSS halA hSA hA0 hA4 hA8 hAC hR hw
  obtain ⟨m', st, q⟩ := WP.run (rm_wp ha0 ha1 hsp (by rw [hra]; exact hret) hal hlo hhi hds hro hc halR hRw hSR hMw
    hML hSM hS0 hSw hSL hSS halA hSA hA0 hA4 hA8 hAC hR hw) (by decide) (hc _ fun _ _ => rfl).a.self hpc
  refine ⟨m', st, ?_⟩
  rcases q with h | ⟨⟨hp, hM, hr⟩, hS⟩
  · exact .inl h
  · exact .inr ⟨hp.trans hra, hM, hr, hS⟩

/-- `RoleKeys::met` from its entry, with the `RoleKeys` at `R` in `a0`
holding the threshold `t` and the listed keys `es`, and in `a1` the
address `A` of the 16 bytes that give the message (`ML` bytes at `MP`)
and the signatures array (`SL` bytes at `SP`). Its stack is the 0x3920
bytes below `sp`, and the code and the constants that it and its callees
read lie outside the stack. It halts in a panic, or it returns to `ra`
with memory outside the stack as before and every register outside
`jClob` as before. When it returns `Ok(true)`, at least `t` distinct
listed keys have a key ID whose first signature in the array checks over
the message. It returns 0 (`Ok`) or 1 (`Err`) in `a0`, and in an `Err` the
low byte of `a1` is an error code below 0x27. -/
theorem tufRoleKeysMet_ret (m : Machine) {retAddr s R A MP SP : Word} {ML SL t : Nat} {es : List RkEntry}
    (hpc : m.pc = TRM) (ha0 : reg m a0 = R) (ha1 : reg m a1 = A) (hsp : reg m sp = s + BitVec.ofNat 32 0x3920)
    (hra : reg m ra = retAddr) (hret : retAddr &&& ~~~1 = retAddr) (hal : s.toNat % 16 = 0)
    (hlo : 0x3FC80000 ≤ s.toNat) (hhi : s.toNat + 0x3920 ≤ 0x3FCE0000)
    (hds : Sep s 0x3920 (BitVec.ofNat 32 (img% dataWindowAddress)) (img% dataWindowSize))
    (hro : Sep s 0x3920 (BitVec.ofNat 32 (img% roWindowAddress)) (img% roWindowSize))
    (hc : ∀ M : Word → BitVec 8, (∀ x, Sep x 1 s 0x3920 → M x = m.mem x) → RmCode M)
    (halR : R.toNat % 4 = 0) (hRw : R.toNat + 0x540 ≤ 0x40000000) (hSR : Sep s 0x3920 R 0x540)
    (hMw : MP.toNat + ML ≤ 0x40000000) (hML : ML < 2 ^ 31) (hSM : Sep s 0x3920 MP ML)
    (hS0 : SP.toNat ≠ 0) (hSw : SP.toNat + SL ≤ 0x40000000) (hSL : SL < 2 ^ 31) (hSS : Sep s 0x3920 SP SL)
    (halA : A.toNat % 4 = 0) (hSA : Sep s 0x3920 A 16) (hA0 : memLoad32 m.mem A = MP)
    (hA4 : memLoad32 m.mem (A + BitVec.ofNat 32 4) = BitVec.ofNat 32 ML)
    (hA8 : memLoad32 m.mem (A + BitVec.ofNat 32 8) = SP)
    (hAC : memLoad32 m.mem (A + BitVec.ofNat 32 12) = BitVec.ofNat 32 SL) (hR : RkAt m.mem R t es) (hw : RkWf es) :
    ∃ m', Steps m m' ∧
      (rmH m'.pc m'.mem (reg m') ∨
        (m'.pc = retAddr ∧ (∀ x, Sep x 1 s 0x3920 → m'.mem x = m.mem x) ∧ (∀ r, r ∉ jClob → reg m' r = reg m r) ∧
          (reg m' a0 = 0 → reg m' a1 ≠ 0 →
            MetSound (memBytes m.mem SP SL) (memBytes m.mem MP ML) t (es.map nbE)) ∧
          (reg m' a0 = 0 ∨ reg m' a0 = 1) ∧ (reg m' a0 ≠ 0 → (reg m' a1 &&& 0xFF).toNat < 0x27))) :=
  let ⟨m', st, q⟩ := tufRoleKeysMet_ret_pi m hpc ha0 ha1 hsp hra hret hal hlo hhi hds hro hc halR hRw hSR hMw hML
    hSM hS0 hSw hSL hSS halA hSA hA0 hA4 hA8 hAC hR hw
  ⟨m', st, q.imp_left And.right⟩

/-- `tufRoleKeysMet_ret_pi` without what it says of `a0` and `a1`. -/
theorem tufRoleKeysMet_correct_pi (m : Machine) {retAddr s R A MP SP : Word} {ML SL t : Nat} {es : List RkEntry}
    (hpc : m.pc = TRM) (ha0 : reg m a0 = R) (ha1 : reg m a1 = A) (hsp : reg m sp = s + BitVec.ofNat 32 0x3920)
    (hra : reg m ra = retAddr) (hret : retAddr &&& ~~~1 = retAddr) (hal : s.toNat % 16 = 0)
    (hlo : 0x3FC80000 ≤ s.toNat) (hhi : s.toNat + 0x3920 ≤ 0x3FCE0000)
    (hds : Sep s 0x3920 (BitVec.ofNat 32 (img% dataWindowAddress)) (img% dataWindowSize))
    (hro : Sep s 0x3920 (BitVec.ofNat 32 (img% roWindowAddress)) (img% roWindowSize))
    (hc : ∀ M : Word → BitVec 8, (∀ x, Sep x 1 s 0x3920 → M x = m.mem x) → RmCode M)
    (halR : R.toNat % 4 = 0) (hRw : R.toNat + 0x540 ≤ 0x40000000) (hSR : Sep s 0x3920 R 0x540)
    (hMw : MP.toNat + ML ≤ 0x40000000) (hML : ML < 2 ^ 31) (hSM : Sep s 0x3920 MP ML)
    (hS0 : SP.toNat ≠ 0) (hSw : SP.toNat + SL ≤ 0x40000000) (hSL : SL < 2 ^ 31) (hSS : Sep s 0x3920 SP SL)
    (halA : A.toNat % 4 = 0) (hSA : Sep s 0x3920 A 16) (hA0 : memLoad32 m.mem A = MP)
    (hA4 : memLoad32 m.mem (A + BitVec.ofNat 32 4) = BitVec.ofNat 32 ML)
    (hA8 : memLoad32 m.mem (A + BitVec.ofNat 32 8) = SP)
    (hAC : memLoad32 m.mem (A + BitVec.ofNat 32 12) = BitVec.ofNat 32 SL) (hR : RkAt m.mem R t es) (hw : RkWf es) :
    ∃ m', Steps m m' ∧
      (rmHI m'.pc m'.mem (reg m') ∨
        (m'.pc = retAddr ∧ (∀ x, Sep x 1 s 0x3920 → m'.mem x = m.mem x) ∧ (∀ r, r ∉ jClob → reg m' r = reg m r) ∧
          (reg m' a0 = 0 → reg m' a1 ≠ 0 →
            MetSound (memBytes m.mem SP SL) (memBytes m.mem MP ML) t (es.map nbE)))) :=
  let ⟨m', st, q⟩ := tufRoleKeysMet_ret_pi m hpc ha0 ha1 hsp hra hret hal hlo hhi hds hro hc halR hRw hSR hMw hML
    hSM hS0 hSw hSL hSS halA hSA hA0 hA4 hA8 hAC hR hw
  ⟨m', st, q.imp id fun h => ⟨h.1, h.2.1, h.2.2.1, h.2.2.2.1⟩⟩

/-- `tufRoleKeysMet_ret` without what it says of `a0` and `a1`. -/
theorem tufRoleKeysMet_correct (m : Machine) {retAddr s R A MP SP : Word} {ML SL t : Nat} {es : List RkEntry}
    (hpc : m.pc = TRM) (ha0 : reg m a0 = R) (ha1 : reg m a1 = A) (hsp : reg m sp = s + BitVec.ofNat 32 0x3920)
    (hra : reg m ra = retAddr) (hret : retAddr &&& ~~~1 = retAddr) (hal : s.toNat % 16 = 0)
    (hlo : 0x3FC80000 ≤ s.toNat) (hhi : s.toNat + 0x3920 ≤ 0x3FCE0000)
    (hds : Sep s 0x3920 (BitVec.ofNat 32 (img% dataWindowAddress)) (img% dataWindowSize))
    (hro : Sep s 0x3920 (BitVec.ofNat 32 (img% roWindowAddress)) (img% roWindowSize))
    (hc : ∀ M : Word → BitVec 8, (∀ x, Sep x 1 s 0x3920 → M x = m.mem x) → RmCode M)
    (halR : R.toNat % 4 = 0) (hRw : R.toNat + 0x540 ≤ 0x40000000) (hSR : Sep s 0x3920 R 0x540)
    (hMw : MP.toNat + ML ≤ 0x40000000) (hML : ML < 2 ^ 31) (hSM : Sep s 0x3920 MP ML)
    (hS0 : SP.toNat ≠ 0) (hSw : SP.toNat + SL ≤ 0x40000000) (hSL : SL < 2 ^ 31) (hSS : Sep s 0x3920 SP SL)
    (halA : A.toNat % 4 = 0) (hSA : Sep s 0x3920 A 16) (hA0 : memLoad32 m.mem A = MP)
    (hA4 : memLoad32 m.mem (A + BitVec.ofNat 32 4) = BitVec.ofNat 32 ML)
    (hA8 : memLoad32 m.mem (A + BitVec.ofNat 32 8) = SP)
    (hAC : memLoad32 m.mem (A + BitVec.ofNat 32 12) = BitVec.ofNat 32 SL) (hR : RkAt m.mem R t es) (hw : RkWf es) :
    ∃ m', Steps m m' ∧
      (rmH m'.pc m'.mem (reg m') ∨
        (m'.pc = retAddr ∧ (∀ x, Sep x 1 s 0x3920 → m'.mem x = m.mem x) ∧ (∀ r, r ∉ jClob → reg m' r = reg m r) ∧
          (reg m' a0 = 0 → reg m' a1 ≠ 0 →
            MetSound (memBytes m.mem SP SL) (memBytes m.mem MP ML) t (es.map nbE)))) :=
  let ⟨m', st, q⟩ := tufRoleKeysMet_correct_pi m hpc ha0 ha1 hsp hra hret hal hlo hhi hds hro hc halR hRw hSR hMw hML
    hSM hS0 hSw hSL hSS halA hSA hA0 hA4 hA8 hAC hR hw
  ⟨m', st, q.imp_left And.right⟩

end

end C3.RV32
