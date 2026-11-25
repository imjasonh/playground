import C3BootProofs.Proofs.TrustedRootReadChainLoop

/-!
# The end of `read_chain`

The loop by induction on its fuel, and the code from 0x4D8 that runs after
it: `next_element` must find the end of the `certificates` array, a first
certificate must exist, and the result goes to `out`.
-/

namespace C3.RV32

open C3.Image C3.Json C3.RV32.Dq C3.RV32.P3

set_option maxRecDepth 20000

theorem rc_ze8 : ∀ b : BitVec 8, (b.zeroExtend 32).extractLsb' 0 8 = b := by decide

theorem rc_cpIn {M : Word → BitVec 8} {dst src : Word} {N i : Nat} (hi : i < N) (hN : N < 2 ^ 32) :
    copyBytes M dst src N (dst + BitVec.ofNat 32 i) = M (src + BitVec.ofNat 32 i) := by
  have e : dst + BitVec.ofNat 32 i - dst = BitVec.ofNat 32 i := by rw [BitVec.add_comm, BitVec.add_sub_cancel]
  unfold copyBytes
  rw [e, ite_eq_left (by rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega)]; exact hi)]

theorem rc_ld2 {M M' : Word → BitVec 8} {b b' : Word}
    (h : ∀ j, j < 4 → M (b + BitVec.ofNat 32 j) = M' (b' + BitVec.ofNat 32 j)) :
    memLoad32 M b = memLoad32 M' b' := by
  unfold memLoad32
  have h0 := h 0 (by decide)
  rw [add_ofNat_zero, add_ofNat_zero] at h0
  rw [h0, show b + 1 = b + BitVec.ofNat 32 1 from rfl, h 1 (by decide),
    show b + 2 = b + BitVec.ofNat 32 2 from rfl, h 2 (by decide),
    show b + 3 = b + BitVec.ofNat 32 3 from rfl, h 3 (by decide)]
  rfl

section
variable {M0 : Word → BitVec 8} {G F out fr fp p : Word} {fl n : Nat} {g0 : Fin 32 → Word}

/-- The return through the epilogue when, since `M`, only `out` and the
16 bytes below the frame changed. -/
theorem RcCtx.exitS (X : RcCtx M0 G F out fr fp fl p n g0) {M Mf : Word → BitVec 8} {f : Fin 32 → Word}
    {r : Except (Option Nat) (RcCert × RcSt)} (hR : RcRegs F out fr g0 f) (hI : RcMemInv M0 G F fr fp fl g0 M)
    (hO : ∀ x, Sep x 1 out 0x40 → Sep (G + BitVec.ofNat 32 0x5B0) 16 x 1 → Mf x = M x)
    (hr : RcOut Mf out fr fp fl r) :
    WP trustedRootReadChainCode TRC (trPost (rcMem M0 G out fr fp fl r) g0) Mf 0x48C f := by
  classical
  refine X.exit (M := fun x => if Sep x 1 out 0x40 then Mf x else M x) hR
    (hI.step X (c := 0x5B0) (l := 16) (by decide) fun x hs _ _ => ?_) (fun x hx => by simp only [hx, ↓reduceIte]) hr
  by_cases h : Sep x 1 out 0x40
  · simp only [h, ↓reduceIte]; exact hO x h hs
  · simp only [h, ↓reduceIte]

/-- The `memcpy` at `off` of the 0x2B bytes at `F + 0x35` to `out + 5`. -/
theorem RcCtx.callMcO (X : RcCtx M0 G F out fr fp fl p n g0) {M : Word → BitVec 8} {f : Fin 32 → Word}
    {Q : Post} {off : Nat} {hi lo : Word}
    (h1 : fetchRel trustedRootReadChainCode off = some (.auipc ra hi, 4))
    (h2 : fetchRel trustedRootReadChainCode (off + 4) = some (.jalr ra ra lo, 4))
    (htgt : (TRC + BitVec.ofNat 32 off + hi + lo) &&& ~~~1 = BMS)
    (hev : (TRC + BitVec.ofNat 32 (off + 8)) &&& ~~~1 = TRC + BitVec.ofNat 32 (off + 8))
    (hR : RcRegs F out fr g0 f) (hI : RcMemInv M0 G F fr fp fl g0 M)
    (ha0 : f a0 = out + BitVec.ofNat 32 5) (ha1 : f a1 = F + BitVec.ofNat 32 0x35)
    (ha2 : f a2 = BitVec.ofNat 32 0x2B)
    (k : ∀ m2 : Machine, (∀ x, Sep (G + BitVec.ofNat 32 0x5B0) 16 x 1 →
        m2.mem x = copyBytes M (out + BitVec.ofNat 32 5) (F + BitVec.ofNat 32 0x35) 0x2B x) →
      WP trustedRootReadChainCode TRC Q m2.mem (off + 8) (clob (upd f ra (TRC + BitVec.ofNat 32 (off + 8))) m2 jClob)) :
    WP trustedRootReadChainCode TRC Q M off f := by
  have gw := X.gw
  have ow := X.ow
  have eG : F + 0xFFFFFFF0 = G + BitVec.ofNat 32 0x5B0 := X.fneg (k := 16) (by decide) (by decide)
  have o5 : (out + BitVec.ofNat 32 5).toNat = out.toNat + 5 := by
    rw [BitVec.toNat_add, BitVec.toNat_ofNat]; omega
  have hd : Sep (out + BitVec.ofNat 32 5) 0x2B (G + BitVec.ofNat 32 0x5B0) 16 :=
    (X.og.sub (c := 5) (l := 0x2B) (by decide)).subR (by decide)
  have hs : Sep (F + BitVec.ofNat 32 0x35) 0x2B (G + BitVec.ofNat 32 0x5B0) 16 := by
    rw [X.fG]; exact X.gsep (Or.inr (by decide)) (by decide) (by decide)
  have hsd : Sep (out + BitVec.ofNat 32 5) 0x2B (F + BitVec.ofNat 32 0x35) 0x2B := by
    rw [X.fG]; exact (X.og.sub (c := 5) (l := 0x2B) (by decide)).subR (by decide)
  refine WP.trCallSaved (P := fun m2 => ∀ x, Sep (G + BitVec.ofNat 32 0x5B0) 16 x 1 →
      m2.mem x = copyBytes M (out + BitVec.ofNat 32 5) (F + BitVec.ofNat 32 0x35) 0x2B x)
    h1 h2 htgt (fun m1 hpc1 hmem1 hreg1 _ => ?_) (fun m2 hP hc => ?_) k
  · have C := X.codeAt hI
    have hs1 : reg m1 sp = F := by rw [hreg1]; trsimp; exact hR.2.1
    obtain ⟨m2, c2, pc2, hsp2, -, hcp, fr'⟩ := memcpy_correct m1 BMS (TRC + BitVec.ofNat 32 (off + 8))
      (out + BitVec.ofNat 32 5) (F + BitVec.ofNat 32 0x35) 0x2B
      (fun i hi => by show m1.mem _ = _; rw [hmem1]; exact C.dec.stub i hi)
      (by decide) hpc1 (by rw [hreg1]; trsimp; exact ha0) (by rw [hreg1]; trsimp; exact ha1)
      (by rw [hreg1]; trsimp; exact ha2) (by rw [hreg1]; trsimp) hev
      (by
        rw [hs1, eG, hmem1]
        exact ⟨by rw [show BMS + 8 = BMB from by decide]; exact C.dec.body,
          tr_lowAt (c := 5) (by omega) (by decide) (by decide), X.glo (by decide) (by decide) (by decide),
          hd, hs, hsd, X.ga4 (by decide) (by decide), by rw [X.gc (by decide)]; omega,
          by rw [o5]; omega, by rw [X.fG, X.gc (by omega)]; omega⟩)
    rw [hs1, eG, hmem1] at hcp
    refine ⟨m2, c2, pc2, hcp, hsp2, fun q hq => ?_⟩
    obtain ⟨e1, e2, e3, e4, e5, e6, e7, e8, e9, e10, e11, e12, e13, e14⟩ := rc_mc_saved q hq
    exact fr' q e1 e2 e3 e4 e5 e6 e7 e8 e9 e10 e11 e12 e13 e14
  · exact hc.hi (fun x hx => by
      rw [hP x (lowSep (by rw [X.gc (by decide)]; omega) hx (by have := x.isLt; omega))]
      exact copyBytes_sep (n := 0x2B) (lowSep (by rw [o5]; omega) hx (by have := x.isLt; omega)) (Nat.le_refl _))
      (by decide) (by decide)

/-- The memory after the stores from 0x52A: `RcOut` for the first
certificate, which the frame held at `F + 0x30`, and the window. -/
theorem RcCtx.finOut (X : RcCtx M0 G F out fr fp fl p n g0) {mB m3 : Word → BitVec 8} {c : RcCert} {s : RcSt}
    {a0 a4 a30 a34 a38 a3C v0 v30 v34 v38 v3C : Word} {v4 : BitVec 8}
    (e0 : a0 = out) (e4 : a4 = out + BitVec.ofNat 32 4) (e30 : a30 = out + BitVec.ofNat 32 0x30)
    (e34 : a34 = out + BitVec.ofNat 32 0x34) (e38 : a38 = out + BitVec.ofNat 32 0x38)
    (e3C : a3C = out + BitVec.ofNat 32 0x3C)
    (ev0 : v0 = memLoad32 mB (F + BitVec.ofNat 32 0x30)) (ev4 : v4 = mB (F + BitVec.ofNat 32 0x34))
    (ev30 : v30 = BitVec.ofNat 32 (s.nb % 2 ^ 32)) (ev34 : v34 = BitVec.ofNat 32 (s.nb / 2 ^ 32))
    (ev38 : v38 = BitVec.ofNat 32 (s.na % 2 ^ 32)) (ev3C : v3C = BitVec.ofNat 32 (s.na / 2 ^ 32))
    (hc : ∀ x, Sep (G + BitVec.ofNat 32 0x5B0) 16 x 1 →
      m3 x = copyBytes mB (out + BitVec.ofNat 32 5) (F + BitVec.ofNat 32 0x35) 0x2B x)
    (hF : RcRec mB (F + BitVec.ofNat 32 0x30) c) (hB : RcBuf mB fr fp fl s.dec) (hnb : s.nb < 2 ^ 64)
    (hna : s.na < 2 ^ 64) :
    (∀ x, Sep x 1 out 0x40 → Sep (G + BitVec.ofNat 32 0x5B0) 16 x 1 →
      memStore32 (memStore32 (memStore32 (memStore32 (memStore8 (memStore32 m3 a0 v0) a4 v4) a30 v30) a34 v34)
        a38 v38) a3C v3C x = mB x) ∧
    RcOut (memStore32 (memStore32 (memStore32 (memStore32 (memStore8 (memStore32 m3 a0 v0) a4 v4) a30 v30) a34 v34)
        a38 v38) a3C v3C) out fr fp fl (.ok (c, s)) := by
  subst a0 a4 a30 a34 a38 a3C v0 v4 v30 v34 v38 v3C
  have ow := X.ow
  have sOO : ∀ c d : Nat, c + 4 ≤ d ∨ d + 4 ≤ c → c + 4 ≤ 0x40 → d + 4 ≤ 0x40 →
      Sep (out + BitVec.ofNat 32 c) 4 (out + BitVec.ofNat 32 d) 4 := fun c d h hc hd =>
    sep_offsets out h (by omega) (by omega)
  have hOut : ∀ x, Sep x 1 out 0x40 →
      memStore32 (memStore32 (memStore32 (memStore32 (memStore8 (memStore32 m3 out
        (memLoad32 mB (F + BitVec.ofNat 32 0x30))) (out + BitVec.ofNat 32 4) (mB (F + BitVec.ofNat 32 0x34)))
        (out + BitVec.ofNat 32 0x30) (BitVec.ofNat 32 (s.nb % 2 ^ 32))) (out + BitVec.ofNat 32 0x34)
        (BitVec.ofNat 32 (s.nb / 2 ^ 32))) (out + BitVec.ofNat 32 0x38) (BitVec.ofNat 32 (s.na % 2 ^ 32)))
        (out + BitVec.ofNat 32 0x3C) (BitVec.ofNat 32 (s.na / 2 ^ 32)) x = m3 x := fun x hx => by
    rw [memStore32_get_sep (hx.symm.sub (c := 0x3C) (l := 4) (by decide)),
      memStore32_get_sep (hx.symm.sub (c := 0x38) (l := 4) (by decide)),
      memStore32_get_sep (hx.symm.sub (c := 0x34) (l := 4) (by decide)),
      memStore32_get_sep (hx.symm.sub (c := 0x30) (l := 4) (by decide)),
      memStore8_ne (fun h => hx 0 (by decide) 4 (by decide) (by rw [add_ofNat_zero]; exact h)),
      memStore32_get_sep (hx.rcSub0 (l := 4) (by decide)).symm]
  have part1 : ∀ x, Sep x 1 out 0x40 → Sep (G + BitVec.ofNat 32 0x5B0) 16 x 1 →
      memStore32 (memStore32 (memStore32 (memStore32 (memStore8 (memStore32 m3 out
        (memLoad32 mB (F + BitVec.ofNat 32 0x30))) (out + BitVec.ofNat 32 4) (mB (F + BitVec.ofNat 32 0x34)))
        (out + BitVec.ofNat 32 0x30) (BitVec.ofNat 32 (s.nb % 2 ^ 32))) (out + BitVec.ofNat 32 0x34)
        (BitVec.ofNat 32 (s.nb / 2 ^ 32))) (out + BitVec.ofNat 32 0x38) (BitVec.ofNat 32 (s.na % 2 ^ 32)))
        (out + BitVec.ofNat 32 0x3C) (BitVec.ofNat 32 (s.na / 2 ^ 32)) x = mB x := fun x hx hs => by
    rw [hOut x hx, hc x hs]
    exact copyBytes_sep (n := 0x2B) (hx.symm.sub (c := 5) (l := 0x2B) (by decide)) (Nat.le_refl _)
  refine ⟨part1, ?_⟩
  have hlate : ∀ k, k + 4 ≤ 0x30 →
      memLoad32 (memStore32 (memStore32 (memStore32 (memStore32 (memStore8 (memStore32 m3 out
        (memLoad32 mB (F + BitVec.ofNat 32 0x30))) (out + BitVec.ofNat 32 4) (mB (F + BitVec.ofNat 32 0x34)))
        (out + BitVec.ofNat 32 0x30) (BitVec.ofNat 32 (s.nb % 2 ^ 32))) (out + BitVec.ofNat 32 0x34)
        (BitVec.ofNat 32 (s.nb / 2 ^ 32))) (out + BitVec.ofNat 32 0x38) (BitVec.ofNat 32 (s.na % 2 ^ 32)))
        (out + BitVec.ofNat 32 0x3C) (BitVec.ofNat 32 (s.na / 2 ^ 32))) (out + BitVec.ofNat 32 k) =
      memLoad32 (memStore8 (memStore32 m3 out (memLoad32 mB (F + BitVec.ofNat 32 0x30)))
        (out + BitVec.ofNat 32 4) (mB (F + BitVec.ofNat 32 0x34))) (out + BitVec.ofNat 32 k) := fun k hk => by
    rw [memLoad32_store32_sep (sOO 0x3C k (Or.inr (by omega)) (by decide) (by omega)),
      memLoad32_store32_sep (sOO 0x38 k (Or.inr (by omega)) (by decide) (by omega)),
      memLoad32_store32_sep (sOO 0x34 k (Or.inr (by omega)) (by decide) (by omega)),
      memLoad32_store32_sep (sOO 0x30 k (Or.inr (by omega)) (by decide) (by omega))]
  have bi : ∀ i, 5 ≤ i → i < 0x30 →
      memStore8 (memStore32 m3 out (memLoad32 mB (F + BitVec.ofNat 32 0x30))) (out + BitVec.ofNat 32 4)
        (mB (F + BitVec.ofNat 32 0x34)) (out + BitVec.ofNat 32 i) = mB (F + BitVec.ofNat 32 (0x30 + i)) := by
    intro i h5 hi
    have s0 : Sep out 4 (out + BitVec.ofNat 32 i) 1 := by
      have := sep_offsets out (c := 0) (n := 4) (d := i) (k := 1) (Or.inl (by omega)) (by decide) (by omega)
      rwa [add_ofNat_zero] at this
    rw [memStore8_ne (add_ofNat_ne out (by omega) (by omega) (by omega)), memStore32_get_sep s0,
      hc _ ((X.og.sub (c := i) (l := 1) (by omega)).subR (c := 0x5B0) (l := 16) (by decide)).symm,
      show out + BitVec.ofNat 32 i = out + BitVec.ofNat 32 5 + BitVec.ofNat 32 (i - 5) by
        rw [add_ofNat_assoc, show 5 + (i - 5) = i by omega],
      rc_cpIn (by omega) (by decide), add_ofNat_assoc, show 0x35 + (i - 5) = 0x30 + i by omega]
  have hRec : RcRec (memStore32 (memStore32 (memStore32 (memStore32 (memStore8 (memStore32 m3 out
        (memLoad32 mB (F + BitVec.ofNat 32 0x30))) (out + BitVec.ofNat 32 4) (mB (F + BitVec.ofNat 32 0x34)))
        (out + BitVec.ofNat 32 0x30) (BitVec.ofNat 32 (s.nb % 2 ^ 32))) (out + BitVec.ofNat 32 0x34)
        (BitVec.ofNat 32 (s.nb / 2 ^ 32))) (out + BitVec.ofNat 32 0x38) (BitVec.ofNat 32 (s.na % 2 ^ 32)))
        (out + BitVec.ofNat 32 0x3C) (BitVec.ofNat 32 (s.na / 2 ^ 32))) out c := by
    have := hF.copy (R' := out) fun k hk4 hk => by
      rw [hlate k (by omega)]
      rcases Nat.eq_zero_or_pos k with rfl | hpos
      · have s4 : Sep (out + BitVec.ofNat 32 4) 1 out 4 := by
          have := sep_offsets out (c := 4) (n := 1) (d := 0) (k := 4) (Or.inr (by decide)) (by decide) (by decide)
          rwa [add_ofNat_zero] at this
        rw [add_ofNat_zero, add_ofNat_zero, memLoad32_store8_sep s4, memLoad32_store32_same]
      · refine rc_ld2 fun j hj => ?_
        rw [add_ofNat_assoc out, add_ofNat_assoc F 0x30 k, add_ofNat_assoc F]
        by_cases h4 : k + j = 4
        · rw [h4, memStore8_same, show 0x30 + k + j = 0x34 by omega]
        · rw [bi (k + j) (by omega) (by omega), show 0x30 + (k + j) = 0x30 + k + j by omega]
    exact this
  have sB : ∀ x, Sep G 0x740 x 1 → Sep (G + BitVec.ofNat 32 0x5B0) 16 x 1 := fun x h => h.sub (by decide)
  obtain ⟨r0, r4, r8, rC, r10, r14, r18, r1C, r20, r24, r28, rnb, rna, -⟩ := hRec
  refine ⟨by rw [add_ofNat_zero] at r0; exact r0, r4, r8, rC, r10, r14, r18, r1C, r20, r24, r28, ?_, ?_, ?_, ?_,
    rnb, rna, hnb, hna, hB.1, ?_, ?_, ?_⟩
  · show memLoad32 _ (out + BitVec.ofNat 32 0x30) = _
    rw [memLoad32_store32_sep (sOO 0x3C 0x30 (Or.inr (by decide)) (by decide) (by decide)),
      memLoad32_store32_sep (sOO 0x38 0x30 (Or.inr (by decide)) (by decide) (by decide)),
      memLoad32_store32_sep (sOO 0x34 0x30 (Or.inr (by decide)) (by decide) (by decide)),
      memLoad32_store32_same]
  · show memLoad32 _ (out + BitVec.ofNat 32 0x34) = _
    rw [memLoad32_store32_sep (sOO 0x3C 0x34 (Or.inr (by decide)) (by decide) (by decide)),
      memLoad32_store32_sep (sOO 0x38 0x34 (Or.inr (by decide)) (by decide) (by decide)),
      memLoad32_store32_same]
  · show memLoad32 _ (out + BitVec.ofNat 32 0x38) = _
    rw [memLoad32_store32_sep (sOO 0x3C 0x38 (Or.inr (by decide)) (by decide) (by decide)),
      memLoad32_store32_same]
  · exact memLoad32_store32_same _ _ _
  · exact (memLoad32_congr fun j hj => part1 _ (sep_pt X.ofr (by omega))
      (sB _ (sep_pt X.frg.symm (by omega)).symm)).trans hB.2.1
  · exact (memLoad32_congr fun j hj => part1 _ (sep_pt (X.ofr.subR (c := 4) (l := 4) (by decide)) hj)
      (sB _ (sep_pt (X.frg.symm.subR (c := 4) (l := 4) (by decide)) hj).symm)).trans hB.2.2.1
  · exact (memBytes_congr fun j hj => part1 _ (sep_pt (X.ofp.rcSub0 hB.1) hj)
      (sB _ (sep_pt (X.bg.symm.rcSub0 (by have := hB.1; omega)) hj).symm)).trans hB.2.2.2

/-- The return with the result of `finOut`. -/
theorem RcCtx.finExit (X : RcCtx M0 G F out fr fp fl p n g0) {mB m3 : Word → BitVec 8} {f : Fin 32 → Word}
    {c : RcCert} {s : RcSt} {a0 a4 a30 a34 a38 a3C v0 v30 v34 v38 v3C : Word} {v4 : BitVec 8}
    (hR : RcRegs F out fr g0 f) (hI : RcMemInv M0 G F fr fp fl g0 mB)
    (e0 : a0 = out) (e4 : a4 = out + BitVec.ofNat 32 4) (e30 : a30 = out + BitVec.ofNat 32 0x30)
    (e34 : a34 = out + BitVec.ofNat 32 0x34) (e38 : a38 = out + BitVec.ofNat 32 0x38)
    (e3C : a3C = out + BitVec.ofNat 32 0x3C)
    (ev0 : v0 = memLoad32 mB (F + BitVec.ofNat 32 0x30)) (ev4 : v4 = mB (F + BitVec.ofNat 32 0x34))
    (ev30 : v30 = BitVec.ofNat 32 (s.nb % 2 ^ 32)) (ev34 : v34 = BitVec.ofNat 32 (s.nb / 2 ^ 32))
    (ev38 : v38 = BitVec.ofNat 32 (s.na % 2 ^ 32)) (ev3C : v3C = BitVec.ofNat 32 (s.na / 2 ^ 32))
    (hc : ∀ x, Sep (G + BitVec.ofNat 32 0x5B0) 16 x 1 →
      m3 x = copyBytes mB (out + BitVec.ofNat 32 5) (F + BitVec.ofNat 32 0x35) 0x2B x)
    (hF : RcRec mB (F + BitVec.ofNat 32 0x30) c) (hB : RcBuf mB fr fp fl s.dec) (hnb : s.nb < 2 ^ 64)
    (hna : s.na < 2 ^ 64) :
    WP trustedRootReadChainCode TRC (trPost (rcMem M0 G out fr fp fl (.ok (c, s))) g0)
      (memStore32 (memStore32 (memStore32 (memStore32 (memStore8 (memStore32 m3 a0 v0) a4 v4) a30 v30) a34 v34)
        a38 v38) a3C v3C) 0x48C f :=
  have h := X.finOut e0 e4 e30 e34 e38 e3C ev0 ev4 ev30 ev34 ev38 ev3C hc hF hB hnb hna
  X.exitS hR hI h.1 h.2

/-- From 0x4D8, after the loop: `next_element` must find the end of the
array, and the first certificate goes to `out` with the window. -/
theorem RcCtx.pFin (X : RcCtx M0 G F out fr fp fl p n g0) {M : Word → BitVec 8} {f : Fin 32 → Word}
    {r : Except (Option Nat) (RcCert × RcSt)} {ap : Word} {an k : Nat} {s : RcSt}
    (hInv : RcLoopInv M0 G F out fr fp fl g0 ap an k s M f) (hA : RcIn p n ap an)
    (hr : r = rcFinish M0 ap an s) :
    WP trustedRootReadChainCode TRC (trPost (rcMem M0 G out fr fp fl r) g0) M 0x4D8 f := by
  obtain ⟨hR, hI, hW, _, _, _, _, _, hm24, hm28, hm2C, hpos, hF, hB⟩ := hInv
  obtain ⟨hA0, hAw⟩ := X.inW hA
  have oA : ∀ c, c % 4 = 0 → c + 4 ≤ 0x40 → (out + BitVec.ofNat 32 c).toNat % 4 = 0 := fun c h4 _ =>
    aligned_add X.oa h4
  have oS : ∀ c k, c + k ≤ 0x40 → Sep (out + BitVec.ofNat 32 c) k TRC trustedRootReadChainCode.length :=
    fun c k h => tr_lowAt (by have := X.ow; omega) (by decide) (by decide)
  refine WP.aluImm trc_at_4d8 ?_; wn
  refine WP.aluImm trc_at_4da ?_; wn
  refine X.callNext (off := 0x4DC) trc_at_4dc trc_at_4e0 (by decide) (by decide) (by rc_r hR) hI
    (by trsimp; rw [hR.2.1]; rfl) (by trsimp; rw [hR.2.1]; rfl) hm24 hm28 hm2C (by omega) hpos hA0 (by omega)
    (X.inG hA) (X.inM hI hA) (fun m2 hI2 hE => ?_)
  obtain ⟨M1, hK1, hER⟩ := hE
  refine WP.lbu trc_at_4e4 ?_; wn
  rcases hn : nextElement (memBytes M0 ap an) s.pos with _ | _ | ⟨st, len, after⟩
  · rw [hn] at hER
    change ElemRes M1 m2.mem _ _ none at hER
    have hE0 : m2.mem (F + 0xE0) = 1 := hER.2.1
    refine WP.branch trc_at_4e8 (fun _ => ?_) (fun hf => absurd hf (by trsimp; rw [hR.2.1, hE0]; decide)); wn
    exact X.e068 (e := some 0x20) (by rw [hr]; simp only [rcFinish, hn]) (by rc_r hR) hI2 (fun b hb => by
      cases hb; exact (congrArg m2.mem (add_ofNat_assoc F 0xE0 1)).symm.trans hER.2.2)
  · rw [hn] at hER
    change ElemRes M1 m2.mem _ _ (some none) at hER
    have hE0 : m2.mem (F + 0xE0) = 0 := hER.2.1
    have hE4 : memLoad32 m2.mem (F + 0xE4) = 0 := by have := hER.2.2; rw [rc_a4] at this; exact this
    refine WP.branch trc_at_4e8 (fun ht => absurd ht (by trsimp; rw [hR.2.1, hE0]; decide)) (fun _ => ?_); wn
    refine WP.lw trc_at_4ec (by (try trsimp); rw [hR.2.1]; exact X.fal (c := 0xE4) (by decide)) ?_; wn
    refine WP.branch trc_at_4ee (fun _ => ?_) (fun hf => absurd hf (by trsimp; rw [hR.2.1, hE4]; decide)); wn
    have hFL : RcFL F M m2.mem := (X.flKeep hK1).trans fun j a b => hER.1 _ (by
      rw [X.fG, X.fG]; exact X.gsep (Or.inl (by omega)) (by omega) (by omega))
    have hG : RcG G M m2.mem := hK1.g.trans fun x hx => hER.1 x (by rw [X.fG]; exact sep_in hx.symm (by decide))
    have hFB := hFL.first hF
    have hBB := X.bufG hB hG
    refine WP.lw trc_at_50e (by (try trsimp); rw [hR.2.1]; exact X.fal (c := 0x30) (by decide)) ?_; wn
    rcases hfs : s.first with _ | c
    · rw [hfs] at hFB
      have hS0 : memLoad32 m2.mem (F + 0x30) = 0 := hFB
      refine WP.branch trc_at_510 (fun _ => ?_) (fun hf => absurd hf (by trsimp; rw [hR.2.1, hS0]; decide)); wn
      exact X.e4f0 (by rw [hr]; simp only [rcFinish, hn, hfs]) (by rc_r hR) hI2
    · rw [hfs] at hFB
      have hS0 : memLoad32 m2.mem (F + 0x30) = c.serial := by have := hFB.1; rw [add_ofNat_zero] at this; exact this
      refine WP.branch trc_at_510 (fun ht => absurd ht (by trsimp; rw [hR.2.1, hS0, rck_beqF hFB.2.2.2.2.2.2.2.2.2.2.2.2.2]; decide))
        (fun _ => ?_); wn
      refine WP.lbu trc_at_512 ?_; wn
      refine WP.aluImm trc_at_516 ?_; wn
      refine WP.aluImm trc_at_51a ?_; wn
      refine WP.aluImm trc_at_51e ?_; wn
      refine X.callMcO (off := 0x522) trc_at_522 trc_at_526 (by decide) (by decide) (by rc_r hR) hI2
        (by trsimp; rw [hR.2.2.1]; rfl) (by trsimp; rw [hR.2.1]; rfl) (by trsimp; (try rw [rc_x0 hR.1]); try rfl)
        (fun m3 hc => ?_)
      refine WP.sw trc_at_52a (by trsimp; rw [hR.2.2.1]; exact oA 0 (by decide) (by decide))
        (by trsimp; rw [hR.2.2.1]; exact oS 0 4 (by decide)) ?_; wn
      refine WP.sb trc_at_52e (by trsimp; rw [hR.2.2.1]; exact oS 4 1 (by decide)) ?_; wn
      refine WP.sw trc_at_532 (by trsimp; rw [hR.2.2.1]; exact oA 0x30 (by decide) (by decide))
        (by trsimp; rw [hR.2.2.1]; exact oS 0x30 4 (by decide)) ?_; wn
      refine WP.sw trc_at_536 (by trsimp; rw [hR.2.2.1]; exact oA 0x34 (by decide) (by decide))
        (by trsimp; rw [hR.2.2.1]; exact oS 0x34 4 (by decide)) ?_; wn
      refine WP.sw trc_at_53a (by trsimp; rw [hR.2.2.1]; exact oA 0x38 (by decide) (by decide))
        (by trsimp; rw [hR.2.2.1]; exact oS 0x38 4 (by decide)) ?_; wn
      refine WP.sw trc_at_53e (by trsimp; rw [hR.2.2.1]; exact oA 0x3C (by decide) (by decide))
        (by trsimp; rw [hR.2.2.1]; exact oS 0x3C 4 (by decide)) ?_; wn
      refine WP.jal trc_at_542 (by decide) ?_; wn
      have hr2 : r = .ok (c, s) := by rw [hr]; simp only [rcFinish, hn, hfs]
      subst hr2
      refine X.finExit (by rc_r hR) hI2 ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ hc hFB hBB hW.2.2.2.2.1 hW.2.2.2.2.2
      · (try trsimp); rw [hR.2.2.1]; exact add_ofNat_zero out
      · (try trsimp); rw [hR.2.2.1]; rfl
      · (try trsimp); rw [hR.2.2.1]; rfl
      · (try trsimp); rw [hR.2.2.1]; rfl
      · (try trsimp); rw [hR.2.2.1]; rfl
      · (try trsimp); rw [hR.2.2.1]; rfl
      · (try trsimp); rw [hR.2.1]; rfl
      · (try trsimp); rw [hR.2.1]; exact rc_ze8 _
      · (try trsimp); exact hW.1
      · (try trsimp); exact hW.2.1
      · (try trsimp); exact hW.2.2.1
      · (try trsimp); exact hW.2.2.2.1
  · rw [hn] at hER
    change ElemRes M1 m2.mem _ _ (some (some (ap + BitVec.ofNat 32 st, len, after))) at hER
    obtain ⟨hbd1, hbd2⟩ := rc_nextBd hn
    rw [memBytes_length] at hbd1 hbd2
    have hq : RcIn p n (ap + BitVec.ofNat 32 st) len := hA.sub (by omega)
    obtain ⟨hq0, hqw⟩ := X.inW hq
    have hq0' : ap + BitVec.ofNat 32 st ≠ 0 := fun h => hq0 (by rw [h]; rfl)
    have hE0 : m2.mem (F + 0xE0) = 0 := hER.2.1
    have hE4 : memLoad32 m2.mem (F + 0xE4) = ap + BitVec.ofNat 32 st := by
      have := hER.2.2.1; rw [rc_a4] at this; exact this
    refine WP.branch trc_at_4e8 (fun ht => absurd ht (by trsimp; rw [hR.2.1, hE0]; decide)) (fun _ => ?_); wn
    refine WP.lw trc_at_4ec (by (try trsimp); rw [hR.2.1]; exact X.fal (c := 0xE4) (by decide)) ?_; wn
    refine WP.branch trc_at_4ee (fun ht => absurd ht (by trsimp; rw [hR.2.1, hE4, rck_beqF hq0']; decide))
      (fun _ => ?_); wn
    exact X.e4f0 (by rw [hr]; simp only [rcFinish, hn]) (by rc_r hR) hI2

/-- The loop from its top at 0xFA with `k` passes of fuel left, then the
end of `read_chain`. -/
theorem RcCtx.pLoop (X : RcCtx M0 G F out fr fp fl p n g0) {r : Except (Option Nat) (RcCert × RcSt)}
    {ap : Word} {an : Nat} (hA : RcIn p n ap an) :
    ∀ k, 1 ≤ k → k ≤ 4 → ∀ (s : RcSt) (M : Word → BitVec 8) (f : Fin 32 → Word),
      RcLoopInv M0 G F out fr fp fl g0 ap an k s M f → r = rcLoopFin M0 fp fl ap an k s →
      WP trustedRootReadChainCode TRC (trPost (rcMem M0 G out fr fp fl r) g0) M 0xFA f
  | 0, h1, _ => absurd h1 (by decide)
  | k + 1, _, h4 => fun s M f hInv hr =>
    X.pFront hInv ⟨by omega, h4⟩ hA hr
      (fun s' M' f' hInv' hk0 hr' => X.pLoop hA k (by omega) (by omega) s' M' f' hInv' hr')
      (fun _ _ _ _ hInv' hr' => X.pFin hInv' hA hr')

end

end C3.RV32
