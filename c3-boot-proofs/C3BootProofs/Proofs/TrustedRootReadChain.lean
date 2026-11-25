import C3BootProofs.Proofs.TrustedRootReadChainHead
import C3BootProofs.Proofs.TrustedRootReadChainErr

/-!
# `read_chain`

The prologue from 0x0 to 0x3B saves `ra` and `s0`–`s11` in the frame and
moves the arguments into saved registers. With `RcCtx.pHead` it gives the
whole function: from its entry with `a0 = out`, `a1 = p`, `a2 = n`, and
`a3 = fr`, it returns to `ra` with `readChainPos` at `out` and in the
scratch slice at `fr`, and changes no memory outside the stack region,
`out`, the scratch slice, and the buffer that the scratch slice names.
-/

namespace C3.RV32

open C3.Image C3.Json

set_option maxRecDepth 20000

/-- The 13 saves of the prologue, through `a4 = A`, which is `F + 0x100`. -/
def rcSave (M : Word → BitVec 8) (A r1 r8 r9 r18 r19 r20 r21 r22 r23 r24 r25 r26 r27 : Word) :
    Word → BitVec 8 :=
  memStore32 (memStore32 (memStore32 (memStore32 (memStore32 (memStore32 (memStore32 (memStore32
    (memStore32 (memStore32 (memStore32 (memStore32 (memStore32 M
    (A + BitVec.ofNat 32 0x7C) r1) (A + BitVec.ofNat 32 0x78) r8) (A + BitVec.ofNat 32 0x74) r9)
    (A + BitVec.ofNat 32 0x70) r18) (A + BitVec.ofNat 32 0x6C) r19) (A + BitVec.ofNat 32 0x68) r20)
    (A + BitVec.ofNat 32 0x64) r21) (A + BitVec.ofNat 32 0x60) r22) (A + BitVec.ofNat 32 0x5C) r23)
    (A + BitVec.ofNat 32 0x58) r24) (A + BitVec.ofNat 32 0x54) r25) (A + BitVec.ofNat 32 0x50) r26)
    (A + BitVec.ofNat 32 0x4C) r27

/-- Proves a load from a word that a run of word stores at other
offsets from the same base left alone. -/
macro "rc_slot" : tactic => `(tactic| (
  repeat refine trdc_slot _ _ (by decide) (by decide) (by decide) ?_
  exact memLoad32_store32_same _ _ _))

theorem rcOut_st {M M1 : Word → BitVec 8} {A v : Word} {c k : Nat} (h : Out M M1 A k) (hc : c + 4 ≤ k) :
    Out M (memStore32 M1 (A + BitVec.ofNat 32 c) v) A k :=
  h.trans (Out.upK rfl (out_store32 _ _ _) hc)

theorem rcSave_spec {M S : Word → BitVec 8} {A r1 r8 r9 r18 r19 r20 r21 r22 r23 r24 r25 r26 r27 : Word}
    (hS : S = rcSave M A r1 r8 r9 r18 r19 r20 r21 r22 r23 r24 r25 r26 r27) :
    Out M S A 0x80 ∧
      memLoad32 S (A + BitVec.ofNat 32 0x7C) = r1 ∧ memLoad32 S (A + BitVec.ofNat 32 0x78) = r8 ∧
      memLoad32 S (A + BitVec.ofNat 32 0x74) = r9 ∧ memLoad32 S (A + BitVec.ofNat 32 0x70) = r18 ∧
      memLoad32 S (A + BitVec.ofNat 32 0x6C) = r19 ∧ memLoad32 S (A + BitVec.ofNat 32 0x68) = r20 ∧
      memLoad32 S (A + BitVec.ofNat 32 0x64) = r21 ∧ memLoad32 S (A + BitVec.ofNat 32 0x60) = r22 ∧
      memLoad32 S (A + BitVec.ofNat 32 0x5C) = r23 ∧ memLoad32 S (A + BitVec.ofNat 32 0x58) = r24 ∧
      memLoad32 S (A + BitVec.ofNat 32 0x54) = r25 ∧ memLoad32 S (A + BitVec.ofNat 32 0x50) = r26 ∧
      memLoad32 S (A + BitVec.ofNat 32 0x4C) = r27 := by
  subst hS
  unfold rcSave
  refine ⟨?_, by rc_slot, by rc_slot, by rc_slot, by rc_slot, by rc_slot, by rc_slot, by rc_slot,
    by rc_slot, by rc_slot, by rc_slot, by rc_slot, by rc_slot, by rc_slot⟩
  repeat refine rcOut_st ?_ (by decide)
  exact fun _ _ => rfl

section
variable {M0 : Word → BitVec 8} {G F out fr fp p : Word} {fl n : Nat} {g0 : Fin 32 → Word}

/-- The whole function, from its entry with `a0 = out`, `a1 = p`,
`a2 = n`, and `a3 = fr`. -/
theorem RcCtx.entry (X : RcCtx M0 G F out fr fp fl p n g0) (h0 : g0 a0 = out) (h1 : g0 a1 = p)
    (h2 : g0 a2 = BitVec.ofNat 32 n) (h3 : g0 a3 = fr) :
    WP trustedRootReadChainCode TRC (trPost (rcMem M0 G out fr fp fl (readChainPos M0 p n fp fl)) g0) M0 0 g0 := by
  have ea : ∀ c d : Nat, c = 0x100 + d →
      F + BitVec.ofNat 32 c = F + BitVec.ofNat 32 0x100 + BitVec.ofNat 32 d := fun c d h => by
    rw [add_ofNat_assoc, h]
  have al : ∀ c : Nat, c % 4 = 0 → (F + BitVec.ofNat 32 0x100 + BitVec.ofNat 32 c).toNat % 4 = 0 :=
    fun c hc => by rw [← ea (0x100 + c) c rfl]; exact aligned_add X.fa4 (by omega)
  have sl : ∀ c : Nat, 0x100 + c + 4 ≤ 0x180 →
      Sep (F + BitVec.ofNat 32 0x100 + BitVec.ofNat 32 c) 4 TRC trustedRootReadChainCode.length :=
    fun c hc => by rw [← ea (0x100 + c) c rfl]; exact X.flo hc
  refine WP.aluImm trc_at_0 ?_; wn
  rw [show aluEval .add (g0 sp) 0xFFFFFE80 = F by rw [X.sp0, ev_add, BitVec.add_assoc]; exact BitVec.add_zero F]
  refine WP.aluImm trc_at_2 ?_; wn
  refine WP.sw trc_at_4 (by trsimp; exact al 0x7C (by decide)) (by trsimp; exact sl 0x7C (by decide)) ?_; wn
  refine WP.sw trc_at_8 (by trsimp; exact al 0x78 (by decide)) (by trsimp; exact sl 0x78 (by decide)) ?_; wn
  refine WP.sw trc_at_a (by trsimp; exact al 0x74 (by decide)) (by trsimp; exact sl 0x74 (by decide)) ?_; wn
  refine WP.sw trc_at_c (by trsimp; exact al 0x70 (by decide)) (by trsimp; exact sl 0x70 (by decide)) ?_; wn
  refine WP.sw trc_at_10 (by trsimp; exact al 0x6C (by decide)) (by trsimp; exact sl 0x6C (by decide)) ?_; wn
  refine WP.sw trc_at_14 (by trsimp; exact al 0x68 (by decide)) (by trsimp; exact sl 0x68 (by decide)) ?_; wn
  refine WP.sw trc_at_18 (by trsimp; exact al 0x64 (by decide)) (by trsimp; exact sl 0x64 (by decide)) ?_; wn
  refine WP.sw trc_at_1c (by trsimp; exact al 0x60 (by decide)) (by trsimp; exact sl 0x60 (by decide)) ?_; wn
  refine WP.sw trc_at_20 (by trsimp; exact al 0x5C (by decide)) (by trsimp; exact sl 0x5C (by decide)) ?_; wn
  refine WP.sw trc_at_24 (by trsimp; exact al 0x58 (by decide)) (by trsimp; exact sl 0x58 (by decide)) ?_; wn
  refine WP.sw trc_at_28 (by trsimp; exact al 0x54 (by decide)) (by trsimp; exact sl 0x54 (by decide)) ?_; wn
  refine WP.sw trc_at_2c (by trsimp; exact al 0x50 (by decide)) (by trsimp; exact sl 0x50 (by decide)) ?_; wn
  refine WP.sw trc_at_30 (by trsimp; exact al 0x4C (by decide)) (by trsimp; exact sl 0x4C (by decide)) ?_; wn
  change WP trustedRootReadChainCode TRC _ (rcSave M0 (F + BitVec.ofNat 32 0x100) (g0 ra) (g0 8) (g0 9) (g0 18)
    (g0 19) (g0 20) (g0 21) (g0 22) (g0 23) (g0 24) (g0 25) (g0 26) (g0 27)) 0x34 _
  obtain ⟨hO, v1, v8, v9, v18, v19, v20, v21, v22, v23, v24, v25, v26, v27⟩ := rcSave_spec (M := M0) rfl
  generalize rcSave M0 (F + BitVec.ofNat 32 0x100) (g0 ra) (g0 8) (g0 9) (g0 18) (g0 19) (g0 20) (g0 21) (g0 22)
    (g0 23) (g0 24) (g0 25) (g0 26) (g0 27) = M1 at hO v1 v8 v9 v18 v19 v20 v21 v22 v23 v24 v25 v26 v27
  have hOG : Out M0 M1 G 0x740 := Out.upK (c := 0x6C0) (by rw [← X.fg, add_ofNat_assoc]) hO (by decide)
  have hI : RcMemInv M0 G F fr fp fl g0 M1 :=
    ⟨fun x a _ _ => hOG x a.symm, (congrArg (memLoad32 M1) (ea 0x17C 0x7C rfl)).trans v1, (congrArg (memLoad32 M1) (ea 0x178 0x78 rfl)).trans v8,
      (congrArg (memLoad32 M1) (ea 0x174 0x74 rfl)).trans v9, (congrArg (memLoad32 M1) (ea 0x170 0x70 rfl)).trans v18,
      (congrArg (memLoad32 M1) (ea 0x16C 0x6C rfl)).trans v19, (congrArg (memLoad32 M1) (ea 0x168 0x68 rfl)).trans v20,
      (congrArg (memLoad32 M1) (ea 0x164 0x64 rfl)).trans v21, (congrArg (memLoad32 M1) (ea 0x160 0x60 rfl)).trans v22,
      (congrArg (memLoad32 M1) (ea 0x15C 0x5C rfl)).trans v23, (congrArg (memLoad32 M1) (ea 0x158 0x58 rfl)).trans v24,
      (congrArg (memLoad32 M1) (ea 0x154 0x54 rfl)).trans v25, (congrArg (memLoad32 M1) (ea 0x150 0x50 rfl)).trans v26,
      (congrArg (memLoad32 M1) (ea 0x14C 0x4C rfl)).trans v27⟩
  have hB : RcBuf M1 fr fp fl [] :=
    ⟨Nat.zero_le _, (hOG.load32 (X.frg.symm.rcSub0 (by decide))).trans (X.hfp.trans (add_ofNat_zero fp).symm),
      (hOG.load32 (X.frg.symm.subR (c := 4) (l := 4) (by decide))).trans X.hfl, rfl⟩
  refine WP.alu trc_at_34 ?_; wn
  refine WP.alu trc_at_36 ?_; wn
  refine WP.alu trc_at_38 ?_; wn
  refine WP.alu trc_at_3a ?_; wn
  exact X.pHead ⟨by trsimp, by trsimp, by trsimp; exact h0, by trsimp; exact h3, by trsimp, by trsimp⟩ hI hB
    (by trsimp; exact h1) (by trsimp; exact h2) (by trsimp; exact h1) (by trsimp; exact h2) rfl

end

/-- `read_chain` at machine-code level. From its entry with `a0 = out`,
`a1 = p`, `a2 = n`, and `a3 = fr`, where `fr` holds the scratch slice of
`fl` bytes at `fp`, it returns to `ra` with `sp` and the saved registers
restored, `readChainPos` at `out` and in the scratch slice, and no change
outside the 0x740 bytes below `sp`, `out`'s 0x40 bytes, the scratch slice,
and the buffer. When it fails, the error byte at `out + 4` is the model's
byte `b`, and `b` is below 0x27. -/
theorem trustedRootReadChain_correct (m : Machine) {sp0 out p fr fp retAddr : Word} {n fl : Nat}
    (hc : RcCode m.mem) (hpc : m.pc = TRC) (ha0 : reg m a0 = out) (ha1 : reg m a1 = p)
    (ha2 : reg m a2 = BitVec.ofNat 32 n) (ha3 : reg m a3 = fr) (hra : reg m ra = retAddr)
    (hret : retAddr &&& ~~~1 = retAddr) (hsp : reg m sp = sp0) (hsa : sp0.toNat % 16 = 0)
    (hsl : 0x740 ≤ sp0.toNat) (hsw : sp0.toNat ≤ 0x40000000)
    (h384 : P3.Fr (sp0 + 0xFFFFF8C0 + BitVec.ofNat 32 0x1A0) 0x420)
    (sRO : Sep (sp0 + 0xFFFFF8C0) 0x740 TVF_RO 0x1400)
    (hoa : out.toNat % 4 = 0) (how : out.toNat + 0x40 ≤ 0x40000000) (sOG : Sep out 0x40 (sp0 + 0xFFFFF8C0) 0x740)
    (sOR : Sep out 0x40 fr 8) (sOB : Sep out 0x40 fp fl)
    (hfa : fr.toNat % 4 = 0) (hfw : fr.toNat + 8 ≤ 0x40000000) (sRG : Sep fr 8 (sp0 + 0xFFFFF8C0) 0x740)
    (sRR : Sep fr 8 TVF_RO 0x1400) (sRB : Sep fr 8 fp fl)
    (hbw : fp.toNat + fl + 14 ≤ 0x40000000) (hb0 : fp.toNat ≠ 0) (sBG : Sep fp (fl + 14) (sp0 + 0xFFFFF8C0) 0x740)
    (sBR : Sep fp fl TVF_RO 0x1400)
    (hfp : memLoad32 m.mem fr = fp) (hfl : memLoad32 m.mem (fr + 4) = BitVec.ofNat 32 fl)
    (hpw : p.toNat + n + 4 ≤ 0x40000000) (hp0 : p.toNat ≠ 0) (sPG : Sep p (n + 4) (sp0 + 0xFFFFF8C0) 0x740)
    (sPR : Sep p n fr 8) (sPB : Sep p n fp fl) :
    ∃ m', Steps m m' ∧ m'.pc = retAddr ∧ reg m' sp = sp0 ∧
      (∀ q : Fin 32, q.val ∈ trSaved → reg m' q = reg m q) ∧
      rcMem m.mem (sp0 + 0xFFFFF8C0) out fr fp fl (readChainPos m.mem p n fp fl) m'.mem ∧
      ∀ e, readChainPos m.mem p n fp fl = .error e →
        ∃ b, b < 0x27 ∧ e = some b ∧ m'.mem (out + 4) = BitVec.ofNat 8 b := by
  have hG : (sp0 + 0xFFFFF8C0 : Word).toNat = sp0.toNat - 0x740 := by
    rw [BitVec.toNat_add, show (0xFFFFF8C0 : Word).toNat = 2 ^ 32 - 0x740 from rfl]; omega
  have X : RcCtx m.mem (sp0 + 0xFFFFF8C0) (sp0 + 0xFFFFF8C0 + BitVec.ofNat 32 0x5C0) out fr fp fl p n (reg m) :=
    { code := hc, fg := rfl, ga := by omega, gw := by omega, f384 := h384, ro := sRO, oa := hoa, ow := how,
      og := sOG, ofr := sOR, ofp := sOB, fa := hfa, fw := hfw, frg := sRG, frro := sRR, frp := sRB, bw := hbw,
      b0 := hb0, bg := sBG, bro := sBR, hfp := hfp, hfl := hfl, pw := hpw, p0 := hp0, pg := sPG, pfr := sPR,
      pb := sPB
      sp0 := by rw [hsp, add_ofNat_assoc, BitVec.add_assoc]; exact (BitVec.add_zero sp0).symm
      ret := by rw [hra]; exact hret }
  obtain ⟨m', hs, hpc', hsp', hk, hR⟩ := WP.run (X.entry ha0 ha1 ha2 ha3) (by decide) hc.self hpc
  refine ⟨m', hs, hpc'.trans hra, hsp'.trans hsp, hk, hR, fun e he => ?_⟩
  obtain ⟨b, rfl, hb⟩ := rce_readChainPos he
  have hO := hR.1
  rw [he] at hO
  exact ⟨b, hb, rfl, hO.2 b rfl⟩

end C3.RV32
