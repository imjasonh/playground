import C3BootProofs.Proofs.AcceptExtractLib
import C3BootProofs.Proofs.AcceptExtractSeq

/-!
# The extract stage's tail, from 0x1778 to 0x1816

Five calls of `memcpy` put the `TrustRoot` together at `sp + 0x1320`: the
Fulcio keys from `sp + 0x1ED0`, the logs from `sp + 0x350`, the timestamp
authorities from `sp + 0x890`, and the identity policy's 0x23 bytes from
`acPolicyAddress`. Then the whole struct goes to `sp + 0xDD0`, and the closure
sets up the call at 0x1816 that copies it on to `sp + 0x1875`.
-/

namespace C3.RV32.Ac

open C3 C3.Image C3.RV32.P3 C3.RV32.Sv C3.Json

def aceT1 : List BInstr :=
  [.lui a0 0x1000, .aluImm .add a0 a0 0x343, .alu .add a0 a0 sp, .lui a1 0x2000,
    .aluImm .add a1 a1 0xFFFFFED0, .alu .add a1 a1 sp, .aluImm .add a2 x0 0x100]

def aceT2 : List BInstr :=
  [.lui a0 0x1000, .aluImm .add a0 a0 0x443, .alu .add a0 a0 sp, .aluImm .add a1 sp 0x350,
    .aluImm .add a2 x0 0x200]

def aceT3 : List BInstr :=
  [.lui a0 0x1000, .aluImm .add a0 a0 0x643, .alu .add a0 a0 sp, .aluImm .add a1 sp 0x7FF,
    .aluImm .add a1 a1 0x91, .aluImm .add a2 x0 0x100]

def aceT4 : List BInstr :=
  [.lui a1 (img% hi20 acPolicyAddress), .aluImm .add a1 a1 (img% lo12 acPolicyAddress), .lui a0 0x1000, .aluImm .add a0 a0 0x320,
    .alu .add a0 a0 sp, .aluImm .add a2 x0 0x23]

def aceT5 : List BInstr :=
  [.aluImm .add a0 sp 0x7FF, .aluImm .add a0 a0 0x5D1, .lui a1 0x1000, .aluImm .add a1 a1 0x320,
    .alu .add a1 a1 sp, .aluImm .add a2 x0 0x423]

def aceT6 : List BInstr :=
  [.lui a0 0x2000, .aluImm .add a0 a0 0xFFFFF875, .alu .add a0 a0 sp, .aluImm .add a1 sp 0x7FF,
    .aluImm .add a1 a1 0x5D1, .aluImm .add a2 x0 0x423]

theorem AceSame.pt0 {M M' : Word → BitVec 8} {a : Word} (h : AceSame M' a M a 1) : M' a = M a := by
  have := h 0 (by decide); rwa [add_ofNat_zero] at this

set_option maxRecDepth 100000 in
set_option maxHeartbeats 16000000 in
/-- **The extract stage's tail.** -/
theorem ace_tail : AceTailStage := by
  intro X ok n fp fs ls ts A K D
  have F := ok.lay.fr
  have hh := F.hi
  have rsp := A.inv.sp
  have E0 := ok.env n.mem A.inv.out
  -- the Fulcio keys to `sp + 0x1343`
  obtain ⟨n1, c1, s1, I1, C1, W1, K1⟩ := ace_bcpy (is := aceT1) (o1 := 0x178C) (d := 0x1343) (N := 0x100)
    (src := acSlot X.B 0x1ED0) F A.code E0.stub E0.body A.st A.inv (by decide)
    (by simp [aceT1, BlockOk, BInstr.ok]) rfl (by decide) (by decide) ac_at_178c ac_at_1790 (by decide)
    (by simp +decide only [aceT1, runBlock, BInstr.run, upd, aluEval, ↓reduceIte]; rw [rsp]; simp only [acSlot]; bv_omega)
    (by simp +decide only [aceT1, runBlock, BInstr.run, upd, aluEval, ↓reduceIte]; rw [rsp]; simp only [acSlot]; bv_omega)
    (by simp +decide only [aceT1, runBlock, BInstr.run, upd, aluEval, ↓reduceIte]) (by decide)
    (ace_sepB' F (.inr (by decide)) (by decide) (by decide)) (ace_sepB' F (.inl (by decide)) (by decide) (by decide))
    (by rw [ace_slotN F (by decide)]; omega)
  have E1 := ok.env n1.mem I1.out
  have s1' : St n1.mem AC n1 0x1794 (reg n1) := s1
  -- the logs to `sp + 0x1443`
  obtain ⟨n2, c2, s2, I2, C2, W2, K2⟩ := ace_bcpy (is := aceT2) (o1 := 0x17A2) (d := 0x1443) (N := 0x200)
    (src := acSlot X.B 0x350) F C1 E1.stub E1.body s1' I1 (by decide)
    (by simp [aceT2, BlockOk, BInstr.ok]) rfl (by decide) (by decide) ac_at_17a2 ac_at_17a6 (by decide)
    (by simp +decide only [aceT2, runBlock, BInstr.run, upd, aluEval, ↓reduceIte]; rw [K1 sp (by decide), rsp]; simp only [acSlot]; bv_omega)
    (by simp +decide only [aceT2, runBlock, BInstr.run, upd, aluEval, ↓reduceIte]; rw [K1 sp (by decide), rsp]; simp only [acSlot]; bv_omega)
    (by simp +decide only [aceT2, runBlock, BInstr.run, upd, aluEval, ↓reduceIte]) (by decide)
    (ace_sepB' F (.inr (by decide)) (by decide) (by decide)) (ace_sepB' F (.inr (by decide)) (by decide) (by decide))
    (by rw [ace_slotN F (by decide)]; omega)
  have E2 := ok.env n2.mem I2.out
  have s2' : St n2.mem AC n2 0x17AA (reg n2) := s2
  -- the timestamp authorities to `sp + 0x1643`
  obtain ⟨n3, c3, s3, I3, C3, W3, K3⟩ := ace_bcpy (is := aceT3) (o1 := 0x17BE) (d := 0x1643) (N := 0x100)
    (src := acSlot X.B 0x890) F C2 E2.stub E2.body s2' I2 (by decide)
    (by simp [aceT3, BlockOk, BInstr.ok]) rfl (by decide) (by decide) ac_at_17be ac_at_17c2 (by decide)
    (by simp +decide only [aceT3, runBlock, BInstr.run, upd, aluEval, ↓reduceIte]
        rw [K2 sp (by decide), K1 sp (by decide), rsp]; simp only [acSlot]; bv_omega)
    (by simp +decide only [aceT3, runBlock, BInstr.run, upd, aluEval, ↓reduceIte]
        rw [K2 sp (by decide), K1 sp (by decide), rsp]; simp only [acSlot]; bv_omega)
    (by simp +decide only [aceT3, runBlock, BInstr.run, upd, aluEval, ↓reduceIte]) (by decide)
    (ace_sepB' F (.inr (by decide)) (by decide) (by decide)) (ace_sepB' F (.inr (by decide)) (by decide) (by decide))
    (by rw [ace_slotN F (by decide)]; omega)
  have E3 := ok.env n3.mem I3.out
  have s3' : St n3.mem AC n3 0x17C6 (reg n3) := s3
  -- the policy's bytes to `sp + 0x1320`
  have pS := ok.lay.polStack
  obtain ⟨n4, c4, s4, I4, C4, W4, K4⟩ := ace_bcpy (is := aceT4) (o1 := 0x17DA) (d := 0x1320) (N := 0x23)
    (src := (img% acPolicyAddress)) F C3 E3.stub E3.body s3' I3 (by decide)
    (by simp [aceT4, BlockOk, BInstr.ok]) rfl (by decide) (by decide) ac_at_17da ac_at_17de (by decide)
    (by simp +decide only [aceT4, runBlock, BInstr.run, upd, aluEval, ↓reduceIte]
        rw [K3 sp (by decide), K2 sp (by decide), K1 sp (by decide), rsp]; simp only [acSlot]; bv_omega)
    (by simp +decide only [aceT4, runBlock, BInstr.run, upd, aluEval, ↓reduceIte])
    (by simp +decide only [aceT4, runBlock, BInstr.run, upd, aluEval, ↓reduceIte]) (by decide)
    (pS.subR (c := 0x3A40) (l := 16) (by decide)) (pS.subR (c := 0x3A50 + 0x1320) (l := 0x23) (by decide)).symm
    (by decide)
  have E4 := ok.env n4.mem I4.out
  have s4' : St n4.mem AC n4 0x17E2 (reg n4) := s4
  -- the struct to `sp + 0xDD0`
  obtain ⟨n5, c5, s5, I5, C5, W5, K5⟩ := ace_bcpy (is := aceT5) (o1 := 0x17F6) (d := 0xDD0) (N := 0x423)
    (src := acSlot X.B 0x1320) F C4 E4.stub E4.body s4' I4 (by decide)
    (by simp [aceT5, BlockOk, BInstr.ok]) rfl (by decide) (by decide) ac_at_17f6 ac_at_17fa (by decide)
    (by simp +decide only [aceT5, runBlock, BInstr.run, upd, aluEval, ↓reduceIte]
        rw [K4 sp (by decide), K3 sp (by decide), K2 sp (by decide), K1 sp (by decide), rsp]; simp only [acSlot]; bv_omega)
    (by simp +decide only [aceT5, runBlock, BInstr.run, upd, aluEval, ↓reduceIte]
        rw [K4 sp (by decide), K3 sp (by decide), K2 sp (by decide), K1 sp (by decide), rsp]; simp only [acSlot]; bv_omega)
    (by simp +decide only [aceT5, runBlock, BInstr.run, upd, aluEval, ↓reduceIte]) (by decide)
    (ace_sepB' F (.inr (by decide)) (by decide) (by decide)) (ace_sepB' F (.inl (by decide)) (by decide) (by decide))
    (by rw [ace_slotN F (by decide)]; omega)
  have s5' : St n5.mem AC n5 0x17FE (reg n5) := s5
  -- the arguments of the call at 0x1816
  have hz5 := s5'.zero
  obtain ⟨n6, c6, u6⟩ := s5'.block (off' := 0x1812) aceT6 C5 (by decide) (by simp [aceT6, BlockOk, BInstr.ok])
  have M6 : n6.mem = n5.mem := u6.mem
  have s6 : St n6.mem AC n6 0x1812 (reg n6) := ⟨u6.pc, rfl, fun _ => rfl⟩
  obtain ⟨n7, e7, u7⟩ := s6.auipc (by rw [M6]; exact C5) ac_at_1812 (off' := 0x1816) (by decide)
  have M7 : n7.mem = n5.mem := u7.mem.trans M6
  have r6 : ∀ q : Fin 32, q.val ∉ [10, 11, 12] → reg n6 q = reg n5 q := fun q hq => by
    rw [u6.regs, runBlock_reg _ _ _ q hz5 (by simp only [aceT6]; revert hq; revert q; decide)]
  have r7 : ∀ q : Fin 32, q ≠ ra → reg n7 q = reg n6 q := fun q hq => by
    rw [u7.regs, updz s6.zero hq]
  have KK : ∀ q : Fin 32, q.val ∈ [2, 3, 4, 21, 25, 27] → reg n7 q = reg n q := fun q hq => by
    have hq' : q.val ∈ [2, 3, 4, 8, 9, 18, 19, 20, 21, 22, 23, 24, 25, 26, 27] := by revert hq; revert q; decide
    rw [r7 q (by intro e; subst e; revert hq; decide), r6 q (by revert hq; revert q; decide), K5 q hq', K4 q hq',
      K3 q hq', K2 q hq', K1 q hq']
  have I7 : AcInv X.B X.Bf X.g X.t X.v X.M0 n7 := I5.same M7 (by rw [KK sp (by decide), K5 sp (by decide),
      K4 sp (by decide), K3 sp (by decide), K2 sp (by decide), K1 sp (by decide)])
    (by rw [KK 3 (by decide), K5 3 (by decide), K4 3 (by decide), K3 3 (by decide), K2 3 (by decide),
      K1 3 (by decide)])
    (by rw [KK 4 (by decide), K5 4 (by decide), K4 4 (by decide), K3 4 (by decide), K2 4 (by decide),
      K1 4 (by decide)])
  have sp5 : reg n5 sp = X.B + 0x3A50 := by
    rw [K5 sp (by decide), K4 sp (by decide), K3 sp (by decide), K2 sp (by decide), K1 sp (by decide), rsp]
  -- memory: what each copy kept
  have O : ∀ x, Sep x 1 X.B 0x5A70 → n5.mem x = n.mem x := fun x hx => by
    rw [ace_cpO W5 (by decide) hx, ace_cpO W4 (by decide) hx, ace_cpO W3 (by decide) hx, ace_cpO W2 (by decide) hx,
      ace_cpO W1 (by decide) hx]
  have KS : ∀ k, 0x3A50 ≤ k → k + 1 ≤ 0x3A50 + 0xDD0 ∨ (0x3A50 + 0x1743 ≤ k ∧ k < 0x5A70) →
      n5.mem (X.B + BitVec.ofNat 32 k) = n.mem (X.B + BitVec.ofNat 32 k) := fun k h1 h2 => by
    rw [(ace_cpR F W5 (by decide) (k := k) (l := 1) h1 (by omega) (by omega)).pt0,
      (ace_cpR F W4 (by decide) (k := k) (l := 1) h1 (by omega) (by omega)).pt0,
      (ace_cpR F W3 (by decide) (k := k) (l := 1) h1 (by omega) (by omega)).pt0,
      (ace_cpR F W2 (by decide) (k := k) (l := 1) h1 (by omega) (by omega)).pt0,
      (ace_cpR F W1 (by decide) (k := k) (l := 1) h1 (by omega) (by omega)).pt0]
  have LS : ∀ s, s + 4 ≤ 0xDD0 ∨ (0x1743 ≤ s ∧ s + 4 ≤ 0x2020) →
      memLoad32 n5.mem (acSlot X.B s) = memLoad32 n.mem (acSlot X.B s) := fun s hs =>
    memLoad32_congr fun j hj => by
      rw [ace_slot]
      refine KS _ (by omega) ?_
      rcases hs with h | ⟨h, h'⟩
      · exact .inl (by omega)
      · exact .inr ⟨by omega, by omega⟩
  have hbuf : ∀ y : Word, X.Bf.toNat + 0x4000 ≤ y.toNat → y.toNat < fp.toNat → n4.mem y = n.mem y := fun y h1 h2 => by
    have hx := ace_bufOut ok.lay (y := y) (by omega) (by have := A.fr.hi; unfold acBufLen; omega)
    rw [ace_cpO W4 (by decide) hx, ace_cpO W3 (by decide) hx, ace_cpO W2 (by decide) hx, ace_cpO W1 (by decide) hx]
  -- the arrays at `sp + 0x1343`
  have Fu : AceSame n4.mem (acSlot X.B 0x1343) n.mem (acSlot X.B 0x1ED0) 0x100 :=
    (ace_cpR F W4 (by decide) (k := 0x3A50 + 0x1343) (l := 0x100) (by omega) (by omega) (by omega)).trans
      ((ace_cpR F W3 (by decide) (k := 0x3A50 + 0x1343) (l := 0x100) (by omega) (by omega) (by omega)).trans
        ((ace_cpR F W2 (by decide) (k := 0x3A50 + 0x1343) (l := 0x100) (by omega) (by omega) (by omega)).trans
          (ace_cpS F W1 (by decide))))
  have Lg : AceSame n4.mem (acSlot X.B 0x1443) n.mem (acSlot X.B 0x350) 0x200 :=
    (ace_cpR F W4 (by decide) (k := 0x3A50 + 0x1443) (l := 0x200) (by omega) (by omega) (by omega)).trans
      ((ace_cpR F W3 (by decide) (k := 0x3A50 + 0x1443) (l := 0x200) (by omega) (by omega) (by omega)).trans
        ((ace_cpS F W2 (by decide)).trans
          (ace_cpR F W1 (by decide) (k := 0x3A50 + 0x350) (l := 0x200) (by omega) (by omega) (by omega))))
  have Ts : AceSame n4.mem (acSlot X.B 0x1643) n.mem (acSlot X.B 0x890) 0x100 :=
    (ace_cpR F W4 (by decide) (k := 0x3A50 + 0x1643) (l := 0x100) (by omega) (by omega) (by omega)).trans
      ((ace_cpS F W3 (by decide)).trans
        ((ace_cpR F W2 (by decide) (k := 0x3A50 + 0x890) (l := 0x100) (by omega) (by omega) (by omega)).trans
          (ace_cpR F W1 (by decide) (k := 0x3A50 + 0x890) (l := 0x100) (by omega) (by omega) (by omega))))
  have KI4 : AceKeysIn X.Bf fp n4.mem (acSlot X.B 0x1343) fs ls ts := by
    refine ⟨ace_array_move K.fulcio Fu hbuf, ?_, ?_⟩
    · unfold AceLogsAt
      rw [show acSlot X.B 0x1343 + 0x100 = acSlot X.B 0x1443 by rw [BitVec.add_assoc]; rfl]
      exact ace_array_move K.logs Lg hbuf
    · unfold AceTsasAt
      rw [show acSlot X.B 0x1343 + 0x300 = acSlot X.B 0x1643 by rw [BitVec.add_assoc]; rfl]
      exact ace_array_move K.tsaKeys Ts hbuf
  -- the struct at `sp + 0xDD0`
  have S5 : AceSame n5.mem (acSlot X.B 0xDD0) n4.mem (acSlot X.B 0x1320) 0x423 := ace_cpS F W5 (by decide)
  have S5k : AceSame n5.mem (acSlot X.B 0xDF3) n4.mem (acSlot X.B 0x1343) 0x400 := by
    have h := S5.sub (k := 0x23) (l := 0x400) (by decide)
    rwa [ace_slot, ace_slot] at h
  have hbuf5 : ∀ y : Word, X.Bf.toNat + 0x4000 ≤ y.toNat → y.toNat < fp.toNat → n5.mem y = n4.mem y :=
    fun y h1 h2 => ace_cpO W5 (by decide) (ace_bufOut ok.lay (y := y) (by omega)
      (by have := A.fr.hi; unfold acBufLen; omega))
  have KI5 := KI4.move S5k hbuf5
  have P3 : AceSame n3.mem (img% acPolicyAddress) X.M0 (img% acPolicyAddress) 0x23 := fun c hc =>
    I3.out _ (pS.sub (c := c) (l := 1) (by omega)) (ok.lay.polBuf.sub (c := c) (l := 1) (by omega))
  have S4 : AceSame n4.mem (acSlot X.B 0x1320) n3.mem (img% acPolicyAddress) 0x23 := ace_cpS F W4 (by decide)
  refine ⟨n7, c1.trans (c2.trans (c3.trans (c4.trans (c5.trans (c6.trans (.single e7)))))),
    .inr ⟨I7, .inr ⟨u7.pc, fp, fs, ls, ts, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩⟩⟩
  · obtain ⟨jr, hr, hc, hl, ht⟩ := K.root
    exact fun pol => ace_extract_spec hr hc hl ht K.fulcio.1 K.logs.1 K.tsaKeys.1 D pol
  · rw [M7]; exact KI5
  · rw [M7]
    exact ace_memBytes_ext fun i hi => (S5 i (by omega)).trans ((S4 i hi).trans (P3 i hi))
  · refine ⟨?_, ?_, A.fr.lo, A.fr.hi⟩
    · rw [M7, LS 0x1FDC (by decide)]; exact A.fr.ptr
    · rw [M7, LS 0x1FE0 (by decide)]; exact A.fr.len
  · refine ⟨fun x hx => ?_, fun q hq => ?_⟩
    · rw [M7, ← A.keep.mem x hx]
      rcases hx with ⟨hx, _⟩ | ⟨k, hk, rfl⟩
      · exact O x hx
      · exact KS _ (by omega) (.inl (by omega))
    · rw [KK q (by revert hq; revert q; decide)]; exact A.keep.regs q hq
  · unfold AceExpiry aceU64
    rw [M7, LS 0x20 (by decide), show acSlot X.B 0x20 + 4 = acSlot X.B 0x24 by rw [BitVec.add_assoc]; rfl,
      LS 0x24 (by decide)]
    have h := A.exp
    unfold AceExpiry aceU64 at h
    rwa [show acSlot X.B 0x20 + 4 = acSlot X.B 0x24 by rw [BitVec.add_assoc]; rfl] at h
  · rw [r7 a0 (by decide), u6.regs]
    simp +decide only [aceT6, runBlock, BInstr.run, upd, aluEval, ↓reduceIte]
    rw [sp5]; simp only [acSlot]; bv_omega
  · rw [r7 a1 (by decide), u6.regs]
    simp +decide only [aceT6, runBlock, BInstr.run, upd, aluEval, ↓reduceIte]
    rw [sp5]; simp only [acSlot]; bv_omega
  · rw [r7 a2 (by decide), u6.regs]
    simp +decide only [aceT6, runBlock, BInstr.run, upd, aluEval, ↓reduceIte]
  · rw [u7.regs]
    simp +decide only [upd, ↓reduceIte]

end C3.RV32.Ac
