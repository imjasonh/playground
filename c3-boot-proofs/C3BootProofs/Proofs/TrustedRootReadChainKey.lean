import C3BootProofs.Proofs.TrustedRootReadChainDer

/-!
# `read_chain`'s calls of the slice compares and `p384_from_sec1`

`p384_key` compares the algorithm's object identifiers with `<[u8]>::eq`
and `<[u8]>::ne`, then decodes the key with `p384_from_sec1`. Each call's
theorem states the callee's result over the bytes it reads and the bytes
of the stack region it may change.
-/

namespace C3.RV32

open C3.Image C3.Json

set_option maxRecDepth 20000

/-- `rcFsOk` over the 97 bytes at `inp` is `FsOk`. -/
theorem rcd_fsOk (M : Word → BitVec 8) (inp : Word) : rcFsOk (memBytes M inp 0x61) ↔ Fs.FsOk M inp := by
  unfold rcFsOk Fs.FsOk Fs.fsVal
  rw [memBytes_drop_take (by decide : 1 + 48 ≤ 0x61), memBytes_drop_take (by decide : 0x31 + 48 ≤ 0x61),
    memBytes_getD (by decide : 0 < 0x61), add_ofNat_zero]
  have h4 : (M inp).toNat = 4 ↔ M inp = 4 := by
    constructor
    · intro h; exact BitVec.eq_of_toNat_eq h
    · intro h; rw [h]; rfl
  rw [h4]

theorem rcd_se_saved : ∀ q : Fin 32, q.val ∈ trSaved → q ≠ a0 ∧ q ≠ a1 ∧ q ≠ a2 ∧ q ≠ a3 ∧ q ≠ a4 ∧ q ≠ t1 := by
  decide

theorem rcd_fs_cases : ∀ q : Fin 32, q.val ∈ trSaved →
    q = Dq.savedReg 0 ∨ q = Dq.savedReg 1 ∨ q = Dq.savedReg 2 ∨ q = Dq.savedReg 3 ∨ q = Dq.savedReg 4 ∨
    q = Dq.savedReg 5 ∨ q = Dq.savedReg 6 ∨ q = Dq.savedReg 7 ∨ q = Dq.savedReg 8 ∨ q = Dq.savedReg 9 ∨
    q = Dq.savedReg 10 ∨ q.val ∈ [3, 4, 26, 27] := by
  decide

theorem rcd_fs_saved {n n' : Machine} (h1 : ∀ k, k < 11 → reg n' (Dq.savedReg k) = reg n (Dq.savedReg k))
    (h2 : ∀ q : Fin 32, q.val ∈ [3, 4, 26, 27] → reg n' q = reg n q) :
    ∀ q : Fin 32, q.val ∈ trSaved → reg n' q = reg n q := by
  intro q hq
  rcases rcd_fs_cases q hq with h | h | h | h | h | h | h | h | h | h | h | h
  all_goals first
    | exact h2 q h
    | (rw [h]; exact h1 _ (by decide))

section
variable {M0 : Word → BitVec 8} {G F out fr fp p : Word} {fl n : Nat} {g0 : Fin 32 → Word}

/-- The call of `<[u8]>::eq` at `off` on the `pl` bytes at `p` and the
`ql` bytes at `q`, which changes only the stack below the frame. -/
theorem RcCtx.callSlEq (X : RcCtx M0 G F out fr fp fl p n g0) {M : Word → BitVec 8} {f : Fin 32 → Word}
    {Q : Post} {off : Nat} {hi lo pa qa : Word} {pl ql : Nat}
    (h1 : fetchRel trustedRootReadChainCode off = some (.auipc ra hi, 4))
    (h2 : fetchRel trustedRootReadChainCode (off + 4) = some (.jalr ra ra lo, 4))
    (htgt : (TRC + BitVec.ofNat 32 off + hi + lo) &&& ~~~1 = RSE)
    (hev : (TRC + BitVec.ofNat 32 (off + 8)) &&& ~~~1 = TRC + BitVec.ofNat 32 (off + 8))
    (hR : RcRegs F out fr g0 f) (hI : RcMemInv M0 G F fr fp fl g0 M)
    (ha0 : f a0 = pa) (ha1 : f a1 = BitVec.ofNat 32 pl) (ha2 : f a2 = qa) (ha3 : f a3 = BitVec.ofNat 32 ql)
    (hpl : pl < 2 ^ 32) (hql : ql < 2 ^ 32) (sP : Sep pa pl G 0x5C0) (sQ : Sep qa ql G 0x5C0)
    (k : ∀ m2 : Machine, RcKeep G M m2.mem → (∀ x, Sep G 0x5C0 x 1 → m2.mem x = M x) →
      RcMemInv M0 G F fr fp fl g0 m2.mem →
      reg m2 a0 = (if memBytes M pa pl = memBytes M qa ql then 1 else 0) →
      WP trustedRootReadChainCode TRC Q m2.mem (off + 8) (clob (upd f ra (TRC + BitVec.ofNat 32 (off + 8))) m2 jClob)) :
    WP trustedRootReadChainCode TRC Q M off f := by
  have eS : F + 0xFFFFFFFC = G + BitVec.ofNat 32 0x5BC := X.fneg (k := 4) (by decide) (by decide)
  refine X.callK (P := fun m2 => (∀ x, Sep G 0x5C0 x 1 → m2.mem x = M x) ∧
      reg m2 a0 = (if memBytes M pa pl = memBytes M qa ql then 1 else 0))
    h1 h2 htgt hI (fun m1 hpc1 hmem1 hreg1 => ?_) (fun m2 hK hP hI' => k m2 hK hP.1 hI' hP.2)
  have C := X.codeAt hI
  rw [← hmem1] at C
  have hsp1 : reg m1 sp = F := by rw [hreg1]; trsimp; exact hR.2.1
  obtain ⟨m2, c2, pc2, hA, hk2, hm2⟩ := sliceEq_correct m1 (base := RSE)
    (retAddr := TRC + BitVec.ofNat 32 (off + 8)) (p := pa) (q := qa) (pl := pl) (ql := ql) (by decide) C.seq
    (by rw [show RSE + 0xFFFFEBAA = RES from by decide]; exact C.esl)
    (by rw [show RSE + 0xBF68 = RMC from by decide]; exact C.mcm) hpc1
    (by rw [hreg1]; trsimp; exact ha0) (by rw [hreg1]; trsimp; exact ha1) (by rw [hreg1]; trsimp; exact ha2)
    (by rw [hreg1]; trsimp; exact ha3) hpl hql (by rw [hreg1]; trsimp) hev (by rw [hsp1]; exact X.fa4)
    (by rw [hsp1, eS]; exact X.glo (by decide) (by decide) (by decide))
    (by rw [hsp1, eS]; exact X.glo (by decide) (by decide) (by decide))
    (by rw [hsp1, eS]; exact sP.symm.sub (by decide)) (by rw [hsp1, eS]; exact sQ.symm.sub (by decide))
  rw [hmem1] at hA
  have hF : ∀ x, Sep G 0x5C0 x 1 → m2.mem x = M x := fun x xa =>
    (hm2 x (by rw [hsp1, eS]; exact rc_gin (rc_g0 xa) (by decide) (by decide))).trans (congrFun hmem1 x)
  refine ⟨m2, c2, pc2, ⟨fun x xa _ => hF x xa, hF, hA⟩,
    hk2 sp (by decide) (by decide) (by decide) (by decide) (by decide) (by decide), fun q hq => ?_⟩
  obtain ⟨e1, e2, e3, e4, e5, e6⟩ := rcd_se_saved q hq
  exact hk2 q e1 e2 e3 e4 e5 e6

/-- The call of `<[u8]>::ne` at `off` on the `pl` bytes at `p` and the
`ql` bytes at `q`, which changes only the stack below the frame. -/
theorem RcCtx.callSlNe (X : RcCtx M0 G F out fr fp fl p n g0) {M : Word → BitVec 8} {f : Fin 32 → Word}
    {Q : Post} {off : Nat} {hi lo pa qa : Word} {pl ql : Nat}
    (h1 : fetchRel trustedRootReadChainCode off = some (.auipc ra hi, 4))
    (h2 : fetchRel trustedRootReadChainCode (off + 4) = some (.jalr ra ra lo, 4))
    (htgt : (TRC + BitVec.ofNat 32 off + hi + lo) &&& ~~~1 = RSN)
    (hev : (TRC + BitVec.ofNat 32 (off + 8)) &&& ~~~1 = TRC + BitVec.ofNat 32 (off + 8))
    (hR : RcRegs F out fr g0 f) (hI : RcMemInv M0 G F fr fp fl g0 M)
    (ha0 : f a0 = pa) (ha1 : f a1 = BitVec.ofNat 32 pl) (ha2 : f a2 = qa) (ha3 : f a3 = BitVec.ofNat 32 ql)
    (hpl : pl < 2 ^ 32) (hql : ql < 2 ^ 32) (sP : Sep pa pl G 0x5C0) (sQ : Sep qa ql G 0x5C0)
    (k : ∀ m2 : Machine, RcKeep G M m2.mem → (∀ x, Sep G 0x5C0 x 1 → m2.mem x = M x) →
      RcMemInv M0 G F fr fp fl g0 m2.mem →
      reg m2 a0 = (if memBytes M pa pl = memBytes M qa ql then 0 else 1) →
      WP trustedRootReadChainCode TRC Q m2.mem (off + 8) (clob (upd f ra (TRC + BitVec.ofNat 32 (off + 8))) m2 jClob)) :
    WP trustedRootReadChainCode TRC Q M off f := by
  have eS : F + 0xFFFFFFEC = G + BitVec.ofNat 32 0x5AC := X.fneg (k := 0x14) (by decide) (by decide)
  refine X.callK (P := fun m2 => (∀ x, Sep G 0x5C0 x 1 → m2.mem x = M x) ∧
      reg m2 a0 = (if memBytes M pa pl = memBytes M qa ql then 0 else 1))
    h1 h2 htgt hI (fun m1 hpc1 hmem1 hreg1 => ?_) (fun m2 hK hP hI' => k m2 hK hP.1 hI' hP.2)
  have C := X.codeAt hI
  rw [← hmem1] at C
  have hsp1 : reg m1 sp = F := by rw [hreg1]; trsimp; exact hR.2.1
  obtain ⟨m2, c2, pc2, hA, hk2, hm2⟩ := sliceNe_correct m1 (base := RSN)
    (retAddr := TRC + BitVec.ofNat 32 (off + 8)) (p := pa) (q := qa) (pl := pl) (ql := ql) (by decide) C.sne
    (by rw [show RSN + 0xFFFFF372 = RSE from by decide]; exact C.seq)
    (by rw [show RSN + 0xFFFFDF1C = RES from by decide]; exact C.esl)
    (by rw [show RSN + 0xB2DA = RMC from by decide]; exact C.mcm) hpc1
    (by rw [hreg1]; trsimp; exact ha0) (by rw [hreg1]; trsimp; exact ha1) (by rw [hreg1]; trsimp; exact ha2)
    (by rw [hreg1]; trsimp; exact ha3) hpl hql (by rw [hreg1]; trsimp) hev (by rw [hsp1]; exact X.fa4)
    (by rw [hsp1, eS]; exact X.glo (by decide) (by decide) (by decide))
    (by rw [hsp1, eS]; exact X.glo (by decide) (by decide) (by decide))
    (by rw [hsp1, eS]; exact X.glo (by decide) (by decide) (by decide))
    (by rw [hsp1, eS]; exact X.glo (by decide) (by decide) (by decide))
    (by rw [hsp1, eS]; exact sP.symm.sub (by decide)) (by rw [hsp1, eS]; exact sQ.symm.sub (by decide))
  rw [hmem1] at hA
  have hF : ∀ x, Sep G 0x5C0 x 1 → m2.mem x = M x := fun x xa =>
    (hm2 x (by rw [hsp1, eS]; exact rc_gin (rc_g0 xa) (by decide) (by decide))).trans (congrFun hmem1 x)
  refine ⟨m2, c2, pc2, ⟨fun x xa _ => hF x xa, hF, hA⟩,
    hk2 sp (by decide) (by decide) (by decide) (by decide) (by decide) (by decide), fun q hq => ?_⟩
  obtain ⟨e1, e2, e3, e4, e5, e6⟩ := rcd_se_saved q hq
  exact hk2 q e1 e2 e3 e4 e5 e6

/-- The call of `p384_from_sec1` at `off` on the 97 bytes at `inp`, with the
result at `F + oc`. It changes the stack below the frame and the result's
0x68 bytes, and its first word is 0 exactly when `rcFsOk` holds. -/
theorem RcCtx.callFs (X : RcCtx M0 G F out fr fp fl p n g0) {M : Word → BitVec 8} {f : Fin 32 → Word}
    {Q : Post} {off oc : Nat} {hi lo inp : Word}
    (h1 : fetchRel trustedRootReadChainCode off = some (.auipc ra hi, 4))
    (h2 : fetchRel trustedRootReadChainCode (off + 4) = some (.jalr ra ra lo, 4))
    (htgt : (TRC + BitVec.ofNat 32 off + hi + lo) &&& ~~~1 = Fs.FP)
    (hev : (TRC + BitVec.ofNat 32 (off + 8)) &&& ~~~1 = TRC + BitVec.ofNat 32 (off + 8))
    (hR : RcRegs F out fr g0 f) (hI : RcMemInv M0 G F fr fp fl g0 M)
    (hoc : 0x60 ≤ oc ∧ oc + 0x68 ≤ 0x14C ∧ oc % 4 = 0)
    (ha0 : f a0 = F + BitVec.ofNat 32 oc) (ha1 : f a1 = inp)
    (sI : Sep inp 0x61 G 0x5C0) (hIw : inp.toNat + 0x61 ≤ 0x40000000)
    (k : ∀ m2 : Machine, RcKeep G M m2.mem →
      (∀ x, Sep G 0x5C0 x 1 → Sep (F + BitVec.ofNat 32 oc) 0x68 x 1 → m2.mem x = M x) →
      RcMemInv M0 G F fr fp fl g0 m2.mem →
      memLoad32 m2.mem (F + BitVec.ofNat 32 oc) = (if rcFsOk (memBytes M inp 0x61) then 0 else 1) →
      WP trustedRootReadChainCode TRC Q m2.mem (off + 8) (clob (upd f ra (TRC + BitVec.ofNat 32 (off + 8))) m2 jClob)) :
    WP trustedRootReadChainCode TRC Q M off f := by
  have gw := X.gw
  have eF : G + BitVec.ofNat 32 0x1A0 + 0x420 = F := by
    rw [← X.fg]; exact add_ofNat_assoc G 0x1A0 0x420
  have eG : G + BitVec.ofNat 32 0x1A0 + 0xFFFFFE60 = G := by
    have h0 : (BitVec.ofNat 32 0x1A0 + 0xFFFFFE60 : Word) = 0#32 := by decide
    rw [BitVec.add_assoc, h0, BitVec.add_zero]
  refine X.callK (P := fun m2 => (∀ x, Sep G 0x5C0 x 1 → Sep (F + BitVec.ofNat 32 oc) 0x68 x 1 → m2.mem x = M x) ∧
      memLoad32 m2.mem (F + BitVec.ofNat 32 oc) = (if rcFsOk (memBytes M inp 0x61) then 0 else 1))
    h1 h2 htgt hI (fun m1 hpc1 hmem1 hreg1 => ?_) (fun m2 hK hP hI' => k m2 hK hP.1 hI' hP.2)
  have C := X.codeAt hI
  rw [← hmem1] at C
  have hsp1 : reg m1 sp = F := by rw [hreg1]; trsimp; exact hR.2.1
  have sO : Sep (F + BitVec.ofNat 32 oc) 0x68 G 0x5C0 := by
    have h := X.gsep (c := 0x5C0 + oc) (k := 0x68) (d := 0) (l := 0x5C0) (Or.inr (by omega)) (by omega) (by decide)
    rw [add_ofNat_zero] at h; rw [X.fG]; exact h
  obtain ⟨m2, c2, hRet, hok, hbad⟩ := Fs.p384FromSec1_correct m1 (S := G + BitVec.ofNat 32 0x1A0) (inp := inp)
    (out := F + BitVec.ofNat 32 oc) C.fs C.p3 X.f384 hpc1 (by rw [hsp1, eF])
    (by rw [hreg1]; trsimp; exact ha0) (by rw [hreg1]; trsimp; exact ha1) (by rw [hreg1]; trsimp; exact hev)
    (by rw [eG]; exact sI) hIw (X.fal hoc.2.2) (by rw [X.fG, X.gc (by omega)]; omega) (by rw [eG]; exact sO)
  obtain ⟨hpc2, hsp2, hs1, hs2, hm2⟩ := hRet
  rw [eG] at hm2
  have hF : ∀ x, Sep G 0x5C0 x 1 → Sep (F + BitVec.ofNat 32 oc) 0x68 x 1 → m2.mem x = M x :=
    fun x xa xo => (hm2 x xa xo).trans (congrFun hmem1 x)
  have hK : RcKeep G M m2.mem := fun x xa xb =>
    hF x xa (by rw [X.fG]; exact rc_gin xb (by omega) (by omega))
  refine ⟨m2, c2, by rw [hpc2, hreg1]; trsimp, ⟨hK, hF, ?_⟩, by rw [hsp2, hsp1, eF], rcd_fs_saved hs1 hs2⟩
  rw [hmem1] at hok hbad
  by_cases h : Fs.FsOk M inp
  · rw [ite_eq_left ((rcd_fsOk M inp).2 h)]; exact (hok h).1
  · rw [ite_eq_right (fun h' => h ((rcd_fsOk M inp).1 h'))]; exact hbad h

end

end C3.RV32
