import C3BootProofs.Proofs.Ed25519VerifyP5b
import C3BootProofs.Proofs.EdNafTable
import C3BootProofs.Proofs.NonAdjacentForm
import C3BootProofs.Proofs.Select
import C3BootProofs.Proofs.DecCall

/-!
# `ed25519_verify`'s calls in the double-base scalar multiplication

Call lemmas for `<&FieldElement2625 as Neg>::neg`, `non_adjacent_form(5)`,
`NafLookupTable5::from`, and the point operations of the loop, each stated
over limb lists and points.
-/

namespace C3.RV32

open C3.Image

/-- `EdwardsPoint - ProjectiveNielsPoint` on limb lists, in the Rust
source's order: the completed point's `X`, `Y`, `Z`, and `T`. -/
def subNL (P N : Pt) : Pt :=
  let PP := mulL (addL P.2.1 P.1) N.2.1
  let MM := mulL (subL P.2.1 P.1) N.1
  let TT := mulL P.2.2.2 N.2.2.2
  let ZZ := mulL P.2.2.1 N.2.2.1
  (subL PP MM, addL PP MM, subL (addL ZZ ZZ) TT, addL (addL ZZ ZZ) TT)

/-- Niels subtraction's theorem, restated over limb lists. -/
theorem esn_pt {M M' : Word → BitVec 8} {out ep np : Word}
    (h : ∀ i, i < 10 →
        limbs M' out i = feSubW (esnPP M ep np) (esnMM M ep np) i ∧
        limbs M' (out + 0x28) i = feAddW (esnPP M ep np) (esnMM M ep np) i ∧
        limbs M' (out + 0x50) i = feSubW (eanZZ2 M ep np) (eanTT M ep np) i ∧
        limbs M' (out + 0x78) i = feAddW (eanZZ2 M ep np) (eanTT M ep np) i) :
    ptAt M' out = subNL (ptAt M ep) (ptAt M np) := by
  have e0 := feW_limbs_ofW fun i hi => (h i hi).1
  have e1 := feW_limbs_ofW fun i hi => (h i hi).2.1
  have e2 := feW_limbs_ofW fun i hi => (h i hi).2.2.1
  have e3 := feW_limbs_ofW fun i hi => (h i hi).2.2.2
  simp only [esnPP, esnMM, eanZZ2, eanTT, ofW_subW, ofW_addW, ofW_mulW, ofW_limbs] at e0 e1 e2 e3
  unfold ptAt subNL
  rw [show out + BitVec.ofNat 32 40 = out + 0x28 from rfl, show out + BitVec.ofNat 32 80 = out + 0x50 from rfl,
    show out + BitVec.ofNat 32 120 = out + 0x78 from rfl, e0, e1, e2, e3]
  rfl

/-- The three coordinates of a projective point at `a`. -/
def prAt (M : Word → BitVec 8) (a : Word) : List Nat × List Nat × List Nat :=
  (feW M a, feW M (a + BitVec.ofNat 32 40), feW M (a + BitVec.ofNat 32 80))

theorem panicFns_lo : ∀ p ∈ panicFns, 0x40000000 ≤ p.1 := by decide

/-- The panic code survives changes to memory below `0x40000000`. -/
theorem PanicCode.hi' {M M' : Word → BitVec 8} (h : PanicCode M) (hx : ∀ x : Word, 0x40000000 ≤ x.toNat → M' x = M x) :
    PanicCode M' := by
  intro p hp
  have h1 := panicFns_lo p hp
  have h2 := (panicFns_hi p hp).2
  have e : (BitVec.ofNat 32 p.1).toNat = p.1 := by rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega)]
  exact (h p hp).hi hx (by rw [e]; exact h1) (by rw [e]; omega)

section
variable {M0 Ms : Word → BitVec 8} {F pk sig msg : Word} {len : Nat} {r0 : Fin 32 → Word}
  {M : Word → BitVec 8} {n : Machine} {off : Nat}

set_option maxRecDepth 20000 in
set_option maxHeartbeats 8000000 in
/-- A call of `neg(F + e)` into `F + d`. -/
theorem EvSt.feNeg (C : EvCtx M0 F pk sig msg len) (D : EvSt M0 Ms F r0 M n off) {imm o : Word} {d e : Nat}
    (h1 : fetchRel ed25519VerifyCode off = some (.auipc ra imm, 4))
    (h2 : fetchRel ed25519VerifyCode (off + 4) = some (.jalr ra ra o, 4))
    (hb : EV + BitVec.ofNat 32 off + imm + o = BitVec.ofNat 32 feNegAddress) (hoff : (off + 8) % 2 = 0)
    (ha0 : reg n a0 = F + BitVec.ofNat 32 d) (ha1 : reg n a1 = F + BitVec.ofNat 32 e) (hd : d + 40 ≤ 0x166C)
    (hd4 : d % 4 = 0) (he : e + 40 ≤ 0x16A0) (he4 : e % 4 = 0) :
    ∃ n', Steps n n' ∧ EvSt M0 Ms F r0 n'.mem n' (off + 8) ∧ (∀ q : Fin 32, q.val ∈ evKeep → reg n' q = reg n q) ∧
      feW n'.mem (F + BitVec.ofNat 32 d) = negL (feW M (F + BitVec.ofNat 32 e)) ∧
      ∀ x, Sep (evG F) 0xA10 x 1 → Sep (F + BitVec.ofNat 32 d) 40 x 1 → n'.mem x = M x := by
  have hc := D.code C
  obtain ⟨n1, c1, pc1, mem1, regs1⟩ := D.st.callRa (cb := BitVec.ofNat 32 feNegAddress) hc h1 h2 hb (by decide)
  have r1 := PEnv.reg1 regs1 D.st.zero
  have hz : (0xFFFFFF60 : Word).toNat = 2 ^ 32 - 0xA0 := rfl
  have hi := D.hiM C
  have E : FNEnv n1.mem (BitVec.ofNat 32 feNegAddress) F (F + BitVec.ofNat 32 d) (F + BitVec.ofNat 32 e) := by
    rw [mem1]
    exact { hP := by decide
            cod := (D.pkEnv C).dec.neg
            red := by rw [show (BitVec.ofNat 32 feNegAddress + 0xFFFFE370 : Word) = BitVec.ofNat 32 feReduceAddress
                        by decide]; exact (D.pkEnv C).dec.red
            hsp := by have := C.hF; omega
            hS := by have := C.hlo; omega
            hout := C.al hd4
            hip := C.al he4
            sGC := (C.zone hz (by decide) (C.hiG (by decide) (by decide)).symm).symm
            sGR := (C.zone hz (by decide) (C.hiG (by decide) (by decide)).symm).symm
            sOC := C.codeF (by omega) (by decide) (by decide)
            sOG := C.zoneF hz (by decide) (by omega)
            sIG := C.zoneF hz (by decide) he }
  obtain ⟨n2, c2, pc2, sp2, k2, w2, f2⟩ := feNeg_correct n1 E pc1 (by rw [r1 _ (by decide), D.hsp])
    (by rw [r1 _ (by decide), ha0]) (by rw [r1 _ (by decide), ha1]) (by rw [regs1]; exact ev_ra)
    (even_clear _ (even_at EV (by decide) (off + 8) hoff))
  rw [mem1] at w2 f2
  have k2' : ∀ q : Fin 32, q.val ∈ evKeep → reg n2 q = reg n q := fun q hq => by
    rw [k2 q (by revert hq; revert q; decide), r1 q (by revert hq; revert q; decide)]
  have fz : ∀ x, Sep (evG F) 0xA10 x 1 → Sep (F + BitVec.ofNat 32 d) 40 x 1 → n2.mem x = M x :=
    fun x hx ho => f2 x (C.zoneIn hz (by decide) hx) ho
  exact ⟨n2, c1.trans c2, D.ret C (d := d) (k := 40) pc2 (by rw [sp2]) (k2' 3 (by decide)) (k2' 4 (by decide)) hd fz,
    k2', feW_neg w2, fz⟩

set_option maxRecDepth 20000 in
set_option maxHeartbeats 8000000 in
/-- A call of `non_adjacent_form(5)` of the scalar at `F + e` into the 256
digits at `F + d`. -/
theorem EvSt.naf (C : EvCtx M0 F pk sig msg len) (D : EvSt M0 Ms F r0 M n off) {imm o : Word} {d e : Nat}
    (h1 : fetchRel ed25519VerifyCode off = some (.auipc ra imm, 4))
    (h2 : fetchRel ed25519VerifyCode (off + 4) = some (.jalr ra ra o, 4))
    (hb : EV + BitVec.ofNat 32 off + imm + o = BitVec.ofNat 32 nonAdjacentFormAddress) (hoff : (off + 8) % 2 = 0)
    (ha0 : reg n a0 = F + BitVec.ofNat 32 d) (ha1 : reg n a1 = F + BitVec.ofNat 32 e) (hd : d + 256 ≤ 0x166C)
    (he : e + 32 ≤ 0x16A0) (hde : d + 256 ≤ e ∨ e + 32 ≤ d) :
    ∃ n', Steps n n' ∧ EvSt M0 Ms F r0 n'.mem n' (off + 8) ∧ (∀ q : Fin 32, q.val ∈ evKeep → reg n' q = reg n q) ∧
      (∀ k, k < 256 → n'.mem (F + BitVec.ofNat 32 d + BitVec.ofNat 32 k) =
        nafSpec (nafScalar M (F + BitVec.ofNat 32 e)) k) ∧
      ∀ x, Sep (evG F) 0xA10 x 1 → Sep (F + BitVec.ofNat 32 d) 256 x 1 → n'.mem x = M x := by
  have hc := D.code C
  obtain ⟨n1, c1, pc1, mem1, regs1⟩ := D.st.callRa (cb := BitVec.ofNat 32 nonAdjacentFormAddress) hc h1 h2 hb
    (by decide)
  have r1 := PEnv.reg1 regs1 D.st.zero
  have hz : (0xFFFFFFA0 : Word).toNat = 2 ^ 32 - 0x60 := rfl
  have hi := D.hiM C
  have E : NAFEnv n1.mem (BitVec.ofNat 32 nonAdjacentFormAddress) F (F + BitVec.ofNat 32 d) (F + BitVec.ofNat 32 e) := by
    rw [mem1]
    exact { hP := by decide
            cod := C.env.naf.hi hi (by decide) (by decide)
            ms := by rw [show (BitVec.ofNat 32 nonAdjacentFormAddress + 0x4236 : Word) = BitVec.ofNat 32 memsetAddress
                       by decide]; exact (D.pkEnv C).iso.mset
            ls := by rw [show (BitVec.ofNat 32 nonAdjacentFormAddress + 0x4450 : Word) = BitVec.ofNat 32 lshrdi3Address
                       by decide]; exact C.env.lsh.hi hi (by decide) (by decide)
            as := by rw [show (BitVec.ofNat 32 nonAdjacentFormAddress + 0x442C : Word) = BitVec.ofNat 32 ashldi3Address
                       by decide]; exact C.env.ash.hi hi (by decide) (by decide)
            hsa := by have := C.hF; omega
            hS := by have := C.hlo; omega
            sGC := (C.zone hz (by decide) (C.hiG (by decide) (by decide)).symm).symm
            sGM := (C.zone hz (by decide) (C.hiG (by decide) (by decide)).symm).symm
            sGL := (C.zone hz (by decide) (C.hiG (by decide) (by decide)).symm).symm
            sGA := (C.zone hz (by decide) (C.hiG (by decide) (by decide)).symm).symm
            sOC := C.codeF (by omega) (by decide) (by decide)
            sOM := C.codeF (by omega) (by decide) (by decide)
            sOL := C.codeF (by omega) (by decide) (by decide)
            sOA := C.codeF (by omega) (by decide) (by decide)
            sOG := C.zoneF hz (by decide) (by omega)
            sSG := C.zoneF hz (by decide) he
            sSO := C.offs (by omega) he (by omega)
            how := by rw [C.fN (by omega)]; have := C.hhi; omega }
  obtain ⟨n2, c2, pc2, sp2, k2, w2, f2⟩ := nonAdjacentForm_correct n1 E pc1 (by rw [r1 _ (by decide), D.hsp])
    (by rw [r1 _ (by decide), ha0]) (by rw [r1 _ (by decide), ha1]) (by rw [regs1]; exact ev_ra)
    (even_clear _ (even_at EV (by decide) (off + 8) hoff))
  rw [mem1] at w2 f2
  have k2' : ∀ q : Fin 32, q.val ∈ evKeep → reg n2 q = reg n q := fun q hq => by
    rw [k2 q (by revert hq; revert q; decide), r1 q (by revert hq; revert q; decide)]
  have fz : ∀ x, Sep (evG F) 0xA10 x 1 → Sep (F + BitVec.ofNat 32 d) 256 x 1 → n2.mem x = M x :=
    fun x hx ho => f2 x (C.zoneIn hz (by decide) hx) ho
  exact ⟨n2, c1.trans c2, D.ret C (d := d) (k := 256) pc2 (by rw [sp2]) (k2' 3 (by decide)) (k2' 4 (by decide)) hd fz,
    k2', w2, fz⟩

set_option maxRecDepth 20000 in
set_option maxHeartbeats 8000000 in
/-- A call of `NafLookupTable5::from` for the point at `A` into the eight
160-byte entries at `F + d`. -/
theorem EvSt.nafTbl (C : EvCtx M0 F pk sig msg len) (D : EvSt M0 Ms F r0 M n off) {imm o A : Word} {d : Nat}
    (h1 : fetchRel ed25519VerifyCode off = some (.auipc ra imm, 4))
    (h2 : fetchRel ed25519VerifyCode (off + 4) = some (.jalr ra ra o, 4))
    (hb : EV + BitVec.ofNat 32 off + imm + o = BitVec.ofNat 32 nafTableFromAddress) (hoff : (off + 8) % 2 = 0)
    (ha0 : reg n a0 = F + BitVec.ofNat 32 d) (ha1 : reg n a1 = A) (hd : d + 0x500 ≤ 0x166C) (hd4 : d % 4 = 0)
    (hA : A.toNat % 4 = 0) (hAw : A.toNat + 0xA0 ≤ 0x40000000) (sA : Sep A 0xA0 (evG F) 0xA10) :
    ∃ n', Steps n n' ∧ EvSt M0 Ms F r0 n'.mem n' (off + 8) ∧ (∀ q : Fin 32, q.val ∈ evKeep → reg n' q = reg n q) ∧
      (∀ i, i < 8 → ptAt n'.mem (F + BitVec.ofNat 32 d + BitVec.ofNat 32 (160 * i)) =
        nafTab (ptAt M A) (feW M apnD) i) ∧
      ∀ x, Sep (evG F) 0xA10 x 1 → Sep (F + BitVec.ofNat 32 d) 0x500 x 1 → n'.mem x = M x := by
  have hc := D.code C
  obtain ⟨n1, c1, pc1, mem1, regs1⟩ := D.st.callRa (cb := BitVec.ofNat 32 nafTableFromAddress) hc h1 h2 hb (by decide)
  have r1 := PEnv.reg1 regs1 D.st.zero
  have hi := D.hiM C
  have E : NtEnv n1.mem := by
    rw [mem1]
    exact { cod := C.env.ntf.hi hi (by decide) (by decide)
            apn := C.env.apn.hi hi (by decide) (by decide)
            ean := C.env.ean.hi hi (by decide) (by decide)
            ext := (D.pkEnv C).iso.ax
            dbl := (D.pkEnv C).iso.dbl
            add := (D.pkEnv C).iso.add
            sub := (D.pkEnv C).iso.sub
            mul := (D.pkEnv C).iso.mul
            red := (D.pkEnv C).iso.red
            sq := (D.pkEnv C).iso.sq
            sqi := (D.pkEnv C).iso.sqi
            mcs := (D.pkEnv C).iso.mcs
            mcb := (D.pkEnv C).iso.mcb }
  have hn1 : ∀ x, Sep (evG F) 0xA10 x 1 → n1.mem x = M x := fun x _ => by rw [mem1]
  obtain ⟨n2, c2, pc2, sp2, k2, w2, f2⟩ := nafTable_correct n1 E pc1 (by rw [r1 _ (by decide), ha0])
    (by rw [r1 _ (by decide), ha1]) (by rw [regs1]; exact ev_ra) (even_clear _ (even_at EV (by decide) (off + 8) hoff))
    (by rw [r1 _ (by decide), D.hsp]) (by have := C.hF; omega) C.hlo (by have := C.hhi; omega) hA hAw (C.al hd4)
    (by rw [C.fN (by omega)]; have := C.hhi; omega) sA (C.zF (by omega)).symm (C.zS (C.ro (by decide) (by decide)))
  rw [mem1] at w2 f2
  have k2' : ∀ q : Fin 32, q.val ∈ evKeep → reg n2 q = reg n q := fun q hq => by
    rw [k2 q (by revert hq; revert q; decide), r1 q (by revert hq; revert q; decide)]
  have fz : ∀ x, Sep (evG F) 0xA10 x 1 → Sep (F + BitVec.ofNat 32 d) 0x500 x 1 → n2.mem x = M x :=
    fun x hx ho => f2 x hx ho
  exact ⟨n2, c1.trans c2, D.ret C (d := d) (k := 0x500) pc2 (by rw [sp2]; try rw [D.hsp]) (k2' 3 (by decide))
    (k2' 4 (by decide)) hd fz, k2', w2, fz⟩

set_option maxRecDepth 20000 in
set_option maxHeartbeats 8000000 in
/-- A call of `ProjectivePoint::double(F + e)` into the completed point at `F + d`. -/
theorem EvSt.dbl (C : EvCtx M0 F pk sig msg len) (D : EvSt M0 Ms F r0 M n off) {imm o : Word} {d e : Nat}
    (h1 : fetchRel ed25519VerifyCode off = some (.auipc ra imm, 4))
    (h2 : fetchRel ed25519VerifyCode (off + 4) = some (.jalr ra ra o, 4))
    (hb : EV + BitVec.ofNat 32 off + imm + o = BitVec.ofNat 32 edDoubleAddress) (hoff : (off + 8) % 2 = 0)
    (ha0 : reg n a0 = F + BitVec.ofNat 32 d) (ha1 : reg n a1 = F + BitVec.ofNat 32 e) (hd : d + 160 ≤ 0x166C)
    (hd4 : d % 4 = 0) (he : e + 120 ≤ 0x16A0) (he4 : e % 4 = 0) :
    ∃ n', Steps n n' ∧ EvSt M0 Ms F r0 n'.mem n' (off + 8) ∧ (∀ q : Fin 32, q.val ∈ evKeep → reg n' q = reg n q) ∧
      ptAt n'.mem (F + BitVec.ofNat 32 d) = edDoubleSpec (prAt M (F + BitVec.ofNat 32 e)).1
        (prAt M (F + BitVec.ofNat 32 e)).2.1 (prAt M (F + BitVec.ofNat 32 e)).2.2 ∧
      ∀ x, Sep (evG F) 0xA10 x 1 → Sep (F + BitVec.ofNat 32 d) 160 x 1 → n'.mem x = M x := by
  have hc := D.code C
  have hz : (0xFFFFFDF0 : Word).toNat = 2 ^ 32 - 0x210 := rfl
  have E : EdDblEnv M (BitVec.ofNat 32 edDoubleAddress) (reg n sp + 0xFFFFFDF0) (reg n a0) (reg n a1) := by
    rw [D.hsp, ha0, ha1]
    exact { hP := by decide
            code := (D.pkEnv C).iso.dbl
            sq := by rw [show (BitVec.ofNat 32 edDoubleAddress + 0xFFFFE164 : Word) = BitVec.ofNat 32 feSquareAddress
                       by decide]; exact (D.pkEnv C).iso.sq
            sqi := by rw [show (BitVec.ofNat 32 edDoubleAddress + 0xFFFFE18A : Word) = BitVec.ofNat 32 feSquareInnerAddress
                        by decide]; exact (D.pkEnv C).iso.sqi
            red := by rw [show (BitVec.ofNat 32 edDoubleAddress + 0xFFFFDDF0 : Word) = BitVec.ofNat 32 feReduceAddress
                        by decide]; exact (D.pkEnv C).iso.red
            add := by rw [show (BitVec.ofNat 32 edDoubleAddress + 0xFFFFE674 : Word) = BitVec.ofNat 32 feAddAddress
                        by decide]; exact (D.pkEnv C).iso.add
            sub := by rw [show (BitVec.ofNat 32 edDoubleAddress + 0xFFFFE6C2 : Word) = BitVec.ofNat 32 feSubAddress
                        by decide]; exact (D.pkEnv C).iso.sub
            mcS := by rw [show (BitVec.ofNat 32 edDoubleAddress + 0x43FC : Word) = BitVec.ofNat 32 memcpyStubAddress
                        by decide]; exact (D.pkEnv C).iso.mcs
            mcB := by rw [show (BitVec.ofNat 32 edDoubleAddress + 0x4404 : Word) = BitVec.ofNat 32 memcpyStubAddress + 8
                        by decide]; exact (D.pkEnv C).iso.mcb
            hG := by rw [C.f16 hz (by decide)]; have := C.hF; have := C.hlo; omega
            hGt := by rw [C.f16 hz (by decide)]; have := C.hhi; omega
            hout := C.al hd4
            hot := by rw [C.fN (by omega)]; have := C.hhi; omega
            hsf := C.al he4
            hst := by rw [C.fN (by omega)]; have := C.hhi; omega
            sGC := (C.zone hz (by decide) (C.hiG (by decide) (by decide)).symm).symm
            sGQ := (C.zone hz (by decide) (C.hiG (by decide) (by decide)).symm).symm
            sGI := (C.zone hz (by decide) (C.hiG (by decide) (by decide)).symm).symm
            sGR := (C.zone hz (by decide) (C.hiG (by decide) (by decide)).symm).symm
            sGA := (C.zone hz (by decide) (C.hiG (by decide) (by decide)).symm).symm
            sGS := (C.zone hz (by decide) (C.hiG (by decide) (by decide)).symm).symm
            sGM := (C.zone hz (by decide) (C.hiG (by decide) (by decide)).symm).symm
            sGB := (C.zone hz (by decide) (C.hiG (by decide) (by decide)).symm).symm
            sOC := C.codeF (by omega) (by decide) (by decide)
            sOQ := C.codeF (by omega) (by decide) (by decide)
            sOI := C.codeF (by omega) (by decide) (by decide)
            sOR := C.codeF (by omega) (by decide) (by decide)
            sOA := C.codeF (by omega) (by decide) (by decide)
            sOS := C.codeF (by omega) (by decide) (by decide)
            sOM := C.codeF (by omega) (by decide) (by decide)
            sOB := C.codeF (by omega) (by decide) (by decide)
            sOG := C.zoneF hz (by decide) (by omega)
            sFG := C.zoneF hz (by decide) he }
  obtain ⟨n2, c2, s2, sp2, k2, w2, f2⟩ := D.st.callEdDouble hc h1 h2 hb (even_at EV (by decide) (off + 8) hoff) E
  rw [D.hsp, ha0] at f2
  rw [ha0, ha1] at w2
  have k2' : ∀ q : Fin 32, q.val ∈ evKeep → reg n2 q = reg n q := fun q hq =>
    k2 q (by revert hq; revert q; decide) (by revert hq; revert q; decide)
  have fz : ∀ x, Sep (evG F) 0xA10 x 1 → Sep (F + BitVec.ofNat 32 d) 160 x 1 → n2.mem x = M x :=
    fun x hx ho => f2 x (C.zoneIn hz (by decide) hx) ho
  exact ⟨n2, c2, D.ret C (d := d) (k := 160) s2.pc (by rw [sp2, D.hsp]) (k2' 3 (by decide)) (k2' 4 (by decide)) hd fz,
    k2', w2.symm, fz⟩

set_option maxRecDepth 20000 in
set_option maxHeartbeats 8000000 in
/-- A call of `CompletedPoint::as_extended(F + e)` into `F + d`. -/
theorem EvSt.ax (C : EvCtx M0 F pk sig msg len) (D : EvSt M0 Ms F r0 M n off) {imm o : Word} {d e : Nat}
    (h1 : fetchRel ed25519VerifyCode off = some (.auipc ra imm, 4))
    (h2 : fetchRel ed25519VerifyCode (off + 4) = some (.jalr ra ra o, 4))
    (hb : EV + BitVec.ofNat 32 off + imm + o = BitVec.ofNat 32 asExtendedAddress) (hoff : (off + 8) % 2 = 0)
    (ha0 : reg n a0 = F + BitVec.ofNat 32 d) (ha1 : reg n a1 = F + BitVec.ofNat 32 e) (hd : d + 160 ≤ 0x166C)
    (hd4 : d % 4 = 0) (he : e + 160 ≤ 0x16A0) (he4 : e % 4 = 0) (hde : d + 160 ≤ e ∨ e + 160 ≤ d) :
    ∃ n', Steps n n' ∧ EvSt M0 Ms F r0 n'.mem n' (off + 8) ∧ (∀ q : Fin 32, q.val ∈ evKeep → reg n' q = reg n q) ∧
      ptAt n'.mem (F + BitVec.ofNat 32 d) = extL (ptAt M (F + BitVec.ofNat 32 e)) ∧
      ∀ x, Sep (evG F) 0xA10 x 1 → Sep (F + BitVec.ofNat 32 d) 160 x 1 → n'.mem x = M x := by
  have hc := D.code C
  have hz : (0xFFFFFEA0 : Word).toNat = 2 ^ 32 - 0x160 := rfl
  have E : AxEnv M (BitVec.ofNat 32 asExtendedAddress) (reg n sp) (reg n a0) (reg n a1) := by
    rw [D.hsp, ha0, ha1]
    exact { hP := by decide
            code := (D.pkEnv C).iso.ax
            mul := by rw [show (BitVec.ofNat 32 asExtendedAddress + 0xFFFFD8E6 : Word) = BitVec.ofNat 32 feMulAddress
                        by decide]; exact (D.pkEnv C).iso.mul
            red := by rw [show (BitVec.ofNat 32 asExtendedAddress + 0xFFFFE3D6 : Word) = BitVec.ofNat 32 feReduceAddress
                        by decide]; exact (D.pkEnv C).iso.red
            hsp := by have := C.hF; omega
            hS := by have := C.hlo; omega
            hout := C.al hd4
            hcp := C.al he4
            sC := (C.zone hz (by decide) (C.hiG (by decide) (by decide)).symm).symm
            sM := (C.zone hz (by decide) (C.hiG (by decide) (by decide)).symm).symm
            sR := (C.zone hz (by decide) (C.hiG (by decide) (by decide)).symm).symm
            oR := C.zoneF hz (by decide) (by omega)
            cR := C.zoneF hz (by decide) he
            oCp := C.offs hde (by omega) he
            oC := C.codeF (by omega) (by decide) (by decide)
            oM := C.codeF (by omega) (by decide) (by decide)
            oRd := C.codeF (by omega) (by decide) (by decide) }
  obtain ⟨n2, c2, s2, sp2, k2, w0, w1, w2, w3, f2⟩ := D.st.callAsExt hc h1 h2 hb (even_at EV (by decide) (off + 8) hoff) E
  rw [D.hsp, ha0] at f2
  rw [ha0, ha1] at w0 w1 w2 w3
  have k2' : ∀ q : Fin 32, q.val ∈ evKeep → reg n2 q = reg n q := fun q hq =>
    k2 q (by revert hq; revert q; decide) (by revert hq; revert q; decide)
  have fz : ∀ x, Sep (evG F) 0xA10 x 1 → Sep (F + BitVec.ofNat 32 d) 160 x 1 → n2.mem x = M x :=
    fun x hx ho => f2 x (C.zoneIn hz (by decide) hx) ho
  refine ⟨n2, c2, D.ret C (d := d) (k := 160) s2.pc (by rw [sp2, D.hsp]) (k2' 3 (by decide)) (k2' 4 (by decide)) hd fz,
    k2', ?_, fz⟩
  unfold ptAt extL
  rw [show F + BitVec.ofNat 32 d + BitVec.ofNat 32 40 = F + BitVec.ofNat 32 d + 0x28 from rfl,
    show F + BitVec.ofNat 32 d + BitVec.ofNat 32 80 = F + BitVec.ofNat 32 d + 0x50 from rfl,
    show F + BitVec.ofNat 32 d + BitVec.ofNat 32 120 = F + BitVec.ofNat 32 d + 0x78 from rfl, w0, w1, w2, w3]
  rfl

set_option maxRecDepth 20000 in
set_option maxHeartbeats 8000000 in
/-- A call of `CompletedPoint::as_projective(F + e)` into `F + d`. -/
theorem EvSt.ap (C : EvCtx M0 F pk sig msg len) (D : EvSt M0 Ms F r0 M n off) {imm o : Word} {d e : Nat}
    (h1 : fetchRel ed25519VerifyCode off = some (.auipc ra imm, 4))
    (h2 : fetchRel ed25519VerifyCode (off + 4) = some (.jalr ra ra o, 4))
    (hb : EV + BitVec.ofNat 32 off + imm + o = BitVec.ofNat 32 asProjectiveAddress) (hoff : (off + 8) % 2 = 0)
    (ha0 : reg n a0 = F + BitVec.ofNat 32 d) (ha1 : reg n a1 = F + BitVec.ofNat 32 e) (hd : d + 120 ≤ 0x166C)
    (hd4 : d % 4 = 0) (he : e + 160 ≤ 0x16A0) (he4 : e % 4 = 0) (hde : d + 120 ≤ e ∨ e + 160 ≤ d) :
    ∃ n', Steps n n' ∧ EvSt M0 Ms F r0 n'.mem n' (off + 8) ∧ (∀ q : Fin 32, q.val ∈ evKeep → reg n' q = reg n q) ∧
      prAt n'.mem (F + BitVec.ofNat 32 d) = (mulL (ptAt M (F + BitVec.ofNat 32 e)).1 (ptAt M (F + BitVec.ofNat 32 e)).2.2.2,
        mulL (ptAt M (F + BitVec.ofNat 32 e)).2.1 (ptAt M (F + BitVec.ofNat 32 e)).2.2.1,
        mulL (ptAt M (F + BitVec.ofNat 32 e)).2.2.1 (ptAt M (F + BitVec.ofNat 32 e)).2.2.2) ∧
      ∀ x, Sep (evG F) 0xA10 x 1 → Sep (F + BitVec.ofNat 32 d) 120 x 1 → n'.mem x = M x := by
  have hc := D.code C
  have hz : (0xFFFFFEB0 : Word).toNat = 2 ^ 32 - 0x150 := rfl
  have E : ApEnv M (BitVec.ofNat 32 asProjectiveAddress) (reg n sp) (reg n a0) (reg n a1) := by
    rw [D.hsp, ha0, ha1]
    exact { hP := by decide
            code := (D.pkEnv C).iso.ap
            mul := by rw [show (BitVec.ofNat 32 asProjectiveAddress + 0xFFFFD34C : Word) = BitVec.ofNat 32 feMulAddress
                        by decide]; exact (D.pkEnv C).iso.mul
            red := by rw [show (BitVec.ofNat 32 asProjectiveAddress + 0xFFFFDE3C : Word) = BitVec.ofNat 32 feReduceAddress
                        by decide]; exact (D.pkEnv C).iso.red
            hsp := by have := C.hF; omega
            hS := by have := C.hlo; omega
            hout := C.al hd4
            hcp := C.al he4
            sC := (C.zone hz (by decide) (C.hiG (by decide) (by decide)).symm).symm
            sM := (C.zone hz (by decide) (C.hiG (by decide) (by decide)).symm).symm
            sR := (C.zone hz (by decide) (C.hiG (by decide) (by decide)).symm).symm
            oR := C.zoneF hz (by decide) (by omega)
            cR := C.zoneF hz (by decide) he
            oCp := C.offs hde (by omega) he
            oC := C.codeF (by omega) (by decide) (by decide)
            oM := C.codeF (by omega) (by decide) (by decide)
            oRd := C.codeF (by omega) (by decide) (by decide) }
  obtain ⟨n2, c2, s2, sp2, k2, w0, w1, w2, f2⟩ := D.st.callAsProj hc h1 h2 hb (even_at EV (by decide) (off + 8) hoff) E
  rw [D.hsp, ha0] at f2
  rw [ha0, ha1] at w0 w1 w2
  have k2' : ∀ q : Fin 32, q.val ∈ evKeep → reg n2 q = reg n q := fun q hq =>
    k2 q (by revert hq; revert q; decide) (by revert hq; revert q; decide)
  have fz : ∀ x, Sep (evG F) 0xA10 x 1 → Sep (F + BitVec.ofNat 32 d) 120 x 1 → n2.mem x = M x :=
    fun x hx ho => f2 x (C.zoneIn hz (by decide) hx) ho
  refine ⟨n2, c2, D.ret C (d := d) (k := 120) s2.pc (by rw [sp2, D.hsp]) (k2' 3 (by decide)) (k2' 4 (by decide)) hd fz,
    k2', ?_, fz⟩
  unfold prAt ptAt
  rw [show F + BitVec.ofNat 32 d + BitVec.ofNat 32 40 = F + BitVec.ofNat 32 d + 0x28 from rfl,
    show F + BitVec.ofNat 32 d + BitVec.ofNat 32 80 = F + BitVec.ofNat 32 d + 0x50 from rfl, w0, w1, w2]
  rfl

set_option maxRecDepth 20000 in
set_option maxHeartbeats 16000000 in
/-- A call of `&EdwardsPoint + &ProjectiveNielsPoint` with the result at `F + d`. -/
theorem EvSt.ean (C : EvCtx M0 F pk sig msg len) (D : EvSt M0 Ms F r0 M n off) {imm o : Word} {d e g : Nat}
    (h1 : fetchRel ed25519VerifyCode off = some (.auipc ra imm, 4))
    (h2 : fetchRel ed25519VerifyCode (off + 4) = some (.jalr ra ra o, 4))
    (hb : EV + BitVec.ofNat 32 off + imm + o = BitVec.ofNat 32 edAddNielsAddress) (hoff : (off + 8) % 2 = 0)
    (ha0 : reg n a0 = F + BitVec.ofNat 32 d) (ha1 : reg n a1 = F + BitVec.ofNat 32 e)
    (ha2 : reg n a2 = F + BitVec.ofNat 32 g) (hd : d + 160 ≤ 0x166C) (hd4 : d % 4 = 0) (he : e + 160 ≤ 0x16A0)
    (he4 : e % 4 = 0) (hg : g + 160 ≤ 0x16A0) (hg4 : g % 4 = 0) (hed : e + 160 ≤ d ∨ d + 160 ≤ e)
    (hgd : g + 160 ≤ d ∨ d + 160 ≤ g) :
    ∃ n', Steps n n' ∧ EvSt M0 Ms F r0 n'.mem n' (off + 8) ∧ (∀ q : Fin 32, q.val ∈ evKeep → reg n' q = reg n q) ∧
      ptAt n'.mem (F + BitVec.ofNat 32 d) = addNL (ptAt M (F + BitVec.ofNat 32 e)) (ptAt M (F + BitVec.ofNat 32 g)) ∧
      ∀ x, Sep (evG F) 0xA10 x 1 → Sep (F + BitVec.ofNat 32 d) 160 x 1 → n'.mem x = M x := by
  have hc := D.code C
  have hz : (0xFFFFFD90 : Word).toNat = 2 ^ 32 - 0x270 := rfl
  have zc : ∀ {b : Word} {k : Nat}, 0x40000000 ≤ b.toNat → b.toNat + k ≤ 2 ^ 32 → Sep (F + 0xFFFFFD90) 0x270 b k :=
    fun h1 h2 => (C.zone hz (by decide) (C.hiG h1 h2).symm).symm
  have oc : ∀ {b : Word} {k : Nat}, 0x40000000 ≤ b.toNat → b.toNat + k ≤ 2 ^ 32 → Sep (F + BitVec.ofNat 32 d) 0xA0 b k :=
    fun h1 h2 => C.codeF (by omega) h1 h2
  have E : EANEnv M (BitVec.ofNat 32 edAddNielsAddress) F (F + BitVec.ofNat 32 d) (F + BitVec.ofNat 32 e)
      (F + BitVec.ofNat 32 g) := by
    exact { hP := by decide
            cod := C.env.ean.hi (D.hiM C) (by decide) (by decide)
            add := by rw [show (BitVec.ofNat 32 edAddNielsAddress + 0xFFFFE79E : Word) = BitVec.ofNat 32 feAddAddress by decide]
                      exact (D.pkEnv C).iso.add
            addS := by rw [show (BitVec.ofNat 32 edAddNielsAddress + 0xFFFFE79E + 0x5D88 : Word) = BitVec.ofNat 32 memcpyStubAddress
                         by decide]; exact (D.pkEnv C).iso.mcs
            addB := by rw [show (BitVec.ofNat 32 edAddNielsAddress + 0xFFFFE79E + 0x5D90 : Word) = BitVec.ofNat 32 memcpyStubAddress + 8
                         by decide]; exact (D.pkEnv C).iso.mcb
            sub := by rw [show (BitVec.ofNat 32 edAddNielsAddress + 0xFFFFE7EC : Word) = BitVec.ofNat 32 feSubAddress by decide]
                      exact (D.pkEnv C).iso.sub
            subR := by rw [show (BitVec.ofNat 32 edAddNielsAddress + 0xFFFFE7EC + 0xFFFFF72E : Word) = BitVec.ofNat 32 feReduceAddress
                         by decide]; exact (D.pkEnv C).iso.red
            mul := by rw [show (BitVec.ofNat 32 edAddNielsAddress + 0xFFFFD42A : Word) = BitVec.ofNat 32 feMulAddress by decide]
                      exact (D.pkEnv C).iso.mul
            mulR := by rw [show (BitVec.ofNat 32 edAddNielsAddress + 0xFFFFD42A + 0xAF0 : Word) = BitVec.ofNat 32 feReduceAddress
                         by decide]; exact (D.pkEnv C).iso.red
            hsp := by have := C.hF; omega
            hS := by have := C.hlo; omega
            hout := C.al hd4
            hep := C.al he4
            hnp := C.al hg4
            how := by rw [C.fN (by omega)]; have := C.hhi; omega
            hew := by rw [C.fN (by omega)]; have := C.hhi; omega
            hnw := by rw [C.fN (by omega)]; have := C.hhi; omega
            sG := ⟨zc (by decide) (by decide), zc (by decide) (by decide), zc (by decide) (by decide), zc (by decide) (by decide), zc (by decide) (by decide), zc (by decide) (by decide), zc (by decide) (by decide), zc (by decide) (by decide)⟩
            sO := ⟨oc (by decide) (by decide), oc (by decide) (by decide), oc (by decide) (by decide), oc (by decide) (by decide), oc (by decide) (by decide), oc (by decide) (by decide), oc (by decide) (by decide), oc (by decide) (by decide)⟩
            sOG := C.zoneF hz (by decide) (by omega)
            sEG := C.zoneF hz (by decide) he
            sNG := C.zoneF hz (by decide) hg
            sEO := C.offs hed he (by omega)
            sNO := C.offs hgd hg (by omega) }
  obtain ⟨n1, c1, pc1, mem1, regs1⟩ := D.st.callRa (cb := BitVec.ofNat 32 edAddNielsAddress) hc h1 h2 hb (by decide)
  have r1 := PEnv.reg1 regs1 D.st.zero
  obtain ⟨n2, c2, pc2, sp2, k2, w2, f2⟩ := edAddNiels_correct n1 (by rw [mem1]; exact E) pc1
    (by rw [r1 _ (by decide), D.hsp]) (by rw [r1 _ (by decide), ha0]) (by rw [r1 _ (by decide), ha1])
    (by rw [r1 _ (by decide), ha2]) (by rw [regs1]; exact ev_ra) (even_clear _ (even_at EV (by decide) (off + 8) hoff))
  rw [mem1] at w2 f2
  have k2' : ∀ q : Fin 32, q.val ∈ evKeep → reg n2 q = reg n q := fun q hq => by
    rw [k2 q (by revert hq; revert q; decide), r1 q (by revert hq; revert q; decide)]
  have fz : ∀ x, Sep (evG F) 0xA10 x 1 → Sep (F + BitVec.ofNat 32 d) 160 x 1 → n2.mem x = M x :=
    fun x hx ho => f2 x (C.zoneIn hz (by decide) hx) ho
  exact ⟨n2, c1.trans c2, D.ret C (d := d) (k := 160) pc2 (by rw [sp2]) (k2' 3 (by decide)) (k2' 4 (by decide)) hd fz,
    k2', ean_pt w2, fz⟩

set_option maxRecDepth 20000 in
set_option maxHeartbeats 16000000 in
/-- A call of `&EdwardsPoint - &ProjectiveNielsPoint` with the result at `F + d`. -/
theorem EvSt.esn (C : EvCtx M0 F pk sig msg len) (D : EvSt M0 Ms F r0 M n off) {imm o : Word} {d e g : Nat}
    (h1 : fetchRel ed25519VerifyCode off = some (.auipc ra imm, 4))
    (h2 : fetchRel ed25519VerifyCode (off + 4) = some (.jalr ra ra o, 4))
    (hb : EV + BitVec.ofNat 32 off + imm + o = BitVec.ofNat 32 edSubNielsAddress) (hoff : (off + 8) % 2 = 0)
    (ha0 : reg n a0 = F + BitVec.ofNat 32 d) (ha1 : reg n a1 = F + BitVec.ofNat 32 e)
    (ha2 : reg n a2 = F + BitVec.ofNat 32 g) (hd : d + 160 ≤ 0x166C) (hd4 : d % 4 = 0) (he : e + 160 ≤ 0x16A0)
    (he4 : e % 4 = 0) (hg : g + 160 ≤ 0x16A0) (hg4 : g % 4 = 0) (hed : e + 160 ≤ d ∨ d + 160 ≤ e)
    (hgd : g + 160 ≤ d ∨ d + 160 ≤ g) :
    ∃ n', Steps n n' ∧ EvSt M0 Ms F r0 n'.mem n' (off + 8) ∧ (∀ q : Fin 32, q.val ∈ evKeep → reg n' q = reg n q) ∧
      ptAt n'.mem (F + BitVec.ofNat 32 d) = subNL (ptAt M (F + BitVec.ofNat 32 e)) (ptAt M (F + BitVec.ofNat 32 g)) ∧
      ∀ x, Sep (evG F) 0xA10 x 1 → Sep (F + BitVec.ofNat 32 d) 160 x 1 → n'.mem x = M x := by
  have hc := D.code C
  have hz : (0xFFFFFD90 : Word).toNat = 2 ^ 32 - 0x270 := rfl
  have zc : ∀ {b : Word} {k : Nat}, 0x40000000 ≤ b.toNat → b.toNat + k ≤ 2 ^ 32 → Sep (F + 0xFFFFFD90) 0x270 b k :=
    fun h1 h2 => (C.zone hz (by decide) (C.hiG h1 h2).symm).symm
  have oc : ∀ {b : Word} {k : Nat}, 0x40000000 ≤ b.toNat → b.toNat + k ≤ 2 ^ 32 → Sep (F + BitVec.ofNat 32 d) 0xA0 b k :=
    fun h1 h2 => C.codeF (by omega) h1 h2
  have E : ESNEnv M (BitVec.ofNat 32 edSubNielsAddress) F (F + BitVec.ofNat 32 d) (F + BitVec.ofNat 32 e)
      (F + BitVec.ofNat 32 g) := by
    exact { hP := by decide
            cod := C.env.esn.hi (D.hiM C) (by decide) (by decide)
            add := by rw [show (BitVec.ofNat 32 edSubNielsAddress + 0xFFFFE2A6 : Word) = BitVec.ofNat 32 feAddAddress by decide]
                      exact (D.pkEnv C).iso.add
            addS := by rw [show (BitVec.ofNat 32 edSubNielsAddress + 0xFFFFE2A6 + 0x5D88 : Word) = BitVec.ofNat 32 memcpyStubAddress
                         by decide]; exact (D.pkEnv C).iso.mcs
            addB := by rw [show (BitVec.ofNat 32 edSubNielsAddress + 0xFFFFE2A6 + 0x5D90 : Word) = BitVec.ofNat 32 memcpyStubAddress + 8
                         by decide]; exact (D.pkEnv C).iso.mcb
            sub := by rw [show (BitVec.ofNat 32 edSubNielsAddress + 0xFFFFE2F4 : Word) = BitVec.ofNat 32 feSubAddress by decide]
                      exact (D.pkEnv C).iso.sub
            subR := by rw [show (BitVec.ofNat 32 edSubNielsAddress + 0xFFFFE2F4 + 0xFFFFF72E : Word) = BitVec.ofNat 32 feReduceAddress
                         by decide]; exact (D.pkEnv C).iso.red
            mul := by rw [show (BitVec.ofNat 32 edSubNielsAddress + 0xFFFFCF32 : Word) = BitVec.ofNat 32 feMulAddress by decide]
                      exact (D.pkEnv C).iso.mul
            mulR := by rw [show (BitVec.ofNat 32 edSubNielsAddress + 0xFFFFCF32 + 0xAF0 : Word) = BitVec.ofNat 32 feReduceAddress
                         by decide]; exact (D.pkEnv C).iso.red
            hsp := by have := C.hF; omega
            hS := by have := C.hlo; omega
            hout := C.al hd4
            hep := C.al he4
            hnp := C.al hg4
            how := by rw [C.fN (by omega)]; have := C.hhi; omega
            hew := by rw [C.fN (by omega)]; have := C.hhi; omega
            hnw := by rw [C.fN (by omega)]; have := C.hhi; omega
            sG := ⟨zc (by decide) (by decide), zc (by decide) (by decide), zc (by decide) (by decide), zc (by decide) (by decide), zc (by decide) (by decide), zc (by decide) (by decide), zc (by decide) (by decide), zc (by decide) (by decide)⟩
            sO := ⟨oc (by decide) (by decide), oc (by decide) (by decide), oc (by decide) (by decide), oc (by decide) (by decide), oc (by decide) (by decide), oc (by decide) (by decide), oc (by decide) (by decide), oc (by decide) (by decide)⟩
            sOG := C.zoneF hz (by decide) (by omega)
            sEG := C.zoneF hz (by decide) he
            sNG := C.zoneF hz (by decide) hg
            sEO := C.offs hed he (by omega)
            sNO := C.offs hgd hg (by omega) }
  obtain ⟨n1, c1, pc1, mem1, regs1⟩ := D.st.callRa (cb := BitVec.ofNat 32 edSubNielsAddress) hc h1 h2 hb (by decide)
  have r1 := PEnv.reg1 regs1 D.st.zero
  obtain ⟨n2, c2, pc2, sp2, k2, w2, f2⟩ := edSubNiels_correct n1 (by rw [mem1]; exact E) pc1
    (by rw [r1 _ (by decide), D.hsp]) (by rw [r1 _ (by decide), ha0]) (by rw [r1 _ (by decide), ha1])
    (by rw [r1 _ (by decide), ha2]) (by rw [regs1]; exact ev_ra) (even_clear _ (even_at EV (by decide) (off + 8) hoff))
  rw [mem1] at w2 f2
  have k2' : ∀ q : Fin 32, q.val ∈ evKeep → reg n2 q = reg n q := fun q hq => by
    rw [k2 q (by revert hq; revert q; decide), r1 q (by revert hq; revert q; decide)]
  have fz : ∀ x, Sep (evG F) 0xA10 x 1 → Sep (F + BitVec.ofNat 32 d) 160 x 1 → n2.mem x = M x :=
    fun x hx ho => f2 x (C.zoneIn hz (by decide) hx) ho
  exact ⟨n2, c1.trans c2, D.ret C (d := d) (k := 160) pc2 (by rw [sp2]) (k2' 3 (by decide)) (k2' 4 (by decide)) hd fz,
    k2', esn_pt w2, fz⟩

set_option maxRecDepth 20000 in
set_option maxHeartbeats 8000000 in
/-- A call of `NafLookupTable5::select(x)` on the table at `F + t`, for
`x ≤ 15`, with the result at `F + d`. -/
theorem EvSt.nsel (C : EvCtx M0 F pk sig msg len) (D : EvSt M0 Ms F r0 M n off) {imm o x : Word} {d t : Nat}
    (h1 : fetchRel ed25519VerifyCode off = some (.auipc ra imm, 4))
    (h2 : fetchRel ed25519VerifyCode (off + 4) = some (.jalr ra ra o, 4))
    (hb : EV + BitVec.ofNat 32 off + imm + o = BitVec.ofNat 32 nafSelectAddress) (hoff : (off + 8) % 2 = 0)
    (ha0 : reg n a0 = F + BitVec.ofNat 32 d) (ha1 : reg n a1 = F + BitVec.ofNat 32 t) (ha2 : reg n a2 = x)
    (hx : x.toNat ≤ 15) (hd : d + 160 ≤ 0x166C) (ht : t + 0x500 ≤ 0x16A0) (hdt : d + 160 ≤ t ∨ t + 0x500 ≤ d) :
    ∃ n', Steps n n' ∧ EvSt M0 Ms F r0 n'.mem n' (off + 8) ∧ (∀ q : Fin 32, q.val ∈ evKeep → reg n' q = reg n q) ∧
      ∀ y, Sep (evG F) 0xA10 y 1 → n'.mem y = copyBytes M (F + BitVec.ofNat 32 d)
        (F + BitVec.ofNat 32 t + BitVec.ofNat 32 (x.toNat / 2 * 160)) 160 y := by
  have hc := D.code C
  have hz : (0xFFFFFFF0 : Word).toNat = 2 ^ 32 - 16 := rfl
  obtain ⟨n1, c1, pc1, mem1, regs1⟩ := D.st.callRa (cb := BitVec.ofNat 32 nafSelectAddress) hc h1 h2 hb (by decide)
  have r1 := PEnv.reg1 regs1 D.st.zero
  have sp1 : reg n1 sp = F := by rw [r1 _ (by decide), D.hsp]
  have hsrc : F + BitVec.ofNat 32 t + BitVec.ofNat 32 (x.toNat / 2 * 160) = F + BitVec.ofNat 32 (t + x.toNat / 2 * 160) :=
    add_ofNat_assoc F _ _
  have hxe : x.toNat / 2 * 160 + 160 ≤ 0x500 := by omega
  have E : McEnv n1.mem (stubBase + 8) (F + BitVec.ofNat 32 d) (F + BitVec.ofNat 32 t + BitVec.ofNat 32 (x.toNat / 2 * 160))
      (reg n1 sp + 0xFFFFFFF0) 160 := by
    rw [mem1, sp1, hsrc]
    exact { code := (D.pkEnv C).iso.mcb
            hDC := C.codeF (by omega) (by decide) (by decide)
            hFC := (C.zone hz (by decide) (C.hiG (by decide) (by decide)).symm).symm
            hdF := C.zoneF hz (by decide) (by omega)
            hsF := C.zoneF hz (by decide) (by omega)
            hsep := C.offs (by omega) (by omega) (by omega)
            hF := by rw [C.f16 hz (by decide)]; have := C.hF; have := C.hlo; omega
            hFw := by rw [C.f16 hz (by decide)]; have := C.hhi; omega
            hdw := by rw [C.fN (by omega)]; have := C.hhi; omega
            hsw := by rw [C.fN (by omega)]; have := C.hhi; omega }
  obtain ⟨n2, c2, pc2, sp2, k2, f2⟩ := (nafSelect_correct n1 (by rw [mem1]; exact C.env.panic.hi' (D.hiM C))
    (by rw [mem1]; exact C.env.nsel.hi (D.hiM C) (by decide) (by decide))
    (by rw [mem1]; exact (D.pkEnv C).iso.mcs) pc1 (by rw [r1 _ (by decide), ha0]) (by rw [r1 _ (by decide), ha1])
    (by rw [r1 _ (by decide), ha2]) (by rw [regs1]; exact ev_ra) (even_clear _ (even_at EV (by decide) (off + 8) hoff))).1
    hx E
  rw [mem1, sp1] at f2
  have k2' : ∀ q : Fin 32, q.val ∈ evKeep → reg n2 q = reg n q := fun q hq => by
    rw [k2 q (by revert hq; revert q; decide), r1 q (by revert hq; revert q; decide)]
  have fz : ∀ y, Sep (evG F) 0xA10 y 1 → n2.mem y = copyBytes M (F + BitVec.ofNat 32 d)
      (F + BitVec.ofNat 32 t + BitVec.ofNat 32 (x.toNat / 2 * 160)) 160 y :=
    fun y hy => f2 y (C.zoneIn hz (by decide) hy)
  exact ⟨n2, c1.trans c2, D.ret C (d := d) (k := 160) pc2 (by rw [sp2, sp1]) (k2' 3 (by decide)) (k2' 4 (by decide)) hd
    (fun y hy ho => by rw [fz y hy]; exact copyBytes_sep ho (Nat.le_refl _)), k2', fz⟩

end

end C3.RV32
