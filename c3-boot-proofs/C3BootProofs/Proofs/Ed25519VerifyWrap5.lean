import C3BootProofs.Proofs.Ed25519VerifyWrap4

/-!
# `ed25519_verify`'s calls in the final compression

Call lemmas for the field operations that turn the result of the loop into
compressed bytes: `mul`, `square`, `pow22501`, `pow2k`, `to_bytes`, and
`is_negative`, each stated over limb lists.
-/

namespace C3.RV32

open C3.Image

/-- The second of `pow22501`'s pair on limbs: `x^11`. -/
def pw3L (l : List Nat) : List Nat := ofW (pwT3 (limbF l))

theorem pwT3_congr {x x' : Nat → Word} (hx : ∀ i, i < 10 → x i = x' i) : pwT3 x = pwT3 x' := by
  have e0 : pwT0 x = pwT0 x' := feSqW_congr hx
  have e1 : pwT1 x = pwT1 x' := by unfold pwT1 pwT0s; rw [e0]
  have e2 : pwT2 x = pwT2 x' := by unfold pwT2; rw [feMulW_congr hx (fun _ _ => rfl), e1]
  unfold pwT3; rw [e0, e2]

theorem feW_pw3 {M M' : Word → BitVec 8} {o x : Word} (h : ∀ i, i < 10 → limbs M' o i = pwT3 (limbs M x) i) :
    feW M' o = pw3L (feW M x) := by
  rw [feW_limbs_ofW h, pwT3_congr (limbs_limbF (M := M) (a := x))]; rfl

section
variable {M0 Ms : Word → BitVec 8} {F pk sig msg : Word} {len : Nat} {r0 : Fin 32 → Word}
  {M : Word → BitVec 8} {n : Machine} {off : Nat}

set_option maxRecDepth 20000 in
set_option maxHeartbeats 8000000 in
/-- A call of `mul(F + e, F + g)` into `F + d`. -/
theorem EvSt.feMul (C : EvCtx M0 F pk sig msg len) (D : EvSt M0 Ms F r0 M n off) {imm o : Word} {d e g : Nat}
    (h1 : fetchRel ed25519VerifyCode off = some (.auipc ra imm, 4))
    (h2 : fetchRel ed25519VerifyCode (off + 4) = some (.jalr ra ra o, 4))
    (hb : EV + BitVec.ofNat 32 off + imm + o = BitVec.ofNat 32 feMulAddress) (hoff : (off + 8) % 2 = 0)
    (ha0 : reg n a0 = F + BitVec.ofNat 32 d) (ha1 : reg n a1 = F + BitVec.ofNat 32 e)
    (ha2 : reg n a2 = F + BitVec.ofNat 32 g) (hd : d + 40 ≤ 0x166C) (hd4 : d % 4 = 0)
    (he : e + 40 ≤ 0x16A0) (he4 : e % 4 = 0) (hg : g + 40 ≤ 0x16A0) (hg4 : g % 4 = 0) :
    ∃ n', Steps n n' ∧ EvSt M0 Ms F r0 n'.mem n' (off + 8) ∧ (∀ q : Fin 32, q.val ∈ evKeep → reg n' q = reg n q) ∧
      feW n'.mem (F + BitVec.ofNat 32 d) = mulL (feW M (F + BitVec.ofNat 32 e)) (feW M (F + BitVec.ofNat 32 g)) ∧
      ∀ x, Sep (evG F) 0xA10 x 1 → Sep (F + BitVec.ofNat 32 d) 40 x 1 → n'.mem x = M x := by
  have hc := D.code C
  have hz : (0xFFFFFEC0 : Word).toNat = 2 ^ 32 - 0x140 := rfl
  have E : FeMEnv M (BitVec.ofNat 32 feMulAddress) (reg n sp) (reg n a0) (reg n a1) (reg n a2) := by
    rw [D.hsp, ha0, ha1, ha2]
    exact { hP := by decide
            code := (D.pkEnv C).dec.mul
            red := by rw [show (BitVec.ofNat 32 feMulAddress + 0xAF0 : Word) = BitVec.ofNat 32 feReduceAddress
                        by decide]; exact (D.pkEnv C).dec.red
            hsp := by have := C.hF; omega
            hS := by have := C.hlo; omega
            hout := C.al hd4
            hx := C.al he4
            hy := C.al hg4
            sGC := (C.zone hz (by decide) (C.hiG (by decide) (by decide)).symm).symm
            sGR := (C.zone hz (by decide) (C.hiG (by decide) (by decide)).symm).symm
            sOC := C.codeF (by omega) (by decide) (by decide)
            sOR := C.codeF (by omega) (by decide) (by decide)
            sOG := C.zoneF hz (by decide) (by omega)
            sXG := C.zoneF hz (by decide) he
            sYG := C.zoneF hz (by decide) hg }
  obtain ⟨n2, c2, s2, sp2, k2, w2, f2⟩ := D.st.callFeMulL hc h1 h2 hb (even_at EV (by decide) (off + 8) hoff) E
  rw [D.hsp, ha0] at f2
  rw [ha0, ha1, ha2] at w2
  have k2' : ∀ q : Fin 32, q.val ∈ evKeep → reg n2 q = reg n q := fun q hq =>
    k2 q (by revert hq; revert q; decide) (by revert hq; revert q; decide)
  have fz : ∀ x, Sep (evG F) 0xA10 x 1 → Sep (F + BitVec.ofNat 32 d) 40 x 1 → n2.mem x = M x :=
    fun x hx ho => f2 x (C.zoneIn hz (by decide) hx) ho
  exact ⟨n2, c2, D.ret C (d := d) (k := 40) s2.pc (by rw [sp2, D.hsp]) (k2' 3 (by decide)) (k2' 4 (by decide)) hd fz,
    k2', w2, fz⟩

set_option maxRecDepth 20000 in
set_option maxHeartbeats 8000000 in
/-- A call of `square(F + e)` into `F + d`. -/
theorem EvSt.feSq (C : EvCtx M0 F pk sig msg len) (D : EvSt M0 Ms F r0 M n off) {imm o : Word} {d e : Nat}
    (h1 : fetchRel ed25519VerifyCode off = some (.auipc ra imm, 4))
    (h2 : fetchRel ed25519VerifyCode (off + 4) = some (.jalr ra ra o, 4))
    (hb : EV + BitVec.ofNat 32 off + imm + o = BitVec.ofNat 32 feSquareAddress) (hoff : (off + 8) % 2 = 0)
    (ha0 : reg n a0 = F + BitVec.ofNat 32 d) (ha1 : reg n a1 = F + BitVec.ofNat 32 e) (hd : d + 40 ≤ 0x166C)
    (hd4 : d % 4 = 0) (he : e + 40 ≤ 0x16A0) (he4 : e % 4 = 0) :
    ∃ n', Steps n n' ∧ EvSt M0 Ms F r0 n'.mem n' (off + 8) ∧ (∀ q : Fin 32, q.val ∈ evKeep → reg n' q = reg n q) ∧
      feW n'.mem (F + BitVec.ofNat 32 d) = sqL (feW M (F + BitVec.ofNat 32 e)) ∧
      ∀ x, Sep (evG F) 0xA10 x 1 → Sep (F + BitVec.ofNat 32 d) 40 x 1 → n'.mem x = M x := by
  have hc := D.code C
  obtain ⟨n1, c1, pc1, mem1, regs1⟩ := D.st.callRa (cb := BitVec.ofNat 32 feSquareAddress) hc h1 h2 hb (by decide)
  have r1 := PEnv.reg1 regs1 D.st.zero
  have hz : (0xFFFFFF50 : Word).toNat = 2 ^ 32 - 0xB0 := rfl
  have E : FeSquareEnv n1.mem (BitVec.ofNat 32 feSquareAddress) F (F + BitVec.ofNat 32 d) (F + BitVec.ofNat 32 e) := by
    rw [mem1]
    exact { hP := by decide
            code := (D.pkEnv C).dec.sq
            sqi := by rw [show (BitVec.ofNat 32 feSquareAddress + 0x26 : Word) = BitVec.ofNat 32 feSquareInnerAddress
                        by decide]; exact (D.pkEnv C).dec.sqi
            red := by rw [show (BitVec.ofNat 32 feSquareAddress + 0xFFFFFC8C : Word) = BitVec.ofNat 32 feReduceAddress
                        by decide]; exact (D.pkEnv C).dec.red
            hsp := by have := C.hF; omega
            hS := by have := C.hlo; omega
            hout := C.al hd4
            hx := C.al he4
            sGC := (C.zone hz (by decide) (C.hiG (by decide) (by decide)).symm).symm
            sGI := (C.zone hz (by decide) (C.hiG (by decide) (by decide)).symm).symm
            sGR := (C.zone hz (by decide) (C.hiG (by decide) (by decide)).symm).symm
            sOC := C.codeF (by omega) (by decide) (by decide)
            sOR := C.codeF (by omega) (by decide) (by decide)
            sOG := C.zoneF hz (by decide) (by omega)
            sXG := C.zoneF hz (by decide) he }
  obtain ⟨n2, c2, pc2, sp2, k2, w2, f2⟩ := feSquare_correct n1 E pc1 (by rw [r1 _ (by decide), ha0])
    (by rw [r1 _ (by decide), ha1]) (by rw [regs1]; exact ev_ra) (even_clear _ (even_at EV (by decide) (off + 8) hoff))
    (by rw [r1 _ (by decide), D.hsp])
  rw [mem1] at w2 f2
  have k2' : ∀ q : Fin 32, q.val ∈ evKeep → reg n2 q = reg n q := fun q hq => by
    rw [k2 q (by revert hq; revert q; decide), r1 q (by revert hq; revert q; decide)]
  have fz : ∀ x, Sep (evG F) 0xA10 x 1 → Sep (F + BitVec.ofNat 32 d) 40 x 1 → n2.mem x = M x :=
    fun x hx ho => f2 x (C.zoneIn hz (by decide) hx) ho
  exact ⟨n2, c1.trans c2, D.ret C (d := d) (k := 40) pc2 (by rw [sp2]) (k2' 3 (by decide)) (k2' 4 (by decide)) hd fz,
    k2', feW_sq w2, fz⟩

set_option maxRecDepth 20000 in
set_option maxHeartbeats 16000000 in
/-- A call of `pow22501(F + e)` into the pair at `F + d`. -/
theorem EvSt.pow22501 (C : EvCtx M0 F pk sig msg len) (D : EvSt M0 Ms F r0 M n off) {imm o : Word} {d e : Nat}
    (h1 : fetchRel ed25519VerifyCode off = some (.auipc ra imm, 4))
    (h2 : fetchRel ed25519VerifyCode (off + 4) = some (.jalr ra ra o, 4))
    (hb : EV + BitVec.ofNat 32 off + imm + o = BitVec.ofNat 32 pow22501Address) (hoff : (off + 8) % 2 = 0)
    (ha0 : reg n a0 = F + BitVec.ofNat 32 d) (ha1 : reg n a1 = F + BitVec.ofNat 32 e) (hd : d + 0x50 ≤ 0x166C)
    (hd4 : d % 4 = 0) (he : e + 40 ≤ 0x16A0) (he4 : e % 4 = 0) (hde : e + 40 ≤ d ∨ d + 0x50 ≤ e) :
    ∃ n', Steps n n' ∧ EvSt M0 Ms F r0 n'.mem n' (off + 8) ∧ (∀ q : Fin 32, q.val ∈ evKeep → reg n' q = reg n q) ∧
      feW n'.mem (F + BitVec.ofNat 32 d) = pw19L (feW M (F + BitVec.ofNat 32 e)) ∧
      feW n'.mem (F + BitVec.ofNat 32 (d + 40)) = pw3L (feW M (F + BitVec.ofNat 32 e)) ∧
      ∀ x, Sep (evG F) 0xA10 x 1 → Sep (F + BitVec.ofNat 32 d) 0x50 x 1 → n'.mem x = M x := by
  have hc := D.code C
  obtain ⟨n1, c1, pc1, mem1, regs1⟩ := D.st.callRa (cb := BitVec.ofNat 32 pow22501Address) hc h1 h2 hb (by decide)
  have r1 := PEnv.reg1 regs1 D.st.zero
  have hz : (0xFFFFFBB0 : Word).toNat = 2 ^ 32 - 0x450 := rfl
  have zc : ∀ {b : Word} {k : Nat}, 0x40000000 ≤ b.toNat → b.toNat + k ≤ 2 ^ 32 → Sep (F + 0xFFFFFBB0) 0x450 b k :=
    fun h1 h2 => (C.zone hz (by decide) (C.hiG h1 h2).symm).symm
  have oc : ∀ {b : Word} {k : Nat}, 0x40000000 ≤ b.toNat → b.toNat + k ≤ 2 ^ 32 →
      Sep (F + BitVec.ofNat 32 d) 0x50 b k := fun h1 h2 => C.codeF (by omega) h1 h2
  have E : PWEnv n1.mem (BitVec.ofNat 32 pow22501Address) F (F + BitVec.ofNat 32 d) (F + BitVec.ofNat 32 e) := by
    rw [mem1]
    have P := D.pkEnv C
    exact { hP := by decide
            cod := P.dec.pw
            sq := by
              rw [show (BitVec.ofNat 32 pow22501Address : Word) + 0x1A8 = BitVec.ofNat 32 feSquareAddress by decide]
              exact P.dec.sq
            sqi := by
              rw [show (BitVec.ofNat 32 pow22501Address : Word) + 0x1A8 + 0x26 = BitVec.ofNat 32 feSquareInnerAddress by
                decide]
              exact P.dec.sqi
            sqR := by
              rw [show (BitVec.ofNat 32 pow22501Address : Word) + 0x1A8 + 0xFFFFFC8C = BitVec.ofNat 32 feReduceAddress by
                decide]
              exact P.dec.red
            mul := by
              rw [show (BitVec.ofNat 32 pow22501Address : Word) + 0xFFFFF344 = BitVec.ofNat 32 feMulAddress by decide]
              exact P.dec.mul
            mulR := by
              rw [show (BitVec.ofNat 32 pow22501Address : Word) + 0xFFFFF344 + 0xAF0 = BitVec.ofNat 32 feReduceAddress by
                decide]
              exact P.dec.red
            pk := by
              rw [show (BitVec.ofNat 32 pow22501Address : Word) + 0x156 = BitVec.ofNat 32 fePow2kAddress by decide]
              exact P.dec.pk
            pkS := by
              rw [show (BitVec.ofNat 32 pow22501Address : Word) + 0x156 + 0x52 = BitVec.ofNat 32 feSquareAddress by decide]
              exact P.dec.sq
            pkI := by
              rw [show (BitVec.ofNat 32 pow22501Address : Word) + 0x156 + 0x78 = BitVec.ofNat 32 feSquareInnerAddress by
                decide]
              exact P.dec.sqi
            pkR := by
              rw [show (BitVec.ofNat 32 pow22501Address : Word) + 0x156 + 0xFFFFFCDE = BitVec.ofNat 32 feReduceAddress by
                decide]
              exact P.dec.red
            pkMS := by
              rw [show (BitVec.ofNat 32 pow22501Address : Word) + 0x156 + 0x62EA = BitVec.ofNat 32 memcpyStubAddress by
                decide]
              exact P.dec.mcs
            pkMB := by
              rw [show (BitVec.ofNat 32 pow22501Address : Word) + 0x156 + 0x62F2 = BitVec.ofNat 32 memcpyStubAddress + 8 by
                decide]
              exact P.dec.mcb
            mcS := by
              rw [show (BitVec.ofNat 32 pow22501Address : Word) + 0x6440 = BitVec.ofNat 32 memcpyStubAddress by decide]
              exact P.dec.mcs
            mcB := by
              rw [show (BitVec.ofNat 32 pow22501Address : Word) + 0x6440 + 8 = BitVec.ofNat 32 memcpyStubAddress + 8 by
                decide]
              exact P.dec.mcb
            hsp := by have := C.hF; omega
            hS := by have := C.hlo; omega
            hout := C.al hd4
            hxp := C.al he4
            how := by rw [C.fN (by omega)]; have := C.hhi; omega
            sG := ⟨zc (by decide) (by decide), zc (by decide) (by decide), zc (by decide) (by decide),
              zc (by decide) (by decide), zc (by decide) (by decide), zc (by decide) (by decide),
              zc (by decide) (by decide), zc (by decide) (by decide), zc (by decide) (by decide),
              zc (by decide) (by decide), zc (by decide) (by decide), zc (by decide) (by decide),
              zc (by decide) (by decide), zc (by decide) (by decide)⟩
            sO := ⟨oc (by decide) (by decide), oc (by decide) (by decide), oc (by decide) (by decide),
              oc (by decide) (by decide), oc (by decide) (by decide), oc (by decide) (by decide),
              oc (by decide) (by decide), oc (by decide) (by decide), oc (by decide) (by decide),
              oc (by decide) (by decide), oc (by decide) (by decide), oc (by decide) (by decide),
              oc (by decide) (by decide), oc (by decide) (by decide)⟩
            sOG := C.zoneF hz (by decide) (by omega)
            sXG := C.zoneF hz (by decide) he
            sXO := C.offs hde he (by omega) }
  obtain ⟨n2, c2, pc2, sp2, k2, w2, f2⟩ := pow22501_correct n1 E pc1 (by rw [r1 _ (by decide), D.hsp])
    (by rw [r1 _ (by decide), ha0]) (by rw [r1 _ (by decide), ha1]) (by rw [regs1]; exact ev_ra)
    (even_clear _ (even_at EV (by decide) (off + 8) hoff))
  rw [mem1] at w2 f2
  have k2' : ∀ q : Fin 32, q.val ∈ evKeep → reg n2 q = reg n q := fun q hq => by
    rw [k2 q (by revert hq; revert q; decide), r1 q (by revert hq; revert q; decide)]
  have fz : ∀ x, Sep (evG F) 0xA10 x 1 → Sep (F + BitVec.ofNat 32 d) 0x50 x 1 → n2.mem x = M x :=
    fun x hx ho => f2 x (C.zoneIn hz (by decide) hx) ho
  refine ⟨n2, c1.trans c2, D.ret C (d := d) (k := 0x50) pc2 (by rw [sp2]) (k2' 3 (by decide)) (k2' 4 (by decide)) hd fz,
    k2', feW_pw19 fun i hi => (w2 i hi).1, ?_, fz⟩
  rw [show F + BitVec.ofNat 32 (d + 40) = F + BitVec.ofNat 32 d + 0x28 from (add_ofNat_assoc F d 40).symm]
  exact feW_pw3 fun i hi => (w2 i hi).2

set_option maxRecDepth 20000 in
set_option maxHeartbeats 16000000 in
/-- A call of `pow2k(F + e, k)` into `F + d`. -/
theorem EvSt.pow2k (C : EvCtx M0 F pk sig msg len) (D : EvSt M0 Ms F r0 M n off) {imm o : Word} {d e k : Nat}
    (h1 : fetchRel ed25519VerifyCode off = some (.auipc ra imm, 4))
    (h2 : fetchRel ed25519VerifyCode (off + 4) = some (.jalr ra ra o, 4))
    (hb : EV + BitVec.ofNat 32 off + imm + o = BitVec.ofNat 32 fePow2kAddress) (hoff : (off + 8) % 2 = 0)
    (hk0 : 0 < k) (hk1 : k < 2 ^ 32)
    (ha0 : reg n a0 = F + BitVec.ofNat 32 d) (ha1 : reg n a1 = F + BitVec.ofNat 32 e)
    (ha2 : reg n a2 = BitVec.ofNat 32 k) (hd : d + 40 ≤ 0x166C)
    (hd4 : d % 4 = 0) (he : e + 40 ≤ 0x16A0) (he4 : e % 4 = 0) :
    ∃ n', Steps n n' ∧ EvSt M0 Ms F r0 n'.mem n' (off + 8) ∧ (∀ q : Fin 32, q.val ∈ evKeep → reg n' q = reg n q) ∧
      feW n'.mem (F + BitVec.ofNat 32 d) = sqIter k (feW M (F + BitVec.ofNat 32 e)) ∧
      ∀ x, Sep (evG F) 0xA10 x 1 → Sep (F + BitVec.ofNat 32 d) 40 x 1 → n'.mem x = M x := by
  have hc := D.code C
  obtain ⟨n1, c1, pc1, mem1, regs1⟩ := D.st.callRa (cb := BitVec.ofNat 32 fePow2kAddress) hc h1 h2 hb (by decide)
  have r1 := PEnv.reg1 regs1 D.st.zero
  have hz : (0xFFFFFEF0 : Word).toNat = 2 ^ 32 - 0x110 := rfl
  have zc : ∀ {b : Word} {k : Nat}, 0x40000000 ≤ b.toNat → b.toNat + k ≤ 2 ^ 32 → Sep (F + 0xFFFFFEF0) 0x110 b k :=
    fun h1 h2 => (C.zone hz (by decide) (C.hiG h1 h2).symm).symm
  have E : FpkEnv n1.mem (BitVec.ofNat 32 fePow2kAddress) (F + 0xFFFFFEF0) (F + BitVec.ofNat 32 d)
      (F + BitVec.ofNat 32 e) := by
    rw [mem1]
    have P := D.pkEnv C
    exact { hP := by decide
            code := P.dec.pk
            sq := by
              rw [show (BitVec.ofNat 32 fePow2kAddress : Word) + 0x52 = BitVec.ofNat 32 feSquareAddress by decide]
              exact P.dec.sq
            sqi := by
              rw [show (BitVec.ofNat 32 fePow2kAddress : Word) + 0x78 = BitVec.ofNat 32 feSquareInnerAddress by decide]
              exact P.dec.sqi
            red := by
              rw [show (BitVec.ofNat 32 fePow2kAddress : Word) + 0xFFFFFCDE = BitVec.ofNat 32 feReduceAddress by decide]
              exact P.dec.red
            mcS := by
              rw [show (BitVec.ofNat 32 fePow2kAddress : Word) + 0x62EA = BitVec.ofNat 32 memcpyStubAddress by decide]
              exact P.dec.mcs
            mcB := by
              rw [show (BitVec.ofNat 32 fePow2kAddress : Word) + 0x62F2 = BitVec.ofNat 32 memcpyStubAddress + 8 by decide]
              exact P.dec.mcb
            hG := aligned_add (by have := C.hF; omega) (k := 0xFFFFFEF0) (by decide)
            hGt := by
              rw [BitVec.toNat_add, hz]; have := C.hlo; have := F.isLt; omega
            hout := C.al hd4
            hot := by rw [C.fN (by omega)]; have := C.hhi; omega
            hx := C.al he4
            sGC := zc (by decide) (by decide)
            sGQ := zc (by decide) (by decide)
            sGI := zc (by decide) (by decide)
            sGR := zc (by decide) (by decide)
            sGM := zc (by decide) (by decide)
            sGB := zc (by decide) (by decide)
            sOC := C.codeF (by omega) (by decide) (by decide)
            sOB := C.codeF (by omega) (by decide) (by decide)
            sOG := C.zoneF hz (by decide) (by omega)
            sXG := C.zoneF hz (by decide) he }
  obtain ⟨n2, c2, pc2, sp2, k2, w2, f2⟩ := fePow2k_correct n1 E hk0 hk1 pc1 (by rw [r1 _ (by decide), ha0])
    (by rw [r1 _ (by decide), ha1]) (by rw [r1 _ (by decide), ha2]) (by rw [regs1]; exact ev_ra)
    (even_clear _ (even_at EV (by decide) (off + 8) hoff))
    (by rw [r1 _ (by decide), D.hsp, BitVec.add_assoc]; exact (BitVec.add_zero F).symm)
  rw [mem1] at w2 f2
  have k2' : ∀ q : Fin 32, q.val ∈ evKeep → reg n2 q = reg n q := fun q hq => by
    rw [k2 q (by revert hq; revert q; decide), r1 q (by revert hq; revert q; decide)]
  have fz : ∀ x, Sep (evG F) 0xA10 x 1 → Sep (F + BitVec.ofNat 32 d) 40 x 1 → n2.mem x = M x :=
    fun x hx ho => f2 x (C.zoneIn hz (by decide) hx) ho
  exact ⟨n2, c1.trans c2, D.ret C (d := d) (k := 40) pc2
    (by rw [sp2, BitVec.add_assoc]; exact BitVec.add_zero F) (k2' 3 (by decide)) (k2' 4 (by decide)) hd fz,
    k2', w2, fz⟩

set_option maxRecDepth 20000 in
set_option maxHeartbeats 8000000 in
/-- A call of `to_bytes(F + e)` into the 32 bytes at `F + d`. -/
theorem EvSt.toBytes (C : EvCtx M0 F pk sig msg len) (D : EvSt M0 Ms F r0 M n off) {imm o : Word} {d e : Nat}
    (h1 : fetchRel ed25519VerifyCode off = some (.auipc ra imm, 4))
    (h2 : fetchRel ed25519VerifyCode (off + 4) = some (.jalr ra ra o, 4))
    (hb : EV + BitVec.ofNat 32 off + imm + o = BitVec.ofNat 32 feToBytesAddress) (hoff : (off + 8) % 2 = 0)
    (ha0 : reg n a0 = F + BitVec.ofNat 32 d) (ha1 : reg n a1 = F + BitVec.ofNat 32 e) (hd : d + 32 ≤ 0x166C)
    (he : e + 40 ≤ 0x16A0) (he4 : e % 4 = 0) :
    ∃ n', Steps n n' ∧ EvSt M0 Ms F r0 n'.mem n' (off + 8) ∧ (∀ q : Fin 32, q.val ∈ evKeep → reg n' q = reg n q) ∧
      memBytes n'.mem (F + BitVec.ofNat 32 d) 32 = bytesL (feW M (F + BitVec.ofNat 32 e)) ∧
      ∀ x, Sep (evG F) 0xA10 x 1 → Sep (F + BitVec.ofNat 32 d) 32 x 1 → n'.mem x = M x := by
  have hc := D.code C
  obtain ⟨n1, c1, pc1, mem1, regs1⟩ := D.st.callRa (cb := BitVec.ofNat 32 feToBytesAddress) hc h1 h2 hb (by decide)
  have r1 := PEnv.reg1 regs1 D.st.zero
  have hz : (0xFFFFFF50 : Word).toNat = 2 ^ 32 - 0xB0 := rfl
  have E : TBEnv n1.mem (BitVec.ofNat 32 feToBytesAddress) F (F + BitVec.ofNat 32 d) (F + BitVec.ofNat 32 e) := by
    rw [mem1]
    exact { hP := by decide
            code := (D.pkEnv C).dec.tb
            red := by rw [show (BitVec.ofNat 32 feToBytesAddress + 0x210 : Word) = BitVec.ofNat 32 feReduceAddress
                        by decide]; exact (D.pkEnv C).dec.red
            hsp := by have := C.hF; omega
            hS := by have := C.hlo; omega
            hfp := C.al he4
            sC := (C.zone hz (by decide) (C.hiG (by decide) (by decide)).symm).symm
            sR := (C.zone hz (by decide) (C.hiG (by decide) (by decide)).symm).symm
            sOC := C.codeF (by omega) (by decide) (by decide)
            sOR := C.zoneF hz (by decide) (by omega)
            sIR := C.zoneF hz (by decide) he }
  obtain ⟨n2, c2, pc2, sp2, k2, w2, f2⟩ := feToBytes_correct n1 E pc1 (by rw [r1 _ (by decide), D.hsp])
    (by rw [r1 _ (by decide), ha0]) (by rw [r1 _ (by decide), ha1]) (by rw [regs1]; exact ev_ra)
    (even_clear _ (even_at EV (by decide) (off + 8) hoff))
  rw [mem1] at w2 f2
  have k2' : ∀ q : Fin 32, q.val ∈ evKeep → reg n2 q = reg n q := fun q hq => by
    rw [k2 q (by revert hq; revert q; decide), r1 q (by revert hq; revert q; decide)]
  have fz : ∀ x, Sep (evG F) 0xA10 x 1 → Sep (F + BitVec.ofNat 32 d) 32 x 1 → n2.mem x = M x :=
    fun x hx ho => f2 x (C.zoneIn hz (by decide) hx) ho
  exact ⟨n2, c1.trans c2, D.ret C (d := d) (k := 32) pc2 (by rw [sp2]) (k2' 3 (by decide)) (k2' 4 (by decide)) hd fz,
    k2', (show _ = feBytesOf M (F + BitVec.ofNat 32 e) from w2).trans (feBytesOf_eq _ _), fz⟩

set_option maxRecDepth 20000 in
set_option maxHeartbeats 8000000 in
/-- A call of `is_negative(F + e)`. -/
theorem EvSt.isNeg (C : EvCtx M0 F pk sig msg len) (D : EvSt M0 Ms F r0 M n off) {imm o : Word} {e : Nat}
    (h1 : fetchRel ed25519VerifyCode off = some (.auipc ra imm, 4))
    (h2 : fetchRel ed25519VerifyCode (off + 4) = some (.jalr ra ra o, 4))
    (hb : EV + BitVec.ofNat 32 off + imm + o = BitVec.ofNat 32 feIsNegativeAddress) (hoff : (off + 8) % 2 = 0)
    (ha0 : reg n a0 = F + BitVec.ofNat 32 e) (he : e + 40 ≤ 0x16A0) (he4 : e % 4 = 0) :
    ∃ n', Steps n n' ∧ EvSt M0 Ms F r0 n'.mem n' (off + 8) ∧ (∀ q : Fin 32, q.val ∈ evKeep → reg n' q = reg n q) ∧
      reg n' a0 = BitVec.ofNat 32 ((bytesL (feW M (F + BitVec.ofNat 32 e))).getD 0 0 % 2) ∧
      ∀ x, Sep (evG F) 0xA10 x 1 → n'.mem x = M x := by
  have hc := D.code C
  obtain ⟨n1, c1, pc1, mem1, regs1⟩ := D.st.callRa (cb := BitVec.ofNat 32 feIsNegativeAddress) hc h1 h2 hb (by decide)
  have r1 := PEnv.reg1 regs1 D.st.zero
  have hz : (0xFFFFFF20 : Word).toNat = 2 ^ 32 - 0xE0 := rfl
  have E : FINEnv n1.mem (BitVec.ofNat 32 feIsNegativeAddress) F (F + BitVec.ofNat 32 e) := by
    rw [mem1]
    exact { hP := by decide
            cod := (D.pkEnv C).dec.isn
            tb := by rw [show (BitVec.ofNat 32 feIsNegativeAddress + 0xFFFFE2E6 : Word) = BitVec.ofNat 32 feToBytesAddress
                        by decide]; exact (D.pkEnv C).dec.tb
            red := by rw [show (BitVec.ofNat 32 feIsNegativeAddress + 0xFFFFE2E6 + 0x210 : Word) =
                          BitVec.ofNat 32 feReduceAddress by decide]; exact (D.pkEnv C).dec.red
            bb := by rw [show (BitVec.ofNat 32 feIsNegativeAddress + 0xFFFFD9F8 : Word) = BitVec.ofNat 32 blackBoxU8Address
                        by decide]; exact (D.pkEnv C).dec.bb
            hsp := by have := C.hF; omega
            hS := by have := C.hlo; omega
            hfp := C.al he4
            sGC := (C.zone hz (by decide) (C.hiG (by decide) (by decide)).symm).symm
            sGT := (C.zone hz (by decide) (C.hiG (by decide) (by decide)).symm).symm
            sGR := (C.zone hz (by decide) (C.hiG (by decide) (by decide)).symm).symm
            sGB := (C.zone hz (by decide) (C.hiG (by decide) (by decide)).symm).symm
            sFG := C.zoneF hz (by decide) he }
  obtain ⟨n2, c2, pc2, sp2, a02, k2, f2⟩ := feIsNegative_correct n1 E pc1 (by rw [r1 _ (by decide), D.hsp])
    (by rw [r1 _ (by decide), ha0]) (by rw [regs1]; exact ev_ra) (even_clear _ (even_at EV (by decide) (off + 8) hoff))
  rw [mem1, feBytesOf_eq] at a02
  rw [mem1] at f2
  have k2' : ∀ q : Fin 32, q.val ∈ evKeep → reg n2 q = reg n q := fun q hq => by
    rw [k2 q (by revert hq; revert q; decide), r1 q (by revert hq; revert q; decide)]
  have fz : ∀ x, Sep (evG F) 0xA10 x 1 → n2.mem x = M x := fun x hx => f2 x (C.zoneIn hz (by decide) hx)
  exact ⟨n2, c1.trans c2, D.ret C (d := 0) (k := 0) pc2 (by rw [sp2]) (k2' 3 (by decide)) (k2' 4 (by decide))
    (by decide) (fun x hx _ => fz x hx), k2', a02, fz⟩

end

end C3.RV32
