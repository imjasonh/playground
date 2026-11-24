import C3BootProofs.Proofs.Ed25519VerifyP5
import C3BootProofs.Proofs.ScalarMont

/-!
# `ed25519_verify`'s calls of `Scalar29::montgomery_mul`
-/

namespace C3.RV32

open C3.Image

section
variable {M0 Ms : Word → BitVec 8} {F pk sig msg : Word} {len : Nat} {r0 : Fin 32 → Word}
  {M : Word → BitVec 8} {n : Machine} {off : Nat}

set_option maxRecDepth 20000 in
set_option maxHeartbeats 8000000 in
/-- A call of `Scalar29::montgomery_mul(F + d, F + e, c)`, with the second
operand at `c` in the read-only data. -/
theorem EvSt.montMul (C : EvCtx M0 F pk sig msg len) (D : EvSt M0 Ms F r0 M n off) {imm o : Word} {d e c : Nat}
    (h1 : fetchRel ed25519VerifyCode off = some (.auipc ra imm, 4))
    (h2 : fetchRel ed25519VerifyCode (off + 4) = some (.jalr ra ra o, 4))
    (hb : EV + BitVec.ofNat 32 off + imm + o = BitVec.ofNat 32 scalar29MontMulAddress) (hoff : (off + 8) % 2 = 0)
    (ha0 : reg n a0 = F + BitVec.ofNat 32 d) (ha1 : reg n a1 = F + BitVec.ofNat 32 e) (ha2 : reg n a2 = BitVec.ofNat 32 c)
    (hd : d + 36 ≤ 0x166C) (hd4 : d % 4 = 0) (he : e + 36 ≤ 0x16A0) (he4 : e % 4 = 0)
    (hc1 : (img% roWindowAddress) ≤ c) (hc2 : c + 36 ≤ 0x3FCC5400) (hc4 : c % 4 = 0) :
    ∃ n', Steps n n' ∧ EvSt M0 Ms F r0 n'.mem n' (off + 8) ∧ (∀ q : Fin 32, q.val ∈ evKeep → reg n' q = reg n q) ∧
      (∀ j, j < 9 → memLoad32 n'.mem (F + BitVec.ofNat 32 d + BitVec.ofNat 32 (4 * j)) =
        BitVec.ofNat 32 (s29Out (smmRed (smmIn M (F + BitVec.ofNat 32 e)) (smmIn M (BitVec.ofNat 32 c))) j)) ∧
      ∀ x, Sep (evG F) 0xA10 x 1 → Sep (F + BitVec.ofNat 32 d) 36 x 1 → n'.mem x = M x := by
  have hc := D.code C
  obtain ⟨n1, c1, pc1, mem1, regs1⟩ := D.st.callRa (cb := BitVec.ofNat 32 scalar29MontMulAddress) hc h1 h2 hb
    (by decide)
  have r1 := PEnv.reg1 regs1 D.st.zero
  have hz : (0xFFFFFE10 : Word).toNat = 2 ^ 32 - 0x1F0 := rfl
  have eG : F + 0xFFFFFE10 + 0x1F0 = F := by rw [BitVec.add_assoc]; exact BitVec.add_zero F
  have hi := D.hiM C
  have E : SMEnv n1.mem (BitVec.ofNat 32 scalar29MontMulAddress) (F + 0xFFFFFE10) (F + BitVec.ofNat 32 d)
      (F + BitVec.ofNat 32 e) (BitVec.ofNat 32 c) := by
    rw [mem1]
    exact { hP := by decide
            code := C.env.smm.hi hi (by decide) (by decide)
            scode := by rw [show (BitVec.ofNat 32 scalar29MontMulAddress + 0xFFFFFCF0 : Word) =
                          BitVec.ofNat 32 scalar29SubAddress by decide]; exact C.env.s29s.hi hi (by decide) (by decide)
            idx := by rw [show (BitVec.ofNat 32 scalar29MontMulAddress + 0xFFFFFCF0 + 0x278 : Word) =
                        BitVec.ofNat 32 scalar29IndexAddress by decide]; exact C.env.s29i.hi hi (by decide) (by decide)
            idxm := by rw [show (BitVec.ofNat 32 scalar29MontMulAddress + 0xFFFFFCF0 + 0x292 : Word) =
                          BitVec.ofNat 32 scalar29IndexMutAddress by decide]; exact C.env.s29im.hi hi (by decide) (by decide)
            mset := by rw [show (BitVec.ofNat 32 scalar29MontMulAddress + 0xFFFFFCF0 + 0x5B9C : Word) =
                          BitVec.ofNat 32 memsetAddress by decide]; exact (D.pkEnv C).iso.mset
            stub := by rw [show (BitVec.ofNat 32 scalar29MontMulAddress + 0xFFFFFCF0 + 0x5C04 : Word) =
                          BitVec.ofNat 32 memcpyStubAddress by decide]; exact (D.pkEnv C).dec.mcs
            body := by rw [show (BitVec.ofNat 32 scalar29MontMulAddress + 0xFFFFFCF0 + 0x5C0C : Word) =
                          BitVec.ofNat 32 memcpyStubAddress + 8 by decide]; exact (D.pkEnv C).dec.mcb
            bb := by rw [show (BitVec.ofNat 32 scalar29MontMulAddress + 0xFFFFFCF0 + 0xFFFFEAFA : Word) =
                        BitVec.ofNat 32 blackBoxU8Address by decide]; exact (D.pkEnv C).dec.bb
            ldata := D.codeRo C C.env.sL (by decide) (by decide)
            hG := by rw [C.f16 hz (by decide)]; have := C.hF; have := C.hlo; omega
            hGt := by rw [C.f16 hz (by decide)]; have := C.hhi; omega
            hout := C.al hd4
            hot := by rw [C.fN (by omega)]; have := C.hhi; omega
            hap := C.al he4
            hbp := by rw [BitVec.toNat_ofNat]; omega
            sGC := (C.zone hz (by decide) (C.hiG (by decide) (by decide)).symm).symm
            sGS := (C.zone hz (by decide) (C.hiG (by decide) (by decide)).symm).symm
            sGI := (C.zone hz (by decide) (C.hiG (by decide) (by decide)).symm).symm
            sGIM := (C.zone hz (by decide) (C.hiG (by decide) (by decide)).symm).symm
            sGM := (C.zone hz (by decide) (C.hiG (by decide) (by decide)).symm).symm
            sGSt := (C.zone hz (by decide) (C.hiG (by decide) (by decide)).symm).symm
            sGB := (C.zone hz (by decide) (C.hiG (by decide) (by decide)).symm).symm
            sGBB := (C.zone hz (by decide) (C.hiG (by decide) (by decide)).symm).symm
            sGL := (C.zone hz (by decide) (C.ro (by decide) (by decide))).symm
            sAG := C.zoneF hz (by decide) he
            sBG := C.zone hz (by decide) (C.ro hc1 hc2)
            sOG := C.zoneF hz (by decide) (by omega)
            sOS := C.codeF (by omega) (by decide) (by decide)
            sOB := C.codeF (by omega) (by decide) (by decide)
            sOC := C.codeF (by omega) (by decide) (by decide) }
  obtain ⟨n2, c2, pc2, sp2, k2, o2, fr2⟩ := scalar29MontMul_correct n1 E pc1 (by rw [r1 _ (by decide), ha0])
    (by rw [r1 _ (by decide), ha1]) (by rw [r1 _ (by decide), ha2]) (by rw [regs1]; exact ev_ra)
    (even_clear _ (even_at EV (by decide) (off + 8) hoff)) (by rw [r1 _ (by decide), D.hsp, eG])
  rw [mem1] at o2 fr2
  have k2' : ∀ q : Fin 32, q.val ∈ evKeep → reg n2 q = reg n q := fun q hq => by
    rw [k2 q (by revert hq; revert q; decide), r1 q (by revert hq; revert q; decide)]
  have fz : ∀ x, Sep (evG F) 0xA10 x 1 → Sep (F + BitVec.ofNat 32 d) 36 x 1 → n2.mem x = M x :=
    fun x hx ho => fr2 x (C.zoneIn hz (by decide) hx) ho
  exact ⟨n2, c1.trans c2, D.ret C (d := d) (k := 36) pc2 (by rw [sp2, eG]) (k2' 3 (by decide)) (k2' 4 (by decide)) hd fz,
    k2', o2, fz⟩

set_option maxRecDepth 20000 in
set_option maxHeartbeats 8000000 in
/-- A call of `Scalar29::index(p, i)`: `a0` becomes `p + 4i`. -/
theorem EvSt.idx (C : EvCtx M0 F pk sig msg len) (D : EvSt M0 Ms F r0 M n off) {imm o p : Word} {i : Nat}
    (h1 : fetchRel ed25519VerifyCode off = some (.auipc ra imm, 4))
    (h2 : fetchRel ed25519VerifyCode (off + 4) = some (.jalr ra ra o, 4))
    (hb : EV + BitVec.ofNat 32 off + imm + o = BitVec.ofNat 32 scalar29IndexAddress) (hoff : (off + 8) % 2 = 0)
    (ha0 : reg n a0 = p) (ha1 : reg n a1 = BitVec.ofNat 32 i) (hi : i < 9) :
    ∃ n', Steps n n' ∧ EvSt M0 Ms F r0 M n' (off + 8) ∧ reg n' a0 = p + BitVec.ofNat 32 (4 * i) ∧
      ∀ r : Fin 32, r ≠ a0 → r ≠ a1 → r ≠ a2 → r ≠ ra → reg n' r = reg n r := by
  have hc := D.code C
  obtain ⟨n1, c1, pc1, mem1, regs1⟩ := D.st.callRa (cb := BitVec.ofNat 32 scalar29IndexAddress) hc h1 h2 hb (by decide)
  have r1 := PEnv.reg1 regs1 D.st.zero
  obtain ⟨n2, c2, pc2, va, k2, m2⟩ := scalar29Index_correct n1 (by rw [mem1]; exact C.env.s29i.hi (D.hiM C) (by decide) (by decide))
    pc1 (by rw [r1 _ (by decide), ha0]) (by rw [r1 _ (by decide), ha1]) hi (by rw [regs1]; exact ev_ra)
    (even_clear _ (even_at EV (by decide) (off + 8) hoff))
  have k2' : ∀ r : Fin 32, r ≠ a0 → r ≠ a1 → r ≠ a2 → r ≠ ra → reg n2 r = reg n r := fun r h0 h1 h2 hr => by
    rw [k2 r h0 h1 h2, r1 r hr]
  have D2 := D.ret C (n' := n2) (d := 0) (k := 0) pc2 (by rw [k2' sp (by decide) (by decide) (by decide) (by decide), D.hsp])
    (k2' 3 (by decide) (by decide) (by decide) (by decide)) (k2' 4 (by decide) (by decide) (by decide) (by decide))
    (by decide) (fun x _ _ => by rw [m2, mem1])
  rw [m2, mem1] at D2
  exact ⟨n2, c1.trans c2, D2, va, k2'⟩

set_option maxRecDepth 20000 in
set_option maxHeartbeats 8000000 in
/-- A call of `Scalar29::index_mut(p, i)`: `a0` becomes `p + 4i`. -/
theorem EvSt.idxm (C : EvCtx M0 F pk sig msg len) (D : EvSt M0 Ms F r0 M n off) {imm o p : Word} {i : Nat}
    (h1 : fetchRel ed25519VerifyCode off = some (.auipc ra imm, 4))
    (h2 : fetchRel ed25519VerifyCode (off + 4) = some (.jalr ra ra o, 4))
    (hb : EV + BitVec.ofNat 32 off + imm + o = BitVec.ofNat 32 scalar29IndexMutAddress) (hoff : (off + 8) % 2 = 0)
    (ha0 : reg n a0 = p) (ha1 : reg n a1 = BitVec.ofNat 32 i) (hi : i < 9) :
    ∃ n', Steps n n' ∧ EvSt M0 Ms F r0 M n' (off + 8) ∧ reg n' a0 = p + BitVec.ofNat 32 (4 * i) ∧
      ∀ r : Fin 32, r ≠ a0 → r ≠ a1 → r ≠ a2 → r ≠ ra → reg n' r = reg n r := by
  have hc := D.code C
  obtain ⟨n1, c1, pc1, mem1, regs1⟩ := D.st.callRa (cb := BitVec.ofNat 32 scalar29IndexMutAddress) hc h1 h2 hb (by decide)
  have r1 := PEnv.reg1 regs1 D.st.zero
  obtain ⟨n2, c2, pc2, va, k2, m2⟩ := scalar29IndexMut_correct n1 (by rw [mem1]; exact C.env.s29im.hi (D.hiM C) (by decide) (by decide))
    pc1 (by rw [r1 _ (by decide), ha0]) (by rw [r1 _ (by decide), ha1]) hi (by rw [regs1]; exact ev_ra)
    (even_clear _ (even_at EV (by decide) (off + 8) hoff))
  have k2' : ∀ r : Fin 32, r ≠ a0 → r ≠ a1 → r ≠ a2 → r ≠ ra → reg n2 r = reg n r := fun r h0 h1 h2 hr => by
    rw [k2 r h0 h1 h2, r1 r hr]
  have D2 := D.ret C (n' := n2) (d := 0) (k := 0) pc2 (by rw [k2' sp (by decide) (by decide) (by decide) (by decide), D.hsp])
    (k2' 3 (by decide) (by decide) (by decide) (by decide)) (k2' 4 (by decide) (by decide) (by decide) (by decide))
    (by decide) (fun x _ _ => by rw [m2, mem1])
  rw [m2, mem1] at D2
  exact ⟨n2, c1.trans c2, D2, va, k2'⟩

end

end C3.RV32

