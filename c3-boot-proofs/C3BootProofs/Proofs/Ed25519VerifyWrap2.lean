import C3BootProofs.Proofs.Ed25519VerifyWrap

/-!
# `ed25519_verify`'s SHA-512 calls

The calls of SHA-512's `update` (on 32 bytes and on the message), of the
closure `finalize` uses to compress a block, and of `hybrid_array`'s
zeroing `from_fn`, each from `EvSt` to `EvSt`.
-/

namespace C3.RV32

open C3.Image

section
variable {M0 Ms : Word → BitVec 8} {F pk sig msg : Word} {len : Nat} {r0 : Fin 32 → Word}
  {M : Word → BitVec 8} {n : Machine} {off : Nat}

theorem keepS5 {q : Fin 32} (hq : q.val ∈ evKeep) :
    q ≠ ra ∧ q ≠ t0 ∧ q ≠ t1 ∧ q ≠ (7 : Fin 32) ∧ q ≠ a0 ∧ q ≠ a1 ∧ q ≠ a2 ∧ q ≠ a3 ∧ q ≠ a4 ∧
      q ≠ a5 ∧ q ≠ a6 ∧ q ≠ a7 ∧ q ≠ (28 : Fin 32) ∧ q ≠ (29 : Fin 32) ∧ q ≠ (30 : Fin 32) ∧ q ≠ (31 : Fin 32) ∧
      q ≠ sp := by
  revert hq; revert q; decide

set_option maxRecDepth 20000 in
/-- The environment SHA-512's `update` needs, with the hasher at `F + s`
and the input at `p`. -/
theorem EvSt.updEnv (C : EvCtx M0 F pk sig msg len) (D : EvSt M0 Ms F r0 M n off) {s : Nat} {p : Word} {k : Nat}
    (hs : s + 0xD0 ≤ 0x16A0) (hs4 : s % 4 = 0) (hpw : p.toNat + k ≤ 0x40000000)
    (sPS : Sep p k (F + BitVec.ofNat 32 s) 0xD0) (sPZ : Sep p k (evG F) 0xA10) :
    S5U.UpdEnv M (F + BitVec.ofNat 32 s) p F k := by
  have hi := D.hiM C
  have hz : (0xFFFFFC50 : Word).toNat = 2 ^ 32 - 0x3B0 := rfl
  exact { cU := C.env.s5u.hi hi (by decide) (by decide)
          cBlk := C.env.s5blk.hi hi (by decide) (by decide)
          cC := C.env.s5c.hi hi (by decide) (by decide)
          cI := by rw [show (BitVec.ofNat 32 sha512CompressAddress + 0xFFFFFFEA : Word) =
                      BitVec.ofNat 32 rangeFromIndexAddress by decide]; exact C.env.rfi.hi hi (by decide) (by decide)
          cZ := by rw [show (BitVec.ofNat 32 sha512CompressAddress + 0x544 : Word) = BitVec.ofNat 32 memsetAddress
                      by decide]; exact (D.pkEnv C).iso.mset
          cK := D.codeRo C C.env.s5k (by decide) (by decide)
          cMS := (D.pkEnv C).dec.mcs
          cMB := (D.pkEnv C).dec.mcb
          hS := C.al hs4
          hSw := by rw [C.fN (by omega)]; have := C.hhi; omega
          hsp := C.hF
          hspl := by have := C.hlo; omega
          hspw := by have := C.hhi; omega
          hDw := hpw
          sDS := sPS
          sDF := by rw [evZ_G F _ hz (by decide)]; exact sPZ.subR (by decide)
          sSF := C.zoneF hz (by decide) hs
          sKS := (C.fS (C.ro (by decide) (by decide)) hs).symm
          sKF := C.zone hz (by decide) (C.ro (by decide) (by decide)) }

set_option maxRecDepth 20000 in
set_option maxHeartbeats 8000000 in
/-- A call of SHA-512's `update` on `k` bytes at `p`, with the hasher at
`F + s` holding `h`. -/
theorem EvSt.upd (C : EvCtx M0 F pk sig msg len) (D : EvSt M0 Ms F r0 M n off) {imm o p : Word} {s k : Nat}
    {h : Bytes} (h1 : fetchRel ed25519VerifyCode off = some (.auipc ra imm, 4))
    (h2 : fetchRel ed25519VerifyCode (off + 4) = some (.jalr ra ra o, 4))
    (hb : EV + BitVec.ofNat 32 off + imm + o = BitVec.ofNat 32 sha512UpdateAddress) (hoff : (off + 8) % 2 = 0)
    (ha0 : reg n a0 = F + BitVec.ofNat 32 s) (ha1 : reg n a1 = p) (ha2 : reg n a2 = BitVec.ofNat 32 k)
    (hs : s + 0xD0 ≤ 0x166C) (hs4 : s % 4 = 0) (hpw : p.toNat + k ≤ 0x40000000)
    (sPS : Sep p k (F + BitVec.ofNat 32 s) 0xD0) (sPZ : Sep p k (evG F) 0xA10)
    (H : S5U.Hasher5At M (F + BitVec.ofNat 32 s) h) (hk : k < 2 ^ 31) (hl : h.length + k < 2 ^ 32) :
    ∃ n', Steps n n' ∧ EvSt M0 Ms F r0 n'.mem n' (off + 8) ∧
      (∀ q : Fin 32, q.val ∈ evKeep → reg n' q = reg n q) ∧
      S5U.Hasher5At n'.mem (F + BitVec.ofNat 32 s) (h ++ memBytes M p k) ∧
      ∀ x, Sep (evG F) 0xA10 x 1 → Sep (F + BitVec.ofNat 32 s) 0xD0 x 1 → n'.mem x = M x := by
  have hc := D.code C
  obtain ⟨n1, c1, pc1, mem1, regs1⟩ := D.st.callRa (cb := BitVec.ofNat 32 sha512UpdateAddress) hc h1 h2 hb (by decide)
  have r1 := PEnv.reg1 regs1 D.st.zero
  have hz : (0xFFFFFC50 : Word).toNat = 2 ^ 32 - 0x3B0 := rfl
  obtain ⟨n2, c2, pc2, sp2, k2, H2, fr2⟩ := S5U.sha512Update_correct n1 (by rw [mem1]; exact D.updEnv C (by omega) hs4 hpw sPS sPZ)
    pc1 (by rw [r1 _ (by decide), ha0]) (by rw [r1 _ (by decide), ha1]) (by rw [r1 _ (by decide), ha2])
    (by rw [regs1]; exact ev_ra) (even_clear _ (even_at EV (by decide) (off + 8) hoff)) (by rw [r1 _ (by decide), D.hsp])
    (by rw [mem1]; exact H) hk hl
  rw [mem1] at H2 fr2
  have k2' : ∀ q : Fin 32, q.val ∈ evKeep → reg n2 q = reg n q := fun q hq => by
    obtain ⟨e1, e3, e4, e5, e6, e7, e8, e9, e10, e11, e12, e13, e14, e15, e16, e17, e18⟩ := keepS5 hq
    rw [k2 q e1 e3 e4 e5 e6 e7 e8 e9 e10 e11 e12 e13 e14 e15 e16 e17 e18, r1 q e1]
  have fz : ∀ x, Sep (evG F) 0xA10 x 1 → Sep (F + BitVec.ofNat 32 s) 0xD0 x 1 → n2.mem x = M x :=
    fun x hx ho => fr2 x (C.zoneIn hz (by decide) hx) ho
  exact ⟨n2, c1.trans c2, D.ret C (d := s) (k := 0xD0) pc2 (by rw [sp2]) (k2' 3 (by decide)) (k2' 4 (by decide)) hs fz,
    k2', H2, fz⟩

set_option maxRecDepth 20000 in
set_option maxHeartbeats 8000000 in
/-- A call of SHA-512's `update` on the 32 bytes at `F + d`, with the
hasher at `F + s` holding `h`. -/
theorem EvSt.upd32 (C : EvCtx M0 F pk sig msg len) (D : EvSt M0 Ms F r0 M n off) {imm o : Word} {s d : Nat}
    {h : Bytes} (h1 : fetchRel ed25519VerifyCode off = some (.auipc ra imm, 4))
    (h2 : fetchRel ed25519VerifyCode (off + 4) = some (.jalr ra ra o, 4))
    (hb : EV + BitVec.ofNat 32 off + imm + o = BitVec.ofNat 32 sha512UpdateArr32Address) (hoff : (off + 8) % 2 = 0)
    (ha0 : reg n a0 = F + BitVec.ofNat 32 s) (ha1 : reg n a1 = F + BitVec.ofNat 32 d)
    (hs : s + 0xD0 ≤ 0x166C) (hs4 : s % 4 = 0) (hd : d + 32 ≤ 0x16A0) (hsd : s + 0xD0 ≤ d ∨ d + 32 ≤ s)
    (H : S5U.Hasher5At M (F + BitVec.ofNat 32 s) h) (hl : h.length + 32 < 2 ^ 32) :
    ∃ n', Steps n n' ∧ EvSt M0 Ms F r0 n'.mem n' (off + 8) ∧
      (∀ q : Fin 32, q.val ∈ evKeep → reg n' q = reg n q) ∧
      S5U.Hasher5At n'.mem (F + BitVec.ofNat 32 s) (h ++ memBytes M (F + BitVec.ofNat 32 d) 32) ∧
      ∀ x, Sep (evG F) 0xA10 x 1 → Sep (F + BitVec.ofNat 32 s) 0xD0 x 1 → n'.mem x = M x := by
  have hc := D.code C
  obtain ⟨n1, c1, pc1, mem1, regs1⟩ := D.st.callRa (cb := BitVec.ofNat 32 sha512UpdateArr32Address) hc h1 h2 hb
    (by decide)
  have r1 := PEnv.reg1 regs1 D.st.zero
  have hz : (0xFFFFFC50 : Word).toNat = 2 ^ 32 - 0x3B0 := rfl
  have hca : CodeIn M (BitVec.ofNat 32 sha512UpdateArr32Address) sha512UpdateArr32Code :=
    C.env.s5a.hi (D.hiM C) (by decide) (by decide)
  have hdw : (F + BitVec.ofNat 32 d).toNat + 32 ≤ 0x40000000 := by rw [C.fN (by omega)]; have := C.hhi; omega
  have E := D.updEnv C (s := s) (p := F + BitVec.ofNat 32 d) (k := 32) (by omega) hs4 hdw
    (C.offs (Or.symm hsd) hd (by omega)) (C.zF hd).symm
  obtain ⟨n2, c2, pc2, sp2, k2, H2, fr2⟩ := S5U.sha512UpdateArr32_correct n1 (by rw [mem1]; exact hca)
    (by rw [mem1]; exact E) pc1 (by rw [r1 _ (by decide), ha0]) (by rw [r1 _ (by decide), ha1])
    (by rw [regs1]; exact ev_ra) (even_clear _ (even_at EV (by decide) (off + 8) hoff)) (by rw [r1 _ (by decide), D.hsp])
    (by rw [mem1]; exact H) hl
  rw [mem1] at H2 fr2
  have k2' : ∀ q : Fin 32, q.val ∈ evKeep → reg n2 q = reg n q := fun q hq => by
    obtain ⟨e1, e3, e4, e5, e6, e7, e8, e9, e10, e11, e12, e13, e14, e15, e16, e17, e18⟩ := keepS5 hq
    rw [k2 q e1 e3 e4 e5 e6 e7 e8 e9 e10 e11 e12 e13 e14 e15 e16 e17 e18, r1 q e1]
  have fz : ∀ x, Sep (evG F) 0xA10 x 1 → Sep (F + BitVec.ofNat 32 s) 0xD0 x 1 → n2.mem x = M x :=
    fun x hx ho => fr2 x (C.zoneIn hz (by decide) hx) ho
  exact ⟨n2, c1.trans c2, D.ret C (d := s) (k := 0xD0) pc2 (by rw [sp2]) (k2' 3 (by decide)) (k2' 4 (by decide)) hs fz,
    k2', H2, fz⟩

set_option maxRecDepth 20000 in
set_option maxHeartbeats 8000000 in
/-- A call of the closure that compresses the 128 bytes at `F + b` into
the hash value at `F + a`. -/
theorem EvSt.finBlock (C : EvCtx M0 F pk sig msg len) (D : EvSt M0 Ms F r0 M n off) {imm o : Word} {a b : Nat}
    (h1 : fetchRel ed25519VerifyCode off = some (.auipc ra imm, 4))
    (h2 : fetchRel ed25519VerifyCode (off + 4) = some (.jalr ra ra o, 4))
    (hb : EV + BitVec.ofNat 32 off + imm + o = BitVec.ofNat 32 sha512FinBlockAddress) (hoff : (off + 8) % 2 = 0)
    (ha0 : reg n a0 = F + BitVec.ofNat 32 a) (ha1 : reg n a1 = F + BitVec.ofNat 32 b)
    (ha : a + 64 ≤ 0x166C) (ha4 : a % 4 = 0) (hbb : b + 128 ≤ 0x16A0) :
    ∃ n', Steps n n' ∧ EvSt M0 Ms F r0 n'.mem n' (off + 8) ∧
      (∀ q : Fin 32, q.val ∈ evKeep → reg n' q = reg n q) ∧
      (s5Hv n'.mem (F + BitVec.ofNat 32 a)).toList =
        Sha512.compress (s5Hv M (F + BitVec.ofNat 32 a)).toList (memBytes M (F + BitVec.ofNat 32 b) 128) ∧
      ∀ x, Sep (evG F) 0xA10 x 1 → Sep (F + BitVec.ofNat 32 a) 64 x 1 → n'.mem x = M x := by
  have hc := D.code C
  obtain ⟨n1, c1, pc1, mem1, regs1⟩ := D.st.callRa (cb := BitVec.ofNat 32 sha512FinBlockAddress) hc h1 h2 hb
    (by decide)
  have r1 := PEnv.reg1 regs1 D.st.zero
  have hz : (0xFFFFFBE0 : Word).toNat = 2 ^ 32 - 0x420 := rfl
  have hi := D.hiM C
  have E : FB5Env n1.mem (F + BitVec.ofNat 32 a) (F + BitVec.ofNat 32 b) F := by
    rw [mem1]
    exact { cF := C.env.s5fb.hi hi (by decide) (by decide)
            cC := C.env.s5c.hi hi (by decide) (by decide)
            cI := C.env.rfi.hi hi (by decide) (by decide)
            cMS := (D.pkEnv C).dec.mcs
            cMB := (D.pkEnv C).dec.mcb
            cZ := (D.pkEnv C).iso.mset
            cK := D.codeRo C C.env.s5k (by decide) (by decide)
            hsp := C.hF
            hspl := by have := C.hlo; omega
            hspw := by have := C.hhi; omega
            hst := C.al ha4
            hstw := by rw [C.fN (by omega)]; have := C.hhi; omega
            hblkw := by rw [C.fN (by omega)]; have := C.hhi; omega
            sStF := C.zoneF hz (by decide) (by omega)
            sBF := C.zoneF hz (by decide) hbb
            sKF := C.zone hz (by decide) (C.ro (by decide) (by decide))
            sStK := C.fS (C.ro (by decide) (by decide)) (by omega) }
  obtain ⟨n2, c2, pc2, sp2, k2, h2', fr2⟩ := sha512FinBlock_correct n1 E pc1 (by rw [r1 _ (by decide), ha0])
    (by rw [r1 _ (by decide), ha1]) (by rw [regs1]; exact ev_ra) (even_clear _ (even_at EV (by decide) (off + 8) hoff))
    (by rw [r1 _ (by decide), D.hsp])
  rw [mem1] at h2' fr2
  have k2' : ∀ q : Fin 32, q.val ∈ evKeep → reg n2 q = reg n q := fun q hq => by
    rw [k2 q (by revert hq; revert q; decide) (by revert hq; revert q; decide) (by revert hq; revert q; decide)
      (by revert hq; revert q; decide) (by revert hq; revert q; decide) (by revert hq; revert q; decide)
      (by revert hq; revert q; decide) (by revert hq; revert q; decide) (by revert hq; revert q; decide)
      (by revert hq; revert q; decide) (by revert hq; revert q; decide) (by revert hq; revert q; decide)
      (by revert hq; revert q; decide) (by revert hq; revert q; decide) (by revert hq; revert q; decide),
      r1 q (by revert hq; revert q; decide)]
  have fz : ∀ x, Sep (evG F) 0xA10 x 1 → Sep (F + BitVec.ofNat 32 a) 64 x 1 → n2.mem x = M x :=
    fun x hx ho => fr2 x (C.zoneIn hz (by decide) hx) ho
  exact ⟨n2, c1.trans c2, D.ret C (d := a) (k := 64) pc2 sp2 (k2' 3 (by decide)) (k2' 4 (by decide)) ha fz,
    k2', h2', fz⟩

set_option maxRecDepth 20000 in
set_option maxHeartbeats 8000000 in
/-- A call of `hybrid_array`'s `from_fn` that zeroes the 64 bytes at
`F + d`. -/
theorem EvSt.zero64 (C : EvCtx M0 F pk sig msg len) (D : EvSt M0 Ms F r0 M n off) {imm o : Word} {d : Nat}
    (h1 : fetchRel ed25519VerifyCode off = some (.auipc ra imm, 4))
    (h2 : fetchRel ed25519VerifyCode (off + 4) = some (.jalr ra ra o, 4))
    (hb : EV + BitVec.ofNat 32 off + imm + o = BitVec.ofNat 32 zeroArray64Address) (hoff : (off + 8) % 2 = 0)
    (ha0 : reg n a0 = F + BitVec.ofNat 32 d) (hd : d + 64 ≤ 0x166C) :
    ∃ n', Steps n n' ∧ EvSt M0 Ms F r0 n'.mem n' (off + 8) ∧
      (∀ q : Fin 32, q.val ∈ evKeep → reg n' q = reg n q) ∧
      ∀ x, Sep (evG F) 0xA10 x 1 → n'.mem x = fillBytes M (F + BitVec.ofNat 32 d) 0 64 x := by
  have hc := D.code C
  obtain ⟨n1, c1, pc1, mem1, regs1⟩ := D.st.callRa (cb := BitVec.ofNat 32 zeroArray64Address) hc h1 h2 hb (by decide)
  have r1 := PEnv.reg1 regs1 D.st.zero
  have hz : (0xFFFFFFA0 : Word).toNat = 2 ^ 32 - 0x60 := rfl
  obtain ⟨n2, c2, pc2, sp2, k2, f2⟩ := zeroArray64_correct n1
    (by rw [mem1]; exact C.env.za64.hi (D.hiM C) (by decide) (by decide)) (by rw [mem1]; exact (D.pkEnv C).dec.mcs)
    (by rw [mem1]; exact (D.pkEnv C).dec.mcb) pc1 (by rw [r1 _ (by decide), ha0]) (by rw [regs1]; exact ev_ra)
    (even_clear _ (even_at EV (by decide) (off + 8) hoff)) (by rw [r1 _ (by decide), D.hsp]) C.hF
    (by have := C.hlo; omega) (by have := C.hhi; omega) (by rw [C.fN (by omega)]; have := C.hhi; omega)
    (C.zoneF hz (by decide) (by omega))
  rw [mem1] at f2
  have k2' : ∀ q : Fin 32, q.val ∈ evKeep → reg n2 q = reg n q := fun q hq => by
    rw [k2 q (by revert hq; revert q; decide) (by revert hq; revert q; decide) (by revert hq; revert q; decide)
      (by revert hq; revert q; decide) (by revert hq; revert q; decide) (by revert hq; revert q; decide)
      (by revert hq; revert q; decide) (by revert hq; revert q; decide) (by revert hq; revert q; decide)
      (by revert hq; revert q; decide) (by revert hq; revert q; decide) (by revert hq; revert q; decide)
      (by revert hq; revert q; decide), r1 q (by revert hq; revert q; decide)]
  exact ⟨n2, c1.trans c2, D.ret C (d := d) (k := 64) (n' := n2) pc2 sp2 (k2' 3 (by decide)) (k2' 4 (by decide)) hd
    (fun x hx hs => by rw [f2 x (C.zoneIn hz (by decide) hx), fillBytes_sep hs (Nat.le_refl _)]), k2',
    fun x hx => f2 x (C.zoneIn hz (by decide) hx)⟩

end

end C3.RV32
