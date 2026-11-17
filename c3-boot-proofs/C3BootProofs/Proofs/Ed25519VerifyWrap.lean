import C3BootProofs.Proofs.Ed25519VerifyCall

/-!
# `ed25519_verify`'s calls

One lemma for each function `ed25519_verify` calls, for a call at any
offset: from `EvSt` before the call to `EvSt` after it, with the
callee-saved registers kept and the callee's result restated over the
memory `M0` on entry where the callee reads what `ed25519_verify` did not
write.
-/

namespace C3.RV32

open C3.Image

/-- `ed25519_public_key_ok` with the constants as `M` holds them. -/
def evPk (M : Word → BitVec 8) (b : Bytes) : Bool :=
  pkOkSpec (memBytes M (BitVec.ofNat 32 0x3FCC4328) 32) (memBytes M (BitVec.ofNat 32 0x3FCC42E8) 32)
    (memBytes M (BitVec.ofNat 32 0x3FCC4388) 32) (feW M (BitVec.ofNat 32 edOneAddress))
    (feW M (BitVec.ofNat 32 edDAddress)) (feW M (BitVec.ofNat 32 edSqrtM1Address)) b

section
variable {M0 Ms : Word → BitVec 8} {F pk sig msg : Word} {len : Nat} {r0 : Fin 32 → Word}
  {M : Word → BitVec 8} {n : Machine} {off : Nat}

/-- The callee-saved registers, `gp`, and `tp`. -/
abbrev evKeep : List Nat := [3, 4, 8, 9, 18, 19, 20, 21, 22, 23, 24, 25, 26, 27]

theorem EvCtx.f16 (C : EvCtx M0 F pk sig msg len) {z : Word} {S : Nat} (hz : z.toNat = 2 ^ 32 - S) (hS : S ≤ 0xA10) :
    (F + z).toNat = F.toNat - S := by
  have := C.hlo; rw [BitVec.toNat_add, hz]; omega

/-- A call's return address. -/
theorem ev_ra {off : Nat} {f : Fin 32 → Word} :
    upd f ra (EV + BitVec.ofNat 32 (off + 8)) ra = EV + BitVec.ofNat 32 (off + 8) := by simp +decide [upd]

theorem EvSt.pkSpec (C : EvCtx M0 F pk sig msg len) (D : EvSt M0 Ms F r0 M n off) (b : Bytes) :
    pkOkSpec (memBytes M (BitVec.ofNat 32 0x3FCC4328) 32) (memBytes M (BitVec.ofNat 32 0x3FCC42E8) 32)
      (memBytes M (BitVec.ofNat 32 0x3FCC4388) 32) (feW M (BitVec.ofNat 32 edOneAddress))
      (feW M (BitVec.ofNat 32 edDAddress)) (feW M (BitVec.ofNat 32 edSqrtM1Address)) b = evPk M0 b := by
  unfold evPk
  rw [D.bytesRo C (by decide) (by decide), D.bytesRo C (by decide) (by decide), D.bytesRo C (by decide) (by decide),
    D.feRo C (by decide) (by decide), D.feRo C (by decide) (by decide), D.feRo C (by decide) (by decide)]

set_option maxRecDepth 20000 in
set_option maxHeartbeats 8000000 in
/-- A call of `ed25519_public_key_ok` at `off` on the 32 bytes at `p`,
with `a0` holding `p`. -/
theorem EvSt.pkOk (C : EvCtx M0 F pk sig msg len)
    (D : EvSt M0 Ms F r0 M n off) {imm o : Word} {p : Word}
    (h1 : fetchRel ed25519VerifyCode off = some (.auipc ra imm, 4))
    (h2 : fetchRel ed25519VerifyCode (off + 4) = some (.jalr ra ra o, 4))
    (hb : EV + BitVec.ofNat 32 off + imm + o = PKO) (hoff : (off + 8) % 2 = 0)
    (ha0 : reg n a0 = p) (sP : Sep p 32 (evG F) 0x20B0) (hp : p.toNat + 32 < 2 ^ 32) :
    ∃ n', Steps n n' ∧ EvSt M0 Ms F r0 n'.mem n' (off + 8) ∧
      (∀ q : Fin 32, q.val ∈ [3, 4, 8, 9, 18, 19, 20, 21, 22, 23, 24, 25, 26, 27] → reg n' q = reg n q) ∧
      reg n' a0 = if evPk M0 (memBytes M0 p 32) then 1 else 0 := by
  have hc := D.code C
  obtain ⟨n1, c1, pc1, mem1, regs1⟩ := D.st.callRa (cb := PKO) hc h1 h2 hb (by decide)
  have r1 := PEnv.reg1 regs1 D.st.zero
  have hF4 : F.toNat % 4 = 0 := by have := C.hF; omega
  obtain ⟨n2, c2, pc2, sp2, k2, a02, fr2⟩ := pkOk_correct n1 (by rw [mem1]; exact D.pkEnv C) pc1
    (by rw [r1 _ (by decide), ha0]) (by rw [regs1]; simp +decide [upd])
    (even_clear _ (even_at EV (by decide) (off + 8) hoff)) (by rw [r1 _ (by decide), D.hsp]) hF4
    (by have := C.hlo; omega) (by have := C.hhi; omega) hp
    (C.zone (z := 0xFFFFF6C0) (by decide) (by decide) sP)
    (C.zone (z := 0xFFFFF6C0) (by decide) (by decide) (C.ro (by decide) (by decide)))
    (C.zone (z := 0xFFFFF6C0) (by decide) (by decide) (C.ro (by decide) (by decide)))
    (C.zone (z := 0xFFFFF6C0) (by decide) (by decide) (C.ro (by decide) (by decide)))
    (C.zone (z := 0xFFFFF6C0) (by decide) (by decide) (C.ro (by decide) (by decide)))
    (C.zone (z := 0xFFFFF6C0) (by decide) (by decide) (C.ro (by decide) (by decide)))
    (C.zone (z := 0xFFFFF6C0) (by decide) (by decide) (C.ro (by decide) (by decide)))
  rw [mem1] at fr2
  rw [mem1, D.pkSpec C, D.bytesOut sP] at a02
  have k2' : ∀ q : Fin 32, q.val ∈ [3, 4, 8, 9, 18, 19, 20, 21, 22, 23, 24, 25, 26, 27] → reg n2 q = reg n q :=
    fun q hq => by rw [k2 q (by revert hq; revert q; decide), r1 q (by revert hq; revert q; decide)]
  refine ⟨n2, c1.trans c2, D.ret C (d := 0) (k := 0) pc2 sp2 (k2' 3 (by decide)) (k2' 4 (by decide)) (by decide)
    (fun x hx _ => fr2 x (C.zoneIn (by decide) (by decide) hx)), k2', a02⟩


set_option maxRecDepth 20000 in
set_option maxHeartbeats 8000000 in
/-- A call of `less_than_le(p, q)`. -/
theorem EvSt.ltLe (C : EvCtx M0 F pk sig msg len) (D : EvSt M0 Ms F r0 M n off) {imm o p q : Word}
    (h1 : fetchRel ed25519VerifyCode off = some (.auipc ra imm, 4))
    (h2 : fetchRel ed25519VerifyCode (off + 4) = some (.jalr ra ra o, 4))
    (hb : EV + BitVec.ofNat 32 off + imm + o = BitVec.ofNat 32 lessThanLeAddress) (hoff : (off + 8) % 2 = 0)
    (ha0 : reg n a0 = p) (ha1 : reg n a1 = q) :
    ∃ n', Steps n n' ∧ EvSt M0 Ms F r0 M n' (off + 8) ∧
      (∀ r : Fin 32, r ≠ a0 → r ≠ a1 → r ≠ a2 → r ≠ a3 → r ≠ a4 → r ≠ ra → reg n' r = reg n r) ∧
      reg n' a0 = if ltLEb (memBytes M p 32) (memBytes M q 32) 32 then 1 else 0 := by
  obtain ⟨n1, c1, pc1, mem1, regs1⟩ := D.st.callRa (cb := BitVec.ofNat 32 lessThanLeAddress) (D.code C) h1 h2 hb
    (by decide)
  have r1 := PEnv.reg1 regs1 D.st.zero
  obtain ⟨n2, c2, pc2, a02, k2, mem2⟩ := lessThanLe_correct n1 (by rw [mem1]; exact (D.pkEnv C).ltl) pc1
    (by rw [r1 _ (by decide), ha0]) (by rw [r1 _ (by decide), ha1]) (by rw [regs1]; exact ev_ra)
    (even_clear _ (even_at EV (by decide) (off + 8) hoff))
  have k2' : ∀ r : Fin 32, r ≠ a0 → r ≠ a1 → r ≠ a2 → r ≠ a3 → r ≠ a4 → r ≠ ra → reg n2 r = reg n r :=
    fun r h0 h1 h2 h3 h4 h5 => by rw [k2 r h0 h1 h2 h3 h4, r1 r h5]
  refine ⟨n2, c1.trans c2, ?_, k2', by rw [a02, mem1, ltLE_bytes _ _ _ 32 (Nat.le_refl _)]⟩
  have D2 := D.ret C (d := 0) (k := 0) (n' := n2) pc2 (by rw [k2' sp (by decide) (by decide) (by decide) (by decide)
    (by decide) (by decide), D.hsp]) (k2' 3 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide))
    (k2' 4 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)) (by decide)
    (fun x _ _ => by rw [mem2, mem1])
  rwa [mem2, mem1] at D2

set_option maxRecDepth 20000 in
set_option maxHeartbeats 8000000 in
/-- A call of `memcpy(F + d, s, N)`. -/
theorem EvSt.memcpy (C : EvCtx M0 F pk sig msg len) (D : EvSt M0 Ms F r0 M n off) {imm o s : Word} {d N : Nat}
    (h1 : fetchRel ed25519VerifyCode off = some (.auipc ra imm, 4))
    (h2 : fetchRel ed25519VerifyCode (off + 4) = some (.jalr ra ra o, 4))
    (hb : EV + BitVec.ofNat 32 off + imm + o = BitVec.ofNat 32 memcpyStubAddress) (hoff : (off + 8) % 2 = 0)
    (ha0 : reg n a0 = F + BitVec.ofNat 32 d) (ha1 : reg n a1 = s) (ha2 : reg n a2 = BitVec.ofNat 32 N)
    (hd : d + N ≤ 0x166C) (sS : Sep s N (evG F) 0xA10) (hsep : Sep (F + BitVec.ofNat 32 d) N s N)
    (hsw : s.toNat + N < 2 ^ 32) :
    ∃ n', Steps n n' ∧ EvSt M0 Ms F r0 n'.mem n' (off + 8) ∧
      (∀ q : Fin 32, q.val ∈ evKeep → reg n' q = reg n q) ∧
      ∀ x, Sep (evG F) 0xA10 x 1 → n'.mem x = copyBytes M (F + BitVec.ofNat 32 d) s N x := by
  have hc := D.code C
  obtain ⟨n1, c1, pc1, mem1, regs1⟩ := D.st.callRa (cb := BitVec.ofNat 32 memcpyStubAddress) hc h1 h2 hb (by decide)
  have r1 := PEnv.reg1 regs1 D.st.zero
  have sp1 : reg n1 sp = F := by rw [r1 _ (by decide), D.hsp]
  have hz : (0xFFFFFFF0 : Word).toNat = 2 ^ 32 - 16 := rfl
  have E : McEnv n1.mem (BitVec.ofNat 32 memcpyStubAddress + 8) (F + BitVec.ofNat 32 d) s (reg n1 sp + 0xFFFFFFF0) N := by
    rw [mem1, sp1]
    exact { code := (D.pkEnv C).dec.mcb
            hDC := C.codeF (by omega) (by decide) (by decide)
            hFC := (C.zone hz (by decide) (C.hiG (by decide) (by decide)).symm).symm
            hdF := C.zoneF hz (by decide) (by omega)
            hsF := by rw [evZ_G F _ hz (by decide)]; exact sS.subR (by decide)
            hsep := hsep
            hF := by rw [C.f16 hz (by decide)]; have := C.hF; have := C.hlo; omega
            hFw := by rw [C.f16 hz (by decide)]; have := C.hhi; omega
            hdw := by rw [C.fN (by omega)]; have := C.hhi; omega
            hsw := hsw }
  obtain ⟨n2, c2, pc2, sp2, _, f2, k2⟩ := memcpy_correct n1 (BitVec.ofNat 32 memcpyStubAddress)
    (EV + BitVec.ofNat 32 (off + 8)) (F + BitVec.ofNat 32 d) s N (fun i hi => by rw [mem1]; exact (D.pkEnv C).dec.mcs i hi) (by decide)
    pc1 (by rw [r1 _ (by decide), ha0]) (by rw [r1 _ (by decide), ha1]) (by rw [r1 _ (by decide), ha2])
    (by rw [regs1]; exact ev_ra) (even_clear _ (even_at EV (by decide) (off + 8) hoff)) E
  rw [mem1, sp1] at f2
  have k2' : ∀ q : Fin 32, q.val ∈ evKeep → reg n2 q = reg n q := fun q hq => by
    rw [k2 q (by revert hq; revert q; decide) (by revert hq; revert q; decide) (by revert hq; revert q; decide)
      (by revert hq; revert q; decide) (by revert hq; revert q; decide) (by revert hq; revert q; decide)
      (by revert hq; revert q; decide) (by revert hq; revert q; decide) (by revert hq; revert q; decide)
      (by revert hq; revert q; decide) (by revert hq; revert q; decide) (by revert hq; revert q; decide)
      (by revert hq; revert q; decide) (by revert hq; revert q; decide), r1 q (by revert hq; revert q; decide)]
  have fz : ∀ x, Sep (evG F) 0xA10 x 1 → n2.mem x = copyBytes M (F + BitVec.ofNat 32 d) s N x :=
    fun x hx => f2 x (C.zoneIn hz (by decide) hx)
  exact ⟨n2, c1.trans c2, D.ret C (d := d) (k := N) pc2 (by rw [sp2, sp1]) (k2' 3 (by decide)) (k2' 4 (by decide)) hd
    (fun x hx hs => by rw [fz x hx, copyBytes_sep hs (Nat.le_refl _)]), k2', fz⟩

set_option maxRecDepth 20000 in
set_option maxHeartbeats 8000000 in
/-- A call of `memset(F + d, b, N)`. -/
theorem EvSt.memset (C : EvCtx M0 F pk sig msg len) (D : EvSt M0 Ms F r0 M n off) {imm o b : Word} {d N : Nat}
    (h1 : fetchRel ed25519VerifyCode off = some (.auipc ra imm, 4))
    (h2 : fetchRel ed25519VerifyCode (off + 4) = some (.jalr ra ra o, 4))
    (hb : EV + BitVec.ofNat 32 off + imm + o = BitVec.ofNat 32 memsetAddress) (hoff : (off + 8) % 2 = 0)
    (ha0 : reg n a0 = F + BitVec.ofNat 32 d) (ha1 : reg n a1 = b) (ha2 : reg n a2 = BitVec.ofNat 32 N)
    (hd : d + N ≤ 0x166C) :
    ∃ n', Steps n n' ∧ EvSt M0 Ms F r0 (fillBytes M (F + BitVec.ofNat 32 d) (b.extractLsb' 0 8) N) n' (off + 8) ∧
      ∀ q : Fin 32, q.val ∈ evKeep → reg n' q = reg n q := by
  have hc := D.code C
  obtain ⟨n1, c1, pc1, mem1, regs1⟩ := D.st.callRa (cb := BitVec.ofNat 32 memsetAddress) hc h1 h2 hb (by decide)
  have r1 := PEnv.reg1 regs1 D.st.zero
  obtain ⟨n2, c2, pc2, mem2, _, k2⟩ := memset_correct n1 (BitVec.ofNat 32 memsetAddress)
    (EV + BitVec.ofNat 32 (off + 8)) (F + BitVec.ofNat 32 d) b N (fun i hi => by rw [mem1]; exact (D.pkEnv C).iso.mset i hi) (by decide)
    pc1 (by rw [r1 _ (by decide), ha0]) (by rw [r1 _ (by decide), ha1]) (by rw [r1 _ (by decide), ha2])
    (by rw [regs1]; exact ev_ra) (even_clear _ (even_at EV (by decide) (off + 8) hoff))
    (by rw [C.fN (by omega)]; have := C.hhi; omega) (C.codeF (by omega) (by decide) (by decide))
  rw [mem1] at mem2
  have k2' : ∀ q : Fin 32, q.val ∈ evKeep → reg n2 q = reg n q := fun q hq => by
    rw [k2 q (by revert hq; revert q; decide) (by revert hq; revert q; decide) (by revert hq; revert q; decide)
      (by revert hq; revert q; decide) (by revert hq; revert q; decide), r1 q (by revert hq; revert q; decide)]
  have D2 := D.ret C (d := d) (k := N) (n' := n2) pc2
    (by rw [k2 sp (by decide) (by decide) (by decide) (by decide) (by decide), r1 _ (by decide), D.hsp])
    (k2' 3 (by decide)) (k2' 4 (by decide)) hd (fun x _ hs => by rw [mem2, fillBytes_sep hs (Nat.le_refl _)])
  rw [mem2] at D2
  exact ⟨n2, c1.trans c2, D2, k2'⟩

set_option maxRecDepth 20000 in
set_option maxHeartbeats 8000000 in
/-- A call of `<u8 as ConstantTimeEq>::ct_eq(x, y)`. -/
theorem EvSt.ctEqU8 (C : EvCtx M0 F pk sig msg len) (D : EvSt M0 Ms F r0 M n off) {imm o x y : Word}
    (h1 : fetchRel ed25519VerifyCode off = some (.auipc ra imm, 4))
    (h2 : fetchRel ed25519VerifyCode (off + 4) = some (.jalr ra ra o, 4))
    (hb : EV + BitVec.ofNat 32 off + imm + o = BitVec.ofNat 32 ctEqU8Address) (hoff : (off + 8) % 2 = 0)
    (ha0 : reg n a0 = x) (ha1 : reg n a1 = y) (hx : x.toNat < 256) (hy : y.toNat < 256) :
    ∃ n', Steps n n' ∧ EvSt M0 Ms F r0 n'.mem n' (off + 8) ∧
      (∀ r : Fin 32, r ≠ a0 → r ≠ a1 → r ≠ t1 → r ≠ ra → reg n' r = reg n r) ∧
      reg n' a0 = (if x = y then 1 else 0) ∧ ∀ z, Sep (evG F) 0xA10 z 1 → n'.mem z = M z := by
  have hc := D.code C
  obtain ⟨n1, c1, pc1, mem1, regs1⟩ := D.st.callRa (cb := BitVec.ofNat 32 ctEqU8Address) hc h1 h2 hb (by decide)
  have r1 := PEnv.reg1 regs1 D.st.zero
  have sp1 : reg n1 sp = F := by rw [r1 _ (by decide), D.hsp]
  have hz : (0xFFFFFFFF : Word).toNat = 2 ^ 32 - 1 := rfl
  have ebb : BitVec.ofNat 32 ctEqU8Address + 0xFFFFE84E = (BitVec.ofNat 32 blackBoxU8Address : Word) := by decide
  obtain ⟨n2, c2, pc2, a02, k2, f2⟩ := ctEqU8_correct n1 (by decide) (by rw [mem1]; exact (D.pkEnv C).dec.cu)
    (by rw [mem1, ebb]; exact (D.pkEnv C).dec.bb) pc1 (by rw [r1 _ (by decide), ha0]) (by rw [r1 _ (by decide), ha1])
    hx hy (by rw [regs1]; exact ev_ra) (even_clear _ (even_at EV (by decide) (off + 8) hoff))
    (by rw [sp1, ebb]; exact (C.zone hz (by decide) (C.hiG (by decide) (by decide)).symm).symm)
  rw [mem1, sp1] at f2
  have k2' : ∀ r : Fin 32, r ≠ a0 → r ≠ a1 → r ≠ t1 → r ≠ ra → reg n2 r = reg n r :=
    fun r h0 h1 h2 h3 => by rw [k2 r h0 h1 h2, r1 r h3]
  refine ⟨n2, c1.trans c2, D.ret C (d := 0) (k := 0) pc2 (by rw [k2' sp (by decide) (by decide) (by decide)
    (by decide), D.hsp]) (k2' 3 (by decide) (by decide) (by decide) (by decide))
    (k2' 4 (by decide) (by decide) (by decide) (by decide)) (by decide)
    (fun z hz' _ => f2 z (C.zoneIn hz (by decide) hz')), k2', a02, fun z hz' => f2 z (C.zoneIn hz (by decide) hz')⟩

set_option maxRecDepth 20000 in
set_option maxHeartbeats 8000000 in
/-- A call of `VerifyingKey::from_bytes(F + d, p)`. -/
theorem EvSt.vkFromBytes (C : EvCtx M0 F pk sig msg len) (D : EvSt M0 Ms F r0 M n off) {imm o p : Word} {d : Nat}
    (h1 : fetchRel ed25519VerifyCode off = some (.auipc ra imm, 4))
    (h2 : fetchRel ed25519VerifyCode (off + 4) = some (.jalr ra ra o, 4))
    (hb : EV + BitVec.ofNat 32 off + imm + o = VKB) (hoff : (off + 8) % 2 = 0)
    (ha0 : reg n a0 = F + BitVec.ofNat 32 d) (ha1 : reg n a1 = p) (hd : d + 0xC4 ≤ 0x166C) (hd4 : d % 4 = 0)
    (sP : Sep p 32 (evG F) 0x20B0) (hp : p.toNat + 32 < 2 ^ 32) :
    ∃ n', Steps n n' ∧ EvSt M0 Ms F r0 n'.mem n' (off + 8) ∧ (∀ q : Fin 32, q.val ∈ evKeep → reg n' q = reg n q) ∧
      VkOut n'.mem (F + BitVec.ofNat 32 d) (memBytes M0 p 32) (decSpec (feW M0 (BitVec.ofNat 32 edOneAddress))
        (feW M0 (BitVec.ofNat 32 edDAddress)) (feW M0 (BitVec.ofNat 32 edSqrtM1Address)) (memBytes M0 p 32)) ∧
      ∀ x, Sep (evG F) 0xA10 x 1 → Sep (F + BitVec.ofNat 32 d) 0xC4 x 1 → n'.mem x = M x := by
  have hc := D.code C
  obtain ⟨n1, c1, pc1, mem1, regs1⟩ := D.st.callRa (cb := VKB) hc h1 h2 hb (by decide)
  have r1 := PEnv.reg1 regs1 D.st.zero
  have hz : (0xFFFFF850 : Word).toNat = 2 ^ 32 - 0x7B0 := rfl
  obtain ⟨n2, c2, pc2, sp2, k2, vk2, fr2⟩ := edVkFromBytes_correct n1 (by rw [mem1]; exact (D.pkEnv C).dec)
    (by rw [mem1]; exact (D.pkEnv C).vkb) pc1 (by rw [r1 _ (by decide), ha0]) (by rw [r1 _ (by decide), ha1])
    (by rw [regs1]; exact ev_ra) (even_clear _ (even_at EV (by decide) (off + 8) hoff))
    (by rw [r1 _ (by decide), D.hsp]) (by have := C.hF; omega) (by have := C.hlo; omega) (by have := C.hhi; omega)
    (C.al hd4) (by rw [C.fN (by omega)]; have := C.hhi; omega) hp (C.zoneF hz (by decide) (by omega))
    (C.zone hz (by decide) sP) (by rw [evF_G]; exact sP.subR (by omega))
    (C.zone hz (by decide) (C.ro (by decide) (by decide))) (C.zone hz (by decide) (C.ro (by decide) (by decide)))
    (C.zone hz (by decide) (C.ro (by decide) (by decide)))
  rw [mem1] at fr2
  rw [mem1, D.bytesOut sP, D.feRo C (by decide) (by decide), D.feRo C (by decide) (by decide),
    D.feRo C (by decide) (by decide)] at vk2
  have k2' : ∀ q : Fin 32, q.val ∈ evKeep → reg n2 q = reg n q := fun q hq => by
    rw [k2 q (by revert hq; revert q; decide), r1 q (by revert hq; revert q; decide)]
  have fz : ∀ x, Sep (evG F) 0xA10 x 1 → Sep (F + BitVec.ofNat 32 d) 0xC4 x 1 → n2.mem x = M x :=
    fun x hx ho => fr2 x (C.zoneIn hz (by decide) hx) ho
  exact ⟨n2, c1.trans c2, D.ret C (d := d) (k := 0xC4) pc2 sp2 (k2' 3 (by decide))
    (k2' 4 (by decide)) hd fz, k2', vk2, fz⟩

end

end C3.RV32
