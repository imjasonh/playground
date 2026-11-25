import C3BootProofs.Proofs.SvDer3
import C3BootProofs.Proofs.Arr32Eq
import C3BootProofs.Proofs.X509ReadTime

/-!
# `sigstore::verify`: byte comparisons

`<[u8] as PartialEq>::ne` from the frame of `sigstore::verify`: 0 in `a0`
when the two slices are equal, 1 when not.
-/

namespace C3.RV32.Sv

open C3.Image C3.RV32.P3 C3.RV32.Dq C3.RV32.Pv

set_option maxRecDepth 20000

theorem sv_sp14 (B : Word) : B + 0x21A0 + 0xFFFFFFEC = B + BitVec.ofNat 32 0x218C := by
  rw [BitVec.add_assoc]; rfl

/-- Bytes a step of `sigstore::verify` doesn't write: outside the stack, or
the constants between `dataWindowAddress` and 0x3FCC4E60. -/
def SvRo (B q : Word) (ql : Nat) : Prop :=
  SvIn B q ql ∨ ((img% dataWindowAddress) ≤ q.toNat ∧ q.toNat + ql ≤ (img% dataWindowAddress + dataWindowSize))

theorem SvRo.sep {B q : Word} {ql : Nat} (F : Fr B 0x2660) (h : SvRo B q ql) {c n : Nat} (hc : c + n ≤ 0x2660) :
    Sep (B + BitVec.ofNat 32 c) n q ql := by
  rcases h with h | ⟨h1, h2⟩
  · exact (h.sepLo hc).symm
  · exact F.bufData hc h1 h2

theorem SvRo.fit {B q : Word} {ql : Nat} (h : SvRo B q ql) : q.toNat + ql < 2 ^ 32 := by
  rcases h with h | ⟨h1, h2⟩
  · exact h.fit
  · omega

set_option maxHeartbeats 8000000 in
/-- **A call to `<[u8]>::ne`** of `pl` bytes at `p` and `ql` bytes at `q`. -/
theorem sv_sneF {M : Word → BitVec 8} {n : Machine} {B : Word} {off : Nat} {imm o p q : Word} {pl ql : Nat}
    (F : Fr B 0x2660) (C : SvCode M) (s : St M SV n off (reg n))
    (h1 : fetchRel sigstoreVerifyCode off = some (.auipc ra imm, 4))
    (h2 : fetchRel sigstoreVerifyCode (off + 4) = some (.jalr ra ra o, 4))
    (hb : SV + BitVec.ofNat 32 off + imm + o = BitVec.ofNat 32 sliceNeAddress)
    (hev : (SV + BitVec.ofNat 32 (off + 8)).toNat % 2 = 0)
    (rsp : reg n sp = B + 0x21A0) (ha0 : reg n a0 = p) (ha1 : reg n a1 = BitVec.ofNat 32 pl)
    (ha2 : reg n a2 = q) (ha3 : reg n a3 = BitVec.ofNat 32 ql) (hp : SvRo B p pl) (hq : SvRo B q ql) :
    ∃ n', Steps n n' ∧ St n'.mem SV n' (off + 8) (reg n') ∧
      (∀ r, r ≠ a0 → r ≠ a1 → r ≠ a2 → r ≠ a3 → r ≠ a4 → r ≠ t1 → r ≠ ra → reg n' r = reg n r) ∧
      reg n' a0 = (if memBytes M p pl = memBytes M q ql then 0 else 1) ∧
      SvKeepL B M n'.mem [] ∧ (∀ x, SvR B x → n'.mem x = M x) := by
  have hFl := F.lo; have hFh := F.hi; have hFa := F.al
  obtain ⟨n1, c1, pc1, mem1, regs1⟩ := s.callRa C.self h1 h2 hb (by decide)
  have r1 := PEnv.reg1 regs1 s.zero
  have hS : (B + (0x21A0 : Word)).toNat = B.toNat + 0x21A0 := F.at 0x21A0 (by decide)
  obtain ⟨n2, c2, pc2, a02, k2, f2⟩ := sliceNe_correct n1 (p := p) (q := q) (pl := pl) (ql := ql) (by decide)
    (by rw [mem1]; exact C.sliceNe) (by rw [mem1]; exact C.sliceEq) (by rw [mem1]; exact C.equalSameLength)
    (by rw [mem1]; exact C.memcmp) pc1 (by rw [r1 a0 (by decide), ha0]) (by rw [r1 a1 (by decide), ha1])
    (by rw [r1 a2 (by decide), ha2]) (by rw [r1 a3 (by decide), ha3]) (by have := hp.fit; omega)
    (by have := hq.fit; omega) (by rw [regs1]; simp +decide [upd]) (even_clear _ hev)
    (by rw [r1 sp (by decide), rsp, hS]; omega)
    (by rw [r1 sp (by decide), rsp, sv_sp14]; exact F.sepHi (by decide) (by decide) (by decide))
    (by rw [r1 sp (by decide), rsp, sv_sp14]; exact F.sepHi (by decide) (by decide) (by decide))
    (by rw [r1 sp (by decide), rsp, sv_sp14]; exact F.sepHi (by decide) (by decide) (by decide))
    (by rw [r1 sp (by decide), rsp, sv_sp14]; exact F.sepHi (by decide) (by decide) (by decide))
    (by rw [r1 sp (by decide), rsp, sv_sp14]; exact hp.sep F (by decide))
    (by rw [r1 sp (by decide), rsp, sv_sp14]; exact hq.sep F (by decide))
  rw [mem1, r1 sp (by decide), rsp, sv_sp14] at f2
  rw [mem1] at a02
  have hfS : ∀ x, SvR B x → Sep (B + BitVec.ofNat 32 0x218C) 0x14 x 1 := fun x hx => by
    have := svR_lo (k := 0x14) hx (by decide) (by decide)
    rwa [sv_lo B 0x14 (by decide)] at this
  refine ⟨n2, c1.trans c2, ⟨by rw [pc2], rfl, fun _ => rfl⟩,
    fun r h0 h1 h2 h3 h4 h5 hra => by rw [k2 r h0 h1 h2 h3 h4 h5, r1 r hra], a02, fun e he _ => ?_,
    fun x hx => f2 x (hfS x hx)⟩
  exact f2 _ (by rw [← sv_base']; exact sepS B (by omega) (by omega) (by omega))

theorem sv_sp60 (B : Word) : B + 0x21A0 + 0xFFFFFFA0 = B + BitVec.ofNat 32 0x2140 := by
  rw [BitVec.add_assoc]; rfl

/-- What `x509::read_time` leaves at offset `oc` and in the reader at `dc`
when the time reads, as `t` with the bytes `r` after it. -/
def RtOkW (M : Word → BitVec 8) (M0 : Word → BitVec 8) (B : Word) (oc dc : Nat) (rp : Word) (rl : Nat) (t : Nat)
    (r : Bytes) : Prop :=
  t < 2 ^ 64 ∧ M (B + 0x21A0 + BitVec.ofNat 32 oc) = 0 ∧
  memLoad32 M (B + 0x21A0 + BitVec.ofNat 32 (oc + 8)) = BitVec.ofNat 32 (t % 2 ^ 32) ∧
  memLoad32 M (B + 0x21A0 + BitVec.ofNat 32 (oc + 12)) = BitVec.ofNat 32 (t / 2 ^ 32) ∧
  ∃ k, k ≤ rl ∧ memLoad32 M (B + 0x21A0 + BitVec.ofNat 32 (dc + 8)) = rp + BitVec.ofNat 32 k ∧
    memLoad32 M (B + 0x21A0 + BitVec.ofNat 32 (dc + 12)) = BitVec.ofNat 32 (rl - k) ∧
    r = memBytes M0 (rp + BitVec.ofNat 32 k) (rl - k)

set_option maxHeartbeats 8000000 in
/-- **A call to `x509::read_time`** with the result at offset `oc` and the
reader at offset `dc`, whose unread bytes are `rl` bytes at `rp`. -/
theorem sv_rtF {M : Word → BitVec 8} {n : Machine} {B : Word} {off : Nat} {imm o rp : Word} {oc dc rl : Nat}
    (F : Fr B 0x2660) (C : SvCode M) (s : St M SV n off (reg n))
    (h1 : fetchRel sigstoreVerifyCode off = some (.auipc ra imm, 4))
    (h2 : fetchRel sigstoreVerifyCode (off + 4) = some (.jalr ra ra o, 4))
    (hb : SV + BitVec.ofNat 32 off + imm + o = BitVec.ofNat 32 x509ReadTimeAddress)
    (hev : (SV + BitVec.ofNat 32 (off + 8)).toNat % 2 = 0)
    (rsp : reg n sp = B + 0x21A0) (ha0 : reg n a0 = B + 0x21A0 + BitVec.ofNat 32 oc)
    (ha1 : reg n a1 = B + 0x21A0 + BitVec.ofNat 32 dc)
    (ho2 : oc + 16 ≤ 0x4C0) (ho3 : oc % 4 = 0) (hd2 : dc + 16 ≤ 0x4C0) (hd3 : dc % 4 = 0)
    (hs : oc + 16 ≤ dc + 8 ∨ dc + 16 ≤ oc)
    (hrp : memLoad32 M (B + 0x21A0 + BitVec.ofNat 32 (dc + 8)) = rp)
    (hrl : memLoad32 M (B + 0x21A0 + BitVec.ofNat 32 (dc + 12)) = BitVec.ofNat 32 rl)
    (hin : SvIn B rp rl) :
    ∃ n', Steps n n' ∧ St n'.mem SV n' (off + 8) (reg n') ∧ reg n' sp = B + 0x21A0 ∧
      (∀ q : Fin 32, q.val ∈ [3, 4, 8, 9, 18, 19, 20, 21, 22, 23, 24, 25, 26, 27] → reg n' q = reg n q) ∧
      SvKeepL B M n'.mem [(oc, 16), (dc + 8, 8)] ∧
      (∀ t r, readTime (memBytes M rp rl) = some (t, r) → RtOkW n'.mem M B oc dc rp rl t r) ∧
      (readTime (memBytes M rp rl) = none → n'.mem (B + 0x21A0 + BitVec.ofNat 32 oc) = 1 ∧
        (n'.mem (B + 0x21A0 + BitVec.ofNat 32 (oc + 1))).toNat < 0x27) ∧
      (∀ x, SvR B x → n'.mem x = M x) := by
  have hFl := F.lo; have hFh := F.hi; have hFa := F.al
  obtain ⟨n1, c1, pc1, mem1, regs1⟩ := s.callRa C.self h1 h2 hb (by decide)
  have r1 := PEnv.reg1 regs1 s.zero
  have d8 := lit8 (B + 0x21A0) dc (by omega)
  have d12 := lit12 (B + 0x21A0) dc (by omega)
  have o8 := lit8 (B + 0x21A0) oc (by omega)
  have o12 := lit12 (B + 0x21A0) oc (by omega)
  have hS : (B + (0x21A0 : Word)).toNat = B.toNat + 0x21A0 := F.at 0x21A0 (by decide)
  obtain ⟨n2, c2, pc2, sp2, k2, Ok, Er, f2⟩ := x509ReadTime_correct n1 (rp := rp) (rl := rl)
    (by rw [mem1]; exact C.x509ReadTime) (by rw [mem1]; exact C.tlv) (by rw [mem1]; exact C.generalizedTime)
    (by rw [mem1]; exact C.dateTime) (by rw [mem1]; exact C.timeDigits2) (by rw [mem1]; exact C.timeDigits4)
    (by rw [mem1]; exact C.allAsciiDigit) pc1
    (by rw [r1 a0 (by decide), ha0]) (by rw [r1 a1 (by decide), ha1]) (by rw [regs1]; simp +decide [upd])
    (even_clear _ hev) (by rw [r1 sp (by decide), rsp]) (by rw [hS]; omega) (by rw [hS]; omega)
    (by rw [hS]; omega) (by rw [sv_at F _ (by omega)]; omega) (sv_al F (by omega) ho3)
    (by rw [sv_at F _ (by omega)]; omega) (sv_al F (by omega) hd3) (by rw [mem1, d8, hrp]) (by rw [mem1, d12, hrl])
    hin.lo hin.pos
    (by rw [sv_sp60, ← sv_base']; exact sepS B (by omega) (by omega) (by omega))
    (by rw [sv_sp60, d8, ← sv_base']; exact sepS B (by omega) (by omega) (by omega))
    (by rw [d8]; exact sepS (B + 0x21A0) (by omega) (by omega) (by omega))
    (by rw [sv_sp60]; exact (hin.sep14.symm.sub (c := 0x1590 + 0x2140) (l := 0x60) (by decide) |> fun h => by
      rw [show B + 0xFFFFEA70 + BitVec.ofNat 32 (0x1590 + 0x2140) = B + BitVec.ofNat 32 0x2140 by
        rw [BitVec.add_assoc]; rfl] at h; exact h.symm))
    (by rw [d8, ← sv_base']; exact (hin.sepLo (by omega)))
  rw [mem1] at Ok Er f2
  rw [sv_sp60, d8] at f2
  have hfS : ∀ x, SvR B x → Sep (B + BitVec.ofNat 32 0x2140) 0x60 x 1 := fun x hx => by
    have := svR_lo (k := 0x60) hx (by decide) (by decide)
    rwa [sv_lo B 0x60 (by decide)] at this
  refine ⟨n2, c1.trans c2, ⟨by rw [pc2], rfl, fun _ => rfl⟩, sp2,
    fun q hq => by rw [k2 q (by revert hq; revert q; decide), r1 q (by revert hq; revert q; decide)],
    fun e he hL => ?_, fun t r h => ?_,
    fun h => ⟨(Er h).1, by
      rw [← add_ofNat_assoc]
      exact Nat.lt_of_le_of_lt (Nat.le_of_eq (congrArg BitVec.toNat (Er h).2)) (xrt_errByte_lt _)⟩,
    fun x hx => f2 x (hfS x hx) (svR_hi hx ho2) (svR_hi hx (by omega))⟩
  · have h1 := hL _ (List.mem_cons_self ..)
    have h2 := hL _ (List.mem_cons_of_mem _ (List.mem_singleton_self _))
    simp only at h1 h2
    exact f2 _ (by rw [← sv_base']; exact sepS B (by omega) (by omega) (by omega))
      (sepS (B + 0x21A0) (by omega) (by omega) (by omega)) (sepS (B + 0x21A0) (by omega) (by omega) (by omega))
  · obtain ⟨h64, b0, w8, w12, k, hk, wd8, wd12, hr⟩ := Ok t r h
    rw [o8] at w8; rw [o12] at w12; rw [d8] at wd8; rw [d12] at wd12
    exact ⟨h64, b0, w8, w12, k, hk, wd8, wd12, hr⟩

theorem sv_sp4 (B : Word) : B + 0x21A0 + 0xFFFFFFFC = B + BitVec.ofNat 32 0x219C := by
  rw [BitVec.add_assoc]; rfl

set_option maxHeartbeats 8000000 in
/-- **A call to `<[u8]>::eq`** of `pl` bytes at `p` and `ql` bytes at `q`. -/
theorem sv_seqEqF {M : Word → BitVec 8} {n : Machine} {B : Word} {off : Nat} {imm o p q : Word} {pl ql : Nat}
    (F : Fr B 0x2660) (C : SvCode M) (s : St M SV n off (reg n))
    (h1 : fetchRel sigstoreVerifyCode off = some (.auipc ra imm, 4))
    (h2 : fetchRel sigstoreVerifyCode (off + 4) = some (.jalr ra ra o, 4))
    (hb : SV + BitVec.ofNat 32 off + imm + o = BitVec.ofNat 32 sliceEqAddress)
    (hev : (SV + BitVec.ofNat 32 (off + 8)).toNat % 2 = 0)
    (rsp : reg n sp = B + 0x21A0) (ha0 : reg n a0 = p) (ha1 : reg n a1 = BitVec.ofNat 32 pl)
    (ha2 : reg n a2 = q) (ha3 : reg n a3 = BitVec.ofNat 32 ql) (hp : SvRo B p pl) (hq : SvRo B q ql) :
    ∃ n', Steps n n' ∧ St n'.mem SV n' (off + 8) (reg n') ∧
      (∀ r, r ≠ a0 → r ≠ a1 → r ≠ a2 → r ≠ a3 → r ≠ a4 → r ≠ t1 → r ≠ ra → reg n' r = reg n r) ∧
      reg n' a0 = (if memBytes M p pl = memBytes M q ql then 1 else 0) ∧
      SvKeepL B M n'.mem [] ∧ (∀ x, SvR B x → n'.mem x = M x) := by
  have hFl := F.lo; have hFh := F.hi; have hFa := F.al
  obtain ⟨n1, c1, pc1, mem1, regs1⟩ := s.callRa C.self h1 h2 hb (by decide)
  have r1 := PEnv.reg1 regs1 s.zero
  have hS : (B + (0x21A0 : Word)).toNat = B.toNat + 0x21A0 := F.at 0x21A0 (by decide)
  obtain ⟨n2, c2, pc2, a02, k2, f2⟩ := sliceEq_correct n1 (p := p) (q := q) (pl := pl) (ql := ql) (by decide)
    (by rw [mem1]; exact C.sliceEq) (by rw [mem1]; exact C.equalSameLength) (by rw [mem1]; exact C.memcmp) pc1
    (by rw [r1 a0 (by decide), ha0]) (by rw [r1 a1 (by decide), ha1])
    (by rw [r1 a2 (by decide), ha2]) (by rw [r1 a3 (by decide), ha3]) (by have := hp.fit; omega)
    (by have := hq.fit; omega) (by rw [regs1]; simp +decide [upd]) (even_clear _ hev)
    (by rw [r1 sp (by decide), rsp, hS]; omega)
    (by rw [r1 sp (by decide), rsp, sv_sp4]; exact F.sepHi (by decide) (by decide) (by decide))
    (by rw [r1 sp (by decide), rsp, sv_sp4]; exact F.sepHi (by decide) (by decide) (by decide))
    (by rw [r1 sp (by decide), rsp, sv_sp4]; exact hp.sep F (by decide))
    (by rw [r1 sp (by decide), rsp, sv_sp4]; exact hq.sep F (by decide))
  rw [mem1, r1 sp (by decide), rsp, sv_sp4] at f2
  rw [mem1] at a02
  have hfS : ∀ x, SvR B x → Sep (B + BitVec.ofNat 32 0x219C) 4 x 1 := fun x hx => by
    have := svR_lo (k := 4) hx (by decide) (by decide)
    rwa [sv_lo B 4 (by decide)] at this
  refine ⟨n2, c1.trans c2, ⟨by rw [pc2], rfl, fun _ => rfl⟩,
    fun r h0 h1 h2 h3 h4 h5 hra => by rw [k2 r h0 h1 h2 h3 h4 h5, r1 r hra], a02, fun e he _ => ?_,
    fun x hx => f2 x (hfS x hx)⟩
  exact f2 _ (by rw [← sv_base']; exact sepS B (by omega) (by omega) (by omega))

end C3.RV32.Sv
