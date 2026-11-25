import C3BootProofs.Proofs.SvFail
import C3BootProofs.Proofs.SvPvModel
import C3BootProofs.Proofs.Sha384Fn

/-!
# `sigstore::verify`: calling `sha384` and `p384_verify_prehash`

Both callees run on the stack below `sigstore::verify`'s frame.
-/

namespace C3.RV32.Sv

open C3.Image C3.RV32.P3 C3.RV32.Dq C3.RV32.Pv

set_option maxRecDepth 20000

/-- The read-only data sits apart from `SvR`'s stack. -/
def SvRoSep (B : Word) : Prop :=
  Sep (B + 0xFFFFEA70) 0x3BF0 (BitVec.ofNat 32 (img% roWindowAddress)) (img% roWindowSize)

theorem SvRo.lo {B q : Word} {ql : Nat} (h : SvRo B q ql) : q.toNat + ql ≤ 0x40000000 := by
  rcases h with h | ⟨_, h2⟩
  · have := h.lo; omega
  · omega

theorem svW_at (B : Word) (c : Nat) (_hc : c ≤ 0x2660) :
    B + 0xFFFFEA70 + BitVec.ofNat 32 (0x1590 + c) = B + BitVec.ofNat 32 c := by
  rw [BitVec.add_assoc]; congr 1; apply BitVec.eq_of_toNat_eq
  rw [BitVec.toNat_add, BitVec.toNat_ofNat, BitVec.toNat_ofNat,
    show (0xFFFFEA70 : Word).toNat = 0xFFFFEA70 from rfl]
  omega

/-- A byte at or above 0x40000000 is outside the stack. -/
theorem svR_hiMem {B x : Word} (F : Fr B 0x2660) (hx : 0x40000000 ≤ x.toNat) : SvR B x :=
  sep_of_le (by
    have hb : (B + 0xFFFFEA70).toNat = B.toNat - 0x1590 := by
      have := F.lo; have := B.isLt
      rw [BitVec.toNat_add, show (0xFFFFEA70 : Word).toNat = 0xFFFFEA70 from rfl]; omega
    have := F.hi; rw [hb]; omega) (by have := x.isLt; omega)

theorem svR_ofW {B x : Word} (hx : Sep (B + 0xFFFFEC10 + 0xFFFFFE60) (0x3A50 + 0x1A0) x 1) : SvR B x := by
  rwa [BitVec.add_assoc, show (0xFFFFEC10 : Word) + 0xFFFFFE60 = 0xFFFFEA70 from rfl] at hx

/-- A byte of the read-only data is outside the stack. -/
theorem roR {B q : Word} {ql : Nat} (RS : SvRoSep B) (h1 : (img% roWindowAddress) ≤ q.toNat)
    (h2 : q.toNat + ql ≤ (img% roWindowAddress + roWindowSize)) (i : Nat) (hi : i < ql) :
    SvR B (q + BitVec.ofNat 32 i) := by
  have hs := RS.subR (c := q.toNat - (img% roWindowAddress) + i) (l := 1) (by omega)
  have e : BitVec.ofNat 32 (img% roWindowAddress) + BitVec.ofNat 32 (q.toNat - (img% roWindowAddress) + i) =
      q + BitVec.ofNat 32 i := by
    apply BitVec.eq_of_toNat_eq
    rw [BitVec.toNat_add, BitVec.toNat_add, BitVec.toNat_ofNat, BitVec.toNat_ofNat, BitVec.toNat_ofNat]
    have := q.isLt
    omega
  rw [e] at hs
  exact hs

set_option maxRecDepth 200000 in
/-- `sha384`'s code and constants survive a change to memory that keeps
outside the stack. -/
theorem HfEnv.sv {B : Word} {M M0 : Word → BitVec 8} (FW : Fr (B + 0xFFFFEC10) 0x3A50) (RS : SvRoSep B)
    (E : HfEnv M0) (h : ∀ x, SvR B x → M x = M0 x) : HfEnv M :=
  have hh : ∀ x : Word, 0x40000000 ≤ x.toNat → M x = M0 x := fun x hx => h x (svR_hiMem (sv_frW FW) hx)
  ⟨codeHi E.cod (by decide) (by decide) hh, codeHi E.blk (by decide) (by decide) hh,
    codeHi E.cmp (by decide) (by decide) hh, codeHi E.rfi (by decide) (by decide) hh,
    codeHi E.fb (by decide) (by decide) hh, codeHi E.za48 (by decide) (by decide) hh,
    codeHi E.za64 (by decide) (by decide) hh, codeHi E.mcs (by decide) (by decide) hh,
    codeHi E.mcb (by decide) (by decide) hh, codeHi E.mset (by decide) (by decide) hh,
    fun i hi => by rw [h _ (roR RS (by decide) (by decide) i hi)]; exact E.k i hi,
    FW.dataIn (fun x hx => h x (svR_ofW hx)) E.iv (by decide) (by decide)⟩

set_option maxRecDepth 200000 in
/-- `p384_verify_prehash`'s code and constants survive a change to memory
that keeps outside the stack. -/
theorem PvEnv7.sv {B : Word} {M M0 : Word → BitVec 8} (FW : Fr (B + 0xFFFFEC10) 0x3A50) (E : PvEnv7 M0)
    (h : ∀ x, SvR B x → M x = M0 x) : PvEnv7 M :=
  have h' : ∀ x, Sep (B + 0xFFFFEC10 + 0xFFFFFE60) (0x3A50 + 0x1A0) x 1 → M x = M0 x :=
    fun x hx => h x (svR_ofW hx)
  have hh : ∀ x : Word, 0x40000000 ≤ x.toNat → M x = M0 x := fun x hx => h x (svR_hiMem (sv_frW FW) hx)
  ⟨⟨⟨⟨⟨⟨E.E.E.E.E.E.C.hi hh, E.E.E.E.E.E.D.of FW h', E.E.E.E.E.E.C2.hi hh, E.E.E.E.E.E.D2.of FW h'⟩,
    E.E.E.E.E.C3.hi hh, E.E.E.E.E.D3.of FW h'⟩, E.E.E.E.C4.hi hh⟩, E.E.E.C5.hi hh⟩, E.E.C6.hi hh⟩,
    E.C7.hi hh, FW.dataIn h' E.aid (by decide) (by decide)⟩

/-- Bytes in `sigstore::verify`'s frame sit apart from the stack below it. -/
theorem sv_pvSep {B : Word} (F : Fr B 0x2660) {c k : Nat} (hc : c + k ≤ 0x4C0) :
    Sep (B + 0x21A0 + BitVec.ofNat 32 c) k (B + 0xFFFFFE60) 0x2340 := by
  have hb : (B + 0xFFFFFE60).toNat = B.toNat - 0x1A0 := F.below 0x1A0 (by decide) (by decide)
  have := F.lo; have := F.hi
  exact (sep_of_le (by rw [hb, sv_at F c (by omega)]; omega) (by rw [sv_at F c (by omega)]; omega)).symm

/-- Bytes outside the stack sit apart from the stack below the frame. -/
theorem SvIn.pvSep {B p : Word} {k : Nat} (h : SvIn B p k) : Sep p k (B + 0xFFFFFE60) 0x2340 := by
  have := h.sep.subR (c := 0x13F0) (l := 0x2340) (by decide)
  rwa [BitVec.add_assoc, show (0xFFFFEA70 : Word) + BitVec.ofNat 32 0x13F0 = 0xFFFFFE60 from rfl] at this

theorem svR_pv {B x : Word} (hx : SvR B x) : Sep (B + 0xFFFFFE60) 0x2340 x 1 := by
  have := hx.sub (c := 0x13F0) (l := 0x2340) (by decide)
  rwa [BitVec.add_assoc, show (0xFFFFEA70 : Word) + BitVec.ofNat 32 0x13F0 = 0xFFFFFE60 from rfl] at this

theorem sv_hfG (B : Word) : hfG (B + BitVec.ofNat 32 0x1F60) = B + BitVec.ofNat 32 0x1B40 := by
  show B + BitVec.ofNat 32 0x1F60 + 0xFFFFFBE0 = _
  rw [BitVec.add_assoc]; rfl

set_option maxHeartbeats 8000000 in
/-- **A call to `c3_crypto::sha::sha384`** on the `nl` bytes at `p`, with
the digest at offset `oc` of the frame. -/
theorem sv_sha384F {M : Word → BitVec 8} {n : Machine} {B : Word} {off : Nat} {imm o p : Word} {oc nl : Nat}
    (FW : Fr (B + 0xFFFFEC10) 0x3A50) (C : SvCode M) (HE : HfEnv M) (RS : SvRoSep B) (s : St M SV n off (reg n))
    (h1 : fetchRel sigstoreVerifyCode off = some (.auipc ra imm, 4))
    (h2 : fetchRel sigstoreVerifyCode (off + 4) = some (.jalr ra ra o, 4))
    (hb : SV + BitVec.ofNat 32 off + imm + o = HF)
    (hev : (SV + BitVec.ofNat 32 (off + 8)).toNat % 2 = 0)
    (rsp : reg n sp = B + 0x21A0) (ha0 : reg n a0 = B + 0x21A0 + BitVec.ofNat 32 oc) (ha1 : reg n a1 = p)
    (ha2 : reg n a2 = BitVec.ofNat 32 nl) (ho : oc + 48 ≤ 0x4C0) (hin : SvRo B p nl) :
    ∃ n', Steps n n' ∧ St n'.mem SV n' (off + 8) (reg n') ∧ reg n' sp = B + 0x21A0 ∧
      (∀ q : Fin 32, q.val ∈ [3, 4, 8, 9, 18, 19, 20, 21, 22, 23, 24, 25, 26] → reg n' q = reg n q) ∧
      SvKeepL B M n'.mem [(oc, 48)] ∧
      memBytes n'.mem (B + 0x21A0 + BitVec.ofNat 32 oc) 48 = sha384 (memBytes M p nl) ∧
      (∀ x, SvR B x → n'.mem x = M x) := by
  have F := sv_frW FW
  have hFl := F.lo; have hFh := F.hi; have hFa := F.al
  obtain ⟨n1, c1, pc1, mem1, regs1⟩ := s.callRa C.self h1 h2 hb (by decide)
  have r1 := PEnv.reg1 regs1 s.zero
  have ra1 : reg n1 ra = SV + BitVec.ofNat 32 (off + 8) := by rw [regs1]; simp +decide [upd]
  have hG := F.at 0x1F60 (by decide)
  have hpl := hin.lo
  have Cx : HfCtx n1.mem (B + BitVec.ofNat 32 0x1F60) (B + 0x21A0 + BitVec.ofNat 32 oc) p nl := by
    rw [mem1]
    refine ⟨HE, by rw [hG]; omega, by rw [hG]; omega, by rw [hG]; omega, ?_, ?_, ?_, hpl, ?_⟩
    · rw [sv_hfG]
      have := RS.sub (c := 0x1590 + 0x1B40) (l := 0x660) (by decide)
      rw [svW_at B 0x1B40 (by decide)] at this
      exact this.symm
    · rw [sv_hfG]; exact (hin.sep F (c := 0x1B40) (n := 0x660) (by decide)).symm
    · rw [sv_hfG, ← sv_base]; exact sepS B (by omega) (by omega) (by omega)
    · rw [sv_at F oc (by omega)]; omega
  obtain ⟨n2, c2, pc2, sp2, k2, g2, t2, dg2, f2⟩ := sha384Fn_correct n1 Cx pc1
    (by rw [r1 sp (by decide), rsp, add_ofNat_assoc]; rfl)
    (by rw [r1 a0 (by decide), ha0]) (by rw [r1 a1 (by decide), ha1]) (by rw [r1 a2 (by decide), ha2])
    (by rw [ra1]; exact even_clear _ hev)
  rw [mem1] at f2 dg2
  have kp : ∀ q : Fin 32, q.val ∈ [8, 9, 18, 19, 20, 21, 22, 23, 24, 25, 26] → reg n2 q = reg n1 q := by
    intro q hq
    have hm : q ∈ hfPs.map Prod.fst := by revert hq; revert q; decide
    obtain ⟨⟨r, o⟩, hro, rfl⟩ := List.mem_map.1 hm
    exact k2 r o hro
  have lo : ∀ x, SvR B x → Sep (hfG (B + BitVec.ofNat 32 0x1F60)) 0x660 x 1 := fun x hx => by
    have := hx.sub (c := 0x1590 + 0x1B40) (l := 0x660) (by decide)
    rwa [svW_at B 0x1B40 (by decide), ← sv_hfG] at this
  refine ⟨n2, c1.trans c2, ⟨by rw [pc2, ra1], rfl, fun _ => rfl⟩, by rw [sp2, r1 sp (by decide), rsp],
    fun q hq => ?_, fun e he hL => ?_, dg2, fun x hx => f2 x (lo x hx) (svR_hi hx ho)⟩
  · rcases (show q = 3 ∨ q = 4 ∨ q.val ∈ [8, 9, 18, 19, 20, 21, 22, 23, 24, 25, 26] by
        revert hq; revert q; decide) with rfl | rfl | h
    · rw [g2, r1 _ (by decide)]
    · rw [t2, r1 _ (by decide)]
    · rw [kp q h, r1 q (by revert h; revert q; decide)]
  · have h1 := hL _ (List.mem_singleton_self _)
    simp only at h1
    exact f2 _ (by rw [sv_hfG, ← sv_base]; exact sepS B (by omega) (by omega) (by omega))
      (sepS (B + 0x21A0) (by omega) (by omega) (by omega))

set_option maxHeartbeats 16000000 in
/-- **A call to `p384_verify_prehash`** from `sigstore::verify`: the result is
`pvModel` of the inputs, or the call panics exactly when `pvModel` is
`none`. The callee keeps out of `sigstore::verify`'s frame. -/
theorem sv_pvF {n : Machine} {B : Word} {off : Nat} {imm o pk ph rp sp' : Word} {len : Nat}
    (F : Fr B 0x2660) (C : SvCode n.mem) (PE : PvEnv7 n.mem) (s : St n.mem SV n off (reg n))
    (h1 : fetchRel sigstoreVerifyCode off = some (.auipc ra imm, 4))
    (h2 : fetchRel sigstoreVerifyCode (off + 4) = some (.jalr ra ra o, 4))
    (hb : SV + BitVec.ofNat 32 off + imm + o = PV) (hev : (SV + BitVec.ofNat 32 (off + 8)).toNat % 2 = 0)
    (rsp : reg n sp = B + 0x21A0) (ha0 : reg n a0 = pk) (ha1 : reg n a1 = ph) (ha2 : reg n a2 = BitVec.ofNat 32 len)
    (ha3 : reg n a3 = rp) (ha4 : reg n a4 = sp')
    (sPK : Sep pk 0x61 (B + 0xFFFFFE60) 0x2340) (hPK : pk.toNat + 0x61 ≤ 0x40000000)
    (sR : Sep rp 48 (B + 0xFFFFFE60) 0x2340) (sS : Sep sp' 48 (B + 0xFFFFFE60) 0x2340)
    (sph : Sep ph len (B + 0xFFFFFE60) 0x2340) (hph : ph.toNat + len < 2 ^ 32)
    (side : PvSide n.mem pk ph len rp sp') :
    (pvModel n.mem pk ph len rp sp' = none ∧ Panics n) ∨
    (∃ v, pvModel n.mem pk ph len rp sp' = some v ∧
      ∃ n', Steps n n' ∧ St n'.mem SV n' (off + 8) (reg n') ∧ reg n' sp = B + 0x21A0 ∧
        (∀ q : Fin 32, q.val ∈ [3, 4, 8, 9, 18, 19, 20, 21, 22, 23, 24, 25, 26, 27] → reg n' q = reg n q) ∧
        reg n' a0 = v ∧ SvKeepL B n.mem n'.mem [] ∧ (∀ x, SvR B x → n'.mem x = n.mem x)) := by
  have FP : Fr B 0x21A0 := ⟨F.al, F.lo, by have := F.hi; omega, by
    have := F.dsep.sub (c := 0) (l := 0x2340) (by decide); rwa [add_ofNat_zero] at this⟩
  obtain ⟨n1, c1, pc1, mem1, regs1⟩ := s.callRa C.self h1 h2 hb (by decide)
  have r1 := PEnv.reg1 regs1 s.zero
  rcases p384VerifyPrehash_correct n1 (by rw [mem1]; exact PE) FP pc1 (by rw [r1 sp (by decide), rsp])
      (by rw [r1 a0 (by decide), ha0]) (by rw [r1 a1 (by decide), ha1]) (by rw [r1 a2 (by decide), ha2])
      (by rw [r1 a3 (by decide), ha3]) (by rw [r1 a4 (by decide), ha4]) (by rw [regs1]; simp +decide [upd])
      (even_clear _ hev) sPK hPK sR sS sph hph (by rw [mem1]; exact side) with
    ⟨hn, hp⟩ | ⟨v, hv, n2, c2, pc2, sp2, sv2, g3, g4, a02, O2⟩
  · rw [mem1] at hn
    exact .inl ⟨hn, hp.of_steps c1⟩
  · rw [mem1] at hv O2
    refine .inr ⟨v, hv, n2, c1.trans c2, ⟨by rw [pc2], rfl, fun _ => rfl⟩, sp2, fun q hq => ?_,
      a02, fun e he _ => O2 _ (sv_pvSep F (c := e) (k := 1) he).symm, fun x hx => O2 x (svR_pv hx)⟩
    have hq' : q = savedReg 1 ∨ q = savedReg 2 ∨ q = savedReg 3 ∨ q = savedReg 4 ∨ q = savedReg 5 ∨
        q = savedReg 6 ∨ q = savedReg 7 ∨ q = savedReg 8 ∨ q = savedReg 9 ∨ q = savedReg 10 ∨ q = savedReg 11 ∨
        q = savedReg 12 ∨ q = 3 ∨ q = 4 := by revert hq; revert q; decide
    rcases hq' with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    all_goals first
      | (rw [g3, r1 _ (by decide)]) | (rw [g4, r1 _ (by decide)])
      | (rw [sv2 _ (by decide), r1 _ (by decide)])

end C3.RV32.Sv
