import C3BootProofs.Proofs.SvLeafHash
import C3BootProofs.Proofs.Pv384Main

/-!
# `sigstore::verify`: calling `p384_verify_prehash`

`verify_leaf` checks the leaf's signature with `p384_verify_prehash`, whose
frame is the stack below `sigstore::verify`'s.
-/

namespace C3.RV32.Sv

open C3.Image C3.RV32.P3 C3.RV32.Dq C3.RV32.Pv

set_option maxRecDepth 20000

/-- `p384_verify_prehash`'s code and constants survive a change to memory
that keeps outside the stack. -/
theorem PvEnv7.sv {B : Word} {M M0 : Word → BitVec 8} (F : Fr B 0x3830) (E : PvEnv7 M0)
    (h : ∀ x, SvR B x → M x = M0 x) : PvEnv7 M :=
  have hh : ∀ x : Word, 0x40000000 ≤ x.toNat → M x = M0 x := fun x hx => h x (sep_of_le (by
    have hb : (B + 0xFFFFFE60).toNat = B.toNat - 0x1A0 := F.below 0x1A0 (by decide) (by decide)
    have := F.hi; rw [hb]; omega) (by have := x.isLt; omega))
  ⟨⟨⟨⟨⟨⟨E.E.E.E.E.E.C.hi hh, E.E.E.E.E.E.D.of F h, E.E.E.E.E.E.C2.hi hh, E.E.E.E.E.E.D2.of F h⟩,
    E.E.E.E.E.C3.hi hh, E.E.E.E.E.D3.of F h⟩, E.E.E.E.C4.hi hh⟩, E.E.E.C5.hi hh⟩, E.E.C6.hi hh⟩,
    E.C7.hi hh, F.dataIn h E.aid (by decide) (by decide)⟩

/-- Bytes in `sigstore::verify`'s frame sit apart from `p384_verify_prehash`'s. -/
theorem sv_pvSep {B : Word} (F : Fr B 0x3830) {c k : Nat} (hc : c + k ≤ 0x1690) :
    Sep (B + 0x21A0 + BitVec.ofNat 32 c) k (B + 0xFFFFFE60) 0x2340 := by
  have hb : (B + 0xFFFFFE60).toNat = B.toNat - 0x1A0 := F.below 0x1A0 (by decide) (by decide)
  have := F.lo; have := F.hi
  exact (sep_of_le (by rw [hb, sv_at F c (by omega)]; omega) (by rw [sv_at F c (by omega)]; omega)).symm

/-- Bytes outside the stack sit apart from `p384_verify_prehash`'s frame. -/
theorem SvIn.pvSep {B p : Word} {k : Nat} (h : SvIn B p k) : Sep p k (B + 0xFFFFFE60) 0x2340 :=
  h.sep.subR (c := 0) (l := 0x2340) (by decide) |> fun s => by rwa [add_ofNat_zero] at s

set_option maxHeartbeats 16000000 in
/-- **A call to `p384_verify_prehash`** from `sigstore::verify`: the result is
`pvModel` of the inputs, or the call panics exactly when `pvModel` is
`none`. The callee keeps out of `sigstore::verify`'s frame. -/
theorem sv_pvF {n : Machine} {B : Word} {off : Nat} {imm o pk ph rp sp' : Word} {len : Nat}
    (F : Fr B 0x3830) (C : SvCode n.mem) (PE : PvEnv7 n.mem) (s : St n.mem SV n off (reg n))
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
      (even_clear _ hev) sPK hPK sR sS sph hph (by rw [mem1]; exact side) with ⟨hn, hp⟩ | ⟨v, hv, n2, c2, pc2, sp2, sv2, g3, g4, a02, O2⟩
  · rw [mem1] at hn
    exact .inl ⟨hn, hp.of_steps c1⟩
  · rw [mem1] at hv O2
    have hS : ∀ x, Sep x 1 (B + 0xFFFFFE60) 0x2340 → n2.mem x = n.mem x := fun x hx => O2 x hx.symm
    refine .inr ⟨v, hv, n2, c1.trans c2, ⟨by rw [pc2], rfl, fun _ => rfl⟩, sp2, fun q hq => ?_,
      a02, fun e he _ => hS _ (sv_pvSep F (c := e) (k := 1) he), fun x hx => O2 x (hx.sub (c := 0) (l := 0x2340) (by decide)
        |> fun s => by rwa [add_ofNat_zero] at s)⟩
    have hq' : q = savedReg 1 ∨ q = savedReg 2 ∨ q = savedReg 3 ∨ q = savedReg 4 ∨ q = savedReg 5 ∨
        q = savedReg 6 ∨ q = savedReg 7 ∨ q = savedReg 8 ∨ q = savedReg 9 ∨ q = savedReg 10 ∨ q = savedReg 11 ∨
        q = savedReg 12 ∨ q = 3 ∨ q = 4 := by revert hq; revert q; decide
    rcases hq' with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    all_goals first
      | (rw [g3, r1 _ (by decide)]) | (rw [g4, r1 _ (by decide)])
      | (rw [sv2 _ (by decide), r1 _ (by decide)])

end C3.RV32.Sv

namespace C3.RV32.Sv

open C3.Image C3.RV32.P3 C3.RV32.Dq C3.RV32.Pv

def svLpv : List BInstr :=
  [.lw a0 sp 0x7C, .lw a0 a0 0xFFFFFFF4, .aluImm .add a4 sp 0x100, .lui a1 0x1000, .aluImm .add a1 a1 0x20,
   .alu .add a1 a1 sp, .aluImm .add a2 x0 0x30, .aluImm .add a3 sp 0xD0]

set_option maxRecDepth 100000 in
theorem svLpv_end : blockEnd sigstoreVerifyCode 0xDC8 svLpv = some 0xDDE := by decide

set_option maxRecDepth 100000 in
set_option maxHeartbeats 16000000 in
/-- **The leaf's signature check**, from 0xDC8 to 0xDE6: `p384_verify_prehash`
on the issuer's key, the digest at offset 0x1020, and `r` and `s` at
offsets 0xD0 and 0x100. -/
theorem sv_lpv {n : Machine} {B q pk : Word} (F : Fr B 0x3830) (E : SvCode n.mem) (PE : PvEnv7 n.mem)
    (s : St n.mem SV n 0xDC8 (reg n)) (rsp : reg n sp = B + 0x21A0)
    (w7c : memLoad32 n.mem (B + 0x21A0 + BitVec.ofNat 32 0x7C) = q) (hpk : memLoad32 n.mem (q + 0xFFFFFFF4) = pk)
    (al : (q + 0xFFFFFFF4).toNat % 4 = 0) (pkIn : SvIn B pk 0x61)
    (side : PvSide n.mem pk (B + 0x21A0 + BitVec.ofNat 32 0x1020) 48 (B + 0x21A0 + BitVec.ofNat 32 0xD0)
      (B + 0x21A0 + BitVec.ofNat 32 0x100)) :
    (pvModel n.mem pk (B + 0x21A0 + BitVec.ofNat 32 0x1020) 48 (B + 0x21A0 + BitVec.ofNat 32 0xD0)
      (B + 0x21A0 + BitVec.ofNat 32 0x100) = none ∧ Panics n) ∨
    (∃ v, pvModel n.mem pk (B + 0x21A0 + BitVec.ofNat 32 0x1020) 48 (B + 0x21A0 + BitVec.ofNat 32 0xD0)
      (B + 0x21A0 + BitVec.ofNat 32 0x100) = some v ∧
      ∃ n', Steps n n' ∧ St n'.mem SV n' 0xDE6 (reg n') ∧ reg n' sp = B + 0x21A0 ∧
        (∀ q : Fin 32, q.val ∈ [3, 4, 8, 9, 18, 19, 20, 21, 22, 23, 24, 25, 26, 27] → reg n' q = reg n q) ∧
        reg n' a0 = v ∧ SvKeepL B n.mem n'.mem [] ∧ (∀ x, SvR B x → n'.mem x = n.mem x)) := by
  have hFh := F.hi
  obtain ⟨n1, c1, u1⟩ := s.block svLpv E.self svLpv_end (by
    simp +decide only [svLpv, BlockOk, BInstr.ok, BInstr.run, upd, ↓reduceIte, and_true]
    rw [rsp]
    refine ⟨sv_al F (c := 0x7C) (by decide) (by decide), ?_⟩
    rw [show memLoad32 n.mem (B + 0x21A0 + 0x7C) = q from w7c]; exact al)
  have m1 : n1.mem = n.mem := u1.mem
  have s1 : St n1.mem SV n1 0xDDE (reg n1) := ⟨u1.pc, rfl, fun _ => rfl⟩
  have k1 : ∀ q : Fin 32, q.val ∈ [2, 3, 4, 8, 9, 18, 19, 20, 21, 22, 23, 24, 25, 26, 27] → reg n1 q = reg n q :=
    fun q hq => by rw [u1.regs, runBlock_reg _ _ _ q s.zero (by revert hq; revert q; decide)]
  have E1 : SvCode n1.mem := by rw [m1]; exact E
  rcases sv_pvF (pk := pk) (ph := B + 0x21A0 + BitVec.ofNat 32 0x1020) (len := 48)
      (rp := B + 0x21A0 + BitVec.ofNat 32 0xD0) (sp' := B + 0x21A0 + BitVec.ofNat 32 0x100)
      F E1 (by rw [m1]; exact PE) s1 sv_at_dde sv_at_de2 (by decide) (by decide) (by rw [k1 sp (by decide), rsp])
      (by rw [u1.regs]; simp +decide only [svLpv, runBlock, BInstr.run, upd, ↓reduceIte]; rw [rsp]
          rw [show memLoad32 n.mem (B + 0x21A0 + 0x7C) = q from w7c]; exact hpk)
      (by rw [u1.regs]; simp +decide only [svLpv, runBlock, BInstr.run, upd, ↓reduceIte]; rw [rsp]; exact sv_hi B 0x1020)
      (by rw [u1.regs]; simp +decide only [svLpv, runBlock, BInstr.run, upd, ↓reduceIte])
      (by rw [u1.regs]; simp +decide only [svLpv, runBlock, BInstr.run, upd, ↓reduceIte]; rw [rsp]; rfl)
      (by rw [u1.regs]; simp +decide only [svLpv, runBlock, BInstr.run, upd, ↓reduceIte]; rw [rsp]; rfl)
      pkIn.pvSep (by have := pkIn.lo; omega) (sv_pvSep F (by decide)) (sv_pvSep F (by decide)) (sv_pvSep F (by decide))
      (by rw [sv_at F _ (by decide)]; omega) (by rw [m1]; exact side) with ⟨hn, hp⟩ | ⟨v, hv, n2, c2, s2, sp2, k2, a2, K2, f2⟩
  · rw [m1] at hn
    exact .inl ⟨hn, hp.of_steps c1⟩
  · rw [m1] at hv K2 f2
    exact .inr ⟨v, hv, n2, c1.trans c2, s2, sp2, fun q hq => by rw [k2 q hq, k1 q (by revert hq; revert q; decide)],
      a2, K2, f2⟩

end C3.RV32.Sv
