import C3BootProofs.Proofs.SvFail
import C3BootProofs.Proofs.SvPv
import C3BootProofs.Proofs.P2vP256
import C3BootProofs.Proofs.PanicFree

/-!
# `sigstore::verify`: calling `p256_verify_prehash`

`p256_verify_prehash` runs on the stack below `sigstore::verify`'s frame,
in the frame `Fr (B + 0xFFFFEC10) 0x3590`, and keeps out of
`sigstore::verify`'s frame. `sv_p2c` runs from 0xA4C to 0xA60: it checks
the image's signature, `r` and `s` at offsets 0x130 and 0x150, over the
image's digest with the leaf's key.
-/

namespace C3.RV32.Sv

open C3.Image C3.RV32.P3 C3.RV32.Dq C3.RV32.Pv C3.RV32.P2v

set_option maxRecDepth 20000

theorem sv_p2Base (B : Word) : B + 0xFFFFEC10 + 0xFFFFFE60 = B + 0xFFFFEA70 := by
  rw [BitVec.add_assoc]; rfl

/-- Bytes in `sigstore::verify`'s frame sit apart from
`p256_verify_prehash`'s stack. -/
theorem sv_p2Sep {B : Word} (F : Fr B 0x2660) {c k : Nat} (hc : c + k ≤ 0x4C0) :
    Sep (B + 0x21A0 + BitVec.ofNat 32 c) k (B + 0xFFFFEA70) 0x3730 := by
  have hb : (B + 0xFFFFEA70).toNat = B.toNat - 0x1590 := by
    have := F.lo; have := B.isLt
    rw [BitVec.toNat_add, show (0xFFFFEA70 : Word).toNat = 0xFFFFEA70 from rfl]; omega
  have := F.lo; have := F.hi
  exact (sep_of_le (by rw [hb, sv_at F c (by omega)]; omega) (by rw [sv_at F c (by omega)]; omega)).symm

theorem SvIn.p2 {B p : Word} {k : Nat} (h : SvIn B p k) : P2vIn (B + 0xFFFFEC10) p k :=
  ⟨by rw [sv_p2Base]; have := h.sep.subR (c := 0) (l := 0x3730) (by decide); rwa [add_ofNat_zero] at this,
    h.pos, by have := h.lo; omega⟩

theorem sv_p2In {B : Word} (F : Fr B 0x2660) {c : Nat} (hc : c + 32 ≤ 0x4C0) :
    P2vIn (B + 0xFFFFEC10) (B + 0x21A0 + BitVec.ofNat 32 c) 32 :=
  ⟨by rw [sv_p2Base]; exact sv_p2Sep F hc, by rw [sv_at F c (by omega)]; omega,
    by have := F.hi; rw [sv_at F c (by omega)]; omega⟩

theorem svR_p2 {B x : Word} (hx : SvR B x) : P2vR (B + 0xFFFFEC10) x := by
  show Sep _ _ _ _
  rw [sv_p2Base]; have := hx.sub (c := 0) (l := 0x3730) (by decide); rwa [add_ofNat_zero] at this

theorem _root_.C3.RV32.P2v.P2vEnv.p2v {M M0 : Word → BitVec 8} {B : Word} (F : Fr B 0x3590) (E : P2vEnv M0)
    (fR : ∀ x, P2vR B x → M x = M0 x) : P2vEnv M := by
  have hx : ∀ x : Word, 0x40000000 ≤ x.toNat → M x = M0 x := fun x hx => fR x (sep_of_le (by
    have hb : (B + 0xFFFFFE60).toNat = B.toNat - 0x1A0 := F.below 0x1A0 (by decide) (by decide)
    have := F.hi; rw [hb]; omega) (by have := x.isLt; omega))
  exact ⟨E.ME.fr F fR, E.EC.p2v F fR, E.IC.p2v F fR, E.UC.p2v F fR, E.D.of F fR, E.BG.p2v F fR, E.BY.p2v F fR,
    codeIn_p2v F fR E.UE (by decide) (by decide), codeIn_p2v F fR E.N8 (by decide) (by decide),
    codeIn_p2v F fR E.PM (by decide) (by decide), codeIn_p2v F fR E.WM (by decide) (by decide),
    E.PT.p2v F fR, E.WN.p2v F fR, E.P2C.hi hx, E.GDC.hi hx, codeIn_p2v F fR E.SC (by decide) (by decide),
    F.dataIn fR E.hid (by decide) (by decide), F.dataIn fR E.GD (by decide) (by decide),
    F.dataIn fR E.OD (by decide) (by decide), F.dataIn fR E.AD (by decide) (by decide),
    F.dataIn fR E.UD (by decide) (by decide)⟩

theorem sep_join {a x : Word} {n m l k : Nat} (h1 : Sep a n x k) (h2 : Sep (a + BitVec.ofNat 32 m) l x k)
    (hm : m ≤ n) : Sep a (m + l) x k := by
  intro i hi j hj
  by_cases h : i < n
  · exact h1 i h j hj
  · have := h2 (i - m) (by omega) j hj
    rwa [BitVec.add_assoc, ← BitVec.ofNat_add, Nat.add_sub_cancel' (by omega)] at this

/-- The window of `p256_verify_prehash`'s stack, and the same window moved up
by `0x4C0`, together cover `sigstore::verify`'s stack. -/
theorem sv_p2Cover {B x : Word} (h1 : P2vR (B + 0xFFFFEC10) x) (h2 : P2vR (B + 0xFFFFF0D0) x) : SvR B x := by
  have e : B + 0xFFFFF0D0 + 0xFFFFFE60 = B + 0xFFFFEA70 + BitVec.ofNat 32 0x4C0 := by
    rw [BitVec.add_assoc, BitVec.add_assoc]; rfl
  unfold P2vR at h1 h2
  rw [sv_p2Base] at h1
  rw [e] at h2
  exact sep_join h1 h2 (by decide)

instance (B x : Word) : Decidable (P2vR B x) := by unfold P2vR Sep; infer_instance

/-- `p256_verify_prehash`'s code and constants survive a change to memory
that keeps outside `sigstore::verify`'s stack. -/
theorem _root_.C3.RV32.P2v.P2vEnv.sv {M M0 : Word → BitVec 8} {B : Word} (FW : Fr (B + 0xFFFFEC10) 0x3A50)
    (E : P2vEnv M0) (fR : ∀ x, SvR B x → M x = M0 x) : P2vEnv M := by
  have F1 : Fr (B + 0xFFFFEC10) 0x3590 := ⟨FW.al, FW.lo, by have := FW.hi; omega, by
    have := FW.dsep.sub (c := 0) (l := 0x3730) (by decide); rwa [add_ofNat_zero] at this⟩
  have F2 : Fr (B + 0xFFFFF0D0) 0x3590 := by
    have := FW.sub (c := 0x4C0) (n := 0x3590) (by decide) (by decide)
    rwa [BitVec.add_assoc] at this
  let Mm : Word → BitVec 8 := fun x => if P2vR (B + 0xFFFFEC10) x then M0 x else M x
  have E1 : P2vEnv Mm := E.p2v F1 fun x hx => by
    show (if _ then _ else _) = _
    simp only [hx, ↓reduceIte]
  exact E1.p2v F2 fun x hx => by
    show _ = if _ then _ else _
    split
    · next h1 => exact fR x (sv_p2Cover h1 hx)
    · rfl

set_option maxHeartbeats 16000000 in
/-- **A call to `p256_verify_prehash`** from `sigstore::verify`, on the key at
`pk`, the digest at `dg`, and `r` and `s` at offsets `rc` and `sc` of the
frame. It panics only if an inversion bound fails (`PanicIf`), returns 0,
or returns 1 with `SvP256Facts`, which the P-256 model turns into
`p256Verify`. -/
theorem sv_p2F {n : Machine} {B : Word} {off : Nat} {imm o pk dg : Word} {rc sc : Nat}
    (FW : Fr (B + 0xFFFFEC10) 0x3A50) (C : SvCode n.mem) (PE : P2vEnv n.mem) (RS : SvRoSep B)
    (s : St n.mem SV n off (reg n))
    (h1 : fetchRel sigstoreVerifyCode off = some (.auipc ra imm, 4))
    (h2 : fetchRel sigstoreVerifyCode (off + 4) = some (.jalr ra ra o, 4))
    (hb : SV + BitVec.ofNat 32 off + imm + o = P2V) (hev : (SV + BitVec.ofNat 32 (off + 8)).toNat % 2 = 0)
    (rsp : reg n sp = B + 0x21A0) (ha0 : reg n a0 = pk) (ha1 : reg n a1 = dg)
    (ha2 : reg n a2 = B + 0x21A0 + BitVec.ofNat 32 rc) (ha3 : reg n a3 = B + 0x21A0 + BitVec.ofNat 32 sc)
    (hrc : rc + 32 ≤ 0x4C0) (hsc : sc + 32 ≤ 0x4C0) (k_in : SvIn B pk 0x41) (dg_in : SvIn B dg 32) :
    PanicIf n ∨
    (∃ n', Steps n n' ∧ St n'.mem SV n' (off + 8) (reg n') ∧ reg n' sp = B + 0x21A0 ∧
        (∀ q : Fin 32, q.val ∈ [3, 4, 8, 9, 18, 19, 20, 21, 22, 23, 24, 25, 26, 27] → reg n' q = reg n q) ∧
        reg n' a0 = 0 ∧ SvKeepL B n.mem n'.mem [] ∧ (∀ x, SvR B x → n'.mem x = n.mem x)) ∨
    (SvP256Facts n.mem pk dg (memBytes n.mem (B + 0x21A0 + BitVec.ofNat 32 rc) 32)
        (memBytes n.mem (B + 0x21A0 + BitVec.ofNat 32 sc) 32) ∧
      ∃ n', Steps n n' ∧ St n'.mem SV n' (off + 8) (reg n') ∧ reg n' sp = B + 0x21A0 ∧
        (∀ q : Fin 32, q.val ∈ [3, 4, 8, 9, 18, 19, 20, 21, 22, 23, 24, 25, 26, 27] → reg n' q = reg n q) ∧
        reg n' a0 = 1 ∧ SvKeepL B n.mem n'.mem [] ∧ (∀ x, SvR B x → n'.mem x = n.mem x)) := by
  have F := sv_frW FW
  have FP : Fr (B + 0xFFFFEC10) 0x3590 := ⟨FW.al, FW.lo, by have := FW.hi; omega, by
    have := FW.dsep.sub (c := 0) (l := 0x3730) (by decide); rwa [add_ofNat_zero] at this⟩
  have RP : P2vRoSep (B + 0xFFFFEC10) := by
    show Sep _ _ _ _
    rw [sv_p2Base]; have := RS.sub (c := 0) (l := 0x3730) (by decide); rwa [add_ofNat_zero] at this
  obtain ⟨n1, c1, pc1, mem1, regs1⟩ := s.callRa C.self h1 h2 hb (by decide)
  have r1 := PEnv.reg1 regs1 s.zero
  have ra1 : reg n1 ra = SV + BitVec.ofNat 32 (off + 8) := by rw [regs1]; simp +decide [upd]
  have fF : ∀ e, e + 1 ≤ 0x4C0 → P2vR (B + 0xFFFFEC10) (B + 0x21A0 + BitVec.ofNat 32 e) := fun e he => by
    show Sep _ _ _ _
    rw [sv_p2Base]; exact (sv_p2Sep F he).symm
  have ret : ∀ {a : Word}, P2vRet (B + 0xFFFFEC10) (fun k => reg n1 (savedReg k)) n1 a →
      ∃ n', Steps n n' ∧ St n'.mem SV n' (off + 8) (reg n') ∧ reg n' sp = B + 0x21A0 ∧
        (∀ q : Fin 32, q.val ∈ [3, 4, 8, 9, 18, 19, 20, 21, 22, 23, 24, 25, 26, 27] → reg n' q = reg n q) ∧
        reg n' a0 = a ∧ SvKeepL B n.mem n'.mem [] ∧ (∀ x, SvR B x → n'.mem x = n.mem x) := by
    intro a e
    obtain ⟨n2, c2, pc2, sp2, sv2, g3, g4, a02, O2⟩ := e
    rw [mem1] at O2
    refine ⟨n2, c1.trans c2, ⟨by rw [pc2]; exact ra1, rfl, fun _ => rfl⟩,
      by rw [sp2, BitVec.add_assoc]; rfl, fun q hq => ?_, a02,
      fun e he _ => O2 _ (fF e he), fun x hx => O2 x (svR_p2 hx)⟩
    have hq' : q = savedReg 1 ∨ q = savedReg 2 ∨ q = savedReg 3 ∨ q = savedReg 4 ∨ q = savedReg 5 ∨
        q = savedReg 6 ∨ q = savedReg 7 ∨ q = savedReg 8 ∨ q = savedReg 9 ∨ q = savedReg 10 ∨ q = savedReg 11 ∨
        q = savedReg 12 ∨ q = 3 ∨ q = 4 := by revert hq; revert q; decide
    rcases hq' with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    all_goals first
      | (rw [g3, r1 _ (by decide)]) | (rw [g4, r1 _ (by decide)])
      | (rw [sv2 _ (by decide)]; exact r1 _ (by decide))
  rcases p256VerifyPrehash_correct_pi n1 (by rw [mem1]; exact PE) FP pc1
      (by rw [r1 sp (by decide), rsp, BitVec.add_assoc]; rfl)
      (by rw [r1 a0 (by decide), ha0]) (by rw [r1 a1 (by decide), ha1]) (by rw [r1 a2 (by decide), ha2])
      (by rw [r1 a3 (by decide), ha3]) (by rw [ra1]; exact even_clear _ hev) RP
      (sv_p2In F hrc) (sv_p2In F hsc) k_in.p2 dg_in.p2 with hp | e | ⟨hf, e⟩
  · exact .inl (PanicIf.of_steps c1 hp)
  · exact .inr (.inl (ret e))
  · rw [mem1] at hf
    exact .inr (.inr ⟨hf, ret e⟩)

def svP2c1 : List BInstr :=
  [.aluImm .add a2 sp 0x130, .aluImm .add a3 sp 0x150, .alu .add a0 x0 (24 : Fin 32), .alu .add a1 x0 (20 : Fin 32)]

theorem svP2c1_end : blockEnd sigstoreVerifyCode 0xA4C svP2c1 = some 0xA54 := by
  simp only [svP2c1]
  rw [blockEnd, sv_at_a4c]; dsimp only; rw [if_pos (by decide)]; simp only [BitVec.reduceToNat, Nat.reduceAdd]
  rw [blockEnd, sv_at_a4e]; dsimp only; rw [if_pos (by decide)]; simp only [BitVec.reduceToNat, Nat.reduceAdd]
  rw [blockEnd, sv_at_a50]; dsimp only; rw [if_pos (by decide)]; simp only [BitVec.reduceToNat, Nat.reduceAdd]
  rw [blockEnd, sv_at_a52]; dsimp only; rw [if_pos (by decide)]; simp only [BitVec.reduceToNat, Nat.reduceAdd]
  rfl

set_option maxHeartbeats 16000000 in
/-- **The image's signature check**: from 0xA4C to 0xA60. `p256_verify_prehash`
checks `r` and `s` at offsets 0x130 and 0x150 over the digest at `x20` with
the key at `x24`. -/
theorem sv_p2c {B out : Word} {v : Nat → Word} {n0 : Machine}
    (FW : Fr (B + 0xFFFFEC10) 0x3A50) (E0 : SvCode n0.mem) (V0 : SvSaves B n0.mem v) (hret : v 0 &&& ~~~1 = v 0)
    (hO : SvOut B out) (s0 : St n0.mem SV n0 0xA4C (reg n0))
    (M0 : Word → BitVec 8) (fM : ∀ x, SvR B x → n0.mem x = M0 x)
    (g0_2 : reg n0 sp = B + 0x21A0) (g0_18 : reg n0 (18 : Fin 32) = out)
    (PE0 : P2vEnv M0) (RS : SvRoSep B)
    (k_in : SvIn B (reg n0 (24 : Fin 32)) 0x41) (dg_in : SvIn B (reg n0 (20 : Fin 32)) 32) :
    SvErrRet B out v n0 ∨ PanicIf n0 ∨
    (SvP256Facts n0.mem (reg n0 (24 : Fin 32)) (reg n0 (20 : Fin 32))
        (memBytes n0.mem (B + 0x21A0 + BitVec.ofNat 32 0x130) 32)
        (memBytes n0.mem (B + 0x21A0 + BitVec.ofNat 32 0x150) 32) ∧
      ∃ n', Steps n0 n' ∧ St n'.mem SV n' 0xA60 (reg n') ∧ SvCode n'.mem ∧ SvSaves B n'.mem v ∧
        (∀ x, SvR B x → n'.mem x = M0 x) ∧ reg n' sp = B + 0x21A0 ∧
        (∀ q : Fin 32, q.val ∈ [3, 4, 8, 9, 18, 19, 20, 21, 22, 23, 24, 25, 26, 27] → reg n' q = reg n0 q) ∧
        SvKeepL B n0.mem n'.mem []) := by
  have F := sv_frW FW
  obtain ⟨n1, c1, u1⟩ := s0.block svP2c1 E0.self svP2c1_end (by
    simp +decide only [svP2c1, BlockOk, BInstr.ok, and_true])
  have m1 : n1.mem = n0.mem := u1.mem
  have s1 : St n1.mem SV n1 0xA54 (reg n1) := ⟨u1.pc, rfl, fun _ => rfl⟩
  have k1 : ∀ q : Fin 32, q.val ∈ [2, 3, 4, 8, 9, 18, 19, 20, 21, 22, 23, 24, 25, 26, 27] → reg n1 q = reg n0 q :=
    fun q hq => by rw [u1.regs, runBlock_reg _ _ _ q s0.zero (by revert hq; revert q; decide)]
  rcases sv_p2F (pk := reg n0 (24 : Fin 32)) (dg := reg n0 (20 : Fin 32)) (rc := 0x130) (sc := 0x150) FW (by rw [m1]; exact E0)
      (PE0.sv FW fun x hx => by rw [m1]; exact fM x hx) RS s1 sv_at_a54 sv_at_a58 (by decide) (by decide)
      (by rw [k1 sp (by decide), g0_2])
      (by rw [u1.regs]; simp +decide only [svP2c1, runBlock, BInstr.run, upd, ↓reduceIte]
          try (simp only [aluEval]; exact BitVec.zero_add _))
      (by rw [u1.regs]; simp +decide only [svP2c1, runBlock, BInstr.run, upd, ↓reduceIte]
          try (simp only [aluEval]; exact BitVec.zero_add _))
      (by rw [u1.regs]; simp +decide only [svP2c1, runBlock, BInstr.run, upd, ↓reduceIte]
          rw [g0_2]; rfl)
      (by rw [u1.regs]; simp +decide only [svP2c1, runBlock, BInstr.run, upd, ↓reduceIte]
          rw [g0_2]; rfl)
      (by decide) (by decide) k_in dg_in with
    hp | ⟨n2, c2, s2, sp2, k2, a2, K2, f2⟩ | ⟨hf, n2, c2, s2, sp2, k2, a2, K2, f2⟩
  · exact .inr (.inl (PanicIf.of_steps c1 hp))
  · rw [m1] at K2 f2
    have E2 : SvCode n2.mem := E0.fr F f2
    obtain ⟨n3, d3, u3⟩ := s2.taken E2.self 0xE4E sv_at_a5c (by decide)
      (by rw [a2, s2.zero]; exact br_beq_t rfl)
    have s3 : St n3.mem SV n3 0xE4E (reg n3) := ⟨u3.pc, rfl, fun _ => rfl⟩
    have m3 : n3.mem = n2.mem := u3.mem
    refine .inl (sv_fail_e4e F (by rw [m3]; exact E2) s3 (c1.trans (c2.trans (.single d3)))
      (fun x hx => by rw [m3]; exact f2 x hx) (by rw [m3]; exact V0.keepL K2 (by decide)) hret
      (by rw [u3.regs, sp2]) (by rw [u3.regs, k2 _ (by decide), k1 _ (by decide), g0_18]) hO
      (by rw [u3.regs, k2 _ (by decide), k1 _ (by decide)]) (by rw [u3.regs, k2 _ (by decide), k1 _ (by decide)]))
  · rw [m1] at hf K2 f2
    have E2 : SvCode n2.mem := E0.fr F f2
    obtain ⟨n3, d3, u3⟩ := s2.notTaken E2.self 0xA60 sv_at_a5c (by decide)
      (by rw [a2, s2.zero]; exact br_beq_f (by decide))
    have s3 : St n3.mem SV n3 0xA60 (reg n3) := ⟨u3.pc, rfl, fun _ => rfl⟩
    have m3 : n3.mem = n2.mem := u3.mem
    refine .inr (.inr ⟨hf, n3, c1.trans (c2.trans (.single d3)), s3, ?_, ?_, ?_, ?_, ?_, ?_⟩)
    · rw [m3]; exact E2
    · rw [m3]; exact V0.keepL K2 (by decide)
    · rw [m3]; exact fun x hx => (f2 x hx).trans (fM x hx)
    · rw [u3.regs, sp2]
    · exact fun q hq => by rw [u3.regs, k2 q hq, k1 q (by revert hq; revert q; decide)]
    · rw [m3]; exact K2

end C3.RV32.Sv
