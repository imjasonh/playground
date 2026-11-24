import C3BootProofs.Proofs.SvCongr

/-!
# `sigstore::verify`: P-256 calls

`VerifyingKey::from_sec1_bytes` on the leaf's 65-byte key, from the frame of
`sigstore::verify`.
-/

namespace C3.RV32.Sv

open C3.Image C3.RV32.P3 C3.RV32.Dq C3.RV32.Pv C3.RV32.Gs C3.RV32.P2

set_option maxRecDepth 20000

/-- `GsOk` reads only the 65 bytes at `inp`. -/
theorem gsOk_congr {M M0 : Word → BitVec 8} {inp : Word}
    (h : ∀ i, i < 0x41 → M (inp + BitVec.ofNat 32 i) = M0 (inp + BitVec.ofNat 32 i)) :
    GsOk M inp ↔ GsOk M0 inp := by
  have e0 : M inp = M0 inp := by have := h 0 (by decide); rwa [add_ofNat_zero] at this
  have e1 : gsVal M inp 1 = gsVal M0 inp 1 := by unfold gsVal; rw [mb_sub h (by decide)]
  have e2 : gsVal M inp 0x21 = gsVal M0 inp 0x21 := by unfold gsVal; rw [mb_sub h (by decide)]
  unfold GsOk; rw [e0, e1, e2]

/-- The P-256 constants are outside the stack. -/
theorem P2Data.sv {M M0 : Word → BitVec 8} {B : Word} (F : Fr B 0x3830) (D : P2Data M0)
    (fR : ∀ x, SvR B x → M x = M0 x) : P2Data M :=
  D.ofR fun i hi => fR _ (by
    have := dataR (q := (img% dataWindowAddress : Word)) (ql := (img% dataWindowSize)) F (by decide) (by decide) i hi
    exact this)

theorem sv_sp2d0 (B : Word) : B + 0x21A0 = B + BitVec.ofNat 32 0x1ED0 + 0x2D0 := by
  rw [BitVec.add_assoc]; rfl

set_option maxHeartbeats 8000000 in
/-- **A call to `VerifyingKey::from_sec1_bytes`** on the 65 bytes at `inp`,
with the result at offset `oc`. -/
theorem sv_gsF {M : Word → BitVec 8} {n : Machine} {B : Word} {off : Nat} {imm o inp : Word} {oc : Nat}
    (F : Fr B 0x3830) (C : SvCode M) (D : P2Data M) (s : St M SV n off (reg n))
    (h1 : fetchRel sigstoreVerifyCode off = some (.auipc ra imm, 4))
    (h2 : fetchRel sigstoreVerifyCode (off + 4) = some (.jalr ra ra o, 4))
    (hb : SV + BitVec.ofNat 32 off + imm + o = BitVec.ofNat 32 p256FromSec1Address)
    (hev : (SV + BitVec.ofNat 32 (off + 8)).toNat % 2 = 0)
    (rsp : reg n sp = B + 0x21A0) (ha0 : reg n a0 = B + 0x21A0 + BitVec.ofNat 32 oc) (ha1 : reg n a1 = inp)
    (ho2 : oc + 0x48 ≤ 0x1690) (ho3 : oc % 4 = 0) (hin : SvIn B inp 0x41) :
    ∃ n', Steps n n' ∧ St n'.mem SV n' (off + 8) (reg n') ∧ reg n' sp = B + 0x21A0 ∧
      (∀ q : Fin 32, q.val ∈ [3, 4, 8, 9, 18, 19, 20, 21, 22, 23, 24, 25, 26, 27] → reg n' q = reg n q) ∧
      SvKeepL B M n'.mem [(oc, 0x48)] ∧
      (GsOk M inp → memLoad32 n'.mem (B + 0x21A0 + BitVec.ofNat 32 oc) = 0) ∧
      (¬ GsOk M inp → memLoad32 n'.mem (B + 0x21A0 + BitVec.ofNat 32 oc) = 1) ∧
      (∀ x, SvR B x → n'.mem x = M x) := by
  have hFl := F.lo; have hFh := F.hi; have hFa := F.al
  obtain ⟨n1, c1, pc1, mem1, regs1⟩ := s.callRa C.self h1 h2 hb (by decide)
  have r1 := PEnv.reg1 regs1 s.zero
  have FS : Fr (B + BitVec.ofNat 32 0x1ED0) 0x2D0 := F.sub (by decide) (by decide)
  have hS : (B + (0x21A0 : Word)).toNat = B.toNat + 0x21A0 := F.at 0x21A0 (by decide)
  have eo : B + 0x21A0 + BitVec.ofNat 32 oc = B + BitVec.ofNat 32 (0x21A0 + oc) := (sv_base' B oc).symm
  have eS : B + BitVec.ofNat 32 0x1ED0 + 0xFFFFFE60 = B + BitVec.ofNat 32 0x1D30 := by
    rw [BitVec.add_assoc]; rfl
  obtain ⟨n2, c2, R, Ok, Er⟩ := p256FromSec1_correct n1 (S := B + BitVec.ofNat 32 0x1ED0) (inp := inp)
    (out := B + 0x21A0 + BitVec.ofNat 32 oc) (by rw [mem1]; exact C.gs) (by rw [mem1]; exact D) FS pc1
    (by rw [r1 sp (by decide), rsp, sv_sp2d0]) (by rw [r1 a0 (by decide), ha0]) (by rw [r1 a1 (by decide), ha1])
    (by rw [regs1]; simp +decide [upd]; exact even_clear _ hev)
    (by rw [eS]; exact hin.sepLo (by decide))
    (by have := hin.lo; omega) (sv_al F (by omega) ho3) (by rw [sv_at F _ (by omega)]; omega)
    (by rw [eS, eo]; exact sepS B (by omega) (by omega) (by omega))
  obtain ⟨pc2, sp2, sv2, k2, f2⟩ := R
  rw [mem1] at f2 Ok Er
  have hfS : ∀ x, SvR B x → Sep (B + BitVec.ofNat 32 0x1D30) 0x470 x 1 := fun x hx => by
    have := svR_lo (k := 0x470) hx (by decide) (by decide)
    rwa [sv_lo B 0x470 (by decide)] at this
  refine ⟨n2, c1.trans c2, ⟨by rw [pc2, regs1]; simp +decide [upd], rfl, fun _ => rfl⟩,
    by rw [sp2, ← sv_sp2d0], fun q hq => ?_, fun e he hL => ?_, fun h => (Ok h).1, Er,
    fun x hx => f2 x (by rw [eS]; exact hfS x hx) (svR_hi hx ho2)⟩
  · have hq' : q.val ∈ [3, 4, 26, 27] ∨ ∃ k, k < 11 ∧ savedReg k = q := by
      revert hq; revert q; decide
    rcases hq' with hq' | ⟨k, hk, rfl⟩
    · rw [k2 q hq', r1 q (by revert hq'; revert q; decide)]
    · rw [sv2 k hk, r1 _ (fun e => by rw [e] at hq; revert hq; decide)]
  · have h1 := hL _ (List.mem_singleton_self _)
    simp only at h1
    exact f2 _ (by rw [eS, ← sv_base']; exact sepS B (by omega) (by omega) (by omega))
      (by rw [eo, ← sv_base']; exact sepS B (by omega) (by omega) (by omega))

end C3.RV32.Sv
