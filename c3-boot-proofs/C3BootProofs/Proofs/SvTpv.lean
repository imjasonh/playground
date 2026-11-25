import C3BootProofs.Proofs.SvSha2
import C3BootProofs.Proofs.SvPv

/-!
# `sigstore::verify`: the TSA's signature

`verify_timestamp` checks the TSA's signature over the signed attributes
with `p384_verify_prehash`, on the TSA key's point, the SHA-256 digest at
offset 0x420, and the token's `r` and `s` at offsets 0x190 and 0x1C0.
-/

namespace C3.RV32.Sv

open C3.Image C3.RV32.P3 C3.RV32.Dq C3.RV32.Pv

set_option maxRecDepth 20000

def svTpv : List BInstr :=
  [.lw a0 sp 0x78, .lw a0 a0 0x18, .aluImm .add a4 sp 0x1C0, .aluImm .add a1 sp 0x420, .aluImm .add a2 x0 0x20,
   .alu .add a3 x0 (26 : Fin 32)]

set_option maxRecDepth 100000 in
theorem svTpv_end : blockEnd sigstoreVerifyCode 0x1416 svTpv = some 0x1426 := by decide

set_option maxRecDepth 100000 in
set_option maxHeartbeats 16000000 in
/-- **The TSA's signature check**, from 0x1416 to 0x142E: `p384_verify_prehash`
on the key the TSA entry at `q` points to, the digest at offset 0x420, and
`r` and `s` at offsets 0x190 and 0x1C0. -/
theorem sv_tpv {n : Machine} {B q pk : Word} (F : Fr B 0x2660) (E : SvCode n.mem) (PE : PvEnv7 n.mem)
    (s : St n.mem SV n 0x1416 (reg n)) (rsp : reg n sp = B + 0x21A0)
    (r26 : reg n (26 : Fin 32) = B + 0x21A0 + BitVec.ofNat 32 0x190)
    (w78 : memLoad32 n.mem (B + 0x21A0 + BitVec.ofNat 32 0x78) = q) (hpk : memLoad32 n.mem (q + 0x18) = pk)
    (al : (q + 0x18).toNat % 4 = 0) (pkIn : SvIn B pk 0x61)
    (side : PvSide n.mem pk (B + 0x21A0 + BitVec.ofNat 32 0x420) 32 (B + 0x21A0 + BitVec.ofNat 32 0x190)
      (B + 0x21A0 + BitVec.ofNat 32 0x1C0)) :
    (pvModel n.mem pk (B + 0x21A0 + BitVec.ofNat 32 0x420) 32 (B + 0x21A0 + BitVec.ofNat 32 0x190)
      (B + 0x21A0 + BitVec.ofNat 32 0x1C0) = none ∧ Panics n) ∨
    (∃ v, pvModel n.mem pk (B + 0x21A0 + BitVec.ofNat 32 0x420) 32 (B + 0x21A0 + BitVec.ofNat 32 0x190)
      (B + 0x21A0 + BitVec.ofNat 32 0x1C0) = some v ∧
      ∃ n', Steps n n' ∧ St n'.mem SV n' 0x142E (reg n') ∧ reg n' sp = B + 0x21A0 ∧
        (∀ q : Fin 32, q.val ∈ [3, 4, 8, 9, 18, 19, 20, 21, 22, 23, 24, 25, 26, 27] → reg n' q = reg n q) ∧
        reg n' a0 = v ∧ SvKeepL B n.mem n'.mem [] ∧ (∀ x, SvR B x → n'.mem x = n.mem x)) := by
  have hFh := F.hi
  obtain ⟨n1, c1, u1⟩ := s.block svTpv E.self svTpv_end (by
    simp +decide only [svTpv, BlockOk, BInstr.ok, BInstr.run, upd, ↓reduceIte, and_true]
    rw [rsp]
    refine ⟨sv_al F (c := 0x78) (by decide) (by decide), ?_⟩
    rw [show memLoad32 n.mem (B + 0x21A0 + 0x78) = q from w78]; exact al)
  have m1 : n1.mem = n.mem := u1.mem
  have s1 : St n1.mem SV n1 0x1426 (reg n1) := ⟨u1.pc, rfl, fun _ => rfl⟩
  have k1 : ∀ q : Fin 32, q.val ∈ [2, 3, 4, 8, 9, 18, 19, 20, 21, 22, 23, 24, 25, 26, 27] → reg n1 q = reg n q :=
    fun q hq => by rw [u1.regs, runBlock_reg _ _ _ q s.zero (by revert hq; revert q; decide)]
  have E1 : SvCode n1.mem := by rw [m1]; exact E
  rcases sv_pvF (pk := pk) (ph := B + 0x21A0 + BitVec.ofNat 32 0x420) (len := 32)
      (rp := B + 0x21A0 + BitVec.ofNat 32 0x190) (sp' := B + 0x21A0 + BitVec.ofNat 32 0x1C0)
      F E1 (by rw [m1]; exact PE) s1 sv_at_1426 sv_at_142a (by decide) (by decide) (by rw [k1 sp (by decide), rsp])
      (by rw [u1.regs]; simp +decide only [svTpv, runBlock, BInstr.run, upd, ↓reduceIte]; rw [rsp]
          rw [show memLoad32 n.mem (B + 0x21A0 + 0x78) = q from w78]; exact hpk)
      (by rw [u1.regs]; simp +decide only [svTpv, runBlock, BInstr.run, upd, ↓reduceIte]; rw [rsp]; rfl)
      (by rw [u1.regs]; simp +decide only [svTpv, runBlock, BInstr.run, upd, ↓reduceIte])
      (by rw [u1.regs]; simp +decide only [svTpv, runBlock, BInstr.run, upd, ↓reduceIte]; rw [r26]
          exact BitVec.zero_add _)
      (by rw [u1.regs]; simp +decide only [svTpv, runBlock, BInstr.run, upd, ↓reduceIte]; rw [rsp]; rfl)
      pkIn.pvSep (by have := pkIn.lo; omega) (sv_pvSep F (by decide)) (sv_pvSep F (by decide)) (sv_pvSep F (by decide))
      (by rw [sv_at F _ (by decide)]; omega) (by rw [m1]; exact side) with ⟨hn, hp⟩ | ⟨v, hv, n2, c2, s2, sp2, k2, a2, K2, f2⟩
  · rw [m1] at hn
    exact .inl ⟨hn, hp.of_steps c1⟩
  · rw [m1] at hv K2 f2
    exact .inr ⟨v, hv, n2, c1.trans c2, s2, sp2, fun q hq => by rw [k2 q hq, k1 q (by revert hq; revert q; decide)],
      a2, K2, f2⟩

end C3.RV32.Sv
