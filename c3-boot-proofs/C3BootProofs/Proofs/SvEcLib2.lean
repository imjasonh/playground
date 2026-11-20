import C3BootProofs.Proofs.SvIvLib
import C3BootProofs.Proofs.P256Scalar

/-!
# `sigstore::verify`: the P-256 check's scalar products

The wrapper for the P-256 scalar field's `mul`, which computes `u₁` and `u₂`
from the inverse of `s`, called from `sigstore::verify`'s frame.
-/

namespace C3.RV32.Sv

open C3.Image C3.RV32.P3 C3.RV32.Dq C3.RV32.Pv

set_option maxRecDepth 100000

/-- The value of `n` limbs whose `j`th is `f j`. -/
def limbSum (f : Nat → Nat) : Nat → Nat
  | 0 => 0
  | n + 1 => limbSum f n + f n * 2 ^ (32 * n)

theorem accV_of_toNats {M : Word → BitVec 8} {p : Word} {f : Nat → Nat} :
    ∀ n, (∀ j, j < n → (memLoad32 M (p + BitVec.ofNat 32 (4 * j))).toNat = f j) → accV M p n = limbSum f n
  | 0, _ => rfl
  | n + 1, h => by
    simp only [accV, limbSum]
    rw [accV_of_toNats n fun j hj => h j (by omega), h n (by omega)]

/-- What `<Scalar as Mul>::mul` leaves for the product `X` of its operands. -/
abbrev psmVal (X : Nat) : Nat := limbSum (psmOut (psmProd X)) 8

set_option maxHeartbeats 8000000 in
/-- **A call to the P-256 scalar field's `mul`** of the scalars at offsets
`ca` and `cb`, into offset `co`. -/
theorem sv_psmF {M : Word → BitVec 8} {n : Machine} {B : Word} {off : Nat} {imm o : Word} {co ca cb : Nat}
    (F : Fr B 0x3830) (C : SvCode M) (hpm : CodeIn M (BitVec.ofNat 32 p256ScalarMulAddress) p256ScalarMulCode)
    (hwm : CodeIn M (BitVec.ofNat 32 wideMulAddress) wideMulCode) (st : St M SV n off (reg n))
    (h1 : fetchRel sigstoreVerifyCode off = some (.auipc ra imm, 4))
    (h2 : fetchRel sigstoreVerifyCode (off + 4) = some (.jalr ra ra o, 4))
    (hb : SV + BitVec.ofNat 32 off + imm + o = BitVec.ofNat 32 p256ScalarMulAddress)
    (hev : (SV + BitVec.ofNat 32 (off + 8)).toNat % 2 = 0) (rsp : reg n sp = B + 0x21A0)
    (ha0 : reg n a0 = B + 0x21A0 + BitVec.ofNat 32 co) (ha1 : reg n a1 = B + 0x21A0 + BitVec.ofNat 32 ca)
    (ha2 : reg n a2 = B + 0x21A0 + BitVec.ofNat 32 cb)
    (hco : co + 32 ≤ 0x1690) (hca : ca + 32 ≤ 0x1690) (hcb : cb + 32 ≤ 0x1690)
    (aco : co % 4 = 0) (aca : ca % 4 = 0) (acb : cb % 4 = 0) :
    ∃ n', Steps n n' ∧ St n'.mem SV n' (off + 8) (reg n') ∧ reg n' sp = B + 0x21A0 ∧
      (∀ q : Fin 32, q.val ∈ [3, 4, 8, 9, 18, 19, 20, 21, 22, 23, 24, 25, 26, 27] → reg n' q = reg n q) ∧
      accV n'.mem (B + 0x21A0 + BitVec.ofNat 32 co) 8 =
        psmVal (accV M (B + 0x21A0 + BitVec.ofNat 32 ca) 8 * accV M (B + 0x21A0 + BitVec.ofNat 32 cb) 8) ∧
      SvKeepL B M n'.mem [(co, 32)] ∧ (∀ x, SvR B x → n'.mem x = M x) := by
  have hFl := F.lo; have hFh := F.hi; have hFa := F.al
  obtain ⟨n1, c1, pc1, mem1, regs1⟩ := st.callRa C.self h1 h2 hb (by decide)
  have r1 := PEnv.reg1 regs1 st.zero
  have hS : (B + (0x21A0 : Word)).toNat = B.toNat + 0x21A0 := F.at 0x21A0 (by decide)
  have FS : Fr (B + 0x21A0) 0x1690 := F.sub (c := 0x21A0) (by decide) (by decide)
  have hGn : (B + 0x21A0 + BitVec.ofNat 32 (2 ^ 32 - 0x100)).toNat = (B + 0x21A0).toNat - 0x100 :=
    FS.below 0x100 (by decide) (by decide)
  have EN : PSMEnv n1.mem (BitVec.ofNat 32 p256ScalarMulAddress) (B + 0x21A0 + 0xFFFFFF00)
      (B + 0x21A0 + BitVec.ofNat 32 co) (B + 0x21A0 + BitVec.ofNat 32 ca) (B + 0x21A0 + BitVec.ofNat 32 cb) := by
    rw [mem1]
    refine ⟨by decide, hpm, ?_, ?_, ?_, ?_, ?_,
      by rw [show (0xFFFFFF00 : Word) = BitVec.ofNat 32 (2 ^ 32 - 0x100) from rfl, hGn, hS]; omega,
      by rw [show (0xFFFFFF00 : Word) = BitVec.ofNat 32 (2 ^ 32 - 0x100) from rfl, hGn, hS]; omega,
      sv_al F (by omega) aco, sv_al F (by omega) aca, sv_al F (by omega) acb,
      FS.lowHi (by decide) rfl (by decide) (by decide), FS.lowHi (by decide) rfl (by decide) (by decide),
      FS.lowHi (by decide) rfl (by decide) (by decide), FS.lowHi (by decide) rfl (by decide) (by decide),
      FS.lowHi (by decide) rfl (by decide) (by decide), FS.lowHi (by decide) rfl (by decide) (by decide),
      FS.lowN (k := 0x100) (by decide) (by decide) hca, FS.lowN (k := 0x100) (by decide) (by decide) hcb,
      FS.lowN (k := 0x100) (by decide) (by decide) hco,
      FS.sepHi hco (by decide) (by decide), FS.sepHi hco (by decide) (by decide)⟩
    · rw [show BitVec.ofNat 32 p256ScalarMulAddress + 0xFFFFB24E = BitVec.ofNat 32 wideMulAddress by decide]; exact hwm
    · rw [show BitVec.ofNat 32 p256ScalarMulAddress + 0xFFFFB24E + 0x7446 = MSET by decide]; exact C.K.mset
    · rw [show BitVec.ofNat 32 p256ScalarMulAddress + 0xFFFFB24E + 0x74AE = MCS by decide]; exact C.K.stub
    · rw [show BitVec.ofNat 32 p256ScalarMulAddress + 0xFFFFB24E + 0x74B6 = MCS + 8 by decide]; exact C.K.body
    · rw [show psmBsub (BitVec.ofNat 32 p256ScalarMulAddress) = BSUB by decide]; exact C.K.bsub
  obtain ⟨n2, c2, pc2, sp2, k2, W2, f2⟩ := p256ScalarMul_correct n1 EN pc1
    (by rw [r1 a0 (by decide), ha0]) (by rw [r1 a1 (by decide), ha1]) (by rw [r1 a2 (by decide), ha2])
    (by rw [regs1]; simp +decide [upd]) (even_clear _ hev)
    (by rw [r1 sp (by decide), rsp, BitVec.add_assoc, show (0xFFFFFF00 : Word) + 0x100 = 0 from rfl]
        exact (BitVec.add_zero _).symm)
  rw [mem1] at W2 f2
  have e1 : B + 0x21A0 + 0xFFFFFF00 = B + BitVec.ofNat 32 0x20A0 := sv_spX B 0x100 (by decide)
  rw [e1] at f2
  refine ⟨n2, c1.trans c2, ⟨by rw [pc2], rfl, fun _ => rfl⟩,
    by rw [sp2, BitVec.add_assoc, show (0xFFFFFF00 : Word) + 0x100 = 0 from rfl]; exact BitVec.add_zero _,
    fun q hq => by rw [k2 q (by revert hq; revert q; decide), r1 q (by revert hq; revert q; decide)],
    accV_of_toNats 8 W2, fun e he hL => ?_,
    fun x hx => f2 x (svR_spX hx (by decide) (by decide) (by decide)) (svR_hi hx hco)⟩
  have h1 := hL _ (List.mem_singleton_self _)
  simp only at h1
  exact f2 _ (by rw [← sv_base']; exact sepS B (by omega) (by omega) (by omega))
    (sepS (B + 0x21A0) (by omega) (by omega) (by omega))

/-- Limbs inside a run of frame bytes copied from `p`. -/
theorem acc_of_frame_at {M M0 : Word → BitVec 8} {B p : Word} {c d n N : Nat}
    (h : ∀ j, j < N → M (B + 0x21A0 + BitVec.ofNat 32 (c + j)) = M0 (p + BitVec.ofNat 32 j)) (hd : d + 4 * n ≤ N) :
    accV M (B + 0x21A0 + BitVec.ofNat 32 (c + d)) n = accV M0 (p + BitVec.ofNat 32 d) n :=
  acc_of_bytes fun j hj => by
    rw [add_ofNat_assoc, add_ofNat_assoc, show c + d + j = c + (d + j) by omega]; exact h _ (by omega)

end C3.RV32.Sv
