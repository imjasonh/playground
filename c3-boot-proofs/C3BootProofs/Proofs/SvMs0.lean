import C3BootProofs.Proofs.SvEc

/-!
# `sigstore::verify`: `memset` with the zeros it writes

The P-256 check clears the inversions' `d` and other buffers with `memset`,
and the stages after it need the zeros.
-/

namespace C3.RV32.Sv

open C3.Image C3.RV32.P3 C3.RV32.Dq C3.RV32.Pv

/-- **A call to `memset`** that clears `N` bytes at offset `c`, with the
zeros it writes. -/
theorem sv_ms3F {n : Machine} {B : Word} {off : Nat} {imm o : Word} {c N : Nat}
    (F : Fr B 0x3830) (C : SvCode n.mem) (s : St n.mem SV n off (reg n))
    (h1 : fetchRel sigstoreVerifyCode off = some (.auipc ra imm, 4))
    (h2 : fetchRel sigstoreVerifyCode (off + 4) = some (.jalr ra ra o, 4))
    (hb : SV + BitVec.ofNat 32 off + imm + o = MSET) (hev : (SV + BitVec.ofNat 32 (off + 8)).toNat % 2 = 0)
    (ha0 : reg n a0 = B + 0x21A0 + BitVec.ofNat 32 c) (ha1 : reg n a1 = 0) (ha2 : reg n a2 = BitVec.ofNat 32 N)
    (hc : c + N ≤ 0x1690) :
    ∃ n', Steps n n' ∧ St n'.mem SV n' (off + 8) (reg n') ∧
      (∀ q : Fin 32, q.val ∈ [2, 3, 4, 8, 9, 18, 19, 20, 21, 22, 23, 24, 25, 26, 27] → reg n' q = reg n q) ∧
      SvKeepL B n.mem n'.mem [(c, N)] ∧ (∀ x, SvR B x → n'.mem x = n.mem x) ∧
      ∀ j, j < N → n'.mem (B + 0x21A0 + BitVec.ofNat 32 (c + j)) = 0 := by
  obtain ⟨n', st, s', mem', regs'⟩ := sv_msF F C s h1 h2 hb hev ha0 ha1 ha2 hc
  refine ⟨n', st, s', fun q hq => regs' q (by revert hq; revert q; decide) (by revert hq; revert q; decide)
    (by revert hq; revert q; decide) (by revert hq; revert q; decide) (by revert hq; revert q; decide)
    (by revert hq; revert q; decide) (by revert hq; revert q; decide), fun e he hL => ?_,
    fun x hx => by rw [mem']; exact fillBytes_sep (svR_hi hx hc) (Nat.le_refl N), fun j hj => ?_⟩
  · have h1 := hL _ (List.mem_singleton_self _)
    simp only at h1
    rw [mem']
    exact fillBytes_sep (sepS (B + 0x21A0) (by omega) (by omega) (by omega)) (Nat.le_refl N)
  · rw [mem']
    unfold fillBytes
    rw [ite_eq_left (by
      rw [← add_ofNat_assoc, BitVec.add_comm (B + 0x21A0 + BitVec.ofNat 32 c), BitVec.add_sub_cancel,
        BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega)]
      exact hj)]
    rfl

theorem acc0_of_fill {M : Word → BitVec 8} {S : Word} {c : Nat}
    (h : ∀ j, j < 32 → M (S + BitVec.ofNat 32 (c + j)) = 0) : accV M (S + BitVec.ofNat 32 c) 8 = 0 := by
  rw [accV_S (M := fun _ => 0) (d := c) 8 fun q hq => h q (by omega)]
  exact (accV_zero_iff 8).2 fun _ _ => by unfold memLoad32; dsimp only; rfl

end C3.RV32.Sv
