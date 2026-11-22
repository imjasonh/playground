import C3BootProofs.Proofs.SvTop

/-!
# `sigstore::verify` from its entry: the memory after the prologue

`sv_pro` runs from the entry to 0x72 and leaves the frame as `svProMem`.
These lemmas give what `sv_verify_72` needs of that memory: outside the
stack it is the entry's, it holds the saved registers, and it holds the
`Der` reader over the leaf certificate at offset 0x2E0.
-/

namespace C3.RV32.Sv

open C3.Image C3.RV32.P3 C3.RV32.Dq C3.RV32.Pv

theorem svProMem_out {M : Word → BitVec 8} {B lp ll : Word} {n : Machine} {x : Word} (hx : SvR B x) :
    svProMem M B n lp ll x = M x := by
  have hs : ∀ c, 0x1A0 + c + 4 ≤ 0x39D0 → Sep (B + BitVec.ofNat 32 c) 4 x 1 := fun c h => by
    have := hx.sub (c := 0x1A0 + c) (l := 4) h
    rwa [show B + 0xFFFFFE60 + BitVec.ofNat 32 (0x1A0 + c) = B + BitVec.ofNat 32 c by
      rw [BitVec.add_assoc]; congr 1; apply BitVec.eq_of_toNat_eq; simp; omega] at this
  have ho : Sep (B + BitVec.ofNat 32 0x37FC) 0x34 x 1 := by
    have := hx.sub (c := 0x1A0 + 0x37FC) (l := 0x34) (by decide)
    rwa [show B + 0xFFFFFE60 + BitVec.ofNat 32 (0x1A0 + 0x37FC) = B + BitVec.ofNat 32 0x37FC by
      rw [BitVec.add_assoc]; rfl] at this
  unfold svProMem
  rw [memStore32_get_sep (hs 0x248C (by decide)), memStore32_get_sep (hs 0x2488 (by decide)),
    memStore32_get_sep (hs 0x2484 (by decide)), memStore32_get_sep (hs 0x2480 (by decide)), svSaves_out ho]

theorem svProMem_saves {M : Word → BitVec 8} {B lp ll : Word} {n : Machine} :
    SvSaves B (svProMem M B n lp ll) (fun k => reg n (savedReg k)) := fun k hk => by
  have hd : (0x382C - 4 * k) % 4 = 0 := by omega
  have hd' : 0x382C - 4 * k + 4 ≤ 0x10000 := by omega
  unfold svProMem
  rw [ld_st_sv (by decide) hd (by decide) hd', ite_eq_right (by omega), ld_st_sv (by decide) hd (by decide) hd',
    ite_eq_right (by omega), ld_st_sv (by decide) hd (by decide) hd', ite_eq_right (by omega),
    ld_st_sv (by decide) hd (by decide) hd', ite_eq_right (by omega)]
  exact svSaves_read k hk

theorem svProMem_reader {M : Word → BitVec 8} {B lp ll : Word} {n : Machine} :
    memLoad32 (svProMem M B n lp ll) (B + 0x21A0 + BitVec.ofNat 32 0x2E0) = lp ∧
    memLoad32 (svProMem M B n lp ll) (B + 0x21A0 + BitVec.ofNat 32 0x2E4) = ll ∧
    memLoad32 (svProMem M B n lp ll) (B + 0x21A0 + BitVec.ofNat 32 0x2E8) = lp ∧
    memLoad32 (svProMem M B n lp ll) (B + 0x21A0 + BitVec.ofNat 32 0x2EC) = ll := by
  have e : ∀ c, B + 0x21A0 + BitVec.ofNat 32 c = B + BitVec.ofNat 32 (0x21A0 + c) := fun c => add_ofNat_assoc B 0x21A0 c
  unfold svProMem
  refine ⟨?_, ?_, ?_, ?_⟩ <;> rw [e] <;>
    simp (disch := decide) only [ld_st_sv, ite_eq_right, ↓reduceIte] <;> rfl

theorem SvOkRet.pre {B out tlo thi ilo ihi : Word} {v : Nat → Word} {n0 n1 : Machine} (h : Steps n0 n1)
    (h3 : reg n1 (3 : Fin 32) = reg n0 (3 : Fin 32)) (h4 : reg n1 (4 : Fin 32) = reg n0 (4 : Fin 32))
    (hm : ∀ x, SvR B x → n1.mem x = n0.mem x) (e : SvOkRet B out v n1 tlo thi ilo ihi) :
    SvOkRet B out v n0 tlo thi ilo ihi := by
  obtain ⟨n', s, pc, sp', sv, r3, r4, o, a, b, c, d, m⟩ := e
  exact ⟨n', h.trans s, pc, sp', sv, r3.trans h3, r4.trans h4, o, a, b, c, d,
    fun x hx hs => (m x hx hs).trans (hm x hx)⟩

end C3.RV32.Sv
