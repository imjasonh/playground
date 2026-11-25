import C3BootProofs.Proofs.TufRoleKeysMetModel
import C3BootProofs.Proofs.SmallFns
import C3BootProofs.Proofs.Arr32Eq

/-!
# The key comparisons in `RoleKeys::met`

`met` compares a key with each key it already counted: P-256 keys with
`memcmp`, P-384 keys with `eq_arr97`, and Ed25519 keys with `arr32_eq`.
These lemmas turn the contracts of `eq_arr97` and `arr32_eq` into the `WP`
form of a call.
-/

namespace C3.RV32

open C3.Image C3.Json

section
variable {code : List Nat} {base : Word} {Q : Post} {M : Word → BitVec 8} {off : Nat} {f : Fin 32 → Word}

theorem tmc_regs {m1 : Machine} {ret : Word} (hreg1 : ∀ x, reg m1 x = upd f ra ret x) :
    ∀ x, x ∉ [ra, 0] → reg m1 x = f x := fun x hx => by
  have h1 : x ≠ ra := fun h => hx (by rw [h]; decide)
  have h2 : x.val ≠ 0 := fun h => hx (by rw [show x = 0 from Fin.ext h]; decide)
  rw [hreg1, upd_app, ite_eq_right h2, ite_eq_right h1]

/-- A call to `eq_arr97(p, q)`. -/
theorem WP.callEq97 {hi lo p q : Word}
    (h1 : fetchRel code off = some (.auipc ra hi, 4)) (h2 : fetchRel code (off + 4) = some (.jalr ra ra lo, 4))
    (htgt : base + BitVec.ofNat 32 off + hi + lo = BitVec.ofNat 32 eqArr97Address) (hev : (off + 8) % 2 = 0)
    (hc : CodeIn M (BitVec.ofNat 32 eqArr97Address) eqArr97Code)
    (hm : CodeIn M (BitVec.ofNat 32 eqArr97Address + 0xC04C) memcmpCode)
    (h0 : f a0 = p) (ha1 : f a1 = q) (hal : (f sp).toNat % 4 = 0)
    (hS : Sep (f sp + 0xFFFFFFF0) 16 (BitVec.ofNat 32 eqArr97Address) eqArr97Code.length)
    (hSm : Sep (f sp + 0xFFFFFFF0) 16 (BitVec.ofNat 32 eqArr97Address + 0xC04C) memcmpCode.length)
    (hP : Sep p 97 (f sp + 0xFFFFFFF0) 16) (hQ : Sep q 97 (f sp + 0xFFFFFFF0) 16)
    (hSb : Sep (f sp + 0xFFFFFFF0) 16 base code.length)
    (k : ∀ m2 : Machine, reg m2 a0 = (if memBytes M p 97 = memBytes M q 97 then 1 else 0) →
      Out M m2.mem (f sp + 0xFFFFFFF0) 16 →
      WP code base Q m2.mem (off + 8) (clob (upd f ra (base + BitVec.ofNat 32 (off + 8))) m2 jClob)) :
    WP code base Q M off f := by
  refine WP.callGen (tb := BitVec.ofNat 32 eqArr97Address) (cl := jClob)
    (P := fun m2 => reg m2 a0 = (if memBytes M p 97 = memBytes M q 97 then 1 else 0) ∧
      Out M m2.mem (f sp + 0xFFFFFFF0) 16)
    h1 h2 (by rw [htgt]; decide) (fun m1 hpc1 hmem1 hreg1 hb => ?_)
    (fun m2 hP hc => hP.2.codeIn hc hSb)
    (fun m2 hP => k m2 hP.1 hP.2)
  have hr := tmc_regs hreg1
  have hs1 : reg m1 sp = f sp := hr sp (by decide)
  obtain ⟨m2, c2, pc2, sp2, ra2, a02, rs2, mem2⟩ := eqArr97_correct m1 (by rw [hmem1]; exact hc)
    (by rw [hmem1]; exact hm) (by decide) hpc1 (by rw [hr a0 (by decide), h0]) (by rw [hr a1 (by decide), ha1])
    (by rw [hreg1]; rsimp) (even_clear _ (even_at base hb _ hev)) (by rw [hs1]; exact hal)
    (by rw [hs1]; exact hS) (by rw [hs1]; exact hSm) (by rw [hs1]; exact hP) (by rw [hs1]; exact hQ)
  rw [hmem1] at a02
  refine ⟨m2, c2, pc2, ⟨a02, fun x hx => by rw [mem2 x (by rw [hs1]; exact hx.symm), hmem1]⟩, fun x hx => ?_⟩
  exact rs2 x (fun h => hx (by rw [h]; decide)) (fun h => hx (by rw [h]; decide))
    (fun h => hx (by rw [h]; decide)) (fun h => hx (by rw [h]; decide)) (fun h => hx (by rw [h]; decide))

/-- A call to `arr32_eq(p, q)`. -/
theorem WP.callArr32 {hi lo p q : Word}
    (h1 : fetchRel code off = some (.auipc ra hi, 4)) (h2 : fetchRel code (off + 4) = some (.jalr ra ra lo, 4))
    (htgt : base + BitVec.ofNat 32 off + hi + lo = BitVec.ofNat 32 arr32EqAddress) (hev : (off + 8) % 2 = 0)
    (hc : CodeIn M (BitVec.ofNat 32 arr32EqAddress) arr32EqCode)
    (hm : CodeIn M (BitVec.ofNat 32 arr32EqAddress + 0xC032) memcmpCode)
    (h0 : f a0 = p) (ha1 : f a1 = q) (hal : (f sp).toNat % 4 = 0)
    (sSC : Sep (f sp + 0xFFFFFFFC) 4 (BitVec.ofNat 32 arr32EqAddress) arr32EqCode.length)
    (sSM : Sep (f sp + 0xFFFFFFFC) 4 (BitVec.ofNat 32 arr32EqAddress + 0xC032) memcmpCode.length)
    (sSP : Sep (f sp + 0xFFFFFFFC) 4 p 32) (sSQ : Sep (f sp + 0xFFFFFFFC) 4 q 32)
    (hSb : Sep (f sp + 0xFFFFFFFC) 4 base code.length)
    (k : ∀ m2 : Machine, reg m2 a0 = (if memBytes M p 32 = memBytes M q 32 then 1 else 0) →
      Out M m2.mem (f sp + 0xFFFFFFFC) 4 →
      WP code base Q m2.mem (off + 8) (clob (upd f ra (base + BitVec.ofNat 32 (off + 8))) m2 jClob)) :
    WP code base Q M off f := by
  refine WP.callGen (tb := BitVec.ofNat 32 arr32EqAddress) (cl := jClob)
    (P := fun m2 => reg m2 a0 = (if memBytes M p 32 = memBytes M q 32 then 1 else 0) ∧
      Out M m2.mem (f sp + 0xFFFFFFFC) 4)
    h1 h2 (by rw [htgt]; decide) (fun m1 hpc1 hmem1 hreg1 hb => ?_)
    (fun m2 hP hc => hP.2.codeIn hc hSb)
    (fun m2 hP => k m2 hP.1 hP.2)
  have hr := tmc_regs hreg1
  have hs1 : reg m1 sp = f sp := hr sp (by decide)
  obtain ⟨m2, c2, pc2, a02, rs2, mem2⟩ := arr32Eq_correct m1 (by decide) (by rw [hmem1]; exact hc)
    (by rw [hmem1]; exact hm) hpc1 (by rw [hr a0 (by decide), h0]) (by rw [hr a1 (by decide), ha1])
    (by rw [hreg1]; rsimp) (even_clear _ (even_at base hb _ hev)) (by rw [hs1]; exact hal)
    (by rw [hs1]; exact sSC) (by rw [hs1]; exact sSM) (by rw [hs1]; exact sSP) (by rw [hs1]; exact sSQ)
  rw [hmem1] at a02
  refine ⟨m2, c2, pc2, ⟨a02, fun x hx => by rw [mem2 x (by rw [hs1]; exact hx.symm), hmem1]⟩, fun x hx => ?_⟩
  exact rs2 x (fun h => hx (by rw [h]; decide)) (fun h => hx (by rw [h]; decide))
    (fun h => hx (by rw [h]; decide)) (fun h => hx (by rw [h]; decide)) (fun h => hx (by rw [h]; decide))

end

end C3.RV32
