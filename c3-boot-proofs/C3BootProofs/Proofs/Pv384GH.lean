import C3BootProofs.Proofs.Pv384H
import C3BootProofs.Proofs.Pv384G2

/-!
# `p384_verify_prehash`: from the tables to the result

Stage G, the main loop of the linear combination, composed with stages H
and I: from 0xA76 to the epilogue at 0x130, or a panic in the loop.
-/

namespace C3.RV32.Pv

open C3.Image C3.RV32.P3 C3.RV32.Dq

set_option maxRecDepth 20000

/-- The sum the main loop leaves, from the identity over `L` positions, or
`none` when a bounds check panics. -/
def mlRun (T0 T1 : Nat → Pt) (D0 D1 : List Nat) (L : Nat) : Option Pt :=
  if L = 0 then some idPt else (mlLoop T0 T1 D0 D1 L (idPt, false)).map Prod.fst

set_option maxHeartbeats 16000000 in
/-- **Stages G to I**, from 0xA76 to 0x130. -/
theorem pv_stGH {B : Word} {T0 T1 : Nat → Pt} {D0 D1 : List Nat} {RM L0 L1 : Nat} {m : Machine}
    (F : Fr B 0x21A0) (E : PvEnv7 m.mem) (s : St m.mem PV m 0xA76 (reg m)) (hsp : reg m sp = B + 0x420)
    (w0 : memLoad32 m.mem (B + 0x420 + BitVec.ofNat 32 0x1924) = BitVec.ofNat 32 L0)
    (w1 : memLoad32 m.mem (B + 0x420 + BitVec.ofNat 32 0x1AAC) = BitVec.ofNat 32 L1)
    (hL0 : L0 ≤ 0x181) (hL1 : L1 ≤ 0x181) (M : GM B m.mem T0 T1 D0 D1 RM)
    (hINV : ∀ P, mlRun T0 T1 D0 D1 (max L0 L1) = some P → hvOk P.2.2 → hvInv (hvLoop 15 (hvInit P.2.2)) < p384) :
    (mlRun T0 T1 D0 D1 (max L0 L1) = none ∧ Panics m) ∨
    (∃ P, mlRun T0 T1 D0 D1 (max L0 L1) = some P ∧
      ∃ m', Steps m m' ∧ St m'.mem PV m' 0x130 (reg m') ∧ PvEnv7 m'.mem ∧ (∀ x, PvR B x → m'.mem x = m.mem x) ∧
        reg m' sp = B + 0x420 ∧ reg m' (3 : Fin 32) = reg m (3 : Fin 32) ∧
        reg m' (4 : Fin 32) = reg m (4 : Fin 32) ∧ reg m' a0 = pvH RM P.1 P.2.2) := by
  obtain ⟨m1, c1, E1, fr1, s1, G1, sp1, r31, r41, r211, M1, A1⟩ := ml_pre F E.E s hsp w0 w1 hL0 hL1 M
  have fin : ∀ {m2 : Machine} {P : Pt}, mlRun T0 T1 D0 D1 (max L0 L1) = some P → Steps m m2 → PvEnv6 m2.mem →
      (∀ x, PvR B x → m2.mem x = m.mem x) → St m2.mem PV m2 0xBEE (reg m2) → reg m2 sp = B + 0x420 →
      reg m2 (3 : Fin 32) = reg m (3 : Fin 32) → reg m2 (4 : Fin 32) = reg m (4 : Fin 32) →
      GM B m2.mem T0 T1 D0 D1 RM → ptV m2.mem B 0xE10 = P →
      ∃ m', Steps m m' ∧ St m'.mem PV m' 0x130 (reg m') ∧ PvEnv7 m'.mem ∧ (∀ x, PvR B x → m'.mem x = m.mem x) ∧
        reg m' sp = B + 0x420 ∧ reg m' (3 : Fin 32) = reg m (3 : Fin 32) ∧
        reg m' (4 : Fin 32) = reg m (4 : Fin 32) ∧ reg m' a0 = pvH RM P.1 P.2.2 :=
    fun {m2 P} hP c2 _ fr2 s2 sp2 r32 r42 M2 A2 => by
      obtain ⟨n3, c3, s3, E3, fr3, sp3, r33, r43, a3⟩ :=
        pv_stH F (E.fr F fr2) s2 sp2 M2.rm (congrArg Prod.fst A2) (congrArg (fun x => x.2.1) A2)
          (congrArg (fun x => x.2.2) A2) (hINV P hP)
      exact ⟨n3, c2.trans c3, s3, E3, fun x hx => by rw [fr3 x hx, fr2 x hx], sp3, by rw [r33, r32],
        by rw [r43, r42], a3⟩
  by_cases hm : max L0 L1 = 0
  · rw [ite_eq_left hm] at s1
    have hP : mlRun T0 T1 D0 D1 (max L0 L1) = some idPt := by rw [mlRun, ite_eq_left hm]
    exact .inr ⟨idPt, hP, fin hP c1 E1 fr1 s1 sp1 r31 r41 M1 A1⟩
  · rw [ite_eq_right hm] at s1
    have hk : max L0 L1 - 1 + 1 = max L0 L1 := Nat.sub_add_cancel (by omega)
    rcases ml_loop F (max L0 L1 - 1) (st := (idPt, false)) E1 s1 (G1 hm) (by rw [r211]; rfl) M1 A1 idPt_lt
        (by omega) with ⟨hn, hp⟩ | ⟨st', h2, m2, c2, E2, fr2, s2, sp2, r32, r42, M2, A2, -⟩
    · rw [hk] at hn
      left
      exact ⟨by rw [mlRun, ite_eq_right hm, hn]; rfl, Panics.of_steps c1 hp⟩
    · rw [hk] at h2
      have hP : mlRun T0 T1 D0 D1 (max L0 L1) = some st'.1 := by rw [mlRun, ite_eq_right hm, h2]; rfl
      exact .inr ⟨st'.1, hP, fin hP (c1.trans c2) E2 (fun x hx => by rw [fr2 x hx, fr1 x hx]) s2 sp2
        r32 r42 M2 A2⟩

end C3.RV32.Pv
