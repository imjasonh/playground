import C3BootProofs.Proofs.AcceptSpecIdx
import C3BootProofs.Proofs.AcceptExtractDup

/-!
# `boot_main`'s first closure: the specification

`acs_spec` composes the stages from the closure's entry to its return. The
stages from the entry to 0x2A6 are `AcsFront`; from 0x2A6 on, the index,
pinned-root, roots, `targets.json`, extract, bundle, and finish stages run in turn.
-/

namespace C3.RV32.Ac

open C3 C3.Image C3.RV32.P3 C3.RV32.Dq C3.RV32.BootMainContract

/-- **The closure's entry**, for `X`: the closure's code in memory `X.M0`,
the stack pointer at the frame's top, the arguments in `a0` to `a3`, and
`gp`, `tp`, and the registers the closure saves at `X.g`, `X.t`, and
`X.v`. -/
structure AcsEntry (X : AcsCtx) (m : Machine) : Prop where
  st : St X.M0 AC m 0 (reg m)
  code : CodeIn X.M0 AC bootMainClosure0Code
  sp : reg m sp = X.B + 0x5A70
  a0 : reg m a0 = X.r
  a1 : reg m a1 = X.level
  a2 : reg m a2 = X.Bf
  a3 : reg m a3 = X.slot
  g : reg m (3 : Fin 32) = X.g
  t : reg m (4 : Fin 32) = X.t
  v : ∀ k, k < 13 → reg m (savedReg k) = X.v k

/-- **The stages from the entry to 0x2A6**: the prologue, the read and
image stages. From the entry, the closure ends as `X.End` says, or reaches
0x2A6 where `AcsAt2A6` holds. -/
def AcsFront : Prop :=
  ∀ (X : AcsCtx), X.Ok → ∀ m, AcsEntry X m →
    (∀ n mf header, AcsAt2A6 X mf header n → X.End n) → X.End m

/-- **The closure's specification**: from its entry, the closure panics, or
returns with `AcsRes`: memory kept outside its stack, `Buffers`, and the
result, and a result that is `None` or a `Some` for the slot that
`bmcAccept` accepts. -/
theorem acs_spec (hF : AcsFront) (hNK : AcsTargetsNoKeys) (hC : AceCaStage) (hT : AceTlogStage)
    (hS : AceTsaStage) (hB : AcsBundleStage) (hFx : AcsFinishBad) {X : AcsCtx} (ok : X.Ok) {m : Machine} (e : AcsEntry X m) : X.End m :=
  hF X ok m e fun _ _ _ S => acs_index hNK (ac_extract_loops hC hT hS ace_dup) hB hFx ok S

/-! ## The contract -/

/-- What the closure needs of memory at the call: `AcsEnvs` in every memory
that agrees with it outside RAM. -/
def AcsE (romBase : Word) (romCode : List Nat) (pinned : Bytes) (policy : Policy) (M : Word → BitVec 8) :
    Prop :=
  ∀ M', (∀ x, AcsOutRam x → M' x = M x) → AcsEnvs romBase romCode pinned policy M'

/-- **Completeness**: when the closure returns `None`, `bmcAccept` rejects
the slot. -/
def AcsComplete : Prop :=
  ∀ (X : AcsCtx), X.Ok → ∀ m, AcsEntry X m → ∀ n, Steps m n → n.pc = X.v 0 → reg n sp = X.B + 0x5A70 →
    n.mem (X.r + 0xC) = 0xFF → bmcAccept X.flash X.pinned X.policy X.level.toNat X.slot = none

theorem acs_keep {m n : Machine} (hsp : reg n sp = reg m sp)
    (sv : ∀ k, k < 13 → reg n (savedReg k) = reg m (savedReg k))
    (r3 : reg n (3 : Fin 32) = reg m (3 : Fin 32)) (r4 : reg n (4 : Fin 32) = reg m (4 : Fin 32)) :
    ∀ q, romKeep q = true → reg n q = reg m q := by
  intro q hq
  simp only [romKeep, decide_eq_true_eq, List.mem_cons, List.not_mem_nil, or_false] at hq
  obtain ⟨q, hq'⟩ := q
  rcases hq with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · rfl
  · exact hsp
  · exact r3
  · exact r4
  · exact sv 1 (by decide)
  · exact sv 2 (by decide)
  · exact sv 3 (by decide)
  · exact sv 4 (by decide)
  · exact sv 5 (by decide)
  · exact sv 6 (by decide)
  · exact sv 7 (by decide)
  · exact sv 8 (by decide)
  · exact sv 9 (by decide)
  · exact sv 10 (by decide)
  · exact sv 11 (by decide)
  · exact sv 12 (by decide)

/-- **The closure meets `Closure0Contract`** with a stack of 0x5C10 bytes:
the frame's 0x5A70 and the 0x1A0 below it that `sigstore::verify` writes. -/
theorem acs_contract (hF : AcsFront) (hNK : AcsTargetsNoKeys) (hC : AceCaStage) (hT : AceTlogStage)
    (hS : AceTsaStage) (hB : AcsBundleStage) (hFx : AcsFinishBad) (hCo : AcsComplete)
    {flash : Nat → BitVec 8} {R romStack : Nat} {romBase : Word} {romCode : List Nat} {pinned : Bytes}
    {policy : Policy} (log : RomFn romBase romCode 0x40000040 romStack fun _ => True) (hrs : romStack ≤ 0x3A50)
    (hR : R ≤ 0x3A50 - 0x180) (hR4 : R % 4 = 0) (rb : 0x40000000 ≤ romBase.toNat)
    (rl : romBase.toNat + romCode.length ≤ 2 ^ 32) :
    Closure0Contract flash R romBase romCode pinned policy 0x5C10 (AcsE romBase romCode pinned policy) := by
  intro rom m res bufs slot level C hE hpc _ h0 h1 h2 h3 hsl A sRB sRS sBS
  have := A.splo; have := A.sphi; have := A.spa; have := A.bufsp; have := A.bufhi
  have hB0 : (reg m sp - BitVec.ofNat 32 0x5A70).toNat = (reg m sp).toNat - 0x5A70 := by
    rw [BitVec.toNat_sub, BitVec.toNat_ofNat]; omega
  have hW : reg m sp - BitVec.ofNat 32 0x5C10 = reg m sp - BitVec.ofNat 32 0x5A70 + 0xFFFFFE60 := by
    apply BitVec.eq_of_toNat_eq
    rw [BitVec.toNat_add, hB0, BitVec.toNat_sub, BitVec.toNat_ofNat]; simp only [BitVec.reduceToNat]; omega
  have hS0 : (reg m sp - BitVec.ofNat 32 0x5C10).toNat = (reg m sp).toNat - 0x5C10 := by
    rw [BitVec.toNat_sub, BitVec.toNat_ofNat]; omega
  let X : AcsCtx := ⟨flash, R, romStack, romBase, romCode, pinned, policy, reg m sp - BitVec.ofNat 32 0x5A70,
    bufs, reg m (3 : Fin 32), reg m (4 : Fin 32), res, slot, level, fun k => reg m (savedReg k), m.mem⟩
  have ok : X.Ok :=
    { rom, log, hrs, hR, hR4, rb, rl
      F := ⟨by show (reg m sp - _).toNat % 16 = 0; rw [hB0]; omega,
        by show _ ≤ (reg m sp - _).toNat; rw [hB0]; omega, by show (reg m sp - _).toNat + _ ≤ _; rw [hB0]; omega,
        by
          show Sep (reg m sp - _ + 0xFFFFFE60) _ _ _
          rw [← hW]; exact (sep_of_le (by simp only [BitVec.reduceToNat]; rw [hS0]; omega)
            (by rw [hS0]; omega)).symm⟩
      blo := by show _ ≤ (reg m sp - _).toNat; rw [hB0]; omega
      bfa := A.bufa
      bflo := by show _ ≤ bufs.toNat; omega
      bfhi := A.bufhi
      sBf := by
        show Sep (reg m sp - _ + 0xFFFFFE60) 0x5C10 bufs (0xB954 + 14)
        rw [← hW]; exact sep_of_le (by rw [hS0]; omega) (by omega)
      ra := A.resa
      rlo := A.reslo
      rhi := A.reshi
      rS := by show Sep res 0x12C (reg m sp - _ + 0xFFFFFE60) _; rw [← hW]; exact sRS
      rB := sRB
      sl := hsl
      lev := A.lev
      ret := A.ra
      env := hE }
  have hTop : reg m sp - BitVec.ofNat 32 0x5A70 + 0x5A70 = reg m sp := BitVec.sub_add_cancel _ _
  have e : AcsEntry X m :=
    ⟨⟨by rw [hpc, add_ofNat_zero], rfl, fun _ => rfl⟩, C, hTop.symm, h0, h1, h2, h3, rfl, rfl, fun _ _ => rfl⟩
  rcases acs_spec hF hNK hC hT hS hB hFx ok e with hp | ⟨n', st, pc, sp', sv, r3, r4, hm, hres⟩
  · exact .inr hp
  refine .inl ⟨n', st, pc.trans A.ra.symm, acs_keep (sp'.trans hTop) sv r3 r4, fun x hs hr hb => ?_, ?_⟩
  · rw [hW] at hs
    exact hm x hs.symm hb.symm hr.symm
  · cases hk : bmcAccept flash pinned policy level.toNat slot with
    | none =>
      rcases hres with h | ⟨_, _, _, h, -⟩
      · exact h
      · exact nomatch hk.symm.trans h
    | some a =>
      obtain ⟨mf, sv, tm⟩ := a
      rcases hres with h | ⟨mf', sv', tm', h, h12, h128, h120, hacc⟩
      · exact nomatch (hCo X ok m e n' st pc sp' h).symm.trans hk
      · rw [hk] at h
        cases h
        exact ⟨h12, h128, h120, hacc⟩

end C3.RV32.Ac
