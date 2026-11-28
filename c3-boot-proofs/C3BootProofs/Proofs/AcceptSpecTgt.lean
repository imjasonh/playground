import C3BootProofs.Proofs.AcceptSpecExt
import C3BootProofs.Proofs.AcceptSpecTime

/-!
# `boot_main`'s first closure: from 0x836 to the return

The `targets.json` stage: what holds at 0x836 (`AcsAt836`) ends the closure.
-/

namespace C3.RV32.Ac

open C3 C3.Image C3.RV32.P3 C3.RV32.BootMainContract

/-- **At 0x836**: the targets stage's precondition, `keys`'s address at
`sp + 0x30`, the bundle in `Buffers`, and what the image stage left. -/
structure AcsAt836 (X : AcsCtx) (mf : Manifest) (header : ImageHeader) (parts : TufParts) (root : TufRoot)
    (re : Nat) (n : Machine) : Prop where
  st : St n.mem AC n 0x836 (reg n)
  inv : AcInv X.B X.Bf X.g X.t X.v X.M0 n
  img : AcsImg X mf header n.mem (reg n (21 : Fin 32)) (reg n (25 : Fin 32)) (reg n (27 : Fin 32))
  tuf : decodeTufParts (flashBytes X.flash (acBase X.slot + mf.tuf.offset) mf.tuf.length) = some parts
  pre : AcTargetsPre X.flash X.pinned parts root re X.B X.Bf X.r n
  keys : memLoad32 n.mem (acSlot X.B 0x30) = X.Bf + 0x6800
  bf : memLoad32 n.mem (acSlot X.B 0x34) = X.Bf
  len : memLoad32 n.mem (acSlot X.B 0x38) = BitVec.ofNat 32 mf.bundle.length
  hL : mf.bundle.length ≤ 0x4000
  bundle : memBytes n.mem X.Bf mf.bundle.length =
    flashBytes X.flash (acBase X.slot + mf.bundle.offset) mf.bundle.length

section
variable {X : AcsCtx} (ok : X.Ok)
include ok

/-- The targets stage doesn't write the frame from `sp + 0x30` to
`sp + 0x244`. -/
theorem acs_tgtSlot {k : Nat} (h1 : 0x30 ≤ k) (h2 : k < 0x244) : ActOut X.B X.Bf (acSlot X.B k) := by
  refine ⟨?_, sep_offsets X.B (.inr (by omega)) (by omega) (by omega),
    sep_offsets X.B (.inr (by omega)) (by omega) (by omega), sep_offsets X.B (.inl (by omega)) (by omega) (by omega),
    sep_offsets X.B (.inl (by omega)) (by omega) (by omega), (ok.sB.sub (by omega)).subR (by decide)⟩
  have := sep_offsets X.B (c := 0x3A50 + k) (n := 1) (d := 0) (k := 0x3A50) (.inr (by omega)) (by omega) (by omega)
  rwa [add_ofNat_zero] at this

/-- The targets stage doesn't write `Buffers` below `doc`. -/
theorem acs_tgtBuf {j : Nat} (hj : j < 0x4000) : ActOut X.B X.Bf (X.Bf + BitVec.ofNat 32 j) := by
  have hb : acBufLen = 0xB954 := rfl
  have := ok.bfhi
  have e1 : (X.Bf + BitVec.ofNat 32 j).toNat = X.Bf.toNat + j := by
    rw [BitVec.toNat_add, BitVec.toNat_ofNat]; omega
  have e2 : (X.Bf + 0x4000).toNat = X.Bf.toNat + 0x4000 := by
    rw [BitVec.toNat_add]; simp only [BitVec.reduceToNat]; omega
  have s := ok.inBf (y := X.Bf + BitVec.ofNat 32 j) (by rw [e1]; omega) (by rw [e1]; omega)
  refine ⟨?_, s.subR (by decide), s.subR (by decide), s.subR (by decide), s.subR (by decide),
    sep_of_le (by rw [e1, e2]; omega) (by rw [e2]; omega)⟩
  have := s.subR (c := 0) (l := 0x3A50) (by decide)
  rwa [add_ofNat_zero] at this

theorem acs_tgtLd {M M' : Word → BitVec 8} (h : ∀ x, ActOut X.B X.Bf x → M' x = M x) {k : Nat} (h1 : 0x30 ≤ k)
    (h2 : k + 4 ≤ 0x244) : memLoad32 M' (acSlot X.B k) = memLoad32 M (acSlot X.B k) :=
  memLoad32_congr fun j hj => by rw [acf_slot_add]; exact h _ (acs_tgtSlot ok (by omega) (by omega))

end

theorem acs_aceU64_le {M : Word → BitVec 8} {a : Word} {x : Nat} (h0 : memLoad32 M a = BitVec.ofNat 32 x)
    (h1 : memLoad32 M (a + 4) = BitVec.ofNat 32 (x / 2 ^ 32)) : aceU64 M a ≤ x := by
  unfold aceU64; rw [h0, h1]; simp only [BitVec.toNat_ofNat]; omega

/-- **From 0x836**: the closure panics or returns with `AcsRes`. -/
theorem acs_tgt (hT : AcTargetsStagePI) (hE : AcExtractStagePI) 
    {X : AcsCtx} (ok : X.Ok) {n : Machine} {mf : Manifest} {header : ImageHeader} {parts : TufParts}
    {root : TufRoot} {re : Nat} (S : AcsAt836 X mf header parts root re n) : X.End n := by
  have E := ok.envsAt S.inv
  refine acs_stage S.inv (hT X.flash X.R X.romBase X.romCode ok.rom n X.B X.Bf X.g X.t X.r X.v X.M0 X.pinned parts
    root re (fun M hM => (ok.envs hM).tgt) E.ac ok.F ok.sB ok.layout.ro ok.sRomB ok.sRomBf ok.bfa ok.bfhi' ok.hR4
    ok.hR S.st S.inv S.pre) (fun _ => ok.fail)
    fun n' I' hpc ⟨⟨te, hv, w20, w24⟩, w28, w2C, r18, r24, hdoc, r19, r22, r21, r25, r27, keep⟩ => ?_
  have A : AcsImg X mf header n'.mem (reg n' (21 : Fin 32)) (reg n' (25 : Fin 32)) (reg n' (27 : Fin 32)) := by
    rw [r21, r25, r27]
    refine S.img.keep fun k hk => keep _ (acs_tgtSlot ok ?_ ?_)
    · rcases hk with ⟨a, -⟩ | ⟨a, -⟩ <;> omega
    · rcases hk with ⟨-, a⟩ | ⟨-, a⟩ <;> omega
  have hm : maxDocLen = 0x2800 := rfl
  have hpl := acs_parts_le S.tuf
  have e2 : (X.Bf + 0x4000).toNat = X.Bf.toNat + 0x4000 := by
    have := ok.bfhi; rw [BitVec.toNat_add]; simp only [BitVec.reduceToNat]; omega
  have l20 : aceU64 n'.mem (acSlot X.B 0x20) ≤ te :=
    acs_aceU64_le w20 (by rw [show acSlot X.B 0x20 + 4 = acSlot X.B 0x24 from acf_slot_add X.B 0x20 4]; exact w24)
  have l28 : aceU64 n'.mem (acSlot X.B 0x28) ≤ re :=
    acs_aceU64_le w28 (by rw [show acSlot X.B 0x28 + 4 = acSlot X.B 0x2C from acf_slot_add X.B 0x28 4]; exact w2C)
  exact acs_ext hE ok (D := X.Bf + 0x4000) (ver := root.version)
    { st := ⟨hpc, rfl, fun _ => rfl⟩
      inv := I'
      img := A
      tuf := S.tuf
      ver := hv
      pre := ⟨by rw [e2]; exact Nat.le_refl _, by rw [e2]; omega, hdoc, r18, r19, r22, r24,
        (acs_tgtLd ok keep (by decide) (by decide)).trans S.keys,
        (acs_tgtLd ok keep (by decide) (by decide)).trans S.pre.2.2.2.2.2.2.2.2⟩
      exp := Nat.le_min.mpr ⟨Nat.le_trans (Nat.min_le_right _ _) l28, Nat.le_trans (Nat.min_le_left _ _) l20⟩
      bf := (acs_tgtLd ok keep (by decide) (by decide)).trans S.bf
      len := (acs_tgtLd ok keep (by decide) (by decide)).trans S.len
      hL := S.hL
      bundle := (memBytes_congr fun j hj => keep _ (acs_tgtBuf ok (by have := S.hL; omega))).trans S.bundle }

end C3.RV32.Ac
