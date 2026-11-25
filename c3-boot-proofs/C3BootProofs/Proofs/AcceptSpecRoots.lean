import C3BootProofs.Proofs.AcceptSpecTgt

/-!
# `boot_main`'s first closure: from 0x584 to the return

The roots stage: what holds at 0x584 (`AcsAt584`) ends the closure.
-/

namespace C3.RV32.Ac

open C3 C3.Image C3.RV32.P3 C3.RV32.BootMainContract C3.Json

/-- **At 0x836 with no `targets` keys**: the last root's `targets` role gave
an error code, at `sp + 0xDD0`. The targets stage then returns that error. -/
def AcsTargetsNoKeys : Prop :=
  ∀ (X : AcsCtx), X.Ok → ∀ (n : Machine) (parts : TufParts) (root : TufRoot) (re : Nat),
    St n.mem AC n 0x836 (reg n) → AcInv X.B X.Bf X.g X.t X.v X.M0 n →
    actRoot X.pinned parts = some root → expires root.md = some re →
    n.mem (acSlot X.B 0xDD0) = 0xFE → (n.mem (acSlot X.B 0xDD0 + 1)).toNat < 0x27 →
    ActDoc X.flash n.mem (acSlot X.B 0x244) (reg n (24 : Fin 32))
      (memLoad32 n.mem (acSlot X.B 0x1C)).toNat parts.targets →
    ActDoc X.flash n.mem (acSlot X.B 0x244) (reg n (24 : Fin 32))
      ((memLoad32 n.mem (acSlot X.B 0x1C)).toNat + 1) parts.trustedRoot →
    reg n (20 : Fin 32) = X.Bf + 0x4000 → memLoad32 n.mem (acSlot X.B 0x40) = X.r → X.End n

/-- **At 0x584**: the roots stage's precondition for the TUF part's roots
and the pinned root, the index's `targets.json` and `trusted_root.json`,
`keys`'s address at `sp + 0x30`, the bundle in `Buffers`, and what the
image stage left. -/
structure AcsAt584 (X : AcsCtx) (mf : Manifest) (header : ImageHeader) (parts : TufParts) (first : TufRoot)
    (n : Machine) : Prop where
  st : St n.mem AC n 0x584 (reg n)
  inv : AcInv X.B X.Bf X.g X.t X.v X.M0 n
  img : AcsImg X mf header n.mem (reg n (21 : Fin 32)) (reg n (25 : Fin 32)) (reg n (27 : Fin 32))
  tuf : decodeTufParts (flashBytes X.flash (acBase X.slot + mf.tuf.offset) mf.tuf.length) = some parts
  pin : parseTufRoot X.pinned = some first
  pre : AcRootsPre X.flash X.B X.Bf X.r parts.roots first n
  tgt : ActDoc X.flash n.mem (acSlot X.B 0x244) (reg n (24 : Fin 32))
    (memLoad32 n.mem (acSlot X.B 0x1C)).toNat parts.targets
  tr : ActDoc X.flash n.mem (acSlot X.B 0x244) (reg n (24 : Fin 32))
    ((memLoad32 n.mem (acSlot X.B 0x1C)).toNat + 1) parts.trustedRoot
  keys : memLoad32 n.mem (acSlot X.B 0x30) = X.Bf + 0x6800
  bf : memLoad32 n.mem (acSlot X.B 0x34) = X.Bf
  len : memLoad32 n.mem (acSlot X.B 0x38) = BitVec.ofNat 32 mf.bundle.length
  hL : mf.bundle.length ≤ 0x4000
  bundle : memBytes n.mem X.Bf mf.bundle.length =
    flashBytes X.flash (acBase X.slot + mf.bundle.offset) mf.bundle.length

theorem acs_ofNat_mod (e : Nat) : BitVec.ofNat 32 (e % 2 ^ 32) = BitVec.ofNat 32 e :=
  BitVec.eq_of_toNat_eq (by simp only [BitVec.toNat_ofNat, Nat.mod_mod])

theorem acs_code_sep {G c : Word} {n l : Nat} (hG : G.toNat + n ≤ 0x40000000) (hc : 0x40000000 ≤ c.toNat)
    (hl : c.toNat + l ≤ 2 ^ 32) : Sep G n c l :=
  sep_of_le (by omega) hl

section
variable {X : AcsCtx} (ok : X.Ok)
include ok

/-- The roots stage doesn't write the frame slots at `sp + 0x1C` and from
`sp + 0x30` to `sp + 0x350`. -/
theorem acs_rootsSlot {k : Nat} (h : 0x1C ≤ k ∧ k < 0x20 ∨ 0x30 ≤ k ∧ k < 0x350) :
    AcoFix X.B X.Bf (acSlot X.B k) := by
  have hk : k < 0x350 := by rcases h with ⟨-, h⟩ | ⟨-, h⟩ <;> omega
  have s0 := sep_offsets X.B (c := 0x3A50 + k) (n := 1) (d := 0) (k := 0x3A50) (.inr (by omega)) (by omega)
    (by omega)
  rw [add_ofNat_zero] at s0
  refine ⟨s0, ?_, sep_offsets X.B (.inl (by omega)) (by omega) (by omega),
    (ok.sB.sub (by omega)).subR (by decide)⟩
  rcases h with ⟨-, h⟩ | ⟨h, -⟩
  · exact sep_offsets X.B (.inl (by omega)) (by omega) (by omega)
  · exact sep_offsets X.B (.inr (by omega)) (by omega) (by omega)

/-- The roots stage doesn't write `Buffers` below `doc`. -/
theorem acs_rootsBuf {j : Nat} (hj : j < 0x4000) : AcoFix X.B X.Bf (X.Bf + BitVec.ofNat 32 j) := by
  have A := acs_tgtBuf ok hj
  have hb : acBufLen = 0xB954 := rfl
  exact ⟨A.1, A.2.2.1, (ok.sB.symm.sub (c := j) (l := 1) (by omega)).subR (c := 0x3A50 + 0x350) (l := 0x1B98)
    (by decide), A.2.2.2.2.2⟩

theorem acs_rootsLd {M M' : Word → BitVec 8} (h : ∀ x, AcoFix X.B X.Bf x → M' x = M x) {k : Nat}
    (hk : k = 0x1C ∨ 0x30 ≤ k ∧ k + 4 ≤ 0x350) : memLoad32 M' (acSlot X.B k) = memLoad32 M (acSlot X.B k) :=
  memLoad32_congr fun j hj => by
    rw [acf_slot_add]
    exact h _ (acs_rootsSlot ok (hk.elim (fun e => .inl ⟨by omega, by omega⟩) fun e => .inr ⟨by omega, by omega⟩))

theorem acs_rootsDoc {M M' : Word → BitVec 8} (h : ∀ x, AcoFix X.B X.Bf x → M' x = M x) {start : Word} {i : Nat}
    {d : Bytes} (hd : ActDoc X.flash M (acSlot X.B 0x244) start i d) :
    ActDoc X.flash M' (acSlot X.B 0x244) start i d := fun o l e =>
  hd o l (by
    rw [← tufIndexDocSpec_congr (M := M) (M' := M') (fun j hj => by
      rw [acf_slot_add]; exact h _ (acs_rootsSlot ok (.inr ⟨by omega, by omega⟩)))]
    exact e)

set_option maxRecDepth 100000 in
/-- The roots stage's code and data, from the closure's. -/
theorem acs_rootsEnv {M : Word → BitVec 8} (E : AcsEnvs X.romBase X.romCode X.pinned X.policy M) :
    AcRootsEnv X.R X.romBase X.romCode X.B X.Bf M := by
  have hb : acBufLen = 0xB954 := rfl
  have bhi := ok.bhi
  have bfhi := ok.bfhi
  have blo := ok.blo
  have hR := ok.hR
  have hR4 := ok.hR4
  have hBa : X.B.toNat % 16 = 0 := ok.F.al
  have hGl : (X.B + BitVec.ofNat 32 (0x38D0 - X.R)).toNat = X.B.toNat + (0x38D0 - X.R) := by
    rw [BitVec.toNat_add, BitVec.toNat_ofNat]; omega
  have hbf : (X.Bf + 0x4000).toNat = X.Bf.toNat + 0x4000 := by
    rw [BitVec.toNat_add]; simp only [BitVec.reduceToNat]; omega
  have hP : TRD + 0x16DA4 + 0xFFFFFEA8 = (img% flashReadAddress : Word) := by decide
  have sOG : Sep (X.Bf + 0x4000) 0x2800 (X.B + BitVec.ofNat 32 (0x38D0 - X.R)) (0x150 + X.R) :=
    (ok.sB.symm.sub (c := 0x4000) (l := 0x2800) (by omega)).subR (by omega)
  refine ⟨E.ac, E.rtRd, E.rtIx, E.rtFp, ?_, E.rtPr, E.rtRm, E.rtTex, E.idx.mcs, E.idx.mcb, E.rtRoot, E.rtTgts,
    ok.layout.ro, ok.sRomB⟩
  rw [hP]
  exact ⟨rfl, E.tgt.fr, E.tgt.frM, E.tgt.frW, by rw [hGl]; omega, hR4, by rw [hGl]; omega,
    by rw [hbf]; simp only [BitVec.reduceToNat]; omega,
    acs_code_sep (by rw [hGl]; omega) (by decide) (by decide),
    acs_code_sep (by rw [hGl]; omega) (by decide) (by decide),
    acs_code_sep (by rw [hGl]; omega) (by decide) (by decide),
    acs_code_sep (by rw [hbf]; simp only [BitVec.reduceToNat]; omega) (by decide) (by decide),
    acs_code_sep (by rw [hbf]; simp only [BitVec.reduceToNat]; omega) (by decide) (by decide),
    sOG, E.idx.rom,
    acs_code_sep (by rw [hGl]; omega) ok.rb ok.rl,
    acs_code_sep (by rw [hbf]; simp only [BitVec.reduceToNat]; omega) ok.rb ok.rl⟩

end

/-- **From 0x584**: the roots stage, then the targets stage and the rest,
end the closure. -/
theorem acs_roots (hG : AcRootsGap) (hNK : AcsTargetsNoKeys) (hT : AcTargetsStage) (hE : AcExtractStage)
    (hB : AcsBundleStage) (hFx : AcsFinishBad) {X : AcsCtx} (ok : X.Ok) {n : Machine} {mf : Manifest}
    {header : ImageHeader} {parts : TufParts} {first : TufRoot} (S : AcsAt584 X mf header parts first n) :
    X.End n := by
  refine acs_stage S.inv (acRootsStage hG X.flash X.R X.romBase X.romCode ok.rom n X.B X.Bf X.g X.t X.r X.v X.M0
    parts.roots first (fun M hM => acs_rootsEnv ok (ok.envs hM)) ok.F ok.sB ok.bfa ok.bfhi'
    (by have := ok.hR; omega) S.st S.inv S.pre) (fun _ => ok.fail)
    fun n' I' hpc ⟨root, hfold, K, KR, _, _, hrt, _, e, hexp, w18, w1C⟩ => ?_
  have kx : ∀ x, AcoFix X.B X.Bf x → n'.mem x = n.mem x := K
  have hact : actRoot X.pinned parts = some root := by
    unfold actRoot; rw [S.pin]; exact hfold
  have r24 : reg n' (24 : Fin 32) = reg n (24 : Fin 32) := KR 24 (by decide)
  have l1C := acs_rootsLd ok kx (k := 0x1C) (.inl rfl)
  have tgt : ActDoc X.flash n'.mem (acSlot X.B 0x244) (reg n' (24 : Fin 32))
      (memLoad32 n'.mem (acSlot X.B 0x1C)).toNat parts.targets := by
    rw [r24, l1C]; exact acs_rootsDoc ok kx S.tgt
  have tr : ActDoc X.flash n'.mem (acSlot X.B 0x244) (reg n' (24 : Fin 32))
      ((memLoad32 n'.mem (acSlot X.B 0x1C)).toNat + 1) parts.trustedRoot := by
    rw [r24, l1C]; exact acs_rootsDoc ok kx S.tr
  have r20 : reg n' (20 : Fin 32) = X.Bf + 0x4000 := (KR 20 (by decide)).trans S.pre.1
  have r40 : memLoad32 n'.mem (acSlot X.B 0x40) = X.r :=
    (acs_rootsLd ok kx (.inr ⟨by decide, by decide⟩)).trans S.pre.2.2.2.2.1
  have st : St n'.mem AC n' 0x836 (reg n') := ⟨hpc, rfl, fun _ => rfl⟩
  rcases hrt with ⟨h0, h1⟩ | ⟨t, es, hrk, hRB⟩
  · refine hNK X ok n' parts root e st I' hact hexp ?_ ?_ tgt tr r20 r40
    · have := h0; simp only [add_ofNat_zero] at this; exact this
    · exact h1
  · have A : AcsImg X mf header n'.mem (reg n' (21 : Fin 32)) (reg n' (25 : Fin 32)) (reg n' (27 : Fin 32)) := by
      rw [KR 21 (by decide), KR 25 (by decide), KR 27 (by decide)]
      refine S.img.keep fun k hk => kx _ (acs_rootsSlot ok (.inr ?_))
      rcases hk with ⟨a, b⟩ | ⟨a, b⟩ <;> exact ⟨by omega, by omega⟩
    exact acs_tgt hT hE hB hFx ok (root := root) (re := e)
      { st := st
        inv := I'
        img := A
        tuf := S.tuf
        pre := ⟨hact, hexp, w18.trans (acs_ofNat_mod e), w1C, ⟨t, es, hrk, hRB, aco_rkwf hrk⟩, tgt, tr, r20, r40⟩
        keys := (acs_rootsLd ok kx (.inr ⟨by decide, by decide⟩)).trans S.keys
        bf := (acs_rootsLd ok kx (.inr ⟨by decide, by decide⟩)).trans S.bf
        len := (acs_rootsLd ok kx (.inr ⟨by decide, by decide⟩)).trans S.len
        hL := S.hL
        bundle := (memBytes_congr fun j hj => kx _ (acs_rootsBuf ok (by have := S.hL; omega))).trans S.bundle }

end C3.RV32.Ac
