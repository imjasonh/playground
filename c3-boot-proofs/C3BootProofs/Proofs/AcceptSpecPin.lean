import C3BootProofs.Proofs.AcceptSpecRoots

/-!
# `boot_main`'s first closure: from 0x4E4 to the return

The pinned-root stage: what holds at 0x4E4 (`AcsAt4E4`) ends the closure.
-/

namespace C3.RV32.Ac

open C3 C3.Image C3.RV32.P3 C3.RV32.BootMainContract C3.Json

/-- **At 0x4E4**: the pinned-root stage's precondition, the number of roots
at `sp + 0x34C`, the index's documents, `doc` at `s4`, `keys`'s address at
`sp + 0x30`, the bundle in `Buffers`, and what the image stage left. -/
structure AcsAt4E4 (X : AcsCtx) (mf : Manifest) (header : ImageHeader) (parts : TufParts) (n : Machine) :
    Prop where
  st : St n.mem AC n 0x4E4 (reg n)
  inv : AcInv X.B X.Bf X.g X.t X.v X.M0 n
  img : AcsImg X mf header n.mem (reg n (21 : Fin 32)) (reg n (25 : Fin 32)) (reg n (27 : Fin 32))
  tuf : decodeTufParts (flashBytes X.flash (acBase X.slot + mf.tuf.offset) mf.tuf.length) = some parts
  pre : AcPinnedPre X.B X.r n
  r20 : reg n (20 : Fin 32) = X.Bf + 0x4000
  cnt : memLoad32 n.mem (acSlot X.B 0x34C) = BitVec.ofNat 32 parts.roots.length
  cntle : parts.roots.length ≤ maxRoots
  docs : AcoDocs X.flash n.mem X.B (reg n (24 : Fin 32)) parts.roots
  tgt : ActDoc X.flash n.mem (acSlot X.B 0x244) (reg n (24 : Fin 32))
    (memLoad32 n.mem (acSlot X.B 0x34C)).toNat parts.targets
  tr : ActDoc X.flash n.mem (acSlot X.B 0x244) (reg n (24 : Fin 32))
    ((memLoad32 n.mem (acSlot X.B 0x34C)).toNat + 1) parts.trustedRoot
  keys : memLoad32 n.mem (acSlot X.B 0x30) = X.Bf + 0x6800
  bf : memLoad32 n.mem (acSlot X.B 0x34) = X.Bf
  len : memLoad32 n.mem (acSlot X.B 0x38) = BitVec.ofNat 32 mf.bundle.length
  hL : mf.bundle.length ≤ 0x4000
  bundle : memBytes n.mem X.Bf mf.bundle.length =
    flashBytes X.flash (acBase X.slot + mf.bundle.offset) mf.bundle.length

/-- The bytes the pinned-root stage doesn't write. -/
def AcsPinOut (B x : Word) : Prop :=
  Sep x 1 B 0x3A50 ∧ Sep x 1 (acSlot B 0x1C) 0x14 ∧ Sep x 1 (acSlot B 0xDD0) 0xA90 ∧ Sep x 1 (acSlot B 0x1870) 0x18

theorem acs_docKeep {flash : Nat → BitVec 8} {M M' : Word → BitVec 8} {idx start : Word} {i : Nat} {d : Bytes}
    (h : ∀ j, j < 0x10C → M' (idx + BitVec.ofNat 32 j) = M (idx + BitVec.ofNat 32 j))
    (hd : ActDoc flash M idx start i d) : ActDoc flash M' idx start i d := fun o l e =>
  hd o l (by rw [← tufIndexDocSpec_congr h]; exact e)

theorem acs_docsKeep {flash : Nat → BitVec 8} {M M' : Word → BitVec 8} {B start : Word} {docs : List Bytes}
    (h : ∀ j, j < 0x10C → M' (acSlot B 0x244 + BitVec.ofNat 32 j) = M (acSlot B 0x244 + BitVec.ofNat 32 j))
    (hd : AcoDocs flash M B start docs) : AcoDocs flash M' B start docs := fun j hj => by
  obtain ⟨o, l, e, hf⟩ := hd j hj
  exact ⟨o, l, by rw [tufIndexDocSpec_congr h]; exact e, hf⟩

/-- `RoleKeys::read`'s result as the roots stage reads it. -/
theorem acs_rk {M : Word → BitVec 8} {a : Word} {dj : Json} {role : Bytes} (h : AcpKeys M a (roleKeys dj role)) :
    AcoRk (fun o => M (a + BitVec.ofNat 32 o)) dj role := by
  unfold AcoRk
  revert h
  rcases roleKeys dj role with _ | ⟨t, es⟩
  · intro ⟨h0, h1⟩
    refine .inl ⟨?_, h1⟩
    show M (a + BitVec.ofNat 32 0) = 0xFE
    rw [add_ofNat_zero]; exact h0
  · intro h; exact .inr ⟨t, es, rfl, h⟩

/-- `tuf::expires`'s result as the roots stage reads it. -/
theorem acs_exp {M : Word → BitVec 8} {B : Word} {md : Meta} (h : AcpExp M (acSlot B 0x1310) (expires md)) :
    AcoExp B M md := by
  have e8 : acSlot B 0x1310 + 8 = acSlot B 0x1318 := acf_slot_add B 0x1310 8
  have eC : acSlot B 0x1310 + 0xC = acSlot B 0x131C := acf_slot_add B 0x1310 0xC
  have e1 : acSlot B 0x1310 + 1 = acSlot B 0x1311 := acf_slot_add B 0x1310 1
  unfold AcoExp
  revert h
  rcases expires md with _ | e
  · intro ⟨h1, h2⟩
    refine ⟨fun h0 => absurd (h1.symm.trans h0) (by decide), fun _ => ?_⟩
    rw [← e1]; exact h2
  · intro ⟨h0, w8, wC⟩
    exact ⟨fun _ => ⟨e, rfl, by rw [← e8]; exact w8, by rw [← eC]; exact wC⟩, fun h => absurd h0 h⟩

/-- The roots stage's view of the trusted root's keys: the first two bytes
in registers, as the pinned-root stage leaves them. -/
theorem acs_tb (B : Word) (M : Word → BitVec 8) :
    acoTB B M ((M (acSlot B 0x1320)).zeroExtend 32) ((M (acSlot B 0x1321)).zeroExtend 32) =
      fun o => M (acSlot B 0x1320 + BitVec.ofNat 32 o) := by
  funext o
  unfold acoTB
  have ze : ∀ b : BitVec 8, (b.zeroExtend 32).extractLsb' 0 8 = b := by decide
  by_cases h0 : o = 0
  · subst h0; simp only [↓reduceIte]; rw [add_ofNat_zero, ze]
  · by_cases h1 : o = 1
    · subst h1; simp only [Nat.one_ne_zero, ↓reduceIte]; rw [acf_slot_add, ze]
    · simp only [h0, h1, ↓reduceIte]

theorem acs_ze_lt (b : BitVec 8) : (b.zeroExtend 32).toNat < 256 := by
  rw [BitVec.toNat_setWidth]; have := b.isLt; omega

/-- The pinned root's `signed` value parses from bytes in memory. -/
theorem acs_src {d : Bytes} {r : TufRoot} {M : Word → BitVec 8} {P : Word} {L : Nat}
    (hp : parseTufRoot d = some r) (hm : memBytes M P L = d) :
    ∃ (M' : Word → BitVec 8) (P' : Word) (L' : Nat), JVal true (memBytes M' P' L') r.md.signed := by
  have hs := prModel_spec d
  rcases hpm : prModel d with e | ⟨gp, gl, q, ql, v⟩ <;> rw [hpm] at hs
  · have h : parseTufRoot d = none := hs
    rw [hp] at h; exact nomatch h
  · obtain ⟨r', sj, h1, -, hJ, -, -⟩ := hs
    rw [hp] at h1; cases h1
    have hl := hJ.1
    rw [← hm, memBytes_length] at hl
    refine ⟨M, P + BitVec.ofNat 32 gp, gl, ?_⟩
    rw [← tuf_memBytes_drop_take hl, hm]; exact hJ.2

theorem acs_pinSlot {X : AcsCtx} {k : Nat} (h1 : 0x30 ≤ k) (h2 : k < 0x350) : AcsPinOut X.B (acSlot X.B k) := by
  have s0 := sep_offsets X.B (c := 0x3A50 + k) (n := 1) (d := 0) (k := 0x3A50) (.inr (by omega)) (by omega)
    (by omega)
  rw [add_ofNat_zero] at s0
  exact ⟨s0, sep_offsets X.B (.inr (by omega)) (by omega) (by omega),
    sep_offsets X.B (.inl (by omega)) (by omega) (by omega), sep_offsets X.B (.inl (by omega)) (by omega) (by omega)⟩

theorem acs_pinLd {X : AcsCtx} {M M' : Word → BitVec 8} (h : ∀ x, AcsPinOut X.B x → M' x = M x) {k : Nat}
    (h1 : 0x30 ≤ k) (h2 : k + 4 ≤ 0x350) : memLoad32 M' (acSlot X.B k) = memLoad32 M (acSlot X.B k) :=
  memLoad32_congr fun j hj => by rw [acf_slot_add]; exact h _ (acs_pinSlot (by omega) (by omega))

theorem acs_pinIdx {X : AcsCtx} {M M' : Word → BitVec 8} (h : ∀ x, AcsPinOut X.B x → M' x = M x) :
    ∀ j, j < 0x10C → M' (acSlot X.B 0x244 + BitVec.ofNat 32 j) = M (acSlot X.B 0x244 + BitVec.ofNat 32 j) :=
  fun j hj => by rw [acf_slot_add]; exact h _ (acs_pinSlot (by omega) (by omega))

theorem acs_pinBuf {X : AcsCtx} (ok : X.Ok) {j : Nat} (hj : j < 0x4000) : AcsPinOut X.B (X.Bf + BitVec.ofNat 32 j) := by
  have hb : acBufLen = 0xB954 := rfl
  have s := ok.sB.symm.sub (c := j) (l := 1) (by omega)
  exact ⟨s.subR (c := 0) (l := 0x3A50) (by decide) |> fun h => by rwa [add_ofNat_zero] at h,
    s.subR (by decide), s.subR (by decide), s.subR (by decide)⟩

/-- **From 0x4E4**: the pinned-root stage, then the roots stage and the
rest, end the closure. -/
theorem acs_pin (hE : AcExtractStagePI) 
    {X : AcsCtx} (ok : X.Ok) {n : Machine} {mf : Manifest} {header : ImageHeader} {parts : TufParts}
    (S : AcsAt4E4 X mf header parts n) : X.End n := by
  have E := ok.envsAt S.inv
  refine acs_stage S.inv (acp_stage_pi X.pinned n X.B X.Bf X.g X.t X.r X.v X.M0 (fun M hM => (ok.envs hM).pin)
    E.ac ok.F (sep_of_le (by simp only [BitVec.toNat_ofNat]; have := ok.blo; omega)
    (by have := ok.bhi; omega)).symm S.st S.inv S.pre) (fun _ => ok.fail)
    fun n' I' hpc ⟨K, KR, h1C, h2C, h28, r22, first, hp, hver, hkr, hkt, hexp⟩ => ?_
  have kx : ∀ x, AcsPinOut X.B x → n'.mem x = n.mem x := fun x h => K x h.1 h.2.1 h.2.2.1 h.2.2.2
  have r24 : reg n' (24 : Fin 32) = reg n (24 : Fin 32) := KR 24 (by decide)
  have A : AcsImg X mf header n'.mem (reg n' (21 : Fin 32)) (reg n' (25 : Fin 32)) (reg n' (27 : Fin 32)) := by
    rw [KR 21 (by decide), KR 25 (by decide), KR 27 (by decide)]
    refine S.img.keep fun k hk => kx _ (acs_pinSlot ?_ ?_)
    · rcases hk with ⟨a, -⟩ | ⟨a, -⟩ <;> omega
    · rcases hk with ⟨-, a⟩ | ⟨-, a⟩ <;> omega
  have hst : AcoState X.B n'.mem (reg n' (22 : Fin 32)) first := by
    refine ⟨hver, by rw [h28]; exact acs_ze_lt _, by rw [r22]; exact acs_ze_lt _, ?_,
      acs_src hp E.pin.pin⟩
    rw [h28, r22, acs_tb]; exact acs_rk hkr
  refine acs_roots act_stage_pi hE ok (first := first)
    { st := ⟨hpc, rfl, fun _ => rfl⟩
      inv := I'
      img := A
      tuf := S.tuf
      pin := hp
      pre := ⟨(KR 20 (by decide)).trans S.r20, S.cntle, h1C.trans S.cnt, h2C,
        (acs_pinLd kx (by decide) (by decide)).trans S.pre.2,
        by rw [r24]; exact acs_docsKeep (acs_pinIdx kx) S.docs, hst, acs_rk hkt, acs_exp hexp⟩
      tgt := by rw [r24, h1C]; exact acs_docKeep (acs_pinIdx kx) S.tgt
      tr := by rw [r24, h1C]; exact acs_docKeep (acs_pinIdx kx) S.tr
      keys := (acs_pinLd kx (by decide) (by decide)).trans S.keys
      bf := (acs_pinLd kx (by decide) (by decide)).trans S.bf
      len := (acs_pinLd kx (by decide) (by decide)).trans S.len
      hL := S.hL
      bundle := (memBytes_congr fun j hj => kx _ (acs_pinBuf ok (by have := S.hL; omega))).trans S.bundle }

end C3.RV32.Ac
