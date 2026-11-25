import C3BootProofs.Proofs.AcceptSpecIdx

/-!
# `boot_main`'s first closure: from 0x1AA to 0x2A6

`acs_image` runs the image stage from 0x1AA and hands its end to
`acs_index` at 0x2A6.
-/

namespace C3.RV32.Ac

open C3 C3.Image C3.RV32.P3

/-- At 0x1AA: the image stage's precondition, the manifest, the TUF
metadata's flash address and length in `s8` and `s1`, and what the frame
holds for the stages after it. -/
structure AcsAt1AA (X : AcsCtx) (mf : Manifest) (n : Machine) : Prop where
  st : St n.mem AC n 0x1AA (reg n)
  inv : AcInv X.B X.Bf X.g X.t X.v X.M0 n
  pre : AcImagePre X.flash X.B X.Bf X.r X.slot X.level mf n
  man : decodeManifest (flashBytes X.flash (acBase X.slot) 32) = some mf
  r24 : (reg n (24 : Fin 32)).toNat = acBase X.slot + mf.tuf.offset
  r9 : (reg n (9 : Fin 32)).toNat = mf.tuf.length
  r20 : reg n (20 : Fin 32) = X.Bf + 0x4000
  bf : memLoad32 n.mem (acSlot X.B 0x34) = X.Bf
  len : memLoad32 n.mem (acSlot X.B 0x38) = BitVec.ofNat 32 mf.bundle.length
  hL : mf.bundle.length ≤ 0x4000
  bundle : memBytes n.mem X.Bf mf.bundle.length =
    flashBytes X.flash (acBase X.slot + mf.bundle.offset) mf.bundle.length
  addr : memLoad32 n.mem (acSlot X.B 0x44) = BitVec.ofNat 32 (acBase X.slot + mf.image.offset)
  digest : memBytes n.mem (acSlot X.B 0xD4) 32 =
    sha256 (flashBytes X.flash (acBase X.slot + mf.image.offset) mf.image.length)

set_option maxRecDepth 100000 in
theorem acs_lev {l : Word} (h : l.toNat < 256) : (l &&& 0xFF).toNat = l.toNat := by
  rw [BitVec.toNat_and]
  show l.toNat &&& 255 = l.toNat
  have k : ∀ y, y < 256 → y &&& 255 = y := by decide
  exact k _ h

/-- **From 0x1AA**: the image stage, then the index stage and the rest, end
the closure. -/
theorem acs_image (hE : AcExtractStage) 
    {X : AcsCtx} (ok : X.Ok) {n : Machine} {mf : Manifest} (S : AcsAt1AA X mf n) : X.End n := by
  have E := ok.envsAt S.inv
  refine acs_stage S.inv (acImage_stage X.flash n X.B X.Bf X.g X.t X.r X.slot X.level X.v X.M0 mf
    (fun M hM => (ok.envs hM).img) E.ac ok.F ok.sB ok.bfhi' S.st S.inv S.pre) (fun _ => ok.fail)
    fun n' I' hpc P => ?_
  obtain ⟨⟨header, hd, hlev, h27, sv, entry, cnt, segs, hh, hout, hcnt, hpos, hkind⟩, -, h20, h21, h23, h24,
    h25, -, -, -, -, -, -, -, -, -, hdig, h139, h238, hkeep⟩ := P
  have Kf : ∀ k, k + 1 ≤ 0xF4 → n'.mem (acSlot X.B k) = n.mem (acSlot X.B k) := fun k hk => by
    have h0 := sep_offsets X.B (c := 0) (n := 0x3A50) (d := 0x3A50 + k) (k := 1) (.inl (by omega)) (by decide)
      (by omega)
    rw [add_ofNat_zero] at h0
    exact hkeep _ h0 (sep_offsets X.B (.inr (by omega)) (by decide) (by omega))
      (sep_offsets X.B (.inr (by omega)) (by decide) (by omega))
  have Ko : ∀ x, Sep x 1 X.B 0x5A70 → n'.mem x = n.mem x := fun x h => by
    have h0 := h.symm.sub (c := 0) (l := 0x3A50) (by decide)
    rw [add_ofNat_zero] at h0
    exact hkeep x h0 (h.symm.sub (by decide)) (h.symm.sub (by decide))
  have ld : ∀ k, k + 4 ≤ 0xF4 → memLoad32 n'.mem (acSlot X.B k) = memLoad32 n.mem (acSlot X.B k) :=
    fun k hk => memLoad32_congr fun j hj => by rw [acf_slot_add]; exact Kf (k + j) (by omega)
  refine acs_index hE ok (header := header)
    { st := ⟨hpc, rfl, fun _ => rfl⟩
      inv := I'
      img := {
        man := S.man
        dec := hd
        lev := by rw [← acs_lev ok.lev]; exact hlev
        r27 := h27
        out := ⟨n'.mem, sv, entry, cnt, segs, hh, hout, hcnt, hpos, hkind, h21, h25, h238, fun i hi => by
          have := acs_mb_pt h139 hi
          rwa [acf_slot_add, acf_slot_add] at this⟩
        addr := (ld 0x44 (by decide)).trans S.addr
        digest := hdig.trans S.digest }
      r24 := by rw [h24]; exact S.r24
      r23 := by rw [h23]; exact S.r9
      r20 := h20.trans S.r20
      res := (ld 0x40 (by decide)).trans S.pre.1
      bf := (ld 0x34 (by decide)).trans S.bf
      len := (ld 0x38 (by decide)).trans S.len
      hL := S.hL
      bundle := by
        rw [← S.bundle]
        exact aci_mb fun i hi => Ko _ (ok.sB.symm.sub (c := i) (l := 1) (by have := S.hL; have : acBufLen = 0xB954 := rfl; omega)) }

end C3.RV32.Ac
