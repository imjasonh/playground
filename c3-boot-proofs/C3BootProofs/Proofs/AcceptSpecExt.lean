import C3BootProofs.Proofs.AcceptSpecBun

/-!
# `boot_main`'s first closure: from 0xC12 to the return

The extract stage: what holds at 0xC12 (`AcsAtC12`) ends the closure.
-/

namespace C3.RV32.Ac

open C3 C3.Image C3.RV32.P3 C3.RV32.BootMainContract

/-- **At 0xC12**: the trusted root's document, the earlier of the times at
`sp + 0x20` and `sp + 0x28` no later than the expiry that `verifyTuf` gives,
the bundle in `Buffers`, and what the image stage left. -/
structure AcsAtC12 (X : AcsCtx) (mf : Manifest) (header : ImageHeader) (parts : TufParts) (ver ex : Nat)
    (D : Word) (n : Machine) : Prop where
  st : St n.mem AC n 0xC12 (reg n)
  inv : AcInv X.B X.Bf X.g X.t X.v X.M0 n
  img : AcsImg X mf header n.mem (reg n (21 : Fin 32)) (reg n (25 : Fin 32)) (reg n (27 : Fin 32))
  tuf : decodeTufParts (flashBytes X.flash (acBase X.slot + mf.tuf.offset) mf.tuf.length) = some parts
  ver : verifyTuf X.pinned parts = some (ver, ex)
  pre : AcExtractPre X.B X.Bf X.r D parts.trustedRoot n
  exp : min (aceU64 n.mem (acSlot X.B 0x20)) (aceU64 n.mem (acSlot X.B 0x28)) ≤ ex
  bf : memLoad32 n.mem (acSlot X.B 0x34) = X.Bf
  len : memLoad32 n.mem (acSlot X.B 0x38) = BitVec.ofNat 32 mf.bundle.length
  hL : mf.bundle.length ≤ 0x4000
  bundle : memBytes n.mem X.Bf mf.bundle.length =
    flashBytes X.flash (acBase X.slot + mf.bundle.offset) mf.bundle.length

theorem acs_u64_of {M : Word → BitVec 8} {a : Word} {x : Nat} (h : aceU64 M a = x) : Sv.SvU64At M a x := by
  unfold aceU64 at h
  have h0 := (memLoad32 M a).isLt
  have h1 := (memLoad32 M (a + 4)).isLt
  refine ⟨by omega, ?_, ?_⟩ <;> apply BitVec.eq_of_toNat_eq <;> rw [BitVec.toNat_ofNat] <;> omega

theorem acs_bufLow {X : AcsCtx} (ok : X.Ok) {j : Nat} (hj : j < 0x4000) :
    AceKept X.B X.Bf (X.Bf + BitVec.ofNat 32 j) := by
  have hb : acBufLen = 0xB954 := rfl
  have := ok.bfhi
  have e1 : (X.Bf + BitVec.ofNat 32 j).toNat = X.Bf.toNat + j := by
    rw [BitVec.toNat_add, BitVec.toNat_ofNat]; omega
  have e2 : (X.Bf + 0x6800).toNat = X.Bf.toNat + 0x6800 := by
    rw [BitVec.toNat_add]; simp only [BitVec.reduceToNat]; omega
  exact .inl ⟨ok.sB.symm.sub (by omega), sep_of_le (by rw [e1, e2]; omega) (by rw [e2]; omega)⟩

theorem acs_slotKept {B Bf : Word} {k : Nat} (h1 : 0x34 ≤ k) (h2 : k + 4 ≤ 0x48) {M M' : Word → BitVec 8}
    (h : ∀ x, AceKept B Bf x → M' x = M x) : memLoad32 M' (acSlot B k) = memLoad32 M (acSlot B k) :=
  memLoad32_congr fun j hj => by rw [acf_slot_add]; exact h _ (.inr ⟨_, .inl ⟨by omega, by omega⟩, rfl⟩)

/-- **From 0xC12**: the closure panics or returns with `AcsRes`. -/
theorem acs_ext (hE : AcExtractStage) {X : AcsCtx} (ok : X.Ok)
    {n : Machine} {mf : Manifest} {header : ImageHeader} {parts : TufParts} {ver ex : Nat} {D : Word}
    (S : AcsAtC12 X mf header parts ver ex D n) : X.End n := by
  have E := ok.envsAt S.inv
  refine acs_stage S.inv (hE n X.B X.Bf X.g X.t X.r D X.v X.M0 parts.trustedRoot (fun M hM => (ok.envs hM).ext)
    ok.layout E.ac S.st S.inv S.pre) (fun _ => ok.fail)
    fun n' I' hpc ⟨fp, fs, ls, ts, hx, hk, hpol, hfr, hkeep, hexp, h0, h1, h2, hra⟩ => ?_
  have A : AcsImg X mf header n'.mem (reg n' (21 : Fin 32)) (reg n' (25 : Fin 32)) (reg n' (27 : Fin 32)) := by
    rw [hkeep.regs 21 (by decide), hkeep.regs 25 (by decide), hkeep.regs 27 (by decide)]
    refine S.img.keep fun k hk => hkeep.mem _ (.inr ⟨k, ?_, rfl⟩)
    rcases hk with ⟨a, b⟩ | h
    · exact .inl ⟨by omega, b⟩
    · exact .inr h
  exact acs_bun ok
    { st := ⟨hpc, rfl, fun _ => rfl⟩
      inv := I'
      img := A
      tuf := S.tuf
      ver := S.ver
      root := hx X.policy
      keys := ⟨fp, hfr.hi, hk⟩
      pol := hpol
      exp := ⟨_, Nat.le_trans (Nat.le_of_eq hexp) S.exp, acs_u64_of rfl⟩
      bf := (acs_slotKept (by decide) (by decide) hkeep.mem).trans S.bf
      len := (acs_slotKept (by decide) (by decide) hkeep.mem).trans S.len
      hL := S.hL
      bundle := (memBytes_congr fun j hj => hkeep.mem _ (acs_bufLow ok (by have := S.hL; omega))).trans S.bundle
      res := (acs_slotKept (by decide) (by decide) hkeep.mem).trans S.pre.res
      a0 := h0
      a1 := h1
      a2 := h2
      ra := hra.trans (add_ofNat_assoc AC 0x1812 0x15000).symm }

end C3.RV32.Ac
