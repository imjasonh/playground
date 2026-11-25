import C3BootProofs.Proofs.AcceptTargetsRd

/-!
# Reading `trusted_root.json`

From 0xB10: `tuf::read_doc` reads document `i + 1`, `trusted_root.json`,
into `doc`, with the result at `sp + 0x1870`. Then `act_hex` runs.
-/

namespace C3.RV32.Ac

open C3.Image C3.RV32.P3 C3.Json

set_option maxRecDepth 200000

section
variable {romBase : Word} {romCode : List Nat} {B Bf g t r : Word} {v : Nat → Word} {M0 : Word → BitVec 8}
  {M M' : Word → BitVec 8} {f : Fin 32 → Word}

/-- A byte of the frame above `sp` that `tuf::read_doc` doesn't write. -/
theorem act_rd_at (X : ActX romBase romCode B Bf M0) {c0 : Nat}
    (hfr : ∀ x, Sep x 1 B 0x3A50 → Sep x 1 (Bf + 0x4000) 0x2800 → Sep x 1 (B + BitVec.ofNat 32 c0) 8 → M' x = M x)
    (hc0 : c0 + 8 ≤ 0x5A70) {c : Nat} (h0 : c + 1 ≤ 0x5A70) (h1 : 0x3A50 ≤ c) (h2 : c + 1 ≤ c0 ∨ c0 + 8 ≤ c) :
    M' (B + BitVec.ofNat 32 c) = M (B + BitVec.ofNat 32 c) :=
  hfr _ (X.sB0 h0 h1) (X.sbf h0 (by decide)) (X.ss h0 hc0 h2)

theorem act_rd_ld (X : ActX romBase romCode B Bf M0) {c0 : Nat}
    (hfr : ∀ x, Sep x 1 B 0x3A50 → Sep x 1 (Bf + 0x4000) 0x2800 → Sep x 1 (B + BitVec.ofNat 32 c0) 8 → M' x = M x)
    (hc0 : c0 + 8 ≤ 0x5A70) {c : Nat} (h0 : c + 4 ≤ 0x5A70) (h1 : 0x3A50 ≤ c) (h2 : c + 4 ≤ c0 ∨ c0 + 8 ≤ c) :
    memLoad32 M' (B + BitVec.ofNat 32 c) = memLoad32 M (B + BitVec.ofNat 32 c) :=
  memLoad32_congr fun j hj => by
    rw [add_ofNat_assoc]; exact act_rd_at X hfr hc0 (by omega) (by omega) (by omega)

theorem act_rd_bytes (X : ActX romBase romCode B Bf M0) {c0 : Nat}
    (hfr : ∀ x, Sep x 1 B 0x3A50 → Sep x 1 (Bf + 0x4000) 0x2800 → Sep x 1 (B + BitVec.ofNat 32 c0) 8 → M' x = M x)
    (hc0 : c0 + 8 ≤ 0x5A70) {c n : Nat} (h0 : c + n ≤ 0x5A70) (h1 : 0x3A50 ≤ c) (h2 : c + n ≤ c0 ∨ c0 + 8 ≤ c) :
    memBytes M' (B + BitVec.ofNat 32 c) n = memBytes M (B + BitVec.ofNat 32 c) n :=
  memBytes_congr fun j hj => by
    rw [add_ofNat_assoc]; exact act_rd_at X hfr hc0 (by omega) (by omega) (by omega)

/-- Every byte the stage doesn't write, for a result in one of its result
slots. -/
theorem act_rd_out {c0 : Nat}
    (hfr : ∀ x, Sep x 1 B 0x3A50 → Sep x 1 (Bf + 0x4000) 0x2800 → Sep x 1 (B + BitVec.ofNat 32 c0) 8 → M' x = M x)
    (hres : ∀ x, ActOut B Bf x → Sep x 1 (B + BitVec.ofNat 32 c0) 8) : ∀ x, ActOut B Bf x → M' x = M x :=
  fun x hx => hfr x hx.1 hx.2.2.2.2.2 (hres x hx)

theorem act_out_1870 : ∀ x, ActOut B Bf x → Sep x 1 (B + BitVec.ofNat 32 0x52C0) 8 := fun x hx => by
  have := act_ks hx.2.2.2.2.1 0x10 8 (by decide); exact this

theorem act_out_350 : ∀ x, ActOut B Bf x → Sep x 1 (B + BitVec.ofNat 32 0x3DA0) 8 := fun x hx => by
  have := hx.2.2.2.1.subR (c := 0) (l := 8) (by decide)
  rwa [add_ofNat_assoc] at this

/-- **From 0xB10**: read `trusted_root.json`, then `act_hex`. -/
theorem act_b10 {flash : Nat → BitVec 8} {R : Nat} (hROM : RomRead flash R romBase romCode)
    (hR4 : R % 4 = 0) (hR : R ≤ 0x3A50 - 0x180)
    (X : ActX romBase romCode B Bf M0) (hI : ActI B Bf g t v M0 M f)
    (hr : memLoad32 M (acSlot B 0x40) = r) {pinned : Bytes} {parts : TufParts} {root : TufRoot} {re te : Nat}
    {x21 x25 x27 : Word} {Mi : Word → BitVec 8} {hiW loW : Word} {val : Nat} {body : Bytes}
    (hO : ∀ x, ActOut B Bf x → M x = Mi x)
    (h18 : memLoad32 M (acSlot B 0x18) = hiW) (h14 : memLoad32 M (acSlot B 0x14) = loW)
    (hval : hiW.toNat * 2 ^ 32 + loW.toNat = val)
    (hdoc : ActDoc flash M (acSlot B 0x244) (f 24) (f 14).toNat parts.trustedRoot)
    (hs4 : f 20 = Bf + 0x4000)
    (hbody : f 9 = 0 → memBytes M (acSlot B 0x351) 64 = body)
    (hspec : val = parts.trustedRoot.length → body = hexBytes (sha256 parts.trustedRoot) →
      verifyTuf pinned parts = some (root.version, min re te))
    (h20 : memLoad32 M (acSlot B 0x20) = BitVec.ofNat 32 te)
    (h24 : memLoad32 M (acSlot B 0x24) = BitVec.ofNat 32 (te / 2 ^ 32))
    (h28 : memLoad32 M (acSlot B 0x28) = BitVec.ofNat 32 re)
    (h2C : memLoad32 M (acSlot B 0x2C) = BitVec.ofNat 32 (re / 2 ^ 32))
    (hs3 : f 19 = acSlot B 0x890) (hs6 : f 22 = acSlot B 0x1310)
    (hs5 : f 21 = x21) (hs9 : f 25 = x25) (hs11 : f 27 = x27) :
    WP bootMainClosure0Code AC (actQ B Bf g t r v M0 (AcTargetsPost pinned parts root re B Bf x21 x25 x27 Mi))
      M 0xB10 f := by
  have F := X.F
  refine WP.zero fun hz => ?_
  refine WP.lui ac_at_b10 ?_; wn
  refine WP.aluImm ac_at_b12 ?_; wn
  refine WP.alu ac_at_b16 ?_; wn
  refine WP.aluImm ac_at_b18 ?_; wn
  refine WP.alu ac_at_b1a ?_; wn
  refine WP.alu ac_at_b1c ?_; wn
  refine WP.alu ac_at_b1e ?_; wn
  refine act_rd (c := 0x52C0) (start := f 24) (plen := f 23) (iw := f 14) hROM hR4 hR X
    (hI.regs (by act_r) (by act_r) (by act_r)) ac_at_b20 ac_at_b24 (by decide) (by decide)
    (by act_r; rw [BitVec.add_comm]; exact act_spc hI.rsp _ _ rfl) (by act_r) (by act_r)
    (by act_r; exact act_spc hI.rsp _ _ rfl) (by act_r) (by act_r; exact hs4) (by decide)
    fun m2 hout hfr => ?_
  have hc0 : 0x52C0 + 8 ≤ 0x5A70 := by decide
  have kO := act_rd_out hfr act_out_1870
  have hres := act_trd_res hout (fun o l h => hdoc o l h) (fun e h => act_tid_err h)
  refine act_hex X ((hI.mem F X.sB kO).regs (by act_r) (by act_r) (by act_r))
    ((act_rd_ld X hfr hc0 (c := 0x3A50 + 0x40) (by decide) (by decide) (by decide)).trans hr)
    (fun x hx => (kO x hx).trans (hO x hx))
    ((act_rd_ld X hfr hc0 (c := 0x3A50 + 0x18) (by decide) (by decide) (by decide)).trans h18)
    ((act_rd_ld X hfr hc0 (c := 0x3A50 + 0x14) (by decide) (by decide) (by decide)).trans h14) hval ?_
    (fun h9 => (act_rd_bytes X hfr hc0 (c := 0x3A50 + 0x351) (n := 64) (by decide) (by decide) (by decide)).trans
      (hbody (by revert h9; act_r; exact id))) hspec
    ((act_rd_ld X hfr hc0 (c := 0x3A50 + 0x20) (by decide) (by decide) (by decide)).trans h20)
    ((act_rd_ld X hfr hc0 (c := 0x3A50 + 0x24) (by decide) (by decide) (by decide)).trans h24)
    ((act_rd_ld X hfr hc0 (c := 0x3A50 + 0x28) (by decide) (by decide) (by decide)).trans h28)
    ((act_rd_ld X hfr hc0 (c := 0x3A50 + 0x2C) (by decide) (by decide) (by decide)).trans h2C)
    (by act_r; exact hs3) (by act_r; exact hs6) (by act_r; exact hs5) (by act_r; exact hs9) (by act_r; exact hs11)
  have e4 : B + BitVec.ofNat 32 0x52C0 + 4 = acSlot B 0x1874 := add_ofNat_assoc B _ _
  rw [e4] at hres
  exact hres

end

end C3.RV32.Ac
