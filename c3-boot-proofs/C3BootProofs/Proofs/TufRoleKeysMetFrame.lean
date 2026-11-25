import C3BootProofs.Proofs.TufRoleKeysMetAt
import C3BootProofs.Proofs.TufRoleKeysMetModel
import C3BootProofs.Proofs.TufRoleKeysEnv

/-!
# The frame of `RoleKeys::met`

`RoleKeys::met` keeps a 0x1F0-byte frame at `F`: the counted slots at
`F + 0x28`, scratch space, and the saved registers at `F + 0x1BC`. Its
deepest callee, `p256_verify_prehash`, uses the 0x3730 bytes below `F`, so
the frame and the callees' stacks are the 0x3920 bytes at
`s = F - 0x3730`. This file holds the facts about the frame that the body's
proofs share, and the epilogue.
-/

namespace C3.RV32

open C3.Image C3.Json

set_option maxRecDepth 20000

/-- The code `RoleKeys::met` runs outside the signature checks. -/
structure RmCodeA (M : Word → BitVec 8) : Prop where
  self : CodeIn M TRM tufRoleKeysMetCode
  rk : RkCode M
  eq97 : CodeIn M (BitVec.ofNat 32 eqArr97Address) eqArr97Code
  eq97m : CodeIn M (BitVec.ofNat 32 eqArr97Address + 0xC04C) memcmpCode
  a32 : CodeIn M (BitVec.ofNat 32 arr32EqAddress) arr32EqCode
  a32m : CodeIn M (BitVec.ofNat 32 arr32EqAddress + 0xC032) memcmpCode

/-- What the body may assume after the prologue: the frame at
`F = s + 0x3730`, the saved registers in `M1`, the bounds on the stack,
the `RoleKeys` at `R`, the message (the `ML` bytes at `MP`), and the
signatures array (the `SL` bytes at `SP`). -/
structure RmBase (M0 M1 : Word → BitVec 8) (s F R MP SP : Word) (ML SL : Nat) (g0 : Fin 32 → Word) : Prop where
  hF : s + BitVec.ofNat 32 0x3730 = F
  hal : s.toNat % 16 = 0
  hlo : 0x3FC80000 ≤ s.toNat
  hhi : s.toNat + 0x3920 ≤ 0x3FCE0000
  hds : Sep s 0x3920 (BitVec.ofNat 32 (img% dataWindowAddress)) (img% dataWindowSize)
  hro : Sep s 0x3920 (BitVec.ofNat 32 (img% roWindowAddress)) (img% roWindowSize)
  hcA : ∀ M : Word → BitVec 8, (∀ x, Sep x 1 s 0x3920 → M x = M0 x) → RmCodeA M
  hO1 : Out M0 M1 s 0x3920
  hv : RkSaved (F + 0x180) g0 M1
  hsp0 : g0 sp = F + BitVec.ofNat 32 0x1F0
  hret : g0 ra &&& ~~~1 = g0 ra
  hz0 : g0 0 = 0
  halR : R.toNat % 4 = 0
  hRw : R.toNat + 0x540 ≤ 0x40000000
  hSR : Sep s 0x3920 R 0x540
  hMw : MP.toNat + ML ≤ 0x40000000
  hML : ML < 2 ^ 31
  hSM : Sep s 0x3920 MP ML
  hS0 : SP.toNat ≠ 0
  hSw : SP.toNat + SL ≤ 0x40000000
  hSL : SL < 2 ^ 31
  hSS : Sep s 0x3920 SP SL

/-- What `RoleKeys::met` leaves: it halts as `H` says, or it returns with
memory outside the 0x3920 bytes at `s` as before, and `S` holds when it
returns `Ok(true)`. `Env` sets `H` to a panic. -/
abbrev rmQ (H : Post) (M0 : Word → BitVec 8) (s : Word) (g0 : Fin 32 → Word) (S : Prop) : Post :=
  fun pc M g => H pc M g ∨
    (RPost (g0 ra) (fun M' => ∀ x, Sep x 1 s 0x3920 → M' x = M0 x) g0 pc M g ∧ (g a0 = 0 → g a1 ≠ 0 → S))

section
variable {M0 M1 Mk : Word → BitVec 8} {s F R MP SP : Word} {ML SL : Nat} {g0 : Fin 32 → Word}

theorem RmBase.Fc (E : RmBase M0 M1 s F R MP SP ML SL g0) (c : Nat) :
    F + BitVec.ofNat 32 c = s + BitVec.ofNat 32 (0x3730 + c) := by
  rw [← E.hF, add_ofNat_assoc]

theorem RmBase.wS (E : RmBase M0 M1 s F R MP SP ML SL g0) {d k : Nat} (hd : d + k ≤ 0x3920) :
    (s + BitVec.ofNat 32 d).toNat + k ≤ 0x40000000 := by
  have := E.hhi; rw [tex_toNat (by omega)]; omega

theorem RmBase.SN (E : RmBase M0 M1 s F R MP SP ML SL g0) {d : Nat} (hd : d ≤ 0x3920) :
    (s + BitVec.ofNat 32 d).toNat = s.toNat + d := by
  have := E.hhi; rw [tex_toNat (by omega)]

theorem RmBase.FN (E : RmBase M0 M1 s F R MP SP ML SL g0) {c : Nat} (hc : c ≤ 0x1F0) :
    (F + BitVec.ofNat 32 c).toNat = s.toNat + 0x3730 + c := by
  rw [E.Fc, E.SN (by omega)]; omega

theorem RmBase.halF (E : RmBase M0 M1 s F R MP SP ML SL g0) : F.toNat % 16 = 0 := by
  have := E.FN (c := 0) (by decide); rw [add_ofNat_zero] at this; have := E.hal; omega

theorem RmBase.alF (E : RmBase M0 M1 s F R MP SP ML SL g0) {c : Nat} (hc : c % 4 = 0) :
    (F + BitVec.ofNat 32 c).toNat % 4 = 0 :=
  aligned_add (by have := E.halF; omega) hc

theorem RmBase.alS (E : RmBase M0 M1 s F R MP SP ML SL g0) {d : Nat} (hd : d % 4 = 0) :
    (s + BitVec.ofNat 32 d).toNat % 4 = 0 :=
  aligned_add (by have := E.hal; omega) hd

theorem RmBase.wF (E : RmBase M0 M1 s F R MP SP ML SL g0) {c k : Nat} (h : c + k ≤ 0x1F0) :
    (F + BitVec.ofNat 32 c).toNat + k ≤ 0x40000000 := by
  rw [E.Fc]; exact E.wS (by omega)

theorem RmBase.lowS (E : RmBase M0 M1 s F R MP SP ML SL g0) {c w : Nat} (h : c + w ≤ 0x3920) {b : Word} {l : Nat}
    (hb : 0x40000000 ≤ b.toNat) (hbl : b.toNat + l ≤ 2 ^ 32) : Sep (s + BitVec.ofNat 32 c) w b l :=
  lowSep (E.wS h) hb hbl

theorem RmBase.lowF (E : RmBase M0 M1 s F R MP SP ML SL g0) {c w : Nat} (h : c + w ≤ 0x1F0) {b : Word} {l : Nat}
    (hb : 0x40000000 ≤ b.toNat) (hbl : b.toNat + l ≤ 2 ^ 32) : Sep (F + BitVec.ofNat 32 c) w b l :=
  lowSep (E.wF h) hb hbl

theorem RmBase.cF (E : RmBase M0 M1 s F R MP SP ML SL g0) {c w : Nat} (h : c + w ≤ 0x1F0) :
    Sep (F + BitVec.ofNat 32 c) w TRM tufRoleKeysMetCode.length :=
  E.lowF h (by decide) (by decide)

theorem rm_ff (F : Word) {c n d k : Nat} (h : c + n ≤ d ∨ d + k ≤ c) (hc : c + n ≤ 0x1F0) (hd : d + k ≤ 0x1F0) :
    Sep (F + BitVec.ofNat 32 c) n (F + BitVec.ofNat 32 d) k :=
  sep_offsets F h (by omega) (by omega)

theorem RmBase.fs (E : RmBase M0 M1 s F R MP SP ML SL g0) {c n d k : Nat} (h : 0x3730 + c + n ≤ d ∨ d + k ≤ 0x3730 + c)
    (hc : c + n ≤ 0x1F0) (hd : d + k ≤ 0x3920) : Sep (F + BitVec.ofNat 32 c) n (s + BitVec.ofNat 32 d) k := by
  rw [E.Fc]; exact sep_offsets s h (by omega) (by omega)

theorem RmBase.ss (_E : RmBase M0 M1 s F R MP SP ML SL g0) {c n d k : Nat} (h : c + n ≤ d ∨ d + k ≤ c)
    (hc : c + n ≤ 0x3920) (hd : d + k ≤ 0x3920) : Sep (s + BitVec.ofNat 32 c) n (s + BitVec.ofNat 32 d) k :=
  sep_offsets s h (by omega) (by omega)

/-- The region at `R` is apart from the frame. -/
theorem RmBase.rS (E : RmBase M0 M1 s F R MP SP ML SL g0) {c w d k : Nat} (hc : c + w ≤ 0x540) (hd : d + k ≤ 0x3920) :
    Sep (R + BitVec.ofNat 32 c) w (s + BitVec.ofNat 32 d) k :=
  (E.hSR.sub hd).symm.sub hc

theorem RmBase.rF (E : RmBase M0 M1 s F R MP SP ML SL g0) {c w d k : Nat} (hc : c + w ≤ 0x540) (hd : d + k ≤ 0x1F0) :
    Sep (R + BitVec.ofNat 32 c) w (F + BitVec.ofNat 32 d) k := by
  rw [E.Fc]; exact E.rS hc (by omega)

theorem RmBase.RN (E : RmBase M0 M1 s F R MP SP ML SL g0) {c : Nat} (hc : c ≤ 0x540) :
    (R + BitVec.ofNat 32 c).toNat = R.toNat + c := by
  have := E.hRw; rw [tex_toNat (by omega)]

theorem RmBase.saveSep (E : RmBase M0 M1 s F R MP SP ML SL g0) {c : Nat} (hc : 0x3C ≤ c) (hc' : c + 4 ≤ 0x70) :
    Sep s 0x38EC (F + 0x180 + BitVec.ofNat 32 c) 4 := by
  rw [show F + 0x180 = F + BitVec.ofNat 32 0x180 from rfl, add_ofNat_assoc, E.Fc]
  exact tex_sepS (by omega) (by have := E.hhi; omega)

/-- Memory that agrees with `M1` outside the 0x38EC bytes at `s` agrees
with `M0` outside the 0x3920. -/
theorem RmBase.agree (E : RmBase M0 M1 s F R MP SP ML SL g0) (hO : Out M1 Mk s 0x38EC) :
    ∀ x, Sep x 1 s 0x3920 → Mk x = M0 x :=
  fun x hx => (hO x (tex_sepR hx (by decide))).trans (E.hO1 x hx)

theorem RmBase.codeA (E : RmBase M0 M1 s F R MP SP ML SL g0) (hO : Out M1 Mk s 0x38EC) : RmCodeA Mk :=
  E.hcA Mk (E.agree hO)

theorem RmBase.bytes (E : RmBase M0 M1 s F R MP SP ML SL g0) (hO : Out M1 Mk s 0x38EC) {q : Word} {l : Nat}
    (hS : Sep s 0x3920 q l) : memBytes Mk q l = memBytes M0 q l :=
  memBytes_congr fun _ hi => E.agree hO _ (sep_pt hS hi)

theorem RmBase.savedS {Ma Mb : Word → BitVec 8} (E : RmBase M0 M1 s F R MP SP ML SL g0)
    (hv : RkSaved (F + 0x180) g0 Ma) (hO : Out Ma Mb s 0x38EC) : RkSaved (F + 0x180) g0 Mb := by
  obtain ⟨v0, v1, v2, v3, v4, v5, v6, v7, v8, v9, v10, v11, v12⟩ := hv
  exact ⟨(hO.load32 (E.saveSep (by decide) (by decide))).trans v0, (hO.load32 (E.saveSep (by decide) (by decide))).trans v1,
    (hO.load32 (E.saveSep (by decide) (by decide))).trans v2, (hO.load32 (E.saveSep (by decide) (by decide))).trans v3,
    (hO.load32 (E.saveSep (by decide) (by decide))).trans v4, (hO.load32 (E.saveSep (by decide) (by decide))).trans v5,
    (hO.load32 (E.saveSep (by decide) (by decide))).trans v6, (hO.load32 (E.saveSep (by decide) (by decide))).trans v7,
    (hO.load32 (E.saveSep (by decide) (by decide))).trans v8, (hO.load32 (E.saveSep (by decide) (by decide))).trans v9,
    (hO.load32 (E.saveSep (by decide) (by decide))).trans v10,
    (hO.load32 (E.saveSep (by decide) (by decide))).trans v11,
    (hO.load32 (E.saveSep (by decide) (by decide))).trans v12⟩

theorem RmBase.saved (E : RmBase M0 M1 s F R MP SP ML SL g0) (hO : Out M1 Mk s 0x38EC) : RkSaved (F + 0x180) g0 Mk :=
  E.savedS E.hv hO

/-- A change inside the frame below the saved registers. -/
theorem RmBase.outF (E : RmBase M0 M1 s F R MP SP ML SL g0) {Ma Mb : Word → BitVec 8} {c l : Nat}
    (h : Out Ma Mb (F + BitVec.ofNat 32 c) l) (hc : c + l ≤ 0x1BC) : Out Ma Mb s 0x38EC := by
  rw [E.Fc] at h; exact h.widen (by omega)

/-- A change in the callees' stacks below `F`. -/
theorem RmBase.outS (_E : RmBase M0 M1 s F R MP SP ML SL g0) {Ma Mb : Word → BitVec 8} {d l : Nat}
    (h : Out Ma Mb (s + BitVec.ofNat 32 d) l) (hd : d + l ≤ 0x38EC) : Out Ma Mb s 0x38EC :=
  h.widen hd

/-- `memcpy` between two parts of the frame above its own 16 bytes. -/
theorem RmBase.mcFF (E : RmBase M0 M1 s F R MP SP ML SL g0) {M : Word → BitVec 8} (hc : RmCodeA M) {c d n : Nat}
    (h : c + n ≤ d ∨ d + n ≤ c) (hcn : c + n ≤ 0x1F0) (hdn : d + n ≤ 0x1F0) :
    McEnv M BMB (F + BitVec.ofNat 32 c) (F + BitVec.ofNat 32 d) (s + BitVec.ofNat 32 0x3720) n :=
  ⟨hc.rk.tps.bmb, E.lowF hcn (by decide) (by decide), E.lowS (by decide) (by decide) (by decide),
    E.fs (Or.inr (by omega)) hcn (by decide), E.fs (Or.inr (by omega)) hdn (by decide), rm_ff F h hcn hdn,
    E.alS (by decide), by have := E.wS (d := 0x3720) (k := 16) (by decide); omega,
    by have := E.wF hcn; omega, by have := E.wF hdn; omega⟩

/-- `memcpy` from slot bytes at `R` into the frame. -/
theorem RmBase.mcFR (E : RmBase M0 M1 s F R MP SP ML SL g0) {M : Word → BitVec 8} (hc : RmCodeA M) {c d n : Nat}
    (hcn : c + n ≤ 0x1F0) (hdn : d + n ≤ 0x540) :
    McEnv M BMB (F + BitVec.ofNat 32 c) (R + BitVec.ofNat 32 d) (s + BitVec.ofNat 32 0x3720) n :=
  ⟨hc.rk.tps.bmb, E.lowF hcn (by decide) (by decide), E.lowS (by decide) (by decide) (by decide),
    E.fs (Or.inr (by omega)) hcn (by decide), E.rS hdn (by decide), (E.rF hdn hcn).symm,
    E.alS (by decide), by have := E.wS (d := 0x3720) (k := 16) (by decide); omega,
    by have := E.wF hcn; omega, by have := E.hRw; rw [E.RN (by omega)]; omega⟩

theorem RmBase.sp (E : RmBase M0 M1 s F R MP SP ML SL g0) (d : Nat) (hd : d ≤ 0x3730) :
    s + BitVec.ofNat 32 d + BitVec.ofNat 32 (0x3730 - d) = F := by
  rw [add_ofNat_assoc, ← E.hF]; congr 2; omega

/-- `F` less `c`, from `s`. -/
theorem RmBase.Fm (E : RmBase M0 M1 s F R MP SP ML SL g0) {c : Nat} (hc : c ≤ 0x3730) {w : Word}
    (hw : w = BitVec.ofNat 32 (2 ^ 32 - c)) : F + w = s + BitVec.ofNat 32 (0x3730 - c) := by
  subst hw; rw [← E.hF, BitVec.add_assoc, ofNat_add_ofNat]
  congr 1; apply BitVec.eq_of_toNat_eq; simp only [BitVec.toNat_ofNat]; omega

/-- A part of the stack and a part of the read-only window are apart. -/
theorem RmBase.roS (E : RmBase M0 M1 s F R MP SP ML SL g0) {c l d k : Nat} (hc : c + l ≤ 0x3920)
    (hd : d + k ≤ img% roWindowSize) {b : Word} (hb : BitVec.ofNat 32 (img% roWindowAddress) + BitVec.ofNat 32 d = b) :
    Sep (s + BitVec.ofNat 32 c) l b k := by
  rw [← hb]; exact (E.hro.sub hc).subR hd

end

section
variable {M0 Mf : Word → BitVec 8} {s F : Word} {g g0 : Fin 32 → Word} {S : Prop} {H : Post}

/-- The epilogue from 0x36E: `a0` is whether the loop stopped early, `a1`
the error byte or the result. -/
theorem rm_epi (hsp : g sp = F) (hv : RkSaved (F + 0x180) g0 Mf)
    (hsp0 : g0 sp = F + BitVec.ofNat 32 0x1F0) (hret : g0 ra &&& ~~~1 = g0 ra) (hal : F.toNat % 4 = 0)
    (hz0 : g0 0 = 0) (hfr : ∀ x, x ∉ rkE → g x = g0 x) (hR : ∀ x, Sep x 1 s 0x3920 → Mf x = M0 x)
    (hS : aluEval .sltu (g 22) (g 20) = 0 → g 26 ≠ 0 → S) :
    WP tufRoleKeysMetCode TRM (rmQ H M0 s g0 S) Mf 0x36E g := by
  obtain ⟨e0, e1, e2, e3, e4, e5, e6, e7, e8, e9, e10, e11, e12⟩ := hv
  have hA : (F + 0x180).toNat % 4 = 0 := aligned_add hal (k := 0x180) (by decide)
  refine WP.alu rkm_at_36e ?_; wn
  refine WP.alu rkm_at_372 ?_; wn
  refine WP.aluImm rkm_at_374 ?_; wn
  rw [hsp, ev_add]
  refine WP.lw rkm_at_376 (by rsimp; exact aligned_add hA (k := 0x6C) (by decide)) ?_; wn
  refine WP.lw rkm_at_37a (by rsimp; exact aligned_add hA (k := 0x68) (by decide)) ?_; wn
  refine WP.lw rkm_at_37c (by rsimp; exact aligned_add hA (k := 0x64) (by decide)) ?_; wn
  refine WP.lw rkm_at_37e (by rsimp; exact aligned_add hA (k := 0x60) (by decide)) ?_; wn
  refine WP.lw rkm_at_382 (by rsimp; exact aligned_add hA (k := 0x5C) (by decide)) ?_; wn
  refine WP.lw rkm_at_386 (by rsimp; exact aligned_add hA (k := 0x58) (by decide)) ?_; wn
  refine WP.lw rkm_at_38a (by rsimp; exact aligned_add hA (k := 0x54) (by decide)) ?_; wn
  refine WP.lw rkm_at_38e (by rsimp; exact aligned_add hA (k := 0x50) (by decide)) ?_; wn
  refine WP.lw rkm_at_392 (by rsimp; exact aligned_add hA (k := 0x4C) (by decide)) ?_; wn
  refine WP.lw rkm_at_396 (by rsimp; exact aligned_add hA (k := 0x48) (by decide)) ?_; wn
  refine WP.lw rkm_at_39a (by rsimp; exact aligned_add hA (k := 0x44) (by decide)) ?_; wn
  refine WP.lw rkm_at_39e (by rsimp; exact aligned_add hA (k := 0x40) (by decide)) ?_; wn
  refine WP.lw rkm_at_3a2 (by rsimp; exact aligned_add hA (k := 0x3C) (by decide)) ?_; wn
  refine WP.aluImm rkm_at_3a6 ?_; wn
  refine WP.ret rkm_at_3a8 (.inr ⟨⟨?_, hR, ?_⟩, ?_⟩)
  · rsimp; erw [e0]; rw [add_lit_zero, hret]
  · refine frame_of (L2 := [ra, sp, 8, 9, 18, 19, 20, 21, 22, 23, 24, 25, 26, 27]) (by keepz hz0) fun x hx => ?_
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hx
    rcases hx with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> rsimp
    · exact e0
    · rw [hsp, hsp0]; rfl
    · exact e1
    · exact e2
    · exact e3
    · exact e4
    · exact e5
    · exact e6
    · exact e7
    · exact e8
    · exact e9
    · exact e10
    · exact e11
    · exact e12
  · rsimp; exact fun h1 h2 => hS h1 fun h3 => h2 (by rw [h3]; rfl)

end

end C3.RV32
