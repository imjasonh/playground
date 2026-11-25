import C3BootProofs.Proofs.TufRoleKeysReadAt
import C3BootProofs.Proofs.TufRoleKeysCalls

/-!
# The frame of `RoleKeys::read`

`RoleKeys::read` keeps a 2752-byte frame at `F`: the `RoleKeys` it builds at
`F + 0x18`, scratch space, the keyid cursor at `F + 0xA6C`, and the saved
registers at `F + 0xA8C`. Its deepest callee, `pem_spki`, uses the 304
bytes below `F`, so the frame and the callees' stacks are the 3056 bytes at
`s = F - 304`. This file holds the prologue, the epilogue, the error tails,
and the facts about the frame that the body's proofs share.
-/

namespace C3.RV32

open C3.Image C3.Json

set_option maxRecDepth 20000

/-- What `RoleKeys::read` leaves: memory outside the 3056 bytes at `s` and
the 0x540 bytes at `out` as before, and at `out` either the error byte
after the tag 0xFE or the keys. -/
def RkRes (M M' : Word → BitVec 8) (s out : Word) : Except Nat (Nat × List RkEntry) → Prop
  | .error e => (∀ x, Sep x 1 s 3056 → Sep x 1 out 0x540 → M' x = M x) ∧ M' out = 0xFE ∧
      M' (out + 1) = BitVec.ofNat 8 e
  | .ok (t, es) => (∀ x, Sep x 1 s 3056 → Sep x 1 out 0x540 → M' x = M x) ∧ RkAt M' out t es

/-- The registers `RoleKeys::read` changes before its epilogue restores
the saved ones. -/
abbrev rkE : List (Fin 32) := jClob ++ [ra, sp, 8, 9, 18, 19, 20, 21, 22, 23, 24, 25, 26, 27]

/-- The saved registers, at `A + 0x3C` to `A + 0x70`. -/
def RkSaved (A : Word) (g0 : Fin 32 → Word) (M : Word → BitVec 8) : Prop :=
  memLoad32 M (A + BitVec.ofNat 32 0x6C) = g0 ra ∧ memLoad32 M (A + BitVec.ofNat 32 0x68) = g0 8 ∧
    memLoad32 M (A + BitVec.ofNat 32 0x64) = g0 9 ∧ memLoad32 M (A + BitVec.ofNat 32 0x60) = g0 18 ∧
    memLoad32 M (A + BitVec.ofNat 32 0x5C) = g0 19 ∧ memLoad32 M (A + BitVec.ofNat 32 0x58) = g0 20 ∧
    memLoad32 M (A + BitVec.ofNat 32 0x54) = g0 21 ∧ memLoad32 M (A + BitVec.ofNat 32 0x50) = g0 22 ∧
    memLoad32 M (A + BitVec.ofNat 32 0x4C) = g0 23 ∧ memLoad32 M (A + BitVec.ofNat 32 0x48) = g0 24 ∧
    memLoad32 M (A + BitVec.ofNat 32 0x44) = g0 25 ∧ memLoad32 M (A + BitVec.ofNat 32 0x40) = g0 26 ∧
    memLoad32 M (A + BitVec.ofNat 32 0x3C) = g0 27

/-- Memory after the prologue's stores. -/
def rkM1 (M : Word → BitVec 8) (A : Word) (g0 : Fin 32 → Word) : Word → BitVec 8 :=
  memStore32 (memStore32 (memStore32 (memStore32 (memStore32 (memStore32 (memStore32 (memStore32 (memStore32
    (memStore32 (memStore32 (memStore32 (memStore32 M (A + 0x6C) (g0 ra)) (A + 0x68) (g0 8)) (A + 0x64) (g0 9))
    (A + 0x60) (g0 18)) (A + 0x5C) (g0 19)) (A + 0x58) (g0 20)) (A + 0x54) (g0 21)) (A + 0x50) (g0 22))
    (A + 0x4C) (g0 23)) (A + 0x48) (g0 24)) (A + 0x44) (g0 25)) (A + 0x40) (g0 26)) (A + 0x3C) (g0 27)

theorem rk_pro (M : Word → BitVec 8) (A : Word) (g0 : Fin 32 → Word) :
    Out M (rkM1 M A g0) A 0x70 ∧ RkSaved A g0 (rkM1 M A g0) := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact ((((((((((((((out_store32 _ _ _).widen (d := 0x6C) (by decide)).trans
      ((out_store32 _ _ _).widen (d := 0x68) (by decide))).trans
      ((out_store32 _ _ _).widen (d := 0x64) (by decide))).trans
      ((out_store32 _ _ _).widen (d := 0x60) (by decide))).trans
      ((out_store32 _ _ _).widen (d := 0x5C) (by decide))).trans
      ((out_store32 _ _ _).widen (d := 0x58) (by decide))).trans
      ((out_store32 _ _ _).widen (d := 0x54) (by decide))).trans
      ((out_store32 _ _ _).widen (d := 0x50) (by decide))).trans
      ((out_store32 _ _ _).widen (d := 0x4C) (by decide))).trans
      ((out_store32 _ _ _).widen (d := 0x48) (by decide))).trans
      ((out_store32 _ _ _).widen (d := 0x44) (by decide))).trans
      ((out_store32 _ _ _).widen (d := 0x40) (by decide))).trans
      ((out_store32 _ _ _).widen (d := 0x3C) (by decide)))
  · exact pa_ld 0x6C (by decide) [0x68, 0x64, 0x60, 0x5C, 0x58, 0x54, 0x50, 0x4C, 0x48, 0x44, 0x40, 0x3C]
      (by decide) (by decide) (memLoad32_store32_same _ _ _)
      [g0 8, g0 9, g0 18, g0 19, g0 20, g0 21, g0 22, g0 23, g0 24, g0 25, g0 26, g0 27]
  · exact pa_ld 0x68 (by decide) [0x64, 0x60, 0x5C, 0x58, 0x54, 0x50, 0x4C, 0x48, 0x44, 0x40, 0x3C]
      (by decide) (by decide) (memLoad32_store32_same _ _ _)
      [g0 9, g0 18, g0 19, g0 20, g0 21, g0 22, g0 23, g0 24, g0 25, g0 26, g0 27]
  · exact pa_ld 0x64 (by decide) [0x60, 0x5C, 0x58, 0x54, 0x50, 0x4C, 0x48, 0x44, 0x40, 0x3C]
      (by decide) (by decide) (memLoad32_store32_same _ _ _)
      [g0 18, g0 19, g0 20, g0 21, g0 22, g0 23, g0 24, g0 25, g0 26, g0 27]
  · exact pa_ld 0x60 (by decide) [0x5C, 0x58, 0x54, 0x50, 0x4C, 0x48, 0x44, 0x40, 0x3C]
      (by decide) (by decide) (memLoad32_store32_same _ _ _)
      [g0 19, g0 20, g0 21, g0 22, g0 23, g0 24, g0 25, g0 26, g0 27]
  · exact pa_ld 0x5C (by decide) [0x58, 0x54, 0x50, 0x4C, 0x48, 0x44, 0x40, 0x3C]
      (by decide) (by decide) (memLoad32_store32_same _ _ _)
      [g0 20, g0 21, g0 22, g0 23, g0 24, g0 25, g0 26, g0 27]
  · exact pa_ld 0x58 (by decide) [0x54, 0x50, 0x4C, 0x48, 0x44, 0x40, 0x3C]
      (by decide) (by decide) (memLoad32_store32_same _ _ _) [g0 21, g0 22, g0 23, g0 24, g0 25, g0 26, g0 27]
  · exact pa_ld 0x54 (by decide) [0x50, 0x4C, 0x48, 0x44, 0x40, 0x3C]
      (by decide) (by decide) (memLoad32_store32_same _ _ _) [g0 22, g0 23, g0 24, g0 25, g0 26, g0 27]
  · exact pa_ld 0x50 (by decide) [0x4C, 0x48, 0x44, 0x40, 0x3C]
      (by decide) (by decide) (memLoad32_store32_same _ _ _) [g0 23, g0 24, g0 25, g0 26, g0 27]
  · exact pa_ld 0x4C (by decide) [0x48, 0x44, 0x40, 0x3C]
      (by decide) (by decide) (memLoad32_store32_same _ _ _) [g0 24, g0 25, g0 26, g0 27]
  · exact pa_ld 0x48 (by decide) [0x44, 0x40, 0x3C]
      (by decide) (by decide) (memLoad32_store32_same _ _ _) [g0 25, g0 26, g0 27]
  · exact pa_ld 0x44 (by decide) [0x40, 0x3C] (by decide) (by decide) (memLoad32_store32_same _ _ _) [g0 26, g0 27]
  · exact pa_ld 0x40 (by decide) [0x3C] (by decide) (by decide) (memLoad32_store32_same _ _ _) [g0 27]
  · exact memLoad32_store32_same _ _ _

/-- What the body may assume after the prologue: the frame at
`F = s + 304`, the saved registers in `M1`, the bounds on the stack and
`out`, and the root document, the `N` bytes at `P`. -/
structure RkEnv (M0 M1 : Word → BitVec 8) (s out F P : Word) (N : Nat) (g0 : Fin 32 → Word) : Prop where
  hF : s + BitVec.ofNat 32 304 = F
  hal : s.toNat % 4 = 0
  hsw : s.toNat + 3056 ≤ 0x40000000
  halo : out.toNat % 4 = 0
  how : out.toNat + 0x540 ≤ 0x40000000
  hso : Sep out 0x540 s 3056
  hro : Sep s 3056 (BitVec.ofNat 32 roWindowAddress) roWindowSize
  hc : RkCode M0
  hO1 : Out M0 M1 s 3056
  hv : RkSaved (F + 0xA50) g0 M1
  hsp0 : g0 sp = F + BitVec.ofNat 32 0xAC0
  hret : g0 ra &&& ~~~1 = g0 ra
  hz0 : g0 0 = 0
  hP0 : P.toNat ≠ 0
  hPN : P.toNat + N < 2 ^ 32
  hN : N < 2 ^ 31
  hSP : Sep s 3056 P N

section
variable {M0 M1 Mk : Word → BitVec 8} {s out F P : Word} {N : Nat} {g0 : Fin 32 → Word}

theorem RkEnv.Fc (E : RkEnv M0 M1 s out F P N g0) (c : Nat) :
    F + BitVec.ofNat 32 c = s + BitVec.ofNat 32 (304 + c) := by
  rw [← E.hF, add_ofNat_assoc]

theorem RkEnv.FN (E : RkEnv M0 M1 s out F P N g0) {c : Nat} (hc : c ≤ 0xAC0) :
    (F + BitVec.ofNat 32 c).toNat = s.toNat + 304 + c := by
  rw [E.Fc, tex_toNat (by have := E.hsw; omega)]; omega

theorem RkEnv.halF (E : RkEnv M0 M1 s out F P N g0) : F.toNat % 4 = 0 := by
  have := E.FN (c := 0) (by decide); rw [add_ofNat_zero] at this; have := E.hal; omega

theorem RkEnv.alF (E : RkEnv M0 M1 s out F P N g0) {c : Nat} (hc : c % 4 = 0) :
    (F + BitVec.ofNat 32 c).toNat % 4 = 0 :=
  aligned_add E.halF hc

theorem RkEnv.wF (E : RkEnv M0 M1 s out F P N g0) {c k : Nat} (h : c + k ≤ 0xAC0) :
    (F + BitVec.ofNat 32 c).toNat + k ≤ 0x40000000 := by
  rw [E.FN (by omega)]; have := E.hsw; omega

theorem RkEnv.wS (E : RkEnv M0 M1 s out F P N g0) {d k : Nat} (hd : d + k ≤ 3056) :
    (s + BitVec.ofNat 32 d).toNat + k ≤ 0x40000000 := by
  have := E.hsw; rw [tex_toNat (by omega)]; omega

theorem rk_ff (F : Word) {c n d k : Nat} (h : c + n ≤ d ∨ d + k ≤ c) (hc : c + n ≤ 0xAC0) (hd : d + k ≤ 0xAC0) :
    Sep (F + BitVec.ofNat 32 c) n (F + BitVec.ofNat 32 d) k :=
  sep_offsets F h (by omega) (by omega)

theorem RkEnv.fs (E : RkEnv M0 M1 s out F P N g0) {c n d k : Nat} (h : 304 + c + n ≤ d ∨ d + k ≤ 304 + c)
    (hc : c + n ≤ 0xAC0) (hd : d + k ≤ 3056) : Sep (F + BitVec.ofNat 32 c) n (s + BitVec.ofNat 32 d) k := by
  rw [E.Fc]; exact sep_offsets s h (by omega) (by omega)

theorem RkEnv.lowS (E : RkEnv M0 M1 s out F P N g0) {c w : Nat} (h : c + w ≤ 3056) {b : Word} {l : Nat}
    (hb : 0x40000000 ≤ b.toNat) (hbl : b.toNat + l ≤ 2 ^ 32) : Sep (s + BitVec.ofNat 32 c) w b l :=
  lowSep (E.wS h) hb hbl

theorem RkEnv.lowF (E : RkEnv M0 M1 s out F P N g0) {c w : Nat} (h : c + w ≤ 0xAC0) {b : Word} {l : Nat}
    (hb : 0x40000000 ≤ b.toNat) (hbl : b.toNat + l ≤ 2 ^ 32) : Sep (F + BitVec.ofNat 32 c) w b l :=
  lowSep (E.wF h) hb hbl

theorem RkEnv.cF (E : RkEnv M0 M1 s out F P N g0) {c w : Nat} (h : c + w ≤ 0xAC0) :
    Sep (F + BitVec.ofNat 32 c) w TRK tufRoleKeysReadCode.length :=
  E.lowF h (by decide) (by decide)

theorem RkEnv.cS (E : RkEnv M0 M1 s out F P N g0) {c w : Nat} (h : c + w ≤ 3056) :
    Sep (s + BitVec.ofNat 32 c) w TRK tufRoleKeysReadCode.length :=
  E.lowS h (by decide) (by decide)

theorem RkEnv.oC (E : RkEnv M0 M1 s out F P N g0) : Sep out 0x540 TRK tufRoleKeysReadCode.length :=
  lowSep E.how (by decide) (by decide)

theorem RkEnv.oF (E : RkEnv M0 M1 s out F P N g0) {c w : Nat} (h : c + w ≤ 0xAC0) :
    Sep out 0x540 (F + BitVec.ofNat 32 c) w := by
  rw [E.Fc]; exact E.hso.subR (by omega)

theorem RkEnv.dF (E : RkEnv M0 M1 s out F P N g0) {c w : Nat} (h : c + w ≤ 0xAC0) :
    Sep (F + BitVec.ofNat 32 c) w P N := by
  rw [E.Fc]; exact E.hSP.sub (by omega)

theorem RkEnv.dS (E : RkEnv M0 M1 s out F P N g0) {c w : Nat} (h : c + w ≤ 3056) :
    Sep (s + BitVec.ofNat 32 c) w P N :=
  E.hSP.sub h

theorem RkEnv.sp (E : RkEnv M0 M1 s out F P N g0) (d : Nat) (hd : d ≤ 304) :
    s + BitVec.ofNat 32 d + BitVec.ofNat 32 (304 - d) = F := by
  rw [add_ofNat_assoc, ← E.hF]; congr 2; omega

theorem RkEnv.alS (E : RkEnv M0 M1 s out F P N g0) {d : Nat} (hd : d % 4 = 0) :
    (s + BitVec.ofNat 32 d).toNat % 4 = 0 :=
  aligned_add E.hal hd

/-- A change inside the frame below the saved registers. -/
theorem RkEnv.outF (E : RkEnv M0 M1 s out F P N g0) {Ma Mb : Word → BitVec 8} {c l : Nat}
    (h : Out Ma Mb (F + BitVec.ofNat 32 c) l) (hc : c + l ≤ 2700) : Out Ma Mb s 3004 := by
  rw [E.Fc] at h; exact h.widen (by omega)

theorem RkEnv.saveSep (E : RkEnv M0 M1 s out F P N g0) {c : Nat} (hc : 0x3C ≤ c) (hc' : c + 4 ≤ 0x70) :
    Sep s 3004 (F + 0xA50 + BitVec.ofNat 32 c) 4 := by
  rw [show F + 0xA50 = F + BitVec.ofNat 32 0xA50 from rfl, add_ofNat_assoc, E.Fc]
  exact tex_sepS (by omega) (by have := E.hsw; omega)

theorem RkEnv.code (E : RkEnv M0 M1 s out F P N g0) (hO : Out M1 Mk s 3004) : RkCode Mk :=
  E.hc.of_out (E.hO1.trans (fun x hx => hO x (tex_sepR hx (by decide)))) E.hsw E.hro

theorem RkEnv.savedS {Ma Mb : Word → BitVec 8} (E : RkEnv M0 M1 s out F P N g0) (hv : RkSaved (F + 0xA50) g0 Ma)
    (hO : Out Ma Mb s 3004) : RkSaved (F + 0xA50) g0 Mb := by
  obtain ⟨v0, v1, v2, v3, v4, v5, v6, v7, v8, v9, v10, v11, v12⟩ := hv
  exact ⟨(hO.load32 (E.saveSep (by decide) (by decide))).trans v0, (hO.load32 (E.saveSep (by decide) (by decide))).trans v1,
    (hO.load32 (E.saveSep (by decide) (by decide))).trans v2, (hO.load32 (E.saveSep (by decide) (by decide))).trans v3,
    (hO.load32 (E.saveSep (by decide) (by decide))).trans v4, (hO.load32 (E.saveSep (by decide) (by decide))).trans v5,
    (hO.load32 (E.saveSep (by decide) (by decide))).trans v6, (hO.load32 (E.saveSep (by decide) (by decide))).trans v7,
    (hO.load32 (E.saveSep (by decide) (by decide))).trans v8, (hO.load32 (E.saveSep (by decide) (by decide))).trans v9,
    (hO.load32 (E.saveSep (by decide) (by decide))).trans v10,
    (hO.load32 (E.saveSep (by decide) (by decide))).trans v11,
    (hO.load32 (E.saveSep (by decide) (by decide))).trans v12⟩

theorem RkEnv.saved (E : RkEnv M0 M1 s out F P N g0) (hO : Out M1 Mk s 3004) : RkSaved (F + 0xA50) g0 Mk :=
  E.savedS E.hv hO

theorem RkEnv.oSave (E : RkEnv M0 M1 s out F P N g0) {c : Nat} (hc : 0x3C ≤ c) (hc' : c + 4 ≤ 0x70) :
    Sep out 0x540 (F + 0xA50 + BitVec.ofNat 32 c) 4 := by
  rw [show F + 0xA50 = F + BitVec.ofNat 32 0xA50 from rfl, add_ofNat_assoc]; exact E.oF (by omega)

theorem RkEnv.savedOut {Mf Mf' : Word → BitVec 8} (E : RkEnv M0 M1 s out F P N g0) (hv : RkSaved (F + 0xA50) g0 Mf)
    (hO : Out Mf Mf' out 0x540) : RkSaved (F + 0xA50) g0 Mf' := by
  obtain ⟨v0, v1, v2, v3, v4, v5, v6, v7, v8, v9, v10, v11, v12⟩ := hv
  exact ⟨(hO.load32 (E.oSave (by decide) (by decide))).trans v0, (hO.load32 (E.oSave (by decide) (by decide))).trans v1,
    (hO.load32 (E.oSave (by decide) (by decide))).trans v2, (hO.load32 (E.oSave (by decide) (by decide))).trans v3,
    (hO.load32 (E.oSave (by decide) (by decide))).trans v4, (hO.load32 (E.oSave (by decide) (by decide))).trans v5,
    (hO.load32 (E.oSave (by decide) (by decide))).trans v6, (hO.load32 (E.oSave (by decide) (by decide))).trans v7,
    (hO.load32 (E.oSave (by decide) (by decide))).trans v8, (hO.load32 (E.oSave (by decide) (by decide))).trans v9,
    (hO.load32 (E.oSave (by decide) (by decide))).trans v10,
    (hO.load32 (E.oSave (by decide) (by decide))).trans v11,
    (hO.load32 (E.oSave (by decide) (by decide))).trans v12⟩

/-- Memory that agrees with `M1` outside the 3004 bytes at `s` agrees with
`M0` outside the 3056. -/
theorem RkEnv.agree (E : RkEnv M0 M1 s out F P N g0) (hO : Out M1 Mk s 3004) : ∀ x, Sep x 1 s 3056 → Mk x = M0 x :=
  fun x hx => (hO x (tex_sepR hx (by decide))).trans (E.hO1 x hx)

theorem RkEnv.bytes (E : RkEnv M0 M1 s out F P N g0) (hO : Out M1 Mk s 3004) {q : Word} {l : Nat}
    (hS : Sep s 3056 q l) : memBytes Mk q l = memBytes M0 q l :=
  memBytes_congr fun _ hi => E.agree hO _ (sep_pt hS hi)

/-- `memcpy` between two parts of the frame above its own 16 bytes. -/
theorem RkEnv.mcFF (E : RkEnv M0 M1 s out F P N g0) {M : Word → BitVec 8} (hc : RkCode M) {c d n : Nat}
    (h : c + n ≤ d ∨ d + n ≤ c) (hc0 : 16 ≤ c) (hd0 : 16 ≤ d) (hcn : c + n ≤ 0xAC0) (hdn : d + n ≤ 0xAC0) :
    McEnv M BMB (F + BitVec.ofNat 32 c) (F + BitVec.ofNat 32 d) (s + BitVec.ofNat 32 288) n :=
  ⟨hc.tps.bmb, E.lowF hcn (by decide) (by decide), E.lowS (by decide) (by decide) (by decide),
    E.fs (Or.inr (by omega)) hcn (by decide), E.fs (Or.inr (by omega)) hdn (by decide), rk_ff F h hcn hdn,
    E.alS (by decide), by have := E.wS (d := 288) (k := 16) (by decide); omega,
    by have := E.wF hcn; omega, by have := E.wF hdn; omega⟩

/-- `memcpy` from the frame to `out`. -/
theorem RkEnv.mcOF (E : RkEnv M0 M1 s out F P N g0) {M : Word → BitVec 8} (hc : RkCode M) {d n : Nat}
    (hd0 : 16 ≤ d) (hn : n ≤ 0x540) (hdn : d + n ≤ 0xAC0) :
    McEnv M BMB out (F + BitVec.ofNat 32 d) (s + BitVec.ofNat 32 288) n :=
  ⟨hc.tps.bmb, tex_sepL (lowSep E.how (by decide) (by decide)) hn, E.lowS (by decide) (by decide) (by decide),
    tex_sepL (E.hso.subR (c := 288) (l := 16) (by decide)) hn, E.fs (Or.inr (by omega)) hdn (by decide),
    tex_sepR (tex_sepL (E.oF hdn) hn) (Nat.le_refl _), E.alS (by decide),
    by have := E.wS (d := 288) (k := 16) (by decide); omega, by have := E.how; omega,
    by have := E.wF hdn; omega⟩

end

section
variable {M0 M1 Mf : Word → BitVec 8} {s out F P : Word} {N : Nat} {g g0 : Fin 32 → Word}

theorem rk_a5 (F : Word) : aluEval .add (aluEval .add F 0x2D0) 0x780 = F + 0xA50 := by
  rw [ev_add, ev_add, BitVec.add_assoc]; rfl

theorem rk_epi {R : (Word → BitVec 8) → Prop} (hsp : g sp = F) (hv : RkSaved (F + 0xA50) g0 Mf)
    (hsp0 : g0 sp = F + BitVec.ofNat 32 0xAC0) (hret : g0 ra &&& ~~~1 = g0 ra) (hal : F.toNat % 4 = 0)
    (hz0 : g0 0 = 0) (hfr : ∀ x, x ∉ rkE → g x = g0 x) (hR : R Mf) :
    WP tufRoleKeysReadCode TRK (RPost (g0 ra) R g0) Mf 0x8F2 g := by
  obtain ⟨e0, e1, e2, e3, e4, e5, e6, e7, e8, e9, e10, e11, e12⟩ := hv
  have hA : (F + 0xA50).toNat % 4 = 0 := aligned_add hal (k := 0xA50) (by decide)
  refine WP.aluImm rkr_at_8f2 ?_; wn
  refine WP.aluImm rkr_at_8f6 ?_; wn
  rw [hsp, rk_a5]
  refine WP.lw rkr_at_8fa (by rsimp; exact aligned_add hA (k := 0x6C) (by decide)) ?_; wn
  refine WP.lw rkr_at_8fe (by rsimp; exact aligned_add hA (k := 0x68) (by decide)) ?_; wn
  refine WP.lw rkr_at_900 (by rsimp; exact aligned_add hA (k := 0x64) (by decide)) ?_; wn
  refine WP.lw rkr_at_902 (by rsimp; exact aligned_add hA (k := 0x60) (by decide)) ?_; wn
  refine WP.lw rkr_at_906 (by rsimp; exact aligned_add hA (k := 0x5C) (by decide)) ?_; wn
  refine WP.lw rkr_at_90a (by rsimp; exact aligned_add hA (k := 0x58) (by decide)) ?_; wn
  refine WP.lw rkr_at_90e (by rsimp; exact aligned_add hA (k := 0x54) (by decide)) ?_; wn
  refine WP.lw rkr_at_912 (by rsimp; exact aligned_add hA (k := 0x50) (by decide)) ?_; wn
  refine WP.lw rkr_at_916 (by rsimp; exact aligned_add hA (k := 0x4C) (by decide)) ?_; wn
  refine WP.lw rkr_at_91a (by rsimp; exact aligned_add hA (k := 0x48) (by decide)) ?_; wn
  refine WP.lw rkr_at_91e (by rsimp; exact aligned_add hA (k := 0x44) (by decide)) ?_; wn
  refine WP.lw rkr_at_922 (by rsimp; exact aligned_add hA (k := 0x40) (by decide)) ?_; wn
  refine WP.lw rkr_at_926 (by rsimp; exact aligned_add hA (k := 0x3C) (by decide)) ?_; wn
  refine WP.aluImm rkr_at_92a ?_; wn
  refine WP.ret rkr_at_92e ⟨?_, hR, ?_⟩
  · rsimp; erw [e0]; rw [add_lit_zero, hret]
  refine frame_of (L2 := [ra, sp, 8, 9, 18, 19, 20, 21, 22, 23, 24, 25, 26, 27]) (by keepz hz0) fun x hx => ?_
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hx
  rcases hx with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> rsimp
  · exact e0
  · rw [hsp0, ev_add, ev_add, BitVec.add_assoc]; rfl
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

end

/-- The postcondition: return to the caller with `r` at `out`. -/
abbrev rkQ (M0 : Word → BitVec 8) (s out : Word) (g0 : Fin 32 → Word) (r : Except Nat (Nat × List RkEntry)) : Post :=
  RPost (g0 ra) (fun M' => RkRes M0 M' s out r) g0

section
variable {M0 M1 Mf : Word → BitVec 8} {s out F P : Word} {N : Nat} {g g0 : Fin 32 → Word} {e : Nat}

theorem rk_errRes (E : RkEnv M0 M1 s out F P N g0) (hO : Out M1 Mf s 3004) (b : BitVec 8) (hb : b = BitVec.ofNat 8 e) :
    RkRes M0 (memStore8 (memStore8 Mf out 0xFE) (out + 1) b) s out (.error e) ∧
      Out Mf (memStore8 (memStore8 Mf out 0xFE) (out + 1) b) out 0x540 := by
  have h1 : Sep out 1 (out + BitVec.ofNat 32 1) 1 := by
    have := sep_offsets out (c := 0) (n := 1) (d := 1) (k := 1) (Or.inl (by decide)) (by decide) (by decide)
    rwa [add_ofNat_zero] at this
  have hOo : Out Mf (memStore8 (memStore8 Mf out 0xFE) (out + 1) b) out 0x540 :=
    (((out_store8 _ _ _).mono (by decide)).trans ((out_store8 _ _ _).widen (d := 1) (by decide)))
  refine ⟨⟨fun x hx ho => (hOo x ho).trans (E.agree hO x hx), ?_, ?_⟩, hOo⟩
  · show memStore8 (memStore8 Mf out 0xFE) (out + BitVec.ofNat 32 1) b out = 0xFE
    rw [memStore8_ne (sep_byte0 h1 (by decide))]; exact memStore8_same _ _ _
  · rw [memStore8_same]; exact hb

/-- The error tail at 0x8E8: the tag 0xFE at `out`, the error byte from
`a0` at `out + 1`, and the epilogue. -/
theorem rk_8e8 (E : RkEnv M0 M1 s out F P N g0) (hO : Out M1 Mf s 3004) (h27 : g 27 = out) (hsp : g sp = F)
    (ha0 : (g a0).extractLsb' 0 8 = BitVec.ofNat 8 e) (hz : g 0 = 0) (hfr : ∀ x, x ∉ rkE → g x = g0 x) :
    WP tufRoleKeysReadCode TRK (rkQ M0 s out g0 (.error e)) Mf 0x8E8 g := by
  refine WP.aluImm rkr_at_8e8 ?_; wn
  refine WP.sb rkr_at_8ea (by (try rsimp); rw [h27, add_lit_zero]; exact tex_sepL E.oC (by decide)) ?_; wn
  refine WP.sb rkr_at_8ee (by (try rsimp); rw [h27]; exact E.oC.sub (c := 1) (l := 1) (by decide)) ?_; wn
  (try rsimp)
  rw [h27, add_lit_zero]
  try rw [show g x0 = 0 from hz]
  rw [show (aluEval .add 0 0xFFFFFFFE : Word).extractLsb' 0 8 = 0xFE by decide]
  obtain ⟨hR, hOo⟩ := rk_errRes E hO _ ha0
  exact rk_epi hsp (E.savedOut (E.saved hO) hOo) E.hsp0 E.hret E.halF E.hz0 (by keepz E.hz0) hR

/-- The error tails that load the error byte from the frame at `F + c`
and jump to 0x8E8. -/
theorem rk_8de (E : RkEnv M0 M1 s out F P N g0) (hO : Out M1 Mf s 3004) (h27 : g 27 = out) (hsp : g sp = F)
    (hb : Mf (F + 0x1C) = BitVec.ofNat 8 e) (hfr : ∀ x, x ∉ rkE → g x = g0 x) :
    WP tufRoleKeysReadCode TRK (rkQ M0 s out g0 (.error e)) Mf 0x8DE g := by
  refine WP.lbu rkr_at_8de ?_; wn
  refine WP.jal rkr_at_8e2 (by decide) ?_; wn
  exact rk_8e8 E hO (by rsimp; exact h27) (by rsimp; exact hsp) (by rsimp; rw [hsp, ri_ze]; exact hb) (by rsimp)
    (by keepz E.hz0)

theorem rk_8e4 (E : RkEnv M0 M1 s out F P N g0) (hO : Out M1 Mf s 3004) (h27 : g 27 = out) (hsp : g sp = F)
    (hb : Mf (F + 0x760) = BitVec.ofNat 8 e) (hfr : ∀ x, x ∉ rkE → g x = g0 x) :
    WP tufRoleKeysReadCode TRK (rkQ M0 s out g0 (.error e)) Mf 0x8E4 g := by
  refine WP.lbu rkr_at_8e4 ?_; wn
  exact rk_8e8 E hO (by rsimp; exact h27) (by rsimp; exact hsp) (by rsimp; rw [hsp, ri_ze]; exact hb) (by rsimp)
    (by keepz E.hz0)

theorem rk_93c (E : RkEnv M0 M1 s out F P N g0) (hO : Out M1 Mf s 3004) (h27 : g 27 = out) (hsp : g sp = F)
    (hb : Mf (F + 0x560) = BitVec.ofNat 8 e) (hfr : ∀ x, x ∉ rkE → g x = g0 x) :
    WP tufRoleKeysReadCode TRK (rkQ M0 s out g0 (.error e)) Mf 0x93C g := by
  refine WP.lbu rkr_at_93c ?_; wn
  refine WP.jal rkr_at_940 (by decide) ?_; wn
  exact rk_8e8 E hO (by rsimp; exact h27) (by rsimp; exact hsp) (by rsimp; rw [hsp, ri_ze]; exact hb) (by rsimp)
    (by keepz E.hz0)

theorem rk_94e (E : RkEnv M0 M1 s out F P N g0) (hO : Out M1 Mf s 3004) (h27 : g 27 = out) (hsp : g sp = F)
    (hb : Mf (F + 0x75D) = BitVec.ofNat 8 e) (hfr : ∀ x, x ∉ rkE → g x = g0 x) :
    WP tufRoleKeysReadCode TRK (rkQ M0 s out g0 (.error e)) Mf 0x94E g := by
  refine WP.lbu rkr_at_94e ?_; wn
  refine WP.jal rkr_at_952 (by decide) ?_; wn
  exact rk_8e8 E hO (by rsimp; exact h27) (by rsimp; exact hsp) (by rsimp; rw [hsp, ri_ze]; exact hb) (by rsimp)
    (by keepz E.hz0)

/-- The error tail at 0x930: error 0x21. -/
theorem rk_930 (E : RkEnv M0 M1 s out F P N g0) (hO : Out M1 Mf s 3004) (h27 : g 27 = out) (hsp : g sp = F)
    (hfr : ∀ x, x ∉ rkE → g x = g0 x) :
    WP tufRoleKeysReadCode TRK (rkQ M0 s out g0 (.error 0x21)) Mf 0x930 g := by
  refine WP.lui rkr_at_930 ?_; wn
  refine WP.aluImm rkr_at_932 ?_; wn
  refine WP.sh rkr_at_936 (by (try rsimp); rw [h27, add_lit_zero]; have := E.halo; omega)
    (by (try rsimp); rw [h27, add_lit_zero]; exact tex_sepL E.oC (by decide)) ?_; wn
  refine WP.jal rkr_at_93a (by decide) ?_; wn
  (try rsimp)
  rw [h27, add_lit_zero]
  unfold memStore16
  rw [show (aluEval .add 0x2000 0x1FE : Word).extractLsb' 0 8 = 0xFE by decide,
    show (aluEval .add 0x2000 0x1FE : Word).extractLsb' 8 8 = BitVec.ofNat 8 0x21 by decide]
  obtain ⟨hR, hOo⟩ := rk_errRes E hO _ rfl
  exact rk_epi hsp (E.savedOut (E.saved hO) hOo) E.hsp0 E.hret E.halF E.hz0 (by keepz E.hz0) hR

/-- The error tail at 0x942, with the error byte in `s0`. -/
theorem rk_942 (E : RkEnv M0 M1 s out F P N g0) (hO : Out M1 Mf s 3004) (h27 : g 27 = out) (hsp : g sp = F)
    (h8 : (g 8).extractLsb' 0 8 = BitVec.ofNat 8 e) (hz : g 0 = 0) (hfr : ∀ x, x ∉ rkE → g x = g0 x) :
    WP tufRoleKeysReadCode TRK (rkQ M0 s out g0 (.error e)) Mf 0x942 g := by
  refine WP.aluImm rkr_at_942 ?_; wn
  refine WP.sb rkr_at_944 (by (try rsimp); rw [h27, add_lit_zero]; exact tex_sepL E.oC (by decide)) ?_; wn
  refine WP.sb rkr_at_948 (by (try rsimp); rw [h27]; exact E.oC.sub (c := 1) (l := 1) (by decide)) ?_; wn
  refine WP.jal rkr_at_94c (by decide) ?_; wn
  (try rsimp)
  rw [h27, add_lit_zero]
  try rw [show g x0 = 0 from hz]
  rw [show (aluEval .add 0 0xFFFFFFFE : Word).extractLsb' 0 8 = 0xFE by decide]
  obtain ⟨hR, hOo⟩ := rk_errRes E hO _ h8
  exact rk_epi hsp (E.savedOut (E.saved hO) hOo) E.hsp0 E.hret E.halF E.hz0 (by keepz E.hz0) hR

/-- The success tail at 0x954: copy the keys at `F + 0x18` to `out`, and
the epilogue. -/
theorem rk_954 {t : Nat} {es : List RkEntry} (E : RkEnv M0 M1 s out F P N g0) (hO : Out M1 Mf s 3004)
    (h27 : g 27 = out) (hsp : g sp = F) (hfr : ∀ x, x ∉ rkE → g x = g0 x)
    (hK : RkAt Mf (F + 0x18) t es) :
    WP tufRoleKeysReadCode TRK (rkQ M0 s out g0 (.ok (t, es))) Mf 0x954 g := by
  have hc := E.code hO
  refine WP.aluImm rkr_at_954 ?_; wn
  refine WP.aluImm rkr_at_956 ?_; wn
  refine WP.alu rkr_at_95a ?_; wn
  refine WP.callMemcpy (dst := out) (src := F + 0x18) (F := s + BitVec.ofNat 32 288) (N := 0x540)
    rkr_at_95c rkr_at_960 (by decide) (by decide) (by decide) hc.tps.bms (E.mcOF hc (d := 0x18) (by decide)
      (by decide) (by decide))
    (by rsimp; rw [ev0]; exact h27) (by rsimp; rw [hsp]; try rfl) (by rsimp; try rfl) (by rsimp; rw [hsp]; exact (E.sp 288 (by decide)).symm)
    (E.cS (by decide)) E.oC fun m2 hm => ?_
  wn
  refine WP.jal rkr_at_964 (by decide) ?_; wn
  have hO1' : Out Mf (copyBytes Mf out (F + 0x18) 0x540) out 0x540 := fun x hx => copyBytes_sep hx.symm (Nat.le_refl _)
  have hO2 : Out (copyBytes Mf out (F + 0x18) 0x540) m2.mem s 3004 := hm.widen (by decide)
  have hv := E.savedS (E.savedOut (E.saved hO) hO1') hO2
  refine rk_epi (by rsimp; exact hsp) hv E.hsp0 E.hret E.halF E.hz0 (by keepz E.hz0) ⟨fun x hx ho => ?_, ?_⟩
  · rw [hO2 x (tex_sepR hx (by decide)), hO1' x ho]; exact E.agree hO x hx
  · refine RkB.congr hK fun o ho => ?_
    show m2.mem (out + BitVec.ofNat 32 o) = Mf (F + 0x18 + BitVec.ofNat 32 o)
    rw [hm _ ((E.hso.subR (c := 288) (l := 16) (by decide)).sub (c := o) (l := 1) (by omega)),
      copyBytes_at ho (by decide)]

end

end C3.RV32
